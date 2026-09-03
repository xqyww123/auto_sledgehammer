# Proof store 双键改造：proof id 之外再带一把可选的 goal hash

记于 2026-09-03，**rev 5**。本文收录作者在本轮讨论中做出的全部裁决，是实施的唯一依据。
凡本文未写的行为，一律保持现状。

评审史：rev 1 至 rev 4 各经一轮两回合对抗评审（4 质问 + 合并 + 逐条辩护 + 裁判，全部 Opus 5）。
第四轮裁判确认 rev 4 的实质设计（`by_hash` 只增不删、单一删除入口）成立。
rev 4 → rev 5 的变化：
① `auto` / `all_auto` 的三步查找写成**一个**共用局部函数，唯一的区分参数是"要解决的子目标数 k"（§2 裁决 R、§3.4）；
② `by_hash` 的值改存 `proof_cache`（时间与文本），不再存整条记录（§2 裁决 E、F）；
③ `A cached proof fails. Re-searching proofs...` 这句留在搜索入口不动，`stale` 保留为只用于选消息的布尔（§2 裁决 N、§3.4）；
④ "本次调用中已试过且失败的记录不再重放"作为一条统一规则，在 `store_hit_replay` 的第 2、3 步之前各查一次；
   比较的是整条 `(time, text)`，不只是文本（§3.4）；
⑤ §3.4 写明 `do_read` 开关覆盖第 1、2 步，`sledgehammer_solver.ML:50-55` 的 `options` 注释列入改写清单；
⑥ `invalidate_proof_cache_by_hash` 的实现体写明（§3.3）；
⑦ 测试补齐：能察觉墓碑与按 hash 作废被漏掉的测试、跳过规则的正反两向、驱动 `hammer_or_AoA` 的测试、
   测试 8/14 去掉 `scan` 表达不出的"tag 3"断言、测试 10/11/13 的记录可区分、测试 17 首个 goal 须 `simp` 可解（§4）。
评审中被作者驳回或延后的意见见 §6。

rev 5 → rev 6（实施完成后的代码评审，2026-09-03；实施提交 auto_sledgehammer `a9c1b0b`、Isa-Mini `59099f0`）：
① 裁决 O 的短路判据从"文本相同、hash 相同"放宽为**整条记录相同**（时间也相同）：被跳过的写入因此对该 id
   是真正的空操作，它要追加的帧是冗余的（§2、§3.3；rev 6 初稿还写了"`by_hash` 不会落后于写入序列"，
   那句话不成立，见 §3.3）；
② `replay_store` 的参数记录缩为 `{do_read, id, hash}`，`thy` 与 `kws` 由它收到的 `ctxt` 推出（§3.4）；
③ 晋升写入的时间语义统一为"晋升是复制"：`record` 只接收已归一的标准机器时间，搜索现场调用它之前自己做
   `standard_time`，按 hash 命中时以取回的记录原样写入，与 `store_hit_replay` 的 `write_l2` 一致（§3.4）；
④ 测试 19 不再要求 G₁ 是 `simp` 不可解的，判别点是逐字文本；新增测试 12b、16b、16c、17b、19c、20b、22b（§4）；
⑤ `try_cached_proof_by_hash_with_key` 是否也读第二把键，延后为独立议题（§6）。

前置工作已完成并提交：`Hasher.digest` 从十六进制字符串改为 `Word64.word`
（auto_sledgehammer 提交 `3be3ce8`，Isa-Mini 跟进提交 `e6c8318`；主仓库 `5ac2ca43` 只推进了 Isa-Mini 的指针，
auto_sledgehammer 的指针随实施提交在主仓库 `6cfefde3` 一起推进）。

行号以 `library/cache_file.ML`、`library/sledgehammer_solver.ML`、`Isa-Mini/Agent/agent_server.ML`、
`Isa-Mini/Agent/proof_store_AoA.ML` 在上述提交之后的状态为准。

---

## 0. 术语表

本文只用下面这些词，同一概念全文一个名字。

| 术语 | 含义 |
| --- | --- |
| **proof store** | 每个 theory 一个的磁盘文件 `<theory>.proof-store`，追加日志；UNIFIED_KEY_MINT_PLAN 里称 **L2** |
| **记录** | proof store 里的一条 PUT，含 proof id、goal hash（可选）、标准机器时间、证明文本 |
| **帧** | 记录在文件里的物理外壳：magic、长度、CRC-32、MessagePack 载荷 |
| **tag** | 载荷二元数组的第一个元素，整数，决定载荷第二个元素的形状 |
| **proof id** | 第一把键，`string`；调用方给的具名键，或 goal hash 的十六进制串 |
| **goal hash** | 第二把键，`Hasher.digest = Word64.word`；由 `Hasher.goal_at` / `Hasher.all_goals` 算出 |
| **内存表** | `openning_stores` 里一个 theory 的条目所含的 `store` 值 |
| **hash 表** | 内存表里以 goal hash 为键的那张表（`by_hash`），`Hasher.Tab`（平衡 2-3 树，O(log n)） |
| **墓碑** | 删除某个 proof id 的动作：内存表 `proofs` 删除该 id，文件追加一条 `TOMB id` 帧 |
| **按 hash 作废** | 删除 `by_hash` 中某个 hash 的项的动作，只动内存，不写帧 |
| **L1** | Isa-Mini 侧经 Python RPC 访问的 SQLite（`IsaMini.proof_store`），键与 L2 同为 proof id 字符串；本文不改它的内容与接口 |
| **晋升** | 按 hash 命中且重放成功后，把该证明以**当前** proof id 再写一条记录（带同一个 hash） |
| **已失败记录** | 本次调用中已经重放过且失败的 `(time, text)` 对；同一对不再重放 |

---

## 1. 问题

今天 proof store 只有一把键（proof id）。goal hash 只活在一张进程全局的内存表
`hash_cache`（`cache_file.ML:803`）里，从不落盘。它的用途（签名注释 `:162-167`）
是：用户在某条 lemma 之前编辑代码，具名键整体位移，但命题没变、hash 没变，于是不用重搜。
这层保护只在一个进程内有效，重启即空。

另有一个副作用：`hash_cache` 是全局的且从不回收，session 构建结束时随 heap 整体存盘
（`ML_Heap.save_child` 就是 `PolyML.SaveState.saveChild`，不做筛选；本轮用一个最小
实验实测确认：`Synchronized.var` 里写入的键值对在子 heap 被新进程加载后原样读回）。
于是一次构建中新搜出来的所有证明文本，包括几十万字符的 AoA 载荷，都进了 heap 并沿父链继承。

---

## 2. 裁决清单

编号沿用讨论中的编号，便于回溯。

| # | 事项 | 裁决 |
| --- | --- | --- |
| A | 第二把键的来源 | **由调用方在 `update_cached_proof` 里显式传入**，`Phi_Proof_Store` 内部永不自己算 hash。hash 不是独立的写入动作，它是记录的一个字段，随记录一起落盘，受现有 `write_store` / `enable_proof_store` 门控；读取同理受 `read_store` 门控，不设新开关 |
| B | `update_cached_proof` 的形状 | 记录参数，字段名写全：`theory -> {id: proof_id, hash: Hasher.digest option} -> proof_cache -> unit`。**hash 保持 option**：现有调用方都有 digest，但接口为未来没有 hash 的调用方留门（§6） |
| C | hash 的类型 | `Hasher.digest = Word64.word`，透明；`Hasher.hex` 是它变成字符串的唯一出口；`Hasher.Tab` 是以它为键的表。**已落地** |
| D | 磁盘编码 | 新增 **tag 3**，载荷 `[3, [id, hash_or_nil, time_ms, proof]]`，hash 用 MessagePack uint64，缺席用 nil。tag 1 继续能读，读成 `hash = NONE`；写入只产生 tag 3 与 tag 2。**不假设旧版本二进制会读新文件**（§6） |
| E | hash 表的归属（rev 5 改） | 并入内存表：`store` 增加 `by_hash : proof_cache Hasher.Tab.table`，值是 `(time, text)`，不含 hash；全局 `hash_cache` 及 `access_hash_cache` / `update_hash_cache` / `clean_hash_cache` **删除**。**不用线性扫描代替这张表**（§6） |
| F | hash 表的语义（rev 5 改） | `by_hash` **只增不删**：写入时更新（后写覆盖先写），墓碑不碰它，压缩不碰它，本身永不序列化；唯一的删除入口是 `invalidate_proof_cache_by_hash`（裁决 Q）。值里没有 hash 字段，所以"值与键不一致"无从发生。**不保证**它交出的证明仍在 `proofs` 里；这是安全的，因为每次 hash 命中都先重放验证再使用，失败不写帧（裁决 I） |
| G | 按 hash 的查询接口 | `get_cached_proof_by_hash : theory -> Hasher.digest -> proof_cache option`，一次 `Hasher.Tab.lookup`，无投影 |
| H | 一个 hash 多条记录 | 后写覆盖先写，单值；不用列表。多条同 hash 活记录经压缩、重载后谁在表里**不作规定**（§3.2） |
| I | hash 命中但重放失败 | 不打墓碑、**不追加任何帧**；调 `invalidate_proof_cache_by_hash` 删掉这一项，然后落到下一步 |
| J | 旧记录自愈 | **不做**。旧记录 hash 为 `NONE`，只能按 id 命中，不补写 |
| K | 一次性迁移脚本 | **不写**。tag 1 的解码规则即迁移；压缩时按 tag 3 重写 |
| L | L1 是否跟进 | **另立议题**。本方案不改 L1 的键、内容与三个 RPC |
| M | 压缩是否保序 | 不需要 |
| N | 墓碑的时机（rev 5 改） | 在**检测到 id 重放失败的那一刻**打，早于 hash 分支与搜索。`stale` 布尔**保留**为 `replay_store` 的局部变量，只剩一个用途：返回 `NONE`（即接下来搜索）之前据它选择打印 `A cached proof fails. Re-searching proofs...` 还是 `Proof store miss`；它不再决定墓碑 |
| O | `live_and_identical` 的判据 | "同一 id 下已有活记录，且**整条记录相同**（证明文本、hash、时间）"才短路（rev 6 放宽，原为文本与 hash 相同）；任何一项变了的重写照常经规则 1 落盘 |
| P | phi / AoA 义务路径的读取（rev 5 改） | `store_hit_replay` 的查找顺序定为 **L2 按 id → L2 按 hash → L1 按 id**；按 hash 命中且重放成功则晋升到当前 key 下，**晋升只写 L2、不写 L1**；已失败记录在第 2、3 步之前都不再重放；`hammer_or_AoA` 里 hash 的计算保留 `if read orelse write then SOME (…) else NONE` 这一行 |
| Q | 按 hash 作废的接口 | `invalidate_proof_cache_by_hash : Hasher.digest -> theory -> unit`，只删 `by_hash[h]`，不碰 `proofs`，不写帧，不打印。`invalidate_proof_cache` 的签名**不变**，不加 hash 参数（§6） |
| R | `auto` 与 `all_auto` 的三步查找（rev 5 新增） | 写成**一个**共用局部函数，唯一的区分参数是要解决的子目标数 `k`（`auto` 为 1，`all_auto` 为 `nprem`）；`record` 与 `search` 仍留在各自入口（§3.4） |

登记不处理：`Hasher` 的配方一变，所有已存的第二把键一起失效，效果等同全部 `NONE`，
只漏命中不会错命中；不引入配方版本号字段。

---

## 3. 设计

### 3.1 记录与磁盘编码（`Proof_Store_Format`，`cache_file.ML:27-134`）

格式层只负责**字节与记录之间的转换**：帧、CRC、`scan`。把记录折叠成内存表不是它的事，
`replay`（`:129-132`）**下移**进 `Phi_Proof_Store`（§3.2 规则 3）。这样格式层不需要认识
`Hasher.Tab` 与 `Task_Queue.task`，仍是纯函数。`Hasher.ML` 先于 `cache_file.ML` 加载
（`Auto_Sledgehammer.thy:22-23`），记录里可以直接写 `Hasher.digest`。

datatype 只保留一个 PUT 构造子，旧格式只存在于解码器：

```sml
datatype record =
    PUT of {id: string, hash: Hasher.digest option, time_ms: int, proof: string}
  | TOMB of string
```

编码（`encode_record`）：

| 值 | 载荷 |
| --- | --- |
| `PUT {id, hash, time_ms, proof}` | `[3, [id, hash_or_nil, time_ms, proof]]`，`hash_or_nil` 经 `packOption packWord64` |
| `TOMB id` | `[2, id]`（不变） |

解码（`rec_unpacker`）：

| tag | 载荷第二元素 | 解成 |
| --- | --- | --- |
| 1 | `[id, time_ms, proof]` | `PUT {id, hash = NONE, time_ms, proof}` |
| 2 | `id` | `TOMB id` |
| 3 | `[id, hash_or_nil, time_ms, proof]` | `PUT {...}`，`hash_or_nil` 经 `unpackOption unpackWord64` |
| 其他 | | `raise U.Unpack`（帧被跳过，现状） |

解码之后没有 tag 字段：tag 1 帧与"hash 为 nil 的 tag 3 帧"解成同一个值。编码器只会产生 tag 3
与 tag 2。tag 1 的解码支持**永久保留**：`phi-system/tools/proofstore-merge.sh` 这个 git 合并驱动
把两个文件直接拼接，从旧分支合并进来的帧随时可能是 tag 1，它是长期存在的生产输入。

`encode_put`（`:92`）的参数改为记录；`is_new_format`、`frame`、`scan` 不变。文件顶部 `:3-26`
的格式说明注释同步改写（增加 tag 3 一行，说明 tag 1 只读；删去对 `replay` 的描述）。

### 3.2 内存表（`PHI_PROOF_STORE`）

```sml
type proof_id = string
type proof_cache = Time.time * string
type proof_record = {hash: Hasher.digest option, time: Time.time, proof: string}
type store = {proofs: proof_record Symtab.table,        (* proof id -> 记录，与文件一致 *)
              by_hash: proof_cache Hasher.Tab.table,    (* goal hash -> (time, text)，只增不删 *)
              async_tasks: Task_Queue.task list}
```

- `proofs` 的记录必须带 hash：压缩（`write_state_new`，`:319`）从 `proofs` 重写文件，
  不带就会把第二把键写丢。
- `by_hash` 的值是 `(time, text)`：它唯一的读者 `get_cached_proof_by_hash` 返回的就是这个类型，
  晋升用的 hash 来自查询的键而不是值，所以值里的 hash 字段无人读取，不存。证明文本仍与 `proofs`
  里的记录共享（ML 字符串是引用），不共享的只是记录外壳这一个小单元。

**四条规则加一条作废规则。** `proofs` 与 `by_hash` 的一切改动只经过规则 1、2、Q：

1. **写入** `store_update_proof (id, rec)`（`:223`）：写 `proofs[id] = rec`；若 `#hash rec` 是
   `SOME h`，写 `by_hash[h] = (#time rec, #proof rec)`，后写覆盖先写。**不删**旧记录的 hash 项：
   被覆盖的旧文本仍然是它自己那个 hash 的有效证明。
2. **墓碑** `store_invalidate_proof id`（`:227`）：只删 `proofs[id]`，`by_hash` 不碰。
   `async_tasks = []`（`:232`）原样保留。
3. **加载** `replay : record list -> store`（从格式层下移到这里）：从 `empty_store` 起按文件
   顺序折叠，PUT 帧走规则 1，TOMB 帧走规则 2。**`replay` 是全函数**：它不抛异常；若它抛了，
   那是 bug，必须让调用方中止（`compact_store` 自己的守卫会把结果降级为 `confirmed`、文件
   原样不动），绝不能退化成空表再被压缩写回。
4. **生命周期**：随 `openning_stores` 条目走。`close_store`（`:637`）与 `invalidate_store`
   （`:653`）整个丢掉；`force_reload`（`:599`）从文件重建。关于 heap 的如实表述：
   `Theory.at_end`（`:781-795`）只等经 `register_async_task` 登记的任务，登记者只有
   auto_sledgehammer 自己的三处（`sledgehammer_solver.ML:986`、`:1948`、`:2040`），所以证明全部
   经 auto_sledgehammer 的 theory，其条目在 session 存 heap 前已被 `close_store` 丢掉
   （`Session.finish` 先 `Future.shutdown`）。Isa-Mini AoA 路径上的两个写回 fork
   （`agent_server.ML:1913-1927`、`:2129-2143`）未登记，可能在 `close_store` 之后把条目重新
   插回（`cache_file.ML:774-780` 的注释已记载），这是既有状况，本方案既不制造也不放大。
   本方案**无条件**消灭的是 §1 那份全局 `hash_cache` 的泄漏（裁决 E）。

Q. **按 hash 作废** `store_forget_hash h`：只删 `by_hash[h]`（`Hasher.Tab.delete_safe`，键不存在时
   无操作），`proofs` 不碰。只由 `invalidate_proof_cache_by_hash` 调用，而它只在"按 hash 命中、
   重放失败"时被调用。

**`by_hash` 派生自记录序列，不是当前表。** 加载后 `by_hash` 含文件里每条带 hash 的 PUT 帧，
包括已被后面的 TOMB 帧覆盖的那些；压缩按 `proofs` 的键序（proof id 字典序，`Symtab.fold` 升序、
`write_state_new` 前插，落盘为降序）重写文件而不是按写入先后，所以多条同 hash 的活记录在压缩、
重载之后谁留在 `by_hash` 里不作规定（裁决 H）。每次 hash 命中都先重放验证，所以"谁在表里"
最多影响一次多余重放。

**进程异常死亡的残留。** 打了墓碑但 theory 未结束（未压缩）时进程死掉，文件里留着"PUT 加 TOMB"；
下次加载时 TOMB 帧只删 `proofs`，`by_hash` 里仍有那条。它按 hash 被取回时会重放一次，失败
则经裁决 I 作废，最多一次有预算上限的多余重放；theory 正常结束一次，压缩就把这两帧清掉。

**为什么墓碑不能删 hash 项（级联例子，rev 3 的缺陷）。** 义务 O₁、O₂、O₃ 在键 K₁、K₂、K₃，记录
(P₁,h₁)、(P₂,h₂)、(P₃,h₃)。前面插入一条新义务 O₀ 后，O₀ 占 K₁，O₁ 挪到 K₂，依此类推，命题与 hash
不变。若墓碑删掉被删记录的 hash 项：O₀ 按 K₁ 命中 (P₁,h₁) 失败，墓碑删 `by_hash[h₁]`；O₁ 按 K₂
命中 (P₂,h₂) 失败，墓碑删 `by_hash[h₂]`，再按 h₁ 查，上一步已删，重搜；O₂、O₃ 同理，全部重搜。
若改为删调用方自己的 hash：O₁ 在 K₂ 失败时删 `by_hash[h₁]`，删掉的正是它下一步要查的自己的证明，
同样重搜。第 1 步（按 id）的失败说明的只是"K 下那条证明不属于现在坐在 K 的义务"，对任何 hash 项
都没有说什么；只有第 2 步（按 hash 取回 P、对当前 goal 重放）失败才说明"P 对 h 不好用"，所以
`by_hash` 的删除只能挂在第 2 步的失败上（裁决 I、Q）。

**随之改变的四个内部函数：**

| 函数 | 现状 | 改为 |
| --- | --- | --- |
| `read_file_state_exn path`（`:297-303`） | 返回 `proof_cache Symtab.table`；`\<^try>` 包住 `replay (scan raw)` 整体 | 返回 `store`：不是文件 → `empty_store`；否则读原文，`is_new_format` 则 `replay (\<^try>\<open>scan raw catch _ => []\<close>)`，否则 `empty_store`；`async_tasks = []`。**catch-all 只包 `scan`**：`scan` 已逐帧吞解码错误（`:122-124`），`replay` 是全函数，它的异常必须上抛（规则 3） |
| `read_file_state path`（`:306-307`） | I/O 失败退化为空表 | 不变形状：`\<^try>\<open>read_file_state_exn path catch _ => empty_store\<close>`，纯读路径仍退化为冷缓存 |
| `load_store_raw thy`（`:594-597`） | 包一层 `{proofs = …, async_tasks = []}` | 直接返回 `read_file_state path` |
| `write_state_new path proofs`（`:319`） | 输入 `proof_cache Symtab.table` | 输入 `proof_record Symtab.table`，**每条记录的 `hash` 字段原样写入**；`compact_store`（`:550`）与 `migrate_legacy`（`:500`）传 `#proofs (read_file_state_exn …)` |

`:275-296` 那段说明两个读取器的注释同步改写："a decode failure degrades to empty" 这一句只指
`scan`。`empty_store`（`:219`）增加 `by_hash = Hasher.Tab.empty`；`store_add_async`（`:235`）透传。

### 3.3 签名变化

删除：

```sml
val access_hash_cache : Hasher.digest -> proof_cache option
val update_hash_cache : Hasher.digest -> proof_cache -> unit
val clean_hash_cache  : unit -> unit
```

以及实现里的 `hash_cache`（`:803-814`）。签名 `:162-167` 那段"另一套机制"的注释删除，
改为一句：hash 表是内存表的一部分，只增不删，见本文 §3.2。

改动：

```sml
val update_cached_proof : theory -> {id: proof_id, hash: Hasher.digest option} -> proof_cache -> unit
```

新增：

```sml
val get_cached_proof_by_hash        : theory -> Hasher.digest -> proof_cache option
val invalidate_proof_cache_by_hash  : Hasher.digest -> theory -> unit
```

`invalidate_proof_cache_by_hash` 的实现体：

```sml
fun invalidate_proof_cache_by_hash h thy =
  Synchronized.change openning_stores
    (Symtab.map_entry (Context.theory_name {long=true} thy)
       (fn (c, f, w) => (store_forget_hash h c, f, w)))
```

它只**收窄**一个已存在的条目：不调 `migrate_legacy`，不经 `get_store_i` / `get_entry_i`，不创建条目，
不做可写性探测，不写帧，不打印。它只可能在 `get_cached_proof_by_hash` 返回 `SOME` 之后被调用；若条目
此时已被 `close_store` 丢掉，`map_entry` 的空操作是正确的，因为 `by_hash` 只在内存里、下次加载从记录
序列重建。`migrate_legacy` 的调用点保持今天的五处不变（`:600`、`:620`、`:625`、`:694`、`:733`），
`:484-488` 那段 D44 注释仍字面成立。参数顺序（键在前、theory 在后）与 `invalidate_proof_cache` 一致。

不变：`get_cached_proof`、`invalidate_proof_cache`（签名 `bool -> proof_id -> theory -> unit`
不加 hash 参数）、`get_store`、`force_reload`、`register_async_task`、`compact_and_store`、
`close_store`、`invalidate_store`、`store_path`、`standard_time`、`tolerant_time`、
`try_cached_proof_by_hash(_at)`、`enable_proof_store`。`get_cached_proof` 的返回仍是
`proof_cache option`：从记录取 `(time, proof)`，hash 不外露。`store` 类型虽导出，仓库内没有任何
模块解构它（`#proofs`、`#async_tasks`、`get_store` 在 cache_file.ML 之外零使用）。

`update_cached_proof` 的实现（`:693-723`）：

- `live_and_identical`（`:703-706`）按裁决 O 改为 `Symtab.lookup (#proofs c) id = SOME r`，r 是本次要写的
  整条记录（rev 6：连时间一起比）。撞键守卫不受影响：`proof_mark`（`:576`）只摘要文本，同文本换 hash 或换
  时间得到同样的摘要，不会误报；逐字节相同的重复写入仍被短路，而被短路的写入对该 id 是真正的空操作，
  它要追加的帧是冗余的。**这不意味着 `by_hash` 与写入序列一致**：短路按 id 判断，`by_hash` 跨 id 只存
  一个值。反例：写 {A, h}(t, P)，再写 {B, h}(t2, Q)，再写 {A, h}(t, P)——第三次因 A 名下记录逐字节相同而
  短路，`by_hash[h]` 停在 (t2, Q)。所以 `by_hash[h]` 是"最近一次**没被短路**的、带 h 的写入"，多个 id 共用
  一个 hash 时留下哪条不作规定（裁决 H），每次按 hash 命中都先重放验证，签名注释照此措辞。
- `written` 表与撞键守卫其余部分不变；追加的帧由 `encode_put` 按新记录编码。

### 3.4 调用点清单

**`auto`（`sledgehammer_solver.ML:1904-1995`）与 `all_auto`（`:1997-2082`）的三步查找**
（裁决 N、I、Q、R）。今天两处的查找代码（`:1951-1994` 与 `:2043-2079`）逐字相同，只差四处：
tracing 标签、交给 `eval_prf_str` 的 protect 数（1 / `nprem`）、成功判据（`nprems_of sequent' < nprem`
/ `no_prems sequent'`）、命中时带出的值（文本 / `(time, 文本)`）。这四处都是"处理 1 个子目标"与
"处理全部 `nprem` 个子目标"的影子：令 `k` 为要解决的子目标数，protect 数就是 `k`，成功判据就是
`nprems_of sequent' <= nprem - k`（`k = 1` 时即 `< nprem`，`k = nprem` 时即 `= 0`），tracing 标签
由 `k` 推出或干脆统一，`record` 两处类型相同（`Time.time * string -> unit`）。

于是在 `:1850-2082` 那个已有的 `local … in` 块里加一个共用函数（与 `after`、`scoped` 同列）：

```sml
(*The three-step lookup shared by auto and all_auto; k = how many leading
  subgoals the cached text must close (1, or all of them).  SOME on a hit
  that replays; NONE means: search -- and the message announcing that is
  printed here, where it is known why.*)
fun replay_store k record {do_read, id, hash} (ctxt, sequent)
  : ((Time.time * string) * (Proof.context * thm)) option
```

参数记录只有三个字段（rev 6）：`thy` 与 `kws` 都由它收到的 `ctxt` 推出，ctxt / thy / kws 不一致因此
不可表达；`kws` 在两个入口除了传给它之外再无用处。返回值原样是 `eval_prf_str` 的结果，所以其中的
时间是本次重放的实测，不是记录里存的预算。

`auto` 拿到结果后只取文本，与它今天在 `:1982` 做的一样；`all_auto` 取整对。`record` 与 `search`
仍留在各自入口，它们的差异是实质的（`Leading` / `Each_Goal`，单段文本 / 拼接文本），本方案不并。
**`record` 的契约（rev 6）：只接收已归一的标准机器时间。** 两个搜索现场在调用它之前自己做
`standard_time`；按 hash 命中的晋升以取回的记录 `s` 原样调用 `record s`，即"晋升是复制"，记录里的
预算随文本一起搬到当前 id 下，与 `store_hit_replay` 的 `write_l2` 同一条规则。
`stale` 是这个函数的**局部变量**：返回 `NONE` 就意味着调用方接下来必然搜索，所以第 3 步入口的那两句
消息由这个函数在返回 `NONE` 之前自己打印，不需要把 `stale` 传出去。

函数体，**整体包在一个 `if do_read` 里**（今天是 `:1955` / `:1973` 与 `:2045` / `:2060` 两处分开判断；
一处判断不会被删掉一半），`do_read` 为假时直接返回 `NONE`：

1. 按 id 查（`get_cached_proof thy id`）。命中且重放成功 → `SOME`。命中但重放失败 →
   **立刻** `invalidate_proof_cache true id thy`（它自己打印 `Proof cache for theory X is outdated!`
   并追加墓碑，只作废第一把键），`stale := true`，把失败的 `(time, text)` 记为已失败记录，继续第 2 步。
   未命中 → 继续第 2 步。
2. 按 hash 查（`get_cached_proof_by_hash thy hash`）。未命中 → `NONE`。命中：若它等于已失败记录
   （**时间与文本都相同**：重放预算 `tolerant_time` 由记录的时间决定，同文本不同时间是两次不同的
   重放），不重放，直接视为失败；否则重放。重放成功 → `record s`（把取回的记录原样晋升到当前 id 下，
   带同一个 hash）→ `SOME`。失败 → `invalidate_proof_cache_by_hash hash thy`（只作废第二把键，不追加任何帧），
   `stale := true` → `NONE`。

返回 `NONE` 之前按 `stale` 选消息打印，**这两行今天的文字原样不动**，只是从调用方的搜索入口搬进
函数的 `NONE` 出口（两处等价：`NONE` 当且仅当接下来搜索）：

```sml
if stale then warning "A cached proof fails. Re-searching proofs..."
else tracing ("Proof store miss, " ^ id)
```

调用方拿到 `NONE` 后直接 `search ()`。`stale` 从此只有这一个用途，不再决定墓碑（墓碑在第 1 步当场打）。`:1968-1971` 那段注释
（"Finding an entry marks the situation stale either way"）删除。搜索成功后 `record` 以同一个 hash
写入，规则 1 的后写覆盖先写会把 `by_hash[hash]` 指向新证明。

`sledgehammer_solver.ML:50-55` 那段 `options` 注释改写：`read_store` 门控的是两把键的读取
（"the in-process hash table" 这个说法所指的机制已被裁决 E 删除）；"store 自维护不受门控"这一句要写明
两个作废函数各自只作废自己那把键，且都只在对应那把键命中之后才可达。

**`store_hit_replay`（`proof_store_AoA.ML:99-146`）的查找顺序**（裁决 P、I、Q）。今天：L2 按 id →
（失败则墓碑）→ L1 按 id → 未命中返回 `NONE`。改为三级，并有一条贯穿三级的规则：**已失败记录不再
重放**（`(time, text)` 都相同即同一记录），第 2 步与第 3 步取回记录后都先查它。

1. L2 按 id（`get_cached_proof thy key`）。命中且重放成功 → 返回，不写。命中但重放失败 →
   `invalidate_proof_cache true key thy`，记为已失败记录，继续第 2 步。未命中 → 第 2 步。
2. L2 按 hash（`hash` 为 `SOME h` 时 `get_cached_proof_by_hash thy h`；`NONE` 则跳到第 3 步）。
   未命中 → 第 3 步。命中：是已失败记录则不重放、直接视为失败；否则重放。
   成功 → 若 `write_store` 则晋升：`update_cached_proof thy {id = key, hash = SOME h}` → 返回。
   失败 → `invalidate_proof_cache_by_hash h thy`，**不追加任何帧** → 第 3 步。
3. L1 按 id（`l1_lookup key`）。命中：是已失败记录则不重放、直接视为失败；否则重放。
   成功 → 若 `write_store` 则升级写回 L2（`{id = key, hash = hash}`）。失败（含跳过）→ `l1_invalidate key`
   及其警告照发（那一行的删除由"同一记录在同一 goal、同一语境、同一预算下已失败"这个事实挣得）。

**晋升只写 L2、不写 L1**，这是明确决定，不要按对称性给第 2 步补一个 `l1_write`：hash 里混了
theory 名，L1 里这样一行只对同名 theory 可见，收益为零；而 `l1_write` 是不带超时的 Python RPC，
`store_hit_replay` 是同步的、在任何 fork 之外，把它放进第 2 步就是给零收益的事加一个挂死面。
第 2 步与第 3 步写 L2 的动作相同（以 `key` 和 hash 写），实现上抽成一个局部函数两处复用。

签名增加参数 `hash: Hasher.digest option`：

```sml
val store_hit_replay : {key: Phi_Proof_Store.proof_id, hash: Hasher.digest option, write_store: bool}
                    -> Proof.context * thm -> (Time.time * string * thm) option
```

头部契约注释（`:31-40`）改写为三级顺序，**并写明三级各自的失败动作**（L2 按 id → 墓碑并下落；
L2 按 hash → 按 hash 作废、不追加帧；L1 → `l1_invalidate` 并报未命中）以及那条贯穿三级的已失败记录
规则。代码里第 2 步的失败分支旁留一句短注释引用裁决 I。hash 的计算**不进** `store_hit_replay`：
它是共享的 level-0 入口，不应持有任何键配方（裁决 A）。**§4 的测试到第 3 步时 L1 必定未命中**：Isa-Mini
测试 theory 里所有 proof id 带前缀 `TPSHH.`，生产代码造不出这个前缀（`run_AoA` 写十六进制摘要，
`hammer_or_AoA` 转发 phi 的义务 id），所以不论 prover 有没有 Python，L1 都查不到，也不会误删作者的真实
L1 缓存。第 3 步的行为靠人工检查。

其余调用点：

| 位置 | 现状 | 改为 |
| --- | --- | --- |
| `sledgehammer_solver.ML:1930-1931`（`auto` 的 `record`） | `update_hash_cache hash (t, prf); update_cached_proof thy (id, (t, prf))` | `update_cached_proof thy {id = id, hash = SOME hash} (t, prf)` |
| `sledgehammer_solver.ML:2018-2019`（`all_auto` 的 `record`） | 同上 | 同上 |
| `cache_file.ML:820-828`（`update_cache_by_hash`） | 两次写 | `update_cached_proof thy {id = Hasher.hex hash, hash = SOME hash} prf'` |
| `Isa-Mini/Agent/agent_server.ML:1882`（`run_AoA`） | `key = Hasher.hex (Hasher.all_goals …)` | `hash = Hasher.all_goals …`，`key = Hasher.hex hash`；`store_hit_replay {key, hash = SOME hash, write_store = write}` |
| `agent_server.ML:1923`（`run_AoA` 写回） | `update_cached_proof thy (key, (std, prf_text))` | `update_cached_proof thy {id = key, hash = SOME hash} (std, prf_text)` |
| `agent_server.ML:2055`（`hammer_or_AoA`） | 只在无 proof_id 时算 hash | 只算一次：`val (key, hash) = case proof_id of SOME id => (id, if read orelse write then SOME (Hasher.all_goals (ctxt, sequent)) else NONE) \| NONE => let val h = Hasher.all_goals (ctxt, sequent) in (Hasher.hex h, SOME h) end`；`store_hit_replay {key, hash, write_store = write}`。`NONE` 只在读写都关闭时出现，那时 `store_hit_replay` 不被调用。`SOME id` 分支在未命中路径上与 `all_auto` 在 `:2009` 对同一 goal 算 hash，配方相同；`all_auto` 在 `async_prove` 的分叉分支里可能先做 beta 规范化再算，那时两个值可能不同，但 `all_auto` 在这条路上是 `read_store = write_store = SOME false`（`:2083`、`:2105`），不读不写，所以不构成第二套键 |
| `agent_server.ML:2139`（`hammer_or_AoA` 写回） | 同 1923 | `update_cached_proof thy {id = key, hash = hash} (std, prf_text)` |
| `Isa-REPL/library/sledgehammer.ML:253` | 处于块注释内 | 不变 |
| `phi-system` | 不直接调 `Phi_Proof_Store`（经 `hammer_obligation_solver` 传 `proof_id`） | 不变；经裁决 P，phi 义务在结构化键位移、命题不变时可按 hash 命中 |

### 3.5 不做的事

- 不补写旧记录的 hash（J）。
- 不写迁移脚本（K）；仓库里 125 个 store 各自在下次构建的 theory 结束时被压缩重写。
- 不改 L1 的键、内容与三个 RPC（L）。裁决 P 只在 L2 内部加一步，L1 仍按 id 查；晋升不写 L1。
- 不改 `Hasher` 的配方；不改 `written` 表、撞键守卫、`migrate_legacy`、写锁、可写性探测。
- 不把 Isa-Mini 的两个写回 fork 登记进 `register_async_task`。这会让 theory 结束的压缩等待
  一次不带超时的 L1 Python RPC，是新的挂死面。**登记为独立议题**：届时先像 §1 那样实测
  `openning_stores` 在 session 末尾的大小，再决定。

---

## 4. 测试

新增 `Test/Test_Proof_Store_Double_Key.thy`，`imports Auto_Sledgehammer.Auto_Sledgehammer`
（带 session 前缀，与 `Test/Test_Ground_Eval.thy:2` 一致，使其在别的 session 下也能解析），
ML 断言，外加 17b / 22b 需要的一个 `method_setup`。`*.proof-store` 与 `.lock` 已被 `.gitignore` 忽略，
测试文件不需要善后。凡是
"`scan` 文件断言帧存在"的断言都是有意的：`try_write`（`:463-465`）与 `append_record`
（`:527-534`）在不可写目录下静默跳过，不检查磁盘的测试会空过。解码后的记录没有 tag 字段，
所以对文件只断言 `hash` 字段，不断言 tag（编码器只产生 tag 3，测试 1 已钉住）。

对 `Proof_Store_Format`（未被签名遮蔽，注释明言为单元测试而暴露）：

1. tag 3 往返：`PUT {hash = SOME h}` 与 `PUT {hash = NONE}` 各编码再解码，逐字段相等；
   载荷第二字节是 `03`。h 取 `0w0` 与 `Word64.notb 0w0`（全 1）两个端点各一次。
2. tag 1 兼容：用 `packPair (packInt, packTuple3 …)` 拼一条 tag 1 载荷，`decode_record`
   得到 `hash = NONE` 的 `PUT`。
3. 混杂扫描：`scan` 一个由 tag 1 帧、tag 3 帧、TOMB 帧拼接成的缓冲区，得到的记录列表按文件序、
   逐字段正确。

对 `Phi_Proof_Store`，用一个 scratch theory，以 `invalidate_store` 起始的空 store：

4. **磁盘对照**：`update_cached_proof {hash = SOME h}` 后，`scan` `store_path thy` 的内容，
   断言存在一条该 id 的 PUT 且 hash 为 `SOME h`。
5. 命中：同一记录经 `get_cached_proof` 与 `get_cached_proof_by_hash` 都命中，返回同一对 `(time, proof)`。
6. 墓碑：`invalidate_proof_cache` 后，按 id 未命中，**按 hash 仍命中**（规则 2 不碰 `by_hash`）。
7. 重载与压缩：`force_reload` 后按 hash 仍命中（PUT 帧仍在文件里）；`compact_and_store` 后再
   `scan`，该 id 的 PUT 与 TOMB 帧都不在；再 `force_reload`，按 hash 未命中。
8. **压缩保留 hash**：写两条记录，一条 `hash = SOME h`、一条 `hash = NONE`；`compact_and_store`；
   `scan` 文件，**按 `id` 字段找到这两条**（压缩后文件是 id 降序，不能按位置找），断言第一条 hash
   为 `SOME h`、第二条为 `NONE`；再 `force_reload` 后按 h 仍命中。`force_reload` 不可省：
   `compact_store` 只改文件不动 `openning_stores`，不重载则内存命中掩盖磁盘丢 hash。
9. `hash = NONE` 的记录只能按 id 命中。
10. 同 hash 两个 id：先写 A 再写 B，**两者文本不同**，按 hash 得到 B 的文本（H）。
11. 同一 id、同一段证明文本、**不同的时间** t₁ 与 t₂，先以 hash h 写（t₁）、再以 hash h' 写（t₂）：
    按 h' 得到 t₂，按 h 仍得到 t₁（规则 1 只增不删），文件多出一帧（裁决 O）。
12. 裁决 O 的短路：同一 id、同文本、同 hash 再写一次，文件**不**多帧。
13. `force_reload` 后第 10、11 条结论不变（`by_hash` 派生自记录序列）。
14. **tag 1 帧端到端**：手工拼一个文件，帧序为 `PUT x`（**tag 1**，用测试 2 的拼法加
    `Proof_Store_Format.frame`）、`PUT a(h)`、`TOMB a`；`force_reload`：x 按 id 命中，h 仍命中
    （只增不删）；`compact_and_store` 后 `scan`：x 的记录仍在、解码后 `hash = NONE`，a 的两帧都不在；
    再 `force_reload`：x 仍按 id 命中，h 未命中。
15. **按 hash 作废**：写一条 `{hash = SOME h}`，`invalidate_proof_cache_by_hash h`：按 hash 未命中，
    按 id 仍命中，文件无新帧。

对 `auto`（裁决 I、N、Q、R 的行为）。所有调用 `options` 写全：`improved = true`（只有这个分支的
竞赛里有 `simp` 竞赛者，能在没装 ATP 的机器上解掉 `simp` 可解的 goal；`improved = false` 只跑
`bare_hammer`，测试就依赖外部证明器）、`async_mode = Sync`、`read_store = SOME true`：

16. **hash 命中失败不打墓碑**：预置一条 id 未命中、hash 命中但重放必失败的记录（文本 `(fail)[1]`），
    对一个 `simp` 能解的 goal 调 `auto`，`write_store = SOME true`：goal 被解决；`scan` 文件后**没有**
    新增 TOMB 帧；预置记录仍在文件里；`get_cached_proof_by_hash` 对该 hash 返回搜索得到的新证明
    （第 3 步的 `record` 覆盖了作废后的空位）。
17. **墓碑与按 hash 作废都可观测**：预置 K₁ → (`(fail)[1]`, `SOME h`)，h 为该 goal 的
    `Hasher.goal_at 1`；对该 `simp` 可解 goal 以 `proof_id = SOME K₁`、**`write_store = SOME false`**
    调 `auto`（第 1 步命中失败、墓碑；第 2 步取回同一记录、跳过规则生效、按 hash 作废；第 3 步搜索
    但因 `write_store` 关闭不写 PUT）：goal 被解决；`scan` 有 `TOMB K₁` 且无新 PUT；
    `get_cached_proof thy K₁ = NONE`；`get_cached_proof_by_hash thy h = NONE`。这是唯一能察觉
    "`stale` 删了、两个作废函数一个没调"的测试。
18. **级联场景（经 `auto`）**：预置 K₁ → (P₁, h₁)，P₁ 是一段**手写**的证明文本（如 `(force)[1]`），
    能证 goal G₁；两次调用都 `write_store = SOME true`。先以 `proof_id = SOME K₁` 对另一个
    **`simp` 可解**的 goal G₀ 调 `auto`（第 1 步命中、失败、墓碑；第 2 步按 h₀ 未命中；第 3 步真的
    搜索，所以 G₀ 必须可解，否则 `Auto_Fail` 会从 ML 块抛出）：`scan` 有 `TOMB K₁`。再以
    `proof_id = SOME K₂` 对 G₁ 调 `auto`：**返回的文本逐字等于 P₁**，文件里 K₂ 下多一条带 h₁ 的 PUT，
    且没有新的 TOMB。文本断言是这条测试真正的判别点：搜索产生的文本一律以
    `Auto_Sledgehammer.pre_simproc_on_concl, ` 开头（`:1783`、`:1900`），手写的 P₁ 不可能由搜索产生，
    而"K₂ 下多一条带 h₁ 的 PUT"在搜索路径上同样会出现（`hash` 每次调用只算一次，`:1919`）。
19. **跳过规则的判别态**：预置 K₁ → (`(fail)[1]`, `NONE`) 和另一个 id → (P₁, `SOME h`)，h 为 goal G₁
    （P₁ 能证；G₁ 能否被搜索解掉无关紧要，判别点是逐字文本，rev 6 去掉了"`simp` 不能解"的要求：
    `improved = true` 的竞赛不只有 `simp`，那个要求买不到它承诺的 `Auto_Fail`）的 `Hasher.goal_at 1`；以 `proof_id = SOME K₁`、`write_store = SOME true`
    对 G₁ 调 `auto`：返回的文本是 P₁（第 1 步失败、第 2 步取回的是**另一条**记录、跳过规则不触发）；
    `scan` 有 `TOMB K₁` 与一条 K₁ 下带 h 的新 PUT（晋升）；`force_reload` 后 K₁ 按 id 命中 P₁。
19b. **`all_auto` 一侧的 `replay_store`（裁决 R 的第二个调用点）**：构造一个有**两个**子目标、都不需要
    ATP 就能关闭的 goal state（如对一个合取 `Goal.init` 后 `resolve_tac ctxt @{thms conjI} 1`）；
    预置一条无关 id 下带 h（`Hasher.all_goals (ctxt, sequent)`，即 `all_auto` 在 `:2009` 用的公式）、
    文本为**两段**手写的记录，如 `((force)[1], (force)[1])`；以 `proof_id = SOME K`（与预置 id 无关）、
    `write_store = SOME false` 调 `all_auto`。断言三件：返回的文本逐字等于预置文本（搜索会拼出以
    `Auto_Sledgehammer.pre_simproc_on_concl, ` 开头的两段）；返回的 sequent `Thm.no_prems`；
    `scan` 无新帧。这条测试针对的是 `k` 传错的后果：`k = 1` 时 `Goal.protect 1` 只暴露一个前提，
    `eval_prf_str` 的 `no_prems` 检查只看得见暴露的那个，两子目标的状态经 `Goal.conclude` 回来剩 1 个
    前提，满足 `1 <= 2 - 1`，`all_auto` 会把一个还开着子目标的状态当作命中交出去。

rev 6 补充的测试（实施评审指出的空白）：

- **12b**：同 id、同文本、同 hash、**不同时间**再写一次，文件多一帧，按 hash 取到新时间（裁决 O 放宽后的判据）。
- **16b / 19c**：**按 id 命中成功**（`auto` / `all_auto` 各一条）：预置 `{hash = NONE}` 的记录，调用时带真实 hash，
  返回文本逐字等于预置、goal 关闭、文件无新帧。预置不带 hash 而调用带 hash，是为了让误发生的晋升写入
  带上不同的 hash、无法被短路吞掉。
- **16c**：`read_store = false`、`write_store = false`：预置在两把键下都可达，返回的文本不是预置文本
  （搜索了）、文件无新帧。这是 §3.4 "一处 `do_read` 判断"的反向。
- **17b / 22b**：**跳过规则的正向**：测试 theory 里用 `method_setup` 声明一个计数后失败的方法 `count_fail`，
  预置 `{id = K, hash = SOME h}`、文本 `(count_fail)[1]`，以 K 调用：第 1 步重放一次（计数 1）、失败、墓碑；
  第 2 步取回同一条记录、跳过。一次重放会调用该方法**不止一次**（`[1]` 组合子会回溯），所以测试先单独
  重放一次量出基准，再断言整次调用的计数等于基准（没有跳过规则时是基准的两倍）；rev 6 初稿写的
  "计数为 1、否则为 2"按字面做不出来。`count_fail` 只对 `method_setup` 之后取的 context 可见，这两条测试
  因此各自取新的 `\<^context>`。
- **Isa-Mini 测试 theory 的 proof id 一律带前缀 `TPSHH.`**（如 `TPSHH.K1`），理由见 §3.4；本节示意用的
  键名省略了前缀。
- **20b**：`store_hit_replay` 的按 id 命中成功，同 16b。

对 `store_hit_replay` 与 `hammer_or_AoA`（裁决 P、I、Q），放在 Isa-Mini 侧
`Isa-Mini/Test/Test_Proof_Store_Hash_Hit.thy`，`imports Minilang_AoA.Minilang_AoA`
（`Isa-Mini/Test/` 不在任何 ROOT 里，必须带 session 前缀，与 `Isa-Mini/Test/Test_eval_simproc.thy` 一致）：

20. phi 形状：对一个 `simp` 可解的 goal，以 id₁、hash h、文本 `(simp)[1]` 写一条记录；调
    `store_hit_replay {key = id₂, hash = SOME h, write_store = true}`：返回 `SOME`，且 `scan`
    文件后 id₂ 下多了一条带 h 的 PUT（晋升）。再以 `write_store = false` 对 id₃ 调一次：
    返回 `SOME`，文件无新帧。
21. **级联场景（经 `store_hit_replay`）**：与第 18 条同构，两次调用分别传 `{key = K₁, hash = SOME h₀}`
    与 `{key = K₂, hash = SOME h₁}`；第一次调用后 `scan` 有 `TOMB K₁`。
22. **跳过规则的判别态（经 `store_hit_replay`）**：预置 K₁ → (`(fail)[1]`, `NONE`) 与 id_good →
    (`(simp)[1]`, `SOME h`)，h 为该 `simp` 可解 goal 的 `Hasher.all_goals`；调
    `store_hit_replay {key = K₁, hash = SOME h, write_store = true}`：返回 `SOME` 且文本是 `(simp)[1]`
    （跳过规则误触发时会返回 `NONE`，因为第 3 步 L1 在无 Python 时静默未命中）；`scan` 有 `TOMB K₁`
    和一条 K₁ 下带 h 的新 PUT；`force_reload` 后 K₁ 按 id 命中 `(simp)[1]`。
23. **hash 命中失败**：用与第 20 条不同的 goal（同 goal 同 hash，裁决 H 会让预置互相覆盖）；预置
    id₁ → `(fail)[1]`、hash h；先 `scan` 记下帧数 N 并断言 id₁ 的帧在；调
    `store_hit_replay {key = id₂, hash = SOME h, write_store = true}`：返回 `NONE`；`scan` 仍是
    N 帧（id₂ 与 id₁ 都没有 TOMB）；按 id₁ 仍命中，按 h 未命中。
24. **驱动 `hammer_or_AoA`**：对一个 `all_auto` 能解（`improved = true`）的 goal，预置一条无关 id₁ 下
    带 h（`Hasher.all_goals`）、文本 `(simp)[1]` 的记录；调 `hammer_or_AoA {proof_id = SOME K,
    read_store = SOME true, write_store = SOME false, async_mode = Sync, …}`，K 与 id₁ 无关：返回的
    文本**逐字**是 `(simp)[1]`。接线正确时第 1 步未命中、第 2 步按 hash 命中并原样返回；接错（传 `NONE`、
    对错的 sequent 算 hash）时第 2 步被跳过、第 3 步静默未命中、未命中路径的 `all_auto` 自己搜出证明并
    返回它拼接出来的文本（以 `Auto_Sledgehammer.pre_simproc_on_concl, ` 开头的复合源码经 `scoped` 拼接，
    `:1783`、`:1900`、`:2036-2037`），与预置的 `(simp)[1]` 逐字不同，断言失败。不需要 ATP、AoA 或 LLM。

`agent_server.ML:1923` 与 `:2139` 两处写回**没有测试**：它们各自骑在一个句柄被 `ignore` 的
`Future.forks` 上（`:1913`、`:2131`），无法 join；驱动 `run_AoA` 越过闸门需要 RPC host 的 Python。
两处只是把已算好的 hash 带进记录参数，第 24 条钉住了那个值。

**编译检查。** auto_sledgehammer 侧：启动 **`Performant_Isabelle_HOL`**（`Performant_Isabelle_ML/ROOT:8-13`，
提供 `Auto_Sledgehammer.thy` 的两个 import，本方案不动它），让 `Auto_Sledgehammer.thy` 及全部
`library/*.ML` 从源码加载；**不能**启动 `Auto_Sledgehammer` session，它的 heap 预编译了被改的两个
文件。Isa-Mini 侧：同样的规则，启动的 session 的 heap 祖先链里不能有任何一个预编译了四个被改文件
（`cache_file.ML`、`sledgehammer_solver.ML`、`proof_store_AoA.ML`、`agent_server.ML`），所以
**不能**启动 `Minilang` 或 `Minilang_AoA`；本机可用的是 `HOL`（前置提交时已用它把
`Minilang_AoA.thy` 加载到 `agent_server.ML`），`Semantic_Embedding` 的 heap 若已构建也可用。
Isabelle-MCP 的启动探测是 `isabelle build -n` 干跑，从不构建；若它判定某个 heap 无法校验，退回 `HOL`。
Python 依赖分两层说：`Minilang_AoA.thy` 本身因 `Semantic_Embedding.thy` 要起 RPC host，prover 的
Python 需带 `Isabelle_RPC_Host`（本机在 `.venv`）才能加载干净，否则 `agent_server.ML` 只能得到
"无类型错误"的间接证据；测试 20–24 只调 `store_hit_replay` / `hammer_or_AoA`，其 L1 RPC 在无
Python 时静默返回未命中（`proof_store_AoA.ML` 的 `\<^try>`），测试本身不需要 Python。

---

## 5. 实施顺序

1. `Proof_Store_Format`：记录类型、编码、解码、格式注释；删除 `replay`（§3.1）。
2. `Phi_Proof_Store`：`store` 类型、规则 1–4 与 Q（含下移的 `replay`）、四个内部函数与 `:275-296`
   注释、签名增删改、`invalidate_proof_cache_by_hash`、`live_and_identical`、删除 `hash_cache`
   （§3.2、§3.3）。
3. `sledgehammer_solver.ML`：共用函数 `replay_store`，`auto` / `all_auto` 改为调用它，`record` 调用点，
   `:50-55` 与 `:1968-1971` 注释；`cache_file.ML` 的 `update_cache_by_hash`（§3.4）。
4. 测试 theory（§4 第 1–19c 条），经 Isabelle-MCP 跑通。
5. Isa-Mini：`store_hit_replay` 三级顺序、签名与契约注释、`run_AoA` / `hammer_or_AoA` 调用点、
   测试 20–24（§3.4、§4）。两处写回 fork 无测试，原因见 §4 末。
   **实测记录（2026-09-03，Isabelle-MCP 的 `HOL` session）**：`Semantic_Embedding.thy:29` 起 RPC host 失败
   （prover 的 `/usr/bin/python3` 没有 `Isabelle_RPC_Host`），`agent_server.ML` 报的错全部是未声明的结构：
   `Theory_Structure`（`:784`）、`Goal_Preprocess`（`:897`）、`Semantic_Store`（`:917`、`:1740`、`:1810`）、
   `Infra_Filter`（`:1356`）；被改的 `:1884-1888`、`:1927`、`:2061-2068`、`:2149` 无错（Isa-Mini 提交
   `e0db3b0` 后的行号）。测试 20–23 含 20b、22b 通过；24 需要 `MiniLang_Agent_AoA`，待 prover 拿到
   `ISABELLE_RPC_PYTHON`（作者的 `.mcp.json`）后再跑。
6. 提交：auto_sledgehammer 一个提交，Isa-Mini 一个提交，主仓库 bump 一个提交。

---

## 6. 评审中被驳回或延后的意见

| 意见 | 处置 | 理由 |
| --- | --- | --- |
| rev 1 F1：旧版本二进制读到全 tag 3 的文件会视为空并在压缩时清空它 | **作者驳回** | 不假设用户会用旧版本读取新文件 |
| rev 1 F1b：压缩时拒绝重写含未解码帧的文件 | 随 F1 作废 | 它只是 F1 的防御半边 |
| rev 1 F4 / SR3：`by_hash` 改存 proof id，查询经 `proofs` 再取一次 | **作者驳回** | 多一次查找；与 rev 5 的"存 `(time, text)`"不同，后者仍是一次查找 |
| rev 1 SR4：把 AoA 写回 fork 登记进 `register_async_task` | 延后 | 见 §3.5 末条 |
| rev 1 F10：`Word64.word` 与 `Hasher.digest` 两种拼法 | 钻牛角尖 | 术语表已等同；统一写 `Hasher.digest` |
| rev 2 SR-F8：不要 `by_hash`，按 hash 查改为在 `proofs` 上线性扫描 | **作者驳回** | 线性扫描慢；`Hasher.Tab` 是平衡 2-3 树，O(log n) |
| rev 2 F7：编译检查的回退只能靠触发重建才能发现 | 驳回 | Isabelle-MCP 的探测是 `isabelle build -n` 干跑，从不构建 |
| rev 2 F10：hash 视图从进程全局缩到每 theory 一份 | 驳回 | hash 含 theory 名，跨 theory 本来就命中不了 |
| rev 2 F11：删掉 `stale` 就删掉了"A cached proof fails"警告 | 已由 rev 5 裁决 N 吸收 | 那句话留在搜索入口，`stale` 保留为选消息用 |
| rev 3 F1 的两个不可行变体：墓碑时删被删记录的 hash 项；墓碑时删调用方自己的 hash 项 | **作者驳回**（改为裁决 Q） | 前者级联删掉下一条义务要查的项，后者删掉自己要查的项；见 §3.2 的级联例子 |
| rev 3 F1 的第三个变体：`invalidate_proof_cache` 加可选 hash 参数，仅当被删记录的 hash 等于该参数时才删 hash 项 | **作者驳回**，改为独立函数 `invalidate_proof_cache_by_hash` | 每把键的失败只作废自己那把键，两件事不缠在一个函数里 |
| rev 3 F4：写入接口与 `store_hit_replay` 的 hash 改为非 option | **作者驳回** | 为未来没有 hash 的调用方留门 |
| rev 3 F4 附带：去掉 `hammer_or_AoA` 里 `if read orelse write` 那一行 | **作者驳回** | 多一个分支没有问题 |
| rev 3 F10：§3.4 表里 Isa-REPL 那一行在块注释内 | 钻牛角尖 | 已在表中注明 |
| rev 3 MD1：`hammer_or_AoA` 与 `all_auto` 算的 hash 因 beta 规范化未必相同 | 措辞改软 | 那条路上 `all_auto` 不读不写，不构成第二套键 |
| rev 4 F1 的选项 (i)（删掉 `A cached proof fails. Re-searching proofs...`）与 (iii)（改措辞） | **作者驳回**，取选项 (ii) | 那句话不动，`stale` 保留为选消息用；见裁决 N |
| rev 4 DROP-1：并发线程在 `get_cached_proof_by_hash` 与 `invalidate_proof_cache_by_hash` 之间写入新项的窗口 | 驳回 | 损失只是一条内存项，且每次命中都重放验证 |
| rev 4 DROP-2：三处源码注释过时（`:221` 的 `open` 注释、`:555` 的"a second table"计数等） | 实施时顺手改 | 不是设计问题 |
| 实施评审：`try_cached_proof_by_hash_with_key` 也读第二把键 | **延后**为独立议题 | 触及 §3.3 明列不变的函数；它的重放约定（`replay_mepo_proof`）与 auto / AoA 的 `(…)[1]` 文本不同，须先确认外来文本只会重放失败而不会误动作 |
| 实施评审：`openning_stores` 条目里无人读取的 bool | 延后 | 先于本次工作；改动触及五处无关写入点 |
| 实施评审：`store_hit_replay` 的第 1 级内联而第 2、3 级具名 | 驳回 | ML 先定义后使用的顺序使然；加一个 `try_id ()` 只是为对称而设的间接层 |
| 实施评审：`replay_store` 的成功判据永远为真，建议删除 | 驳回 | 它是把 k 的含义写成后置条件的唯一位置，注释已说明它是断言 |

---

## 7. 实施交接（写于 2026-09-03，开工前的上下文压缩之前）

给压缩之后接手实施的那个"我"看的，只记方案正文里没有的事。

**已定、不再讨论。** 裁决 A–R 全部经作者裁定，§6 的驳回项不得重提。第五轮短复核判定可开工；
作者要求开工前先问一句，得到"开工"再动代码。作者的额外要求：实施完成后把**每一处**改动的位置
（文件、行号、函数名）列出来供审阅；优雅性是硬要求，特别是 `replay_store` 必须保持"唯一区分参数
是 k"的形状，不许变成参数拼盘。

**命名已定。** 共用函数 `replay_store`（`sledgehammer_solver.ML` 的 `local … in` 块内）、
内存表作废函数 `store_forget_hash`（`cache_file.ML`）、导出接口 `get_cached_proof_by_hash`、
`invalidate_proof_cache_by_hash`。测试 theory：`Test/Test_Proof_Store_Double_Key.thy`、
`Isa-Mini/Test/Test_Proof_Store_Hash_Hit.thy`。

**工作区里别人的未提交改动，开工时就在那里，不是我做的，不要动、不要提交：**

- `auto_sledgehammer/ROOT`：另一位 agent 加的临时 `options [ML_debugger = true, ML_exception_debugger = true]`
  （注释自述 TEMPORARY，用于 `exception Option` 追查）。**绝不能进我的提交**：提交时用
  `git commit -- <明确路径>`，不要 `git add -A`。
- `auto_sledgehammer/library/Hasher.ML`：另一位 agent 加了 `Hasher.compact`（8 字节大端渲染）。
  本方案不改 `Hasher.ML`，不要暂存它。
- `auto_sledgehammer/library/cache_file.ML`：签名里 `get_cached_proof` / `update_cached_proof` 的类型
  被改用 `proof_cache` 别名、文件末尾补了换行。这两处会被本方案的改动覆盖，随我的提交一起进去即可。
- `Isa-Mini`：`Agent/Minilang_AoA.unicode.thy`、`Agent/agent_hint.ML`、`ROOT`、`library/aux.ML` 有别人
  的改动，`translator` 是未跟踪目录。我的 Isa-Mini 提交只暂存 `Agent/proof_store_AoA.ML`、
  `Agent/agent_server.ML`、`Test/Test_Proof_Store_Hash_Hit.thy`。

**已暂存、待随本方案一起提交的：** `PROOF_CACHE_READONLY_PLAN.md → ai-artifacts/` 的移动（`git mv`
已做）。本文件 `ai-artifacts/PROOF_STORE_DOUBLE_KEY_PLAN.md` 尚未跟踪，随 auto_sledgehammer 的实施
提交一起加入。

**提交格式。** 三个提交（auto_sledgehammer、Isa-Mini、主仓库 bump），提交信息末尾两行：
`Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>` 与
`Claude-Session: https://claude.ai/code/session_01B7H27BHagTetrEXkbetsrP`。主仓库的 bump 用
`git commit -q -F - -- contrib/Isa-Mini`（`contrib` 被 `.gitignore` 忽略，`git add` 会拒绝，
路径限定的 `commit` 可以）。不推送。

**编译与测试的实际做法（前置提交时验证过）。** Isabelle-MCP：`isabelle_launch` 用 session `HOL`、
`session_dirs` 给 `contrib/Performant_Isabelle_ML` 与 `contrib/auto_sledgehammer`（`Performant_Isabelle_HOL`
的 heap 被 MCP 判为无法校验，`HOL` 能从源码把一切加载起来，几分钟）。`isabelle_evaluate_to` 到测试
theory 末尾，`isabelle_command_output` 看断言输出。**永远不跑 `isabelle build`**。用完 `isabelle_terminate`。
`.thy` 文件里不要写非 ASCII 符号（MCP 会警告）。Isa-Mini 侧：同样 `HOL`，但 `Minilang_AoA.thy` 因
`Semantic_Embedding.thy` 要起 RPC host，在 MCP 的 prover（用 `/usr/bin/python3`，没有 `Isabelle_RPC_Host`）
下加载不干净，`agent_server.ML` 会报一串"结构未声明"，测试 20–24 因此跑不起来。解法要**问作者**：
给 prover 设 `ISABELLE_RPC_PYTHON`（`.venv/bin/python` 带这个包）属于改他的 Isabelle 全局配置。
在此之前 Isa-Mini 侧只能得到"没有类型错误"的间接证据，§5 第 5 步已预留"如实记录"。

**评审记录的位置**（只作参考）：五轮裁判结论在本 session 的 scratchpad
`/tmp/claude-1002/-home-qiyuan-Current-MLML/35b6ec05-f0f5-4b86-a05e-40b481073dbc/scratchpad/verdict*.json`；
scratchpad 是 tmpfs，随时可能没了，方案正文已自足。
