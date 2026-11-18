# auto_sledgehammer：每次只证第 1 个子目标、没有 target 的上下文、候选池为空时的 MePo（修复方案）

状态：rev 3，2026-11-18。**没有改任何源码。** rev 1 经第一轮对抗评审（Workflow
`wf_1ef722eb-6df`）判为「修改后接受，需要复评」；rev 2 并入了评审保留的九条意见和作者据此作的决定；
复评（Workflow `wf_56693458-8d8`）判 rev 2「修改后接受，不需要再评」，保留的三条都关于测试，rev 3
已并入（第 7 节）。三部分的方向、导出函数的签名、本稿的形状都已由作者批准；作者 2026-11-18：与测试、
文档相关的，在不改变需求、设计和作者决策的前提下，我可以自决。

标记：【已定】= 作者已决定；【实测】= 跑过；【评审实测】= 评审 agent 跑过、我没有重跑；【读码】= 只读了
源码。

源码位置都指 `library/sledgehammer_solver.ML`（HEAD `d3a7b0d`），另有说明的除外。探针在 MLML 仓库的
`ai-artifacts/sh_auto_split_probe/`、`ai-artifacts/sh_leading_subgoal_probe/` 下（评审 agent 的在后者的
`review/` 下），不提交。

## 0. 来源和已定的事

这三个问题是在 Sledgehammer fact trigger 第 4 版的工作中发现的，记录在 feature repository
（`contrib/sledgehammer_fact_trigger`）的 `ai-artifacts/RELEASE_4_WORK_PLAN.md` 第 9.3 节第 11 条，以及
`ai-artifacts/RELEASE_4_REPAIR_PLAN.md` 第 4 节第 7、9 条。

作者 2026-11-17 定下的：
- 本质是 Sledgehammer 的 tactic prover 违反 Sledgehammer 自己的约定（见 1.1）。fact trigger 第 4 版
  不修这个根源；auto_sledgehammer 自己守住。理由：auto_sledgehammer 的 conda 包只依赖
  `isabelle >=2026,<2026.1`，会跑在不带任何补丁的 Isabelle 上。
- 修法的方向：在原来的 `raw_sledgehammer` 里，交给 Sledgehammer 之前用 `Goal.protect 1` 藏起其余
  子目标；在同一个被保护的状态上重放，只接受证完第 1 个子目标的候选，之后去掉保护；写进证明文本的
  每一步外加 `[1]`。作者认为「循环改成还有子目标就继续」会弄得比较麻烦。
- 没有 target 的问题一起修：没有 target 时把背景理论的全局事实当作要减去的部分，第 403、1107、
  1238 行三处。
- `fast_mepo` 候选池为空时也调用 MePo。
- 测试用导出的函数做确定的检查。
- 原则：「不影响我们的 auto_sledgehammer 的 bugs 全都先不修」。
- auto_sledgehammer 是否发新版本，等作者下令。

作者 2026-11-18 定下的（第一轮评审之后）：
- 签名注释加一句 hasty 模式（下面原文的倒数第二句）；`"<cheat>"` 不加 `[1]`。
- 重放的就是已经加了 `[1]` 的文本，返回的也是它。
- 第二部分用一个共用函数 `named_facts_of`（2.1）；`looping_simp.ML` 的两处一起改（2.2）。

导出函数的签名（2026-11-17 批准，2026-11-18 加 hasty 一句）：

```sml
(* Sledgehammer on the LEADING subgoal of the state, with every other subgoal hidden from
   Sledgehammer and from the replay of what it finds.  SOME (text, state') on success:
   text proves exactly the leading subgoal and is written "(...)[1]", so it replays the same
   on a state with more subgoals; state' is the state without that subgoal.  In hasty mode,
   text is "<cheat>" and state' is obtained by cheating.  NONE when no proof that
   Sledgehammer found could be replayed. *)
val sledgehammer_leading_subgoal :
  Time.time option -> Sledgehammer.fact_override -> bool (*hasty*) -> Proof.state ->
  (string * Proof.state) option
```

## 1. 第一部分：每次调用只证掉第 1 个子目标

### 1.1 问题

**一句话**：auto_sledgehammer 让 Sledgehammer 证第 1 个子目标，但 Sledgehammer 的 tactic prover
`auto` 给出的证明会顺带证掉别的子目标，auto_sledgehammer 重放这段证明时也就一起证掉了；它的循环
按开始时的子目标数固定转 N 圈，于是后面某一圈没有子目标可证，报错 `No subgoal!`。

**背景**【读码】。改进模式（`auto_sledgehammer`、`auto_sledgehammers` 方法）在函数 `sledgehammer`
（第 1447 行起）里并行跑几条路，其中一条是「先拆再证」的 `hammer'`（第 1568 行起）：先用
`auto_split` 或 `clarsimp_split` 把目标拆成 N 个子目标，再由 `hammer`（第 1494 行起）固定循环 N 次，
每次调用 `raw_sledgehammer`（第 668 行起）证当时的第 1 个子目标。`raw_sledgehammer` 做三件事：
1. 在整个证明状态上调用 `Sledgehammer.run_sledgehammer`，子目标编号 1（第 763 行）。
2. Sledgehammer 每报一条「Try this: …」，回调 `dirty_hack` 从消息里取出证明文本，经
   `mk_proof_candidates` 改写（`using F by m` 变成 `(insert F)[1], m`），再用 `eval_prf_str_stat`
   在**整个**证明状态上重放（第 732、740 行）。重放成功的第一个文本和重放后的状态就是结果。
3. `hammer` 把各圈的文本用逗号连起来：`(prf0, p1, p2, …)`，最后整体再验证一次（第 1701 行起）。

**违反的约定**【读码，fact trigger 维修方案第 4 节第 7 条】。Sledgehammer 自己写证明时守一个约定：
为子目标 i 写的证明只作用在子目标 i 上（`sledgehammer_proof_methods.ML` 的 `proof_method_command`：
前面加 `prefer i`，还有别的子目标时用 `apply`，`auto` 这类作用于多个子目标的方法再加 `[1]`）。
tactic prover 不守这个约定：它显示的是 Try0 自己运行的命令，而 Try0 把 `auto` 登记为作用于全部
子目标、成功后接着证后面的子目标。

**例子**【实测，2026-11-16、17，探针 `sh_auto_split_probe/No_Subgoal_Probe.thy`、`pending/`】。公理
`R7: "R 7"`，目标 `R 7 ∧ rev (rev xs) = xs`，`auto_sledgehammer_params = "provers = auto, learn = false"`，
方法 `(auto_sledgehammer del: rev_rev_ident)`：
- `auto_split` 带 `simp del: rev_rev_ident`，留下两个子目标 `R 7` 和 `rev (rev xs) = xs`，N = 2。
- 第 1 圈：Sledgehammer 证第 1 个子目标，给出 `using R7 by auto`；改写成 `(insert R7)[1], auto`；
  重放时 `auto` 用的是普通的 simpset，里面有 `rev_rev_ident`，两个子目标都被证掉。
- 第 2 圈：没有子目标，`raw_sledgehammer` 报 `No subgoal!`。这个 `ERROR` 被 `classify` 归为
  `Internal_Failure`，按设计直接报给用户（第 1675 行起的 `run_branch`），整个方法失败。
- 7 次尝试里 2 次这样失败；其余几次是「整个目标直接证」那条路（`bare_hammer`）先证出。不带
  `del:` 的对照成功。

**触发条件**【实测】：`auto_split` 留下了 `auto` 自己就能证的子目标。`del:` 是确定的办法；`auto`
不幂等的情形很少（十个小目标里没找到）。`clarsimp_split` 不会拆出多个子目标（`clarify` 不用拆分
目标的规则），所以多个子目标只来自 `auto_split`。这个问题在 fact trigger 第 4 版之前就有；第 4 版
让 `auto` 能拿到全局事实（维修方案 3.1），多了「第 1 个要靠事实、后面的 `auto` 自己能证」的情形。

### 1.2 修法

`raw_sledgehammer` 改名为 `sledgehammer_leading_subgoal`，签名和注释如第 0 节，加进
`PHI_SLEDGEHAMMER_SOLVER`。它在入口把状态换成「只露出第 1 个子目标」的状态，此后 Sledgehammer、
`dirty_hack` 里的两处重放、`hasty` 模式的 `cheat_tac` 都只用这个状态。

**被保护的状态是什么**：证明状态的目标定理形如 `A1 ⟹ A2 ⟹ … ⟹ An ⟹ #C`（`#` 是 `Goal.protect`
加的保护标记，被保护的部分对方法来说是一个不可分解的整体）。`Goal.protect 1` 把它变成
`A1 ⟹ #(A2 ⟹ … ⟹ An ⟹ #C)`：只剩 `A1` 是子目标，其余的都藏进了被保护的结论里。证完 `A1` 之后
目标是 `#(A2 ⟹ … ⟹ #C)`。`Goal.finish`（`Pure/goal.ML` 第 81–85 行）先检查没有子目标了（否则抛
`THM`），再去掉最外层的保护，得到 `A2 ⟹ … ⟹ #C`。`eval_prf_str0`（第 533 行）和 `head_only`
（第 510 行）已经这样用 `Goal.protect` / `Goal.conclude`。

**用现成的部件**：
- `scoped`（第 1818 行）就是把文本写成 `(…)[1]`，它的注释说明了为什么要括号（`[n]` 只接在单个方法名
  或括起来的组后面）。它挪到 `sledgehammer_leading_subgoal` 之前，两处都用它。
- `Goal.finish` 就是「证完了才去掉保护」，它的类型正是 `Proof.refine_primitive` 要的
  `Proof.context -> thm -> thm`。

草图（细节在实现时定，结构不变）：

```sml
fun sledgehammer_leading_subgoal timeout_opt override hasty stat0 =
  let val N = #goal (Proof.goal stat0) |> Thm.nprems_of
      val _ = if N = 0 then error "No subgoal!" else ()
      (*every other subgoal is hidden in the protected conclusion*)
      val stat = Proof.refine_primitive (K (Goal.protect 1)) stat0
      ...
      (*a candidate counts only if its scoped text closes the subgoal: Goal.finish raises
        otherwise*)
      fun replay timeout prf =
        let val text = scoped prf
            val (_, stat') = eval_prf_str_stat keywords timeout NONE text stat
        in (text, Proof.refine_primitive Goal.finish stat') end
      (*the one place where a result is taken; the other tasks are cancelled*)
      fun take result =
        ((Single_Assignment.assign shortcut result handle Fail _ => ()); Future.cancel_group group)

      (*in dirty_hack:
          hasty:      take ("<cheat>", stat |> Proof.refine (cheat_tac 1) |> Seq.the_result ...
                                            |> Proof.refine_primitive Goal.finish)
          fast path:  case try (replay 3) prf of SOME r => take r | NONE => eval_future ()
          forked:     case try (Future.interruptible_task (replay pptimeout)) p of
                        SOME r => take r | NONE => ()*)
      ...
   in ...  (*as before*)
     ; Single_Assignment.peek shortcut
  end
```

逐点说明：
- **Sledgehammer 只看到一个子目标**。它数出的子目标数是 1，所以写证明用 `by`，tactic prover 的
  `auto` 也只能证这一个。
- **重放的是加了 `[1]` 的文本，返回的也正是它**【已定】。在只露出一个子目标的状态上，`(p)[1]` 与 `p`
  效果相同【评审实测】；这样返回的文本就是被验证过的那段，字面上相同。例：
  `((insert R7)[1], auto)[1]`。里面原有的 `(insert R7)[1]` 的 `[1]` 变得多余，无害，不去掉。
- **只接受证完的候选**。`eval_prf_str_stat` 只要方法成功就返回，不管子目标证完没有；`Goal.finish`
  在没证完时抛异常。两处重放原来就包在 `try` 里，异常与重放失败一样被当作「这个候选不行」。
- **取结果只有一处**：`take`。原来三份「记下结果，取消其余任务」的拷贝（hasty、快速路径、并行重放）
  合成一份。并行那条路上 `Future.interruptible_task` 只包住重放、不包住 `take`：取消在可中断区域里
  进行会经 `expose_interrupt` 打断自己的线程【评审读码】。
- **hasty 模式**【已定】：`cheat_tac 1` 本来就只作用于第 1 个子目标；它的文本 `"<cheat>"` 不是证明，
  不加 `[1]`，签名注释写明。它同样在被保护的状态上 cheat，再 `Goal.finish`，由 `take` 记下。第 1700 行
  把 hasty 的整个结果换成 `"<cheat>"`，从不重放。
- **末尾只剩 `Single_Assignment.peek shortcut`**：每个产生结果的地方记下的已经是最终的文本和状态，不再
  比较字符串 `"<cheat>"`，也不再在末尾去保护。
- **`hammer` 的循环固定 N 次由此正确**：每圈恰好消掉一个子目标，N 圈正好证完 N 个。`No subgoal!`
  的检查保留，作为内部断言。
- 只改名 ML 函数。Isar 方法 `raw_sledgehammer`（第 2049 行，是非改进模式的 `auto_sledgehammer`）
  与它同名但无关，不改。
- 调用者只有 `hammer`（第 1511 行）；第 1742 行的注释里提到旧名字，一并改。

**机制的实测**【实测，2026-11-18，探针 `sh_leading_subgoal_probe/Leading_Subgoal_Probe.thy`，release 4
的 private tree，`Auto_Sledgehammer` 会话】。状态：`R 7 ∧ rev (rev xs) = xs` 用 `rule conjI` 拆成两个
子目标，local theory 上下文。
- `Proof.refine_primitive (K (Goal.protect 1))` 之后状态里只剩子目标 `R 7`。
- 在被保护的状态上跑 `Sledgehammer.run_sledgehammer`（`provers = auto`）：找到 `using R7 by auto`，
  1.97 秒。（在未保护的状态上同样给出 `using R7 by auto`，没有 `apply`、没有 `[1]`：这就是 1.1 说的
  不守约定。）
- 在被保护的状态上重放 `(insert R7)[1], auto`：0 个子目标；`Goal.conclude` 之后剩
  `rev (rev xs) = xs`。
- 对照：同一文本在未保护的状态上重放，0 个子目标（两个都证掉，即 bug 的成因）；外加 `[1]` 写成
  `((insert R7)[1], auto)[1]` 之后，在未保护的状态上重放剩 `rev (rev xs) = xs`。
- `eval_prf_str_stat` 接受只化简、不证完的方法：被保护的 `P (0 + n) ∧ True` 上重放 `simp`，返回成功，
  剩子目标 `P n`。
- 【评审实测，`review/Part1_Finish_Probe.thy`】重放 `scoped p` 再 `Goal.finish` 得到的状态与上面相同；
  只化简的 `simp` 经 `Goal.finish` 被拒绝（`try` 得 `NONE`）。
- 【评审实测，`review2/R2_Def_Protect_Probe.thy`，共享树和 private tree 结果相同】三个子目标
  `rev (rev xs) = xs`、`rev (rev ys) = ys`、`P z`（最后一个 `auto` 证不了）：在未保护的状态上 Sledgehammer
  给出 `apply auto [2]`（Try0 证掉两个、停在第三个，即 1.1 说的不守约定），这段文本加 `[1]` 写成
  `((auto)[ 2 ])[1]` 之后重放失败；在被保护的状态上给出 `by auto`，`(auto)[1]` 证掉第 1 个子目标。所以
  只加 `[1]`、不做保护是不够的：Sledgehammer 给出的文本本身就作用于多个子目标。

### 1.3 后果

- **只化简、不证完第 1 个子目标的候选现在被拒绝，这是纯粹的修正**【评审读码】。旧代码接受这样的
  候选之后，N 圈转完仍剩子目标；`hammer` 把剩下的目标交回（第 1565 行），这条路仍可能在
  `Par_List.get_some` 的竞赛里胜出，最后的整体验证（`eval_prf_str`）报 `Subgoal_unsolved`，没有后备。
  接受它还取消了 Sledgehammer，使它来不及给出一个能证完的候选。现在 `sledgehammer_leading_subgoal`
  继续等 Sledgehammer 的下一个候选，都不行就返回 `NONE`（`hammer` 以 `Application_Fails` 放弃这条路，
  其它路照常）。
- **这种候选从哪里来**【评审读码】：Sledgehammer 自己 preplay 失败的消息走 `failed_command_line`，里面
  没有 sendback，根本不会成为候选（`sledgehammer_proof_methods.ML` 第 255–264 行）。主要来源是 preplay
  超时或被关掉（`preplay_timeout = 0`）的消息：它们带 sendback，auto_sledgehammer 用 10 秒的时限重放，
  而 Sledgehammer 的 preplay 只给 1 秒。auto_sledgehammer 的改写（`using F by m` → `(insert F)[1], m`）
  去掉的只有 `by` 的收尾一步，是次要来源。
- **`No subgoal!` 不再从这里出现**，「先拆再证」那条路不再因此让整个方法失败。
- **存进证明缓存的新文本长一点**：每步多了 `(…)[1]`。缓存里的旧文本照旧重放：缓存的重放用
  `eval_prf_str`（`Goal.protect 1` 加「证完」检查），旧文本证得完就仍然证得完。
- 开销：`Goal.protect`、`Goal.finish` 各是一次 `Thm` 的推理步，相对 Sledgehammer 可以忽略。

## 2. 第二部分：没有 target 的上下文

### 2.1 问题和修法

**一句话**：auto_sledgehammer 有几处要区分「证明里的局部东西」和「证明外面的东西」，用的是 local
theory 的 target（`Local_Theory.target_of`，即证明所在的 theory 或 locale 的上下文）作为「外面」；
上下文不是 local theory、没有 target 时，这几处把「外面」当成空的，于是背景理论的全局事实都被当成
了局部事实。

**哪些上下文没有 target**：
- theory 里 `ML ‹…›` 块的 `\<^context>`（`Local_Theory.level` 是 0），以及 `Proof_Context.init_global`
  一类的上下文【实测】。
- theory 层的 `theory_to_proof` 命令打开的证明：单独的 `instance`（arity 和 classrel 两种）【评审实测】，
  `rep_datatype`、`specification`、`cpodef`【评审读码】。它们先 `init_global` 再 `Proof.theorem`
  （`class.ML` 第 519–527、783–794 行）。`instantiation` 块里的 `instance` 证明有 target。
- 正常的 `lemma … by auto_sledgehammer` 有 target（level 1）。Isa-REPL、TAT、Minilang/AoA 传的都是
  Isar 证明状态的上下文【读码，fact trigger 工作计划 9.3 第 11 条】；它们的证明若在上面那种命令里，
  同样没有 target。

**实测的后果**：
- 【实测，2026-11-16】从 ML 用 theory 的 `\<^context>` 调用 auto_sledgehammer 的方法时，
  `find_local_may_false` 把一条结论为 `False` 的、关于 `dvd` 的全局引理当成局部事实，在证明前插入
  （`wrapper`，第 1124 行起），Sledgehammer 因此放弃。
- 【评审实测，`review/Instance_False_Probe.thy`】单独的 `instance` 证明里，同样得到约 24830 条「局部
  事实」，`find_local_may_false` 选中 `gcd_nat.asym`（结论为 `False` 的全局引理）；同样的检查在 `lemma`
  里得 `NONE`。所以这个 bug 从普通的 Isar 就能碰到。

**三处**【读码；数字是实测，2026-11-18，`Leading_Subgoal_Probe.thy`】：
1. `should_be_inserted`（第 402–412 行）：判断一条规则是否要用 `insert` 放进目标（而不是作为
   `simp:` 等规则加进去），标准之一是规则里有「新」的自由变量，即在证明里固定、在 target 里没有固定
   的变量（`Variable.is_newly_fixed ctxt target`）。没有 target 时每个自由变量都算新的。实测：
   没有 target 时 `P x`（`x` 没有固定）得 `true`，local theory 里得 `false`。
2. `find_local_may_false`（第 1104–1120 行）：找一条可能推出 `False` 的局部事实。局部事实 =
   `Facts.dest_static false [target 的事实] (上下文的事实)`；没有 target 时减去的是空表，全局事实全算
   局部。
3. `facts_as_mepo_lazy_facts true`（第 1232–1260 行）：给 `fast_mepo` 的 MePo 候选池，只要局部事实；
   算法同上。实测：没有 target 时得到 24819 条（全部全局事实），local theory 里 0 条。

**修法**【已定】：没有 target 时，「证明外面」是背景理论的全局上下文：没有固定变量，事实就是理论的
全局事实。这正是 `init_global` 的意思，上面那些命令打开证明时用的也是它。【实测】没有 target 的
上下文的事实减去 `Global_Theory.facts_of thy`，或减去
`Proof_Context.facts_of (Proof_Context.init_global thy)`，都剩 0 条。Isabelle 自己列局部事实时就这么减：
`Proof_Context.pretty_local_facts`（`Pure/Isar/proof_context.ML` 第 1588–1594 行）用的是
`Facts.dest_static verbose [Global_Theory.facts_of (theory_of ctxt)] facts`。

**写法**【已定】：「证明外面的上下文」只定义一次，放在最先加载的 `helpers0.ML`（`Phi_Help`）里，签名
加一项，因为 2.2 的 `looping_simp.ML` 也用它：

```sml
(*the context outside the proof: the local theory target, or, if there is none, the global
  context of the background theory*)
fun outer_context ctxt =
  if Local_Theory.level ctxt > 0 then Local_Theory.target_of ctxt
  else Proof_Context.init_global (Proof_Context.theory_of ctxt)
```

`find_local_may_false` 和 `facts_as_mepo_lazy_facts` 的两种模式算的是同一样东西：上下文的具名事实，
去掉 `local.this`；只要局部事实时再减去外面的事实。现在是两份拷贝。合成一个函数（放在
`sledgehammer_solver.ML`，不导出），三处都调用它：

```sml
(*the named facts of ctxt, without "this"; with local_only, only those that are not
  facts of the context outside the proof*)
fun named_facts_of local_only ctxt =
  Facts.dest_static false
    (if local_only then [Proof_Context.facts_of (Phi_Help.outer_context ctxt)] else [])
    (Proof_Context.facts_of ctxt)
  |> filter_out (fn (name, _) => name = \<^unchecked_name>\<open>local.this\<close>)
```

- `find_local_may_false` 用 `named_facts_of true`；`facts_as_mepo_lazy_facts local_only` 用
  `named_facts_of local_only`。`local_only = false` 时不算外面的上下文，与现在相同。
- `should_be_inserted`：`Variable.is_newly_fixed ctxt (Phi_Help.outer_context ctxt)`，不再有
  `NONE => true`。外面的上下文在返回的闭包外面算一次，与现在的 `outter` 一样。
- 用 `Local_Theory.level` 而不是 `try Local_Theory.target_of`：`target_of` 恰在 level 为 0 时报错
  （`local_theory.ML` 第 140–141、243 行），两者等价；`level` 不吞别的异常，`looping_simp.ML` 已经这样
  写。
- 开销【实测】：`Proof_Context.init_global` 每次约 24 微秒，`Local_Theory.target_of` 约 0.1 微秒；只在
  没有 target 时多花这 24 微秒。

**行为变化**：有 target 时完全不变。没有 target 时：全局事实不再当作局部事实（不再插入、不再进
`fast_mepo` 的候选池）；`should_be_inserted` 只把上下文里固定了的自由变量当作新的。后一点与有 target
时一致【实测，`Fixed_Probe.thy`】：`Proof.theorem` 会固定目标里的自由变量（没有 target 的上下文里也
是），`lemma "P x"` 里 `should_be_inserted` 对 `P x` 得 `true`、对目标里没有的 `P y` 得 `false`；改后
没有 target 时也是这样。

### 2.2 `looping_simp.ML` 的两处同类写法【已定：一起改】

扫描时发现，不在原先的三处之内。`library/looping_simp.ML` 里两处以「有没有 local theory」区分局部变量，
改成用 `Phi_Help.outer_context`：
- `has_local_free_vars`（第 45–48 行）：level 为 0 时任何自由变量都算局部，否则算「在证明里固定、在
  target 里没有固定」的。改成 `Variable.add_newly_fixed ctxt (Phi_Help.outer_context ctxt) t []` 非空。
  level 为 0 时只有固定了的变量算局部，与 2.1 的 `should_be_inserted` 同理。
- `schematize_local_frees`（第 50–55 行）：level 为 0 时没有要保留的变量（`K false`），否则保留 target
  里固定的变量。改成 `Variable.is_fixed (Phi_Help.outer_context ctxt)`；全局上下文没有固定变量，所以
  level 为 0 时仍是「没有」：**行为不变**，只是写法统一。

谁受影响【读码，全文搜索 MLML 的 `contrib/`，不含 ICSE27】：auto_sledgehammer 自己唯一的调用
（`run_mepo_and_render` 第 1357–1361 行）配置是 `only_check_local = false`、`local_ignore_cond = false`，
在这个配置下 `has_local_free_vars` 的结果不影响判断，所以不影响 auto_sledgehammer 的结果。其它调用者
是 Isa-Mini（`Agent/agent.ML` 第 1023、1995 行，`Agent/agent_server.ML` 第 1756 行，`library/proof.ML`
第 5561 行）：它在没有 target 的证明里（2.1 列的那些命令）运行时，变的只是**没有固定**的自由变量，
从「局部」变成「不是局部」。

开销：`has_local_free_vars` 每检查一条规则最多调用两次；没有 target 时每次多约 24 微秒（`init_global`），
50 条规则约 2.4 毫秒。

旁注（不在本方案内，按「不影响 auto_sledgehammer 的先不修」只记下）【评审读码】：Isa-Mini 的
`Agent/agent_server.ML` 第 321–323 行 `global_context_of` 直接调用 `Local_Theory.target_of`，在单独的
`instance` 证明里会报 `Missing local theory context`。

## 3. 第三部分：候选池为空时也调用 MePo

### 3.1 问题

【实测，fact trigger 维修方案第 4 节第 9 条】`fast_mepo` 在没有局部事实时根本不调用 MePo，触发器
不运行，方法以普通的失败结束。原因在 `run_mepo_and_render` 第 1338–1339 行：

```sml
    val mepo_pairs =
      if null lazy_facts then []
      else ...
```

### 3.2 修法【已定】

去掉 `if null lazy_facts then [] else`，候选池为空也调用 `Sledgehammer_MePo.mepo_suggested_facts`。
其后的 `if null selected then map … lazy_facts else selected`（第 1344–1346 行）不变：MePo 什么都没
选出时退回用整个池；池为空时结果仍是空表。

注释的新文字：
- 签名（第 153 行）：`(*MePo pool; [] skips MePo*)` 改为 `(*MePo pool; may be empty*)`。
- 函数前（第 1325 行）：`lazy_facts: pool for MePo selection (empty = skip MePo).` 改为
  `lazy_facts: pool for MePo selection; may be empty, and MePo still runs (fact triggers may add facts).`

【实测，2026-11-18】
- 带 fact trigger 的 Isabelle（release 4 的 private tree）：池为空、注册一个触发器时，触发器被调用
  2 次，MePo 选出触发器给的候选 `T1`。池为空且 `max_facts = 0` 时选出 0 条：
  `mepo_suggested_facts_with_origin` 在 `max_facts <= 0` 时直接返回空表，不进入 MePo 的轮次【读码，
  `sledgehammer_mepo.ML` 第 681–682 行】，所以也不调用触发器（【评审实测】0 次）。（池不为空时
  `max_facts = 0` 不是「选出 0 条」：MePo 返回空表，代码退回用整个池。）
- 不带本包的 Isabelle2026（MLML 的共享树 `contrib/Isabelle2026`，其 `sledgehammer_mepo.ML` 里没有
  `add_trigger`）：池为空时 MePo 返回空表，耗时计为 0.000 秒（`Stock_Mepo_Probe.thy`）。

### 3.3 谁受影响

`run_mepo_and_render` 的调用者【读码】：
- `fast_mepo_tac`（第 1413 行起；`fast_mepo` 方法）：候选池是局部事实，没有局部事实时现在会调用 MePo。
- 改进模式的 `fastforce` 分支（第 1614 行起）的四个阶段：第 1 阶段 `max_facts = 0`、池为空，按上面的
  实测不调用触发器，行为不变；第 2 阶段的池是局部事实，为空时原来等于用更长的时限重跑第 1 阶段，现在
  会调用 MePo；第 3、4 阶段的池是全部事实，不为空，不变。
- Isa-Mini 的 `Agent/agent.ML` 第 1183–1186 行（FactInTime 的记录，`facts_as_mepo_lazy_facts true` 加
  `run_mepo_and_render`）：同 `fast_mepo_tac`。

**行为变化**：只在注册了触发器的 Isabelle 上、候选池为空时出现：触发器生成的事实可以被选中。不带
fact trigger 的 Isabelle 上行为不变（MePo 对空池返回空表）。

## 4. 测试

### 4.1 怎样跑

现在的测试是 `Test/*.thy`，手工跑，CI 不跑（`conda/recipe.yaml` 只装源码）。

**不能用 `-l Auto_Sledgehammer`**【评审读码】：`process_theories` 先调用
`Build.build_logic(…, build_heap = true)`（`Pure/Tools/process_theories.scala` 第 96–97 行），heap 过期时
就完整构建它。改了源码之后，第一次跑测试就等于一次没下令的 `isabelle build`。所以一律把
`Auto_Sledgehammer` 当 theory 从源码加载【评审实测：两种树上都没有写出 `Auto_Sledgehammer` 的 heap，
md5 核对】：

```
cd /home/qiyuan/Current/MLML
<tree>/bin/isabelle process_theories -l Performant_Isabelle_HOL -d contrib/Performant_Isabelle_ML \
  -d <session dir> -O -U -f <session dir>/Test/X.thy Auto_Sledgehammer.Auto_Sledgehammer X
```

会话根目录下的 `Test_Hasher.thy` 和 `Auto_Sledgehammer_Doc.thy` 写的是不带会话名的
`imports Auto_Sledgehammer`，被 `-f` 拷进 Draft 目录后读不到【评审实测】。它们不用 `-f`，按带会话名的
theory 名从源码加载（同一机制，`process_theories.scala` 第 40–110 行只对 `-l` 调用 `build_logic`）
【评审实测：退出码 0，没有写出 heap】，两个文件不改：

```
<tree>/bin/isabelle process_theories -l Performant_Isabelle_HOL -d contrib/Performant_Isabelle_ML \
  -d <session dir> -O -U Auto_Sledgehammer.Test_Hasher
```

（`Auto_Sledgehammer.Auto_Sledgehammer_Doc` 另跑一次。）这样跑时它们在自己旁边读写
`Test_Hasher.proof-store`、`Auto_Sledgehammer_Doc.proof-store`，与在 jEdit 里一样；这些文件被
`.gitignore` 忽略，第一次跑从头求值。

**跑之前查 heap 链**：`build_logic` 构建整条链，祖先也算在内，所以要查的是 Pure → HOL →
`Performant_Isabelle_HOL` 整条，在每棵树上、每次跑测试之前查。做法是只读地比较会话数据库：
- 每个会话的 `isabelle_sources` 里记的每个文件的 SHA1 都与磁盘上的文件相同；
- 每个子会话记的 `input_heaps` 都等于父会话记的 `output_heap`；
- `ROOT` 只进了一个合并的 `meta_info` 摘要，上面的比较不重算它，所以另外要求这几个会话的 `ROOT`
  文件不比它们的 heap 新。

共享树上 Pure 和 HOL 的数据库在 `contrib/Isabelle2026/heaps`，`Performant_Isabelle_HOL` 的在用户 heap
目录。评审写的脚本在 MLML 的 `ai-artifacts/sh_leading_subgoal_probe/review2/heap_chain_check.py`（不提交；
2026-11-18 两棵树都是干净的）。**有任何不同就停下来问作者，不跑测试。** 不用 `isabelle build -n`：
任何 `isabelle build` 都不能自己跑。按 mtime 扫源码目录会误报（共享树上的 `Wfrec.unicode.thy`），不用。

两种树：MLML 的共享树 `contrib/Isabelle2026`（不带本包），release 4 的 private tree。`Auto_Sledgehammer`
heap 的重建另等作者下令，与测试无关。

### 4.2 检查

**`Test/Test_Leading_Subgoal.thy`**（新文件；不依赖 fact trigger，两种树上都要通过）：

1. 第一部分。`consts P :: "nat ⇒ bool"`；目标 `rev (rev xs) = xs ∧ rev (rev ys) = ys ∧ P z`，在有 target
   的上下文里拆成三个子目标；`auto_sledgehammer_params` 设 `provers = auto, learn = false`；调用
   `sledgehammer_leading_subgoal NONE no_fact_override false`。要求：结果是 `SOME (text, state')`；
   `state'` 恰好剩 `rev (rev ys) = ys` 和 `P z`；`text` 以 `)[1]` 结尾；把 `text` 在原来那个三个子目标的
   状态上重放，也恰好剩这两个。
   为什么要有证不了的第三个子目标：在未保护的状态上，Isabelle2026 的 Try0 会写出 `apply auto [2]`
   （1.1 的不守约定），这段文本放进 `[1]` 里重放不了；只有两个子目标时，不做保护的实现也能通过这条
   检查（复评指出，见 1.2 实测的最后一条和 `review2/R2_Def_Protect_Probe.thy`、`out_def_protect*.txt`）。
   为什么不用任何事实（偏离 2026-11-17 批准的测试描述，那里用公理 `R7`；按作者 2026-11-18 的授权由我
   定）：tactic prover `auto` 按 slice 拿事实，第一个 slice 0 条，第二个 16 条。【评审实测，模拟原版
   Try0 的登记方式，5 次里 5 次】在不带补丁的 Isabelle2026 上，`R7` 无论是公理还是局部事实都证不出：
   0 条事实证不了 `R 7`；16 条的那次里 `R7` 和 15 条全局事实一起给，原版 Try0 把全局事实写在方法名
   后面（`full_attrs` 的 `allows_directs = true`，`try0_util.ML` 第 52 行），`auto` 报 `Bad arguments`、
   整次放弃。不用事实的目标在 0 条事实的 slice 里就证出【评审实测：被保护的状态上给出 `by auto`，两种
   Try0 登记方式都是】，与事实选择、MaSh、Try0 怎么传事实都无关。不带补丁的树上的真实运行在实施时做。
2. hasty 模式。同一个三个子目标的状态，`hasty = true`：结果的 `state'` 恰好剩后两个子目标，`text` 是
   `"<cheat>"`。【评审实测】Normal 模式下 Sledgehammer 的消息里有 `auto found a proof...`，所以 hasty
   那条路确定会走到。
3. 第二部分，没有 target（theory 的 `\<^context>`，level 0）：
   - `facts_as_mepo_lazy_facts true \<^context>` 是空表（现在是 24819 条）；
   - 在这个上下文里用 `Proof_Context.note_thms` 记一条局部事实 `H` 之后，`facts_as_mepo_lazy_facts true`
     恰好给出 `H` 一条。这条正面检查抓的是「把外面的上下文写成 ctxt 本身」：那样上一条检查也会得到
     空表；
   - `should_be_inserted \<^context>` 对 `P y`（`y` 没有固定）得 `false`（现在是 `true`）；在
     `Variable.add_fixes ["y"]` 之后的上下文里得 `true`；
   - 对照：同样的检查在 local theory 上下文（`Named_Target.theory_init`）里结果相同。
   `find_local_may_false` 没有导出，只能经 `auto` 走到，而 `auto` 每次都跑 Sledgehammer；它与
   `facts_as_mepo_lazy_facts` 共用 `named_facts_of`，上面的检查覆盖这个共用函数。

**`Test/Test_Fast_Mepo_Trigger.thy`**（新文件；只在带 fact trigger 的树上跑，因为要用
`Sledgehammer_MePo.add_trigger`；文件开头一句话写明）：

4. 第三部分。`consts g :: "nat ⇒ nat"`，`axiomatization where g_eq: "g x = x + 1"`（不声明为 simp
   规则）；注册一个触发器，给出候选 `g_eq`；在没有局部事实的 `lemma "g 2 = 3"` 里用 `fast_mepo_tac` 证。
   要求证出（现在失败：池为空，MePo 不被调用，`fastforce` 不知道 `g_eq`）。
   `declare [[enable_proof_store = false]]`，与现有测试相同。
   （实施时改的【实测，2026-11-18】：原先写的 `T1: "T 1"` 不行。MePo 在空池上照样调用触发器、选出
   `T1`，但 `T 1` 归为 `T_UNKNOWN`，按 simp 规则加入，而 Isabelle 的 `fastforce` 带着 simp 规则 `T1`
   证不了 `T 1`（Isar 里 `by (fastforce simp: T1)` 也失败；作 intro 规则则证得出）。等式 `g_eq` 归为
   `T_SIMP`，没有触发器时证不出，有触发器时证得出。探针在 `sh_leading_subgoal_probe/debug/`。）

**现有的 `Test/Test_Looping_Detection.thy`**（加一条检查，不新建文件）：

5. 2.2 的 `has_local_free_vars`。在第一个 ML 块（theory 的 `\<^context>`，level 0）里：配置
   `local_ignore_cond = true`，规则 `P x ⟹ f x = g (f x)`（`x` 没有固定）得 `false`【评审实测：现在得
   `true`，改后得 `false`】。文件里已有的 level 0、`y` 固定的那条（得 `true`，改前改后相同）作正面
   对照。第 49–50 行的注释相应改写。

现有的其它 `Test/*.thy`、`Test_Hasher.thy`、`Auto_Sledgehammer_Doc.thy` 在两种树上都要照旧通过。

### 4.3 变异核对

做法：把 `ROOT`、`Auto_Sledgehammer.thy`、`library/`、`document/` 拷到临时目录，在副本上改坏，用 `-d`
指向副本代替 `contrib/auto_sledgehammer`，用 4.1 的命令跑测试；要求对应的检查失败。只在 release 4 的
private tree 上做：共享树上副本会因同名会话被拒绝载入（`Duplicate session`，【评审实测】）。绝不在
共享的工作树里原地改源码。只数失败的检查，装载失败单独报。

| 变异体 | 应失败的检查 |
|---|---|
| 不做保护：没有 `Goal.protect`，`replay` 和 hasty 那条路也不做 `Goal.finish` | 1（Sledgehammer 看到三个子目标，写出 `apply auto [2]`，加 `[1]` 后重放不了，结果是 `NONE`） |
| 不加 `[1]`（重放、返回的都是 `p`） | 1（文本结尾；`auto` 在三个子目标的原状态上重放后只剩 `P z`） |
| hasty 那条路不做 `Goal.finish` | 2（`state'` 里一个子目标也没露出来） |
| `outer_context` 在没有 target 时返回空的外面（即现状） | 3 |
| `outer_context` 在没有 target 时返回 ctxt 本身 | 3（正面检查） |
| 恢复 `if null lazy_facts then []` | 4 |
| `has_local_free_vars` 保留 level 为 0 的分支 | 5 |

**没有测试抓得到的**：把 `replay` 里的 `Goal.finish` 换回 `Goal.conclude`（即不检查证完）。要
Sledgehammer 给出一个在 auto_sledgehammer 的重放下只化简、不证完的候选，我构造不出确定的例子；探针
只证实了 `eval_prf_str_stat` 本身会接受这种方法、`Goal.finish` 会拒绝它（1.2 的实测）。若要直接测，
可以把 `replay` 导出，签名多一项；本稿不这样做。

## 5. 不在范围内

- Sledgehammer 的 tactic prover 违反约定这一根源：fact trigger 第 4 版不修（第 0 节）。
- `hammer` 的循环结构不改（作者：改成「还有子目标就继续」会弄得比较麻烦）。
- 版本号（`VERSION` 现在是 0.3.1）和 conda 发布：等作者下令。
- 2.2 末尾的 Isa-Mini 旁注。
- 别的会话留下的未跟踪文件（`ai-artifacts/ISABELLE2026_PORT_PLAN.md`、`PROOF_REPLAY_PLAN.md`、`port2026/`、
  `reraise_probe/`）不动。

## 6. 顺序

1. 评审和复评已完成（第 7 节），不需要再评。
2. 改源码。改之前确认 `library/.sledgehammer_solver.ML.swn`：2026-11-18 查过，三个交换文件是
   2026-08-09、08-11 的，源文件 2026-11-11 改过，没有 vim 进程开着这个文件，看来是旧的残留；仍然
   先问作者。
3. 按 4.1 跑测试：两种树各跑一遍现有和新增的测试；按 4.3 做变异核对。
4. 提交，只推 `origin`；MLML 的 submodule 指针另问。
5. `Auto_Sledgehammer` heap 的重建、版本和发布：等作者下令。

## 7. 评审记录

**第一轮**（2026-11-18，Workflow `wf_1ef722eb-6df`；三个挑战者分别看第一部分、第二三部分、测试和范围，
每条意见一个新的辩护者，一个裁判）：九条意见，判「修改后接受，需要复评」。保留的意见和处理：
1. 【阻断】测试 1 在不带补丁的 Isabelle 上证不出 → 改用不需要事实的目标（4.2 第 1 条）。
2. 测试命令会构建 heap，变异核对的做法在共享树上不可行 → 4.1、4.3。
3. 草图手写了 `scoped` 和 `Goal.finish`；取结果有三份拷贝 → 1.2 重写；加 hasty 的检查和变异体。
4. hasty 的 `"<cheat>"` 与批准的签名注释不一致；「先重放再加 `[1]`」改为重放加好 `[1]` 的文本 →
   作者定：签名注释加一句、重放加好的文本（第 0 节）。
5. 1.3 对旧行为和候选来源的描述不准 → 1.3 重写；4.3 写明没有测试的那个变异体。
6. 没有 target 的上下文还包括 theory 层的 `instance` 等证明；2.2「谁受影响」不准；测试缺正面检查 →
   2.1、2.2、4.2 第 3 条。
7. 原提案的共用函数仍留着第二份拷贝；不共用时 `find_local_may_false` 没有测试 → 作者定：
   `named_facts_of`（2.1）。
8. 注释的新文字没写出来 → 3.2。
9. 2.2 若改，`has_local_free_vars` 没有检查和变异体 → 作者定改；4.2 第 5 条、4.3。

被驳回的：两处重放各自漏检查的风险（最后的整体验证兜底）；改用 `eval_prf_str` 在重新保护的定理上
重放（离「同一个被保护的状态」更远，还要把定理换进状态）；MaSh 干扰测试 1（无实例）；变异体会覆盖
共享树的 heap（副本载不进去）；第 1 阶段依赖 MePo 内部及给它加 `max_facts <= 0` 的守卫（会改变
`fast_mepo_max_facts = 0` 的含义）；Isa-Mini 的 `global_context_of`（在本库之外）；第二部分那条定为
major（降为 minor）。

**复评**（2026-11-18，Workflow `wf_56693458-8d8`；两个挑战者分别看 1.2–1.3 和第 4 节及第二三部分的
改动，每条意见一个新的辩护者，一个裁判）：看第一部分的挑战者没有提出意见；裁判自己对照源码查过草图，
用评审探针确认检查 1、2 与第二部分的结果。判「修改后接受，不需要再评」，保留三条，都在作者授权我
自决的测试范围内，rev 3 已并入：
1. 变异体表第一行的理由不对：加了 `[1]` 之后，只有两个子目标时不做保护的实现也通过检查 1 → 检查 1
   加证不了的第三个子目标 `P z`，第一行换成「不做保护、也不做 `Goal.finish`」（4.2、4.3；1.2 补实测）。
2. 4.1 的命令跑不了根目录下的 `Test_Hasher.thy`、`Auto_Sledgehammer_Doc.thy` → 按带会话名的 theory 名
   加载，两个文件不改（4.1）。
3. 跑之前只查 `Performant_Isabelle_HOL` 的 heap 不够，`build_logic` 也会重建过期的祖先 → 查整条链，
   用会话数据库比较（4.1）。

被驳回的：只有导出 `replay`（改签名）才能测到保护（三个子目标的测试就够）；改两个根目录文件的
`imports` 来迁就测试命令；按 mtime 扫源码目录、只查 private tree 的 HOL。

**代码评审**（2026-11-18，Workflow `wf_44862436-640`；作者要求在提交前做；两个挑战者分别看 library 的
代码和测试，每条意见一个新的辩护者，一个裁判）：看代码的挑战者没有提出意见，裁判逐项核对代码与 rev 3
一致；判「修改后接受，不需要再评」。保留一条（测试，我自决）：检查 1 里自写的 `apply_text` 与已导出的
`eval_prf_str_stat` 重复，`(intro conjI)` 要加括号只是因为这份重复 → 改用 `eval_prf_str_stat`；第 8 节
补上测试文件最终版本的运行记录。

## 8. 实施记录（2026-11-18，未提交）

作者 2026-11-18 准许改源码，并让我直接删掉 `library/.sledgehammer_solver.ML.swn`（已删；同目录 2026-08 的
`.swo`、`.swp` 未动）。

**改动**（按 rev 3）：`library/helpers0.ML`（`Phi_Help.outer_context`，签名加一项）；
`library/looping_simp.ML`（两处用 `outer_context`）；`library/sledgehammer_solver.ML`（导出
`sledgehammer_leading_subgoal`，`scoped` 挪到它之前，`replay`/`take`，`named_facts_of`，空池也调用 MePo，
注释）；`Test/Test_Leading_Subgoal.thy`、`Test/Test_Fast_Mepo_Trigger.thy`（新）；
`Test/Test_Looping_Detection.thy`（加检查 5，改那段注释）。

**测试**【实测】，按 4.1（从源码加载，不建 heap；跑之前两棵树的 heap 链都干净，`ROOT` 都不比 heap 新）；
输出在 MLML 的 `ai-artifacts/sh_leading_subgoal_probe/run_*`：

| | private tree | 共享树 |
|---|---|---|
| `Test_Leading_Subgoal`（检查 1–3） | 通过 | 通过 |
| `Test_Fast_Mepo_Trigger`（检查 4） | 通过 | 不跑 |
| `Test_Looping_Detection`（含检查 5） | 通过 | 通过 |
| `Test_Staged_Fastforce`、`Test_SMT_CVC5_Variant`、`Test_Proof_Store_Double_Key` | 通过 | 通过 |
| `Test_Hasher`、`Auto_Sledgehammer_Doc`（按带会话名的 theory 名） | 通过 | 通过 |
| `Test_Ground_Eval` | 失败 | 失败 |

`Test_Ground_Eval` 失败在第 43 行 `lemma "fact (6::nat) = 720" by auto_sledgehammer`（`Fail to prove the
goal fact 6 = (720::'a)`：`fact` 的结果类型是多态的，目标在类型上不是 ground）。用 `git archive HEAD`
导出的源码在 private tree 上跑同一测试，同一行同一报错，所以是原有的，与本方案无关。作者 2026-11-18
定：是测试本身的问题，改成 `fact (6::nat) = (720::nat)`；改后两棵树上都通过（`run_ground_private`、
`run_ground_stock`）。

实施时改正的测试本身的错误：检查 1 期望的子目标取自原状态（`tl (subgoals st3)`），因为原目标里 `xs`、
`ys` 的类型变量不同，另写的 `\<^prop>` 对不上；检查 4 的事实见 4.2。检查 1 的状态用已导出的
`eval_prf_str_stat` 拆出三个子目标（代码评审之后改的，原先是测试里一份重复的写法）。测试文件的最终版本
的运行：`run_final_private`（`Test_Leading_Subgoal`、`Test_Fast_Mepo_Trigger`）、`run_final_stock`
（`Test_Leading_Subgoal`），都通过，跑之前两棵树的 heap 链都干净。

**变异核对**【实测】，按 4.3，在 private tree 上、源码副本上：七个变异体都让对应的检查失败，没有装载
失败。M1 不做保护：检查 1 得 `NONE`；M2 不加 `[1]`：检查 1，文本是 `auto`；M3 hasty 不做
`Goal.finish`：检查 2，一个子目标也没露出；M4 没有 target 时外面为空：检查 3，列出的是 `ATP.fAll_def`
等全局事实；M5 外面 = ctxt 本身：检查 3 的正面检查得空表；M6 恢复空池跳过：检查 4，`g 2 = 3` 证不出；
M7 保留 level 0 分支：检查 5，`loops=true`。

**原 bug 的复现**【实测】：1.1 的探针 `No_Subgoal_Probe.thy` 在新代码上（private tree）：对照和三次
`(auto_sledgehammer del: rev_rev_ident)` 全部成功；三次里「先拆再证」那条路都走到了第 2 圈（tracing
`Sledgehammering on the 2th goal (total 2)`），即第 1 圈只证掉了一个子目标。修复前第 2 圈在这里报
`No subgoal!`（7 次里 2 次）。输出在 `sh_leading_subgoal_probe/repro/`。

`Auto_Sledgehammer` heap 没有重建（等作者下令）。
