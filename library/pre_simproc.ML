structure Pre_Simproc : sig
  datatype scope = Everywhere | Concl_Only
  type entry = {name: string, pattern: term,
                proc: Proof.context -> cterm -> thm option, scope: scope}
  val register : entry -> Context.generic -> Context.generic

  (* For SIMP/REWRITE: Everywhere entries on full goal, Concl_Only on conclusion *)
  val pre_simproc_on_sequent : Proof.context -> thm -> thm

  (* For HAMMER/auto_sledgehammer: ALL entries on conclusion only *)
  val pre_simproc_on_concl : Proof.context -> thm -> thm
end = struct

datatype scope = Everywhere | Concl_Only

type entry = {name: string, pattern: term,
              proc: Proof.context -> cterm -> thm option, scope: scope}

structure Data = Generic_Data(
  type T = entry list
  val empty = []
  fun merge (a, b) =
    let val names = fold (fn {name, ...} => Symset.insert name) b Symset.empty
    in filter (fn {name, ...} => not (Symset.member names name)) a @ b end
)

val register = Data.map o cons

fun get_entries ctxt = Data.get (Context.Proof ctxt)

fun pre_simproc_conv entries ctxt ct =
  let
    val thy = Proof_Context.theory_of ctxt
    val tm = Thm.term_of ct
    fun try_entries [] = Conv.no_conv ct
      | try_entries ({name, pattern, proc, ...} :: rest) =
          if Pattern.matches thy (pattern, tm) then
            (case \<^try>\<open>proc ctxt ct\<close> of
               SOME (SOME th) =>
                 if Thm.nprems_of th = 0 then th
                 else try_entries rest
             | _ => try_entries rest)
          else try_entries rest
  in try_entries entries end

fun mk_top_restart_conv entries ctxt =
  Conv.repeat_conv (Conv.changed_conv
    (Conv.top_sweep_conv (K (pre_simproc_conv entries ctxt)) ctxt))

fun concl_conv conv ctxt ct =
  case Thm.term_of ct of
    Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs _ =>
      Conv.arg_conv (Conv.abs_conv (concl_conv conv o snd) ctxt) ct
  | Const (\<^const_name>\<open>Pure.imp\<close>, _) $ _ $ _ =>
      Conv.arg_conv (concl_conv conv ctxt) ct
  | _ => conv ct

fun pre_simproc_on_sequent ctxt st =
  if Thm.nprems_of st = 0 then st
  else
    let val entries = get_entries ctxt
    in if null entries then st
       else
         let
           val everywhere = filter (fn {scope, ...} => scope = Everywhere) entries
           val concl_only = filter (fn {scope, ...} => scope = Concl_Only) entries
           val st = if null everywhere then st
                    else Conv.gconv_rule (mk_top_restart_conv everywhere ctxt) 1 st
                         handle CTERM _ => st | THM _ => st
           val st = if null concl_only then st
                    else Conv.gconv_rule
                           (concl_conv (mk_top_restart_conv concl_only ctxt) ctxt) 1 st
                         handle CTERM _ => st | THM _ => st
         in st end
    end

fun pre_simproc_on_concl ctxt st =
  if Thm.nprems_of st = 0 then st
  else
    let val entries = get_entries ctxt
    in if null entries then st
       else
         Conv.gconv_rule
           (concl_conv (mk_top_restart_conv entries ctxt) ctxt) 1 st
         handle CTERM _ => st | THM _ => st
    end

end

val _ = Theory.setup (
  Method.setup \<^binding>\<open>auto'\<close>
    (Scan.lift (Scan.option (Parse.nat -- Parse.nat)) --|
      Method.sections Clasimp.clasimp_modifiers >>
    (fn NONE => (fn ctxt =>
          SIMPLE_METHOD (CHANGED_PROP (
            PRIMITIVE (Pre_Simproc.pre_simproc_on_sequent ctxt)
            THEN Clasimp.auto_tac ctxt)))
      | SOME (m, n) => (fn ctxt =>
          SIMPLE_METHOD (CHANGED_PROP (
            PRIMITIVE (Pre_Simproc.pre_simproc_on_sequent ctxt)
            THEN Clasimp.mk_auto_tac ctxt m n)))))
    "pre-simproc preprocessing followed by auto"
)
