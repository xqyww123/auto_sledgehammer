structure Eval_Thunk_Data = Proof_Data(
  type T = unit -> term
  val init = fn _ => fn () => error "Eval_Thunk_Data"
);

structure Ground_Eval : sig
  val is_ground : term -> bool
  val eval_ground : int -> Proof.context -> cterm -> thm option
end = struct

fun has_typ_vars_or_frees t =
  Term.exists_type (Term.exists_subtype (fn TFree _ => true | TVar _ => true | _ => false)) t

fun is_ground t =
  not (Term.exists_subterm Term.is_Free t) andalso not (Term.is_schematic t)
  andalso not (has_typ_vars_or_frees t)

fun is_executable_const ctxt thy c =
  Code.is_constr thy c
  orelse Code.is_abstr thy c
  orelse is_some (Axclass.class_of_param thy c)
  orelse (let val cert = Code.get_cert ctxt [] c
              val (_, eqns) = Code.equations_of_cert thy cert
          in is_some eqns end
          handle ERROR _ => true)

fun all_consts_executable ctxt t =
  let val thy = Proof_Context.theory_of ctxt
      val consts = Term.add_const_names t []
  in forall (is_executable_const ctxt thy) consts end

fun mk_equals ctxt lhs_ct rhs_term =
  let
    val ty = Thm.typ_of_cterm lhs_ct
    val eq = Thm.cterm_of ctxt \<^Const>\<open>Pure.eq ty\<close>
    val rhs_ct = Thm.cterm_of ctxt rhs_term
  in Thm.mk_binop eq lhs_ct rhs_ct end

val (_, ground_eval_oracle) =
  Theory.setup_result (Thm.add_oracle (\<^binding>\<open>ground_code_eval\<close>,
    fn (ctxt, ct, rhs_term) => mk_equals ctxt ct rhs_term))

fun eval_bool ctxt ct =
  let val prop_ct = Thm.apply \<^cterm>\<open>Trueprop\<close> ct
  in
    (let val eq = Code_Runtime.dynamic_holds_conv ctxt prop_ct
     in if Thm.is_reflexive eq
        then let val neg_ct = Thm.apply \<^cterm>\<open>Not\<close> ct
                 val neg_prop_ct = Thm.apply \<^cterm>\<open>Trueprop\<close> neg_ct
                 val eq = Code_Runtime.dynamic_holds_conv ctxt neg_prop_ct
              in if Thm.is_reflexive eq then NONE
                 else SOME (eq RS @{lemma \<open>(Trueprop (\<not>P) \<equiv> Trueprop True) \<Longrightarrow> P \<equiv> False\<close>
                                       by (simp add: atomize_eq)})
              end
        else SOME (eq RS @{thm strip_Trueprop_eq})
     end)
  end

fun compile_to_thunk ctxt (program_code, value_code) =
  let
    val code = program_code ^
      "\nval _ = Context.put_generic_context (SOME (Context.map_proof (" ^
      "Eval_Thunk_Data.put (fn () => " ^ value_code ^
      ")) (Context.the_generic_context ())))"
    val ctxt' = ctxt
      |> Eval_Thunk_Data.put (fn () => error "Bad compilation for Eval_Thunk_Data")
      |> Context.proof_map (ML_Context.exec (fn () =>
           ML_Compiler0.ML ML_Env.context
             {line = 0, file = "generated code", verbose = false, debug = false} code))
  in Eval_Thunk_Data.get ctxt' end

fun eval_value exec_timeout ctxt tm =
  let
    val t = HOLogic.mk_term_of (fastype_of tm) tm
    val _ = (Sign.no_frees ctxt o Sign.no_vars ctxt o map_types (K dummyT)) t

    fun comp program _ vs_ty_t deps =
      Exn.result (fn () =>
        let
          val (ml_modules, value_name) =
            Code_Target.compilation_text ctxt "Eval" program deps false vs_ty_t
          val program_code = space_implode "\n\n" (map (Bytes.content o snd) ml_modules)
          val value_code = value_name ^ " ()"
        in compile_to_thunk ctxt (program_code, value_code) end) ()

    fun postproc f = Exn.map_res (fn thunk => f o thunk)

    val thunk_exn = Code_Thingol.dynamic_value ctxt postproc comp t
  in
    case thunk_exn of
      Exn.Exn _ => NONE
    | Exn.Res thunk =>
        SOME (Timeout.apply exec_timeout thunk ())
        handle Timeout.TIMEOUT _ => NONE
  end
  handle Match => NONE | Bind => NONE | ERROR _ => NONE

fun eval_ground seconds ctxt ct =
  let val tm = Thm.term_of ct
      val timeout = Time.fromSeconds (Int.toLarge seconds)
      val is_bool = (Thm.typ_of (Thm.ctyp_of_cterm ct) = \<^typ>\<open>bool\<close>)
  in if is_ground tm andalso all_consts_executable ctxt tm then
       if is_bool then
         Timeout.apply timeout (fn () => eval_bool ctxt ct) ()
         handle Match => NONE | ERROR _ => NONE | Timeout.TIMEOUT _ => NONE
       else
         case eval_value timeout ctxt tm of
           SOME rhs_term =>
             let val thm = ground_eval_oracle (ctxt, ct, rhs_term)
             in if Thm.is_reflexive thm then NONE else SOME thm end
         | NONE => NONE
     else NONE
  end

end
