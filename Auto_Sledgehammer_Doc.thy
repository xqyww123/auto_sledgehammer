theory Auto_Sledgehammer_Doc
  imports Auto_Sledgehammer
begin

section \<open>Installation\<close>

text \<open>This is a standard Isabelle package, following the standard installation instructions
  (We refer readers to Isabelle's \<open>system\<close> document). Basically, you could run the following
  commands

  \<^item> \<^verbatim>\<open>isabelle components <THE BASE DIR OF OUR CODE> \<close>
  \<^item> \<^verbatim>\<open>isabelle build Auto_Sledgehammer\<close>
\<close>

section \<open>Usage\<close>

text \<open>Method \<open>auto_sledgehammer\<close> is a slightly smart wrapper of Sledgehammer, allowing users to
  call Sledgehammer using a normal tactic like \<open>auto\<close>\<close>

lemma foo: \<open>(1::nat) + 2 = 3\<close>
  by auto_sledgehammer

text \<open>
  This tactics first applies \<open>auto\<close> or \<open>clarsimp; ((rule conj)+)?\<close> to simplify and split the
  target proof goal into several subgoals. For each obtained subgoal, it applies Sledgehammer
  successively.

  The proofs obtained by Sledgehammer are cached by the hash of the proof goal.
  When Isabelle's evaluation reaches the last \<open>end\<close> command of a theory file, the cache will be
  stored into a file named "<theory-name>.proof-cache". This cache will be loaded when later
  Isabelle re-evaluates the same theory, so that \<open>auto_sledgehammer\<close> can reuse the cached
  proofs without rerunning Sledgehammer again.

  Sledgehammer can return multiple tactics, while not all of them can terminate in a short
  time. Our \<open>auto_sledgehammer\<close> will replay each tactic within a time limit (by default 20 seconds).
  You could configure this timeout as follows.
\<close>

declare [[auto_sledgehammer_preplay_timeout = 10]] \<comment> \<open>always in the unit of seconds\<close>

text \<open>The first successfully replayed tactic will be returned immediately, killing all other working
  replays and the Sledgehammer process. It speeds up the proof search a lot.
  When Sledgehammer typically spends one minute, this strategy can allow our \<open>auto_sledgehammer\<close> to
  terminate within few seconds.
\<close>

text \<open>
  Before applying Sledgehammer, \<open>auto_sledgehammer\<close> applies \<open>auto\<close> to split a big goal into small
  subgoals. According to our experience, it could improve the success rate of Sledgehammering a lot.
  However, \<open>auto\<close> can non-terminate for complex goals. Thus we impose a time limit (by default, 3 seconds).
  If \<open>auto\<close> timeouts, the tactic tries \<open>clarsimp; ((rule conj)+)?\<close> instead. If it still timeouts,
  the tactic tries plain Sledgehammer without any prelude.

  The Sledgehammer parameters used by this tactic are configurable as follows.
\<close>

declare [[auto_sledgehammer_params = "isar_proofs = false, timeout = 666, minimize = false"]]

text \<open>You can also add additional simplification rules that will be used by our prelude \<open>auto\<close> that
  splits goals.\<close>

declare foo [[\<phi>sledgehammer_simps]]

end