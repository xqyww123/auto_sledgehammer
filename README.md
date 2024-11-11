Auto Sledgehammer is a slightly smart wrapper of Sledgehammer, allowing users to call Sledgehammer using a normal tactic like ‹auto›.

Example:
```isabelle
lemma foo: ‹(1::nat) + 2 = 3›
  by auto_sledgehammer
```

For more details, we refer readers to [README.pdf](README.pdf).

## Installation

Ensuring `<ISABELLE-BASE-DIRECTORY>/bin` is in your `$PATH` environment, then run the following commands
```
isabelle components -u <THE-BASE-DIRECTORY-OF-OUR-PROGRAM>
isabelle build Auto_Sledgehammer
```
