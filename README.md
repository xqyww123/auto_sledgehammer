Auto Sledgehammer is a slightly smart wrapper of Sledgehammer, allowing users to call Sledgehammer using a normal tactic like ‹auto›.

Example:
```isabelle
lemma foo: ‹(1::nat) + 2 = 3›
  by auto_sledgehammer
```

For more details, we refer readers to [README.pdf](README.pdf).

## Installation

We **only** support [Isabelle2023](https://isabelle.in.tum.de/website-Isabelle2023/index.html) and [Isabelle2024](https://isabelle.in.tum.de/website-Isabelle2024/index.html).

Ensuring `<ISABELLE-BASE-DIRECTORY>/bin` is in your `$PATH` environment, then run the following commands
```
git clone https://github.com/xqyww123/auto_sledgehammer.git
cd auto_sledgehammer
git checkout $(isabelle version) # Error can raise if you are using an unsupported version of Isabelle
isabelle components -u .
isabelle build Auto_Sledgehammer
```
