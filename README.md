Auto Sledgehammer is a slightly smart wrapper of Sledgehammer, allowing users to call Sledgehammer using a normal tactic like ‹auto›.

Example:
```isabelle
lemma foo: ‹(1::nat) + 2 = 3›
  by auto_sledgehammer
```

For more details, we refer readers to [README.pdf](README.pdf).
