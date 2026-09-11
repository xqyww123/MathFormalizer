# MathFormalizer

A base theory for mathematical formalisation in Isabelle/HOL on top of HOL-Algebra.

`Math_Formalizer.thy` imports `HOL-Algebra.Algebra` and installs a term order for the simplifier
that knows the ring operations of HOL-Algebra (`ring_term_ord.ML`). With it, ordered rewriting with
`ring_simprules` / `cring_simprules` reaches the same normal forms as the `algebra` method, while
the AC normal forms of every other operator stay exactly as with the default order.

Details, and the one known behavioural consequence (`zero`/`one` are ordered before variables, the
default order puts them after), are documented at the top of `ring_term_ord.ML`.
`Math_Formalizer_Tests.thy` checks both properties.

## Use

```
isabelle build -d . MathFormalizer
```

or import `Math_Formalizer` from a theory in a session based on `HOL-Algebra`.
