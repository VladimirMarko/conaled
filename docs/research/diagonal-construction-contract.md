# Diagonal fixture: native contract before abstraction

Issue [#444](https://github.com/VladimirMarko/conaled/issues/444).
This contract was written before the fixture implementation.

For independent types `A` and `Y`, the raw data are `e : A → A → Y`
and `h : Y → Y`. The construction uses the same bound argument twice:
`d a = h (e a a)`. Representation evidence selects a code `c : A` and
an equality `e c a = d a` for every `a`. Its observable witness is `e c c`.
The expected theorem is `h (e c c) = e c c`. Surjectivity of `e` is a
sufficient, stronger hypothesis; Mathlib already proves existential fixed
points from it. Neither hypothesis becomes a global axiom.

The initial worked cases are:

- Boolean constant rows and constant-false `h` select false and yield false.
- Singleton values admit surjective representation and a fixed point.
- Boolean negation admits no selected representation, hence no surjective
  representation of all Boolean-valued functions.
- Translating the sole source code to false among two target codes preserves
  evaluation on translated inputs, but misses a target input that invalidates
  representation. This rejects unconditional transfer of representation.
- Two distinct codes with singleton values have the same fixed-point witness.
  Forgetting the selected code cannot have a left inverse.

Only after these obligations are fixed will a map of constructions be added.
Its independent laws preserve evaluation on translated code pairs and commute
with `h`. They imply local diagonal preservation; transferring representation
also needs coverage of target codes. Invertible changes of presentation must
recover the selected code and value. This is a structure map, with checked
identity/composition laws, without a claim of an already supplied category.

The compiler comparison will retain the duplicated variable in its existing
binding-aware syntax and reuse `compile_sound`. The compiler's single base
sort limits that checked comparison to `A = Y`; the native result keeps the
sorts independent. Compilation does not supply representation evidence.
Curry–Löb will remain a paper-level rule comparison, with truth, provability,
reflection, and diagonalization explicitly separated.
