# Native structure identity: implementation direction

Issue [#625](https://github.com/VladimirMarko/conaled/issues/625) needs a native
family of structures over the carrier universe, followed by a total internal
path/isomorphism theorem. Use native Sigma and Pi to interpret descriptions;
retain the existing set-level `Transport` interface and prove comparisons at
presented carriers.

The independent [foundations](foundations.md), [use](use.md), and
[alternatives](alternatives.md) assessments agree on this direction. They answer
[this brief](brief.md) by inspecting declarations; their proposed proofs were
not compiled. In particular, native functions contain restriction-indexed data,
so pointwise host functions are not their general semantics. Transport along
bijections cannot define an action on arbitrary decoder restrictions.

Implement [#605](https://github.com/VladimirMarko/conaled/issues/605)'s fixed-level
Cartesian constructor admission first. The original model already has this
layer. Then develop native descriptions, a total Sigma-path comparison using
each model's own univalence, and independently defined structure preservation.
Laws require admitted proposition families and explicit sethood assumptions
where equality is intended to be propositional. Dependent non-proposition
fields must retain their witnesses.

A native family alone does not complete #625. Neither does a theorem whose
structure-isomorphism relation is defined to be a dependent path over ua:
fieldwise preservation, law semantics, existing-client recovery, and the
specified comparisons remain obligations. Restricting the original model's ua
also does not identify it with the independently chosen Cartesian ua.

A discrete-carrier subuniverse remains a possible complementary formulation.
It needs its own admission, equivalence closure, and higher path recovery;
there is no existing shortcut through a global presentation or `PathDiscrete`.
Keep this alternative available if it serves arbitrary equivariant data beyond
the description grammar. Do not require it for constructor admission.
