# Varying bodies under a dependent telescope

[#382](https://github.com/VladimirMarko/conaled/issues/382) extends the
[fixed nominal telescope](nominal-dependent-telescope.md) with a generated
body language. [NominalBodies](../../SquareKit/Internal/NominalBodies.lean)
constructs substitution and interpretation; its
[checked cases](../../Examples/NominalBodies.lean) preserve three distinct
selected results through the same two base changes. The earlier interface and
its clients remain unchanged.

## Selected contract

The inputs remain `a : Fin(N+1)` and `b : Fin(|a|+1)`, with free natural
expressions `N,Z`. Bodies contain first and second projections, arbitrary free
expressions, and binary addition. Their arithmetic value is reduced modulo
`Z+|a|+1`; the output is the selected element of `Fin(Z+|a|+1)`, observed
together with that dependent index. This contract was fixed before the named
representation. Modulo is an explicit operation of this fragment, including
when a sum wraps; it is not an implicit identification of arbitrary natural
outputs.

At `Z=5,a=2,b=1`, the second projection selects 1 and the sum of the two bound
inputs selects 3. Adding a free leaf whose transported value is 3 selects 6.
The examples derive observations `(7,1)`, `(7,3)`, and `(7,6)` using
`two_substitutions`. Reconstructing the earlier fixed second projection loses
two of these results, as `reset_body_fails` checks.

`contextual` is an intrinsic function into the dependent finite family. The
body grammar is uniformly typed by that interpretation: every generated body
has the same dependent result family at given inputs. There is no separate
arbitrary type-expression grammar or claim of a general dependent typing
calculus. The contextual program retains the two free bounds and the entire
body tree, without bound atom names.

## Named realization and local laws

A representative contains a body tree and a finite-permutation `Frame` fixing
an initial segment containing the free atoms of **both bounds and the body**.
`Body.concretize` recursively produces an actual named expression. Its bound
occurrences use the two frame names; free leaves retain their expression
syntax. `Representative.annotations` supplies the named dependent type
annotations, and `annotations_eval` proves their indices and the body value
agree with the independent contextual interpretation. The nominal interpreter
evaluates the named result annotation and body, then constructs its finite
result. `Representative.comparison` preserves the full dependent observation.

Alpha is defined by unchanged body constructors together with the existing
admissible finite-permutation orbit on frames. Its definition mentions no
interpreter or contextual erasure. `Body.concretize_action` proves that the
frame action really renames all named body occurrences; free expressions stay
fixed by the support condition. Every body has a canonical fresh frame.
`alpha_iff` derives, rather than assumes, that representatives are related
exactly when their body trees agree. Accordingly the quotient has many classes
at fixed `N,Z`; it does not identify different arithmetic syntax merely because
some evaluations agree.

`reopen` chooses a fresh frame for a quotient body; `reopen_abstract` proves
that abstracting it returns the original class. `contextual_roundtrip` and
`nominal_roundtrip` compare whole programs. These are bounded presentations:
named expressions are generated from the body grammar and a simultaneous
frame, rather than accepted by a parser for unrestricted named syntax.

`Body.subst` traverses every free-expression leaf. Its identity, composition
and evaluation laws follow by structural induction and the existing expression
laws. `under` sends old bound atoms to the new bound atoms and other atoms to
the substitution images. `free_under` discharges its freshness condition;
`concretize_subst` connects the recursive body substitution with raw expression
substitution under the telescope. This raw equation alone does not assert the
new frame avoids substitution images. `substitute` constructs a canonical
frame at the *new* support, so `Frame.fresh` supplies that missing fact.

The quotient identity/composition laws follow from these local syntax laws
and the proved presentation round trips. `observe_substitute` uses the existing
typed lifts beneath both dependent binders and the new body evaluation law.
`substitute_preserves` connects the quotient operation to that result;
`two_substitutions` composes it. No field assumes a whole substitution theorem.
The comparison uses Lean equality of dependent finite values, retaining index
and selected number, with proof irrelevance for the inequalities.

## Controls and maintenance obligations

The body-only free atom 8 forces initial bound names 9 and 10, even though
neither type bound mentions it. Substituting free atom 9 requires fresh bound
names 10 and 11. The checked raw substitution equation uses `concretize_subst`.
At free value 7 and bound inputs 2,1, fresh evaluation gives 8. Reusing the old
frame captures free atom 9 and gives 3. The original two colliding substitutions
are also reused for all three selected observations.

`no_bound_name_observer` proves that an observer returning the chosen first
binder spelling cannot descend to the new quotient, for every admitted body.
The selected-value reset to zero fails independently of resetting the whole
body. A wrapping-sum example checks the explicit residue contract at `Z=0`.
The original second projection is recovered by `second_specialization` using
its bound to prove the modulo operation is inactive. `selectedTail_retains`
connects the old third-tail client to this specialization, and `third_selected`
uses the existing two-change tail theorem to retain `(7,1,1)`. This does not
assert that an arbitrary varying result admits the old third component: its
family depends on the selected second value, and a changed body can change
that bound.

The extension from the old fixed body reuses finite permutations, frames,
freshness, intrinsic input families and their typed lifts without changes.
Adding first/free/add requires their concrete syntax, support, interpretation,
and structural cases in the three body substitution laws and the two
concretion laws. The quotient round trips and program substitution proofs use
those local laws; they do not examine particular arithmetic examples. Extending
the grammar again would require the corresponding new structural cases and
a result-typing proof if the residue contract changed. A new dependent binder
or nested abstraction would also change frames, annotation typing and lifting;
none follows from the present two-binder experiment.

The contextual formulation avoids support and frame proofs. The nominal route
provides explicit named syntax and checked capture avoidance. Both meet the
same selected contract. No productivity advantage follows from their source
sizes, and no native client must migrate. Under
[#289](https://github.com/VladimirMarko/conaled/issues/289), the remaining
binding obligations are nested/varying telescopes and body-dependent typing;
weak-model coherence is still separate. This result does not choose a universal
nominal frontend. #107 remains paused, #108's held-out theorem unselected,
and #260 inactive.
