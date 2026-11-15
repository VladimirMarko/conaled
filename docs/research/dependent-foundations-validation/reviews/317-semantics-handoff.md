# Sigma semantic implementation handoff

Owned files are `SquareKit/Internal/DependentJudgments/Sigma/Capability.lean`,
`Stability.lean`, `Maps.lean`, `Native.lean`, and the root-approved additional
`PairStability.lean`. All are ready for the main implementer's coordinated commit.
No helper commits, tracker operations, workflow restarts, or independent review
were performed. Source-level operation admission and partial-map integration
remain with the main implementer and reindex helper.

## Contract and derivation

`Capability M` quantifies over every context Γ, family A over Γ, and family B
over Γ.A in a specified `PathTransport.Typed.StructuralModel`. It adds the
family `sigma A B`, substitutions `pack : Γ.A.B → Γ.Sigma(A,B)` and `unpack`
in the reverse direction, `pack_over`, and both inverse equations
`unpack_pack` / `pack_unpack`. These accompany new operations. The underlying
structural operations, their substitution laws, comprehension beta/eta, and
identity operations retain their previous definitions and assumptions.

`Capability.split_type` proves C[pack][unpack] = C by **pack_unpack**. Thus
semantic judgmental eta is used to type dependent elimination. This is a full
comprehension-isomorphism contract, not beta-only Sigma. `split` is reindexing
the branch by unpack followed by this cast. `split_beta` uses unpack_pack;
`split_eta`, `split_unique`, and `subTm_pack_injective` follow from the inverse
laws and structural substitution. No final client result is a field. The
metatheoretic equality here interprets the selected judgmental equations; it
is not an object-identity proof or a statement about definitional equality in
Lean.

`Stable M` adds only `sigma_sub` and `pack_sub`. The latter uses the existing
`familyComparison (sigma_sub ...).symm` so that the lifted Sigma substitution
has the correct source context. `sumMap` names that composite. Its projection,
variable, identity, and composition equations are derived. `sigma_comp` and
`sumMap_comp` keep the family comparison between iterated and composite
reindexing. `unpack_sub`, `branch_type`, `branch`, `split_sub`, and
`split_sub_comp` are derived; the composition result includes the actual
comparison rather than silently equating different presentations.

`PairStability` consumes the main implementer's `Capability.pair` and
`pairSubstitution`. `Stable.pairSecond_type` and `pairSecond` do not have an S
argument: their type equality uses only the old structural `section_lift`.
`pairSubstitution_sub` uses `pack_sub` and the existing `lift_pair_square`.
`pair_sub` then follows from generic-variable naturality. The second component
is reindexed with its dependent type cast, not treated as an independent term.

## Model maps and comparison scope

`Map S T` extends the existing `StructuralMap M N`; M and N may have different
universes. Its additional fields are Sigma formation preservation and pack
preservation. `displayFamily` transports the mapped B across the inherited
context-extension equality. `Map.unpack` follows from mapped inverse equations
and target inverse uniqueness. `Map.motive` and `Map.branch` construct the
required context/family transports. `Map.split` is a theorem for every C and d,
proving HEq between the mapped source eliminator and target elimination at
those transported data. It does not require this conclusion as input.
Identity maps and composition are constructed; their unit and associativity
equations are proved. This is the existing strict structural-map boundary;
arbitrary unequal family presentations are covered separately below.

`Native.capability` and `Native.stable` instantiate the existing native Type
model's structural reduct with actual dependent pairs. `packEquiv` is the
reassociation equivalence given by pack/unpack. The native presentation layer
reuses `CoherentTypePresentations.FamilyComparison`: f compares A over a context
equivalence e; g compares B over f.total; `sigmaComparison` constructs the
sum-family comparison. `pack_compare` is its constructor square. For any motive
comparison m over the resulting total equivalence, `comparedBranch` constructs
the transformed branch and `split_compare` follows from the existing general
`extension_map` theorem. This does not pretend the unequal fiber types are
strictly equal or that this native comparison is an arbitrary strict Map.
No higher-groupoid or cubical model claim is made.

## Checked cases and statement review

The initial discriminating obligation was to eliminate a dependent pair with
B(a) = Fin(a+1) into the motive C(a,b) = Fin(a+1), returning b. Native evaluation
can compute this directly; the missing connection was the reusable capability
eliminator and its beta theorem. `Native.bounded_split` uses `split_apply`, which
states the generic capability eliminator's actual dependent evaluation.
`Native.bounded_beta` specializes `Capability.split_beta` at this nonconstant
family and motive. The expected selected value is the supplied bounded index,
not a constant family or an object-identity certificate.

The next case changes presentation: `Native.FiniteOption` reuses the existing
Nat × Bool context equivalence that flips the Boolean, compares the first
Fin(n+1) component with Option(Fin n), and compares the second Fin(a.val+1)
component and the motive with their Option presentations. `preserves_selected`
uses `Native.split_compare`. At the retained sample, the selected source index
is one and the target result is `some zero`; `target_selected_some_zero` uses
`preserves_selected` and `FamilyComparison.term_apply`, so the concrete result
is connected to preservation. `recovers_selected` uses the inverse of the
motive equivalence to recover the whole source section. The theorem retains
exact selected data, not merely inhabitation.

`Native.FiniteOption.split_shift` instantiates `Stable.split_sub` at the
nonconstant source family/motive and the nonidentity base substitution
(n,b) ↦ (n+1,!b). `pair_shift` instantiates `Stable.pair_sub` with first and second
sections selected as Fin.last n; the second section's bound depends on the
first. `pair_sample` checks the intended two last-index components directly.
These use the public substitution results. Universal `sumMap_id` /
`sumMap_comp`, Map identity/composition, and split eta/uniqueness cover the
corresponding helper laws without duplicating each helper as an artificial
example.

Statement review checked the direction of every substitution and inverse;
Γ.A indexing of B; Γ.Sigma(A,B) indexing of C; the pulled-back branch type;
identity versus judgmental/metatheoretic equality; the source contexts in
family comparisons; the quantifiers over arbitrary models, motives, branches,
and map universes; and satisfiability through `Native.stable`. No unused
hypothesis, circular final-theorem field, false beta-only interpretation, or
higher-witness claim was found. The pure structural pair-second conversion
was left independent of Stable. The result of boundedBranch is a bounded
index, and its comment was corrected from an erroneous vector description.

## Validation

- Focused builds of Capability, Stability, Maps, PairStability, and Native pass.
- Final retained-case build: `direnv exec . lake build
  SquareKit.Internal.DependentJudgments.Sigma.Native`, successful with 841 jobs.
  Log: `/tmp/conaled-314-320/reviews/317-semantics-build.log`.
- Explicit statement and axiom spot checks passed using
  `/tmp/conaled-314-320/reviews/317-semantics-statements.lean`; output is in
  `317-semantics-statements.log`. Checked the types of split typing/beta/eta,
  composition, split/pair substitution, map split/composition, native comparison,
  and the selected-presentation theorem. Spot checks introduce no placeholder
  axioms; proof dependencies are recorded in the log.
- No `sorry`, `admit`, or new `axiom` occurs in the five owned source files.
- Existing imported module-system and main-owned unused-simp warnings remain;
  the owned modules' final builds emit no new warnings.
- Full guarded candidate build, exhaustive proof audit, regression fixtures,
  public-entrypoint coverage, and candidate verification belong to the main
  implementation loop and are not claimed by this helper's focused checks.

The final focused build observed shared worktree HEAD
`c7ddcfc552b56bdeb4260a45edbfd56ee539f794`; this is a development checkpoint,
not a separately reviewed helper candidate. The implementation started from
the dispatched approved base `bb77d671`.

## Additional SourceMaps assignment

Root additionally authorized the new `Sigma/SourceMaps.lean` after the first
five files were released. This file is complete and now released to main.

`SourceMap S T` extends the existing full `Typed.ModelMap M N`, then adds only
Sigma formation and pack preservation. Its `toSigmaMap` shares the exact
inherited `toStructuralMap`; there are no independent structural-map records
whose agreement a client must prove. Contextual J preservation remains the
inherited `mapJ` field. Identity and composite SourceMaps are constructed from
the previously proved maps and satisfy unit/associativity equations.

`inputs_some` / `inputs_map` retain the actual dependent B after the operation
decoder succeeds. `operation_map` uses `Map.sigma`, `Map.pack`, and the derived
`Map.unpack`. It requires that the source operation is defined. `partialAlgebra`
proves failure strictness and `partialHom` extends `Contextual.partialHom` over
the new operations. `interpret_map` is the existing generic PartialHom.eval
applied to this constructed partial hom. It covers arbitrary nested expressions
on the extended signature, independently of a particular axiom theory.

The ordinary base-theory facade mirrors #315: Defined is generated from typing
for contexts, families, terms, substitutions, and telescopes. Positive guards
imply argument definedness. TypedAssumptions requires both operands of each
equality assumption to have such source typing. `premises_map` transports those
assumptions and `interpret_target` admits the same derivation at the target.
`Tm.interpret_map` preserves the actual selected interpreted Value using source
typing, without requiring TypedAssumptions for every surrounding raw equality.
`TypedEquality.map` requires typed results and their source equality. It neither
reflects equality nor transports arbitrary source equations involving invalid
values. An arbitrary target derivation conclusion is proved by target-model
soundness under transported assumptions, not by claiming raw equality naturality.

The retained generic author cases `Tm.pair_map` and `Tm.split_map` consume the
ordinary constructor typings and `Tm.interpret_map`. `splitDerivation_target`
uses the previously fixed model-independent split derivation through
`interpret_target`; `splitAssumptions_typed` discharges its assumption boundary
because all its premises are positive typing guards. These exhibit ordinary
reuse without a final client preservation field. SourceMap identity at the
existing native model was also checked to establish an inhabited interface.
The native instance requires explicitly naming `(M := NativeType.model ...)`
when constructing SourceMap.identityMap: Lean cannot infer the full model from
its structural reduct alone. This is host elaboration bookkeeping, not a new
mathematical requirement.

The base typed facade names `Sigma.theory`. The reindexing extension has the
same signature but more admitted rules; it should consume the theory-independent
`interpret_map` or `interpret_term_map`. The latter accepts a semantic term guard
from any admitted theory. Thus a stable-reindexing author obtains it by passing
`Reindexing.interpret d M S ρ hΩ`, without duplicating Defined or constructor
coherence. No claim is made that the base-theory derivation type includes later
reindexing axioms.

Statement review checked the full versus structural ModelMap boundary; exact
sharing of the structural map; operation decoder dependence; definedness and
typed-equality quantifiers; selected Value equality; positive-guard mapping; and
the distinction between target soundness and unconditional raw-equality transport.
No additional stronger assumption or equality-reflection claim was introduced.

Focused validation: `direnv exec . lake build
SquareKit.Internal.DependentJudgments.Sigma.SourceMaps` passed with 837 jobs and
no warnings from the new file. Log: `317-source-maps-build.log`. Explicit type
and axiom spot checks, including the native SourceMap identity, passed in
`317-source-maps-statements.lean` / `317-source-maps-statements.log`. Axioms of
source interpreter preservation are the existing Lean standard axioms
`propext`, `Classical.choice`, and `Quot.sound`; no placeholder axiom is present.
Full candidate acceptance remains with the main loop.
