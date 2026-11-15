# Issue #108 independent candidate and protocol

Phase 1 scope dossier, 2026-11-09. This document contains no Lean proof,
motive, proof skeleton, or theorem-specific helper. A separate solution-free
scope check and coordinating phase release are required before construction.

## Candidate and provenance

I independently select `foundation-core.identity-types.inv-inv` from
[agda-unimath at 75518656f287c203b41cb7f71df46e02b987a084](https://github.com/UniMath/agda-unimath/blob/75518656f287c203b41cb7f71df46e02b987a084/src/foundation-core/identity-types.lagda.md).
The declaration is under the section “Inverting identifications is an
involution”. Its exact statement, including surrounding parameters, is:

```agda
module _
  {l : Level} {A : UU l}
  where

  inv-inv : {x y : A} (p : x ＝ y) → inv (inv p) ＝ p
```

The source license is MIT, copyright (c) 2022 Egbert Maarten Rijke. The complete
[notice at the same revision](https://github.com/UniMath/agda-unimath/blob/75518656f287c203b41cb7f71df46e02b987a084/LICENSE.md)
is retained in `inputs/upstream/LICENSE.md`, with the exact upstream identity
and universe-level files. Any adaptation will retain the notice. I inspected
the public upstream proof and neighboring declarations; that is a declared
permitted input, not an implementer-supplied solution. No Agda compilation was
run, and no claim is made about a compiler-checked minimal dependency export.

Selection occurred after the repository freeze at
`2f89f8651843797822efbb7da038311ab3d9f04d`. The parent supplied no candidate or
candidate-specific guidance. The author launch/exposure record is in
`prospective-log.md`. No private conversation, scratch directory, other worker
checkout, or unpublished solution was read. I have no prior participation in
#115/#116/#117 or any other listed excluded work in this agent session.

## Declaration closure and fragment fit

| Dependency | Origin | Requirement |
| --- | --- | --- |
| `Level`, `UU` | `foundation.universe-levels`, reexporting `Agda.Primitive` | Ambient universe/type parameters |
| `Id`, `_＝_`, `refl` | `foundation-core.identity-types` | Identity formation and reflexivity, also at a path type |
| `inv` | Same identity-types module | Derived path reversal, with endpoints exchanged |
| `inv-inv` | Same module | An identity between double reversal and the supplied path |

The declaration/proof closure needs identity elimination and its reflexivity
computation, dependent context formation, substitution, and conversion. It does
not need concatenation, transport composition, function extensionality, UIP/K,
univalence, higher inductive types, cubical primitives, or a universe *inside*
the generated source language. Agda's implicit functions and type/level
parameters become an externally quantified generated judgment schema. This is
the same bounded treatment of universes as the earlier transfer, not a claim
to encode Agda's universe hierarchy. The generic source carrier may itself be
an identity family; it is not restricted to a set or a discrete model.

The frozen guarded theory admits the required identity rules and contextual
operations. An inverse source recipe was not found in the inspected guarded
public API. Constructing any required recipe, substitution laws, or conversion
helpers is incremental author effort within the cap, not permission to change
the frozen theory. No such code has been constructed in Phase 1.

## Intended generated conclusion

For arbitrary generated context Γ, family A over Γ, sections x and y, and
p of source identity type `Id A x y`, construct one generated term with type

```text
Id (Id A x y) (inverse (inverse p)) p.
```

Here `inverse` denotes the source operation corresponding to upstream `inv`;
it is not Lean equality symmetry or a semantic-only operation. The theorem
must remain valid for arbitrary p and endpoints. Restricting p to reflexivity,
assuming double inversion as a premise, or returning a bare target theorem
would fail this scope. The source assumptions must be conventional typing
assumptions for the supplied context, family, endpoints and path. No
caller-supplied model-code equality or source conclusion assumption is allowed.

The source conclusion is an inhabited identity type, retaining the selected
certificate. It is not merely an untyped equality between raw syntax trees.
The final correspondence record must explain how the upstream operation and
argument were preserved. This dossier deliberately contains no construction
plan for either source inversion or its involution proof.

## Semantic applications and statement review

A successful attempt must interpret that same generated derivation through the
frozen guarded soundness theorem and retain the evaluated source certificate.
It must establish the source assumptions for the actual application inputs.
Required applications are:

1. A general ordinary-groupoid application: for arbitrary context, family,
   endpoint sections and path section, identify the interpreted source inverse
   with categorical inversion and the two endpoints with double inversion and
   the original path. The same source certificate must supply the resulting
   identity section; a separately proved groupoid law cannot replace it.
2. Faithful and ineffective C4 applications using the frozen labeled models.
   Arbitrary labels must retain the double-inversion conclusion. A checked
   nonzero example must observe label 1, whose single inverse is label 3 and
   whose double inverse is label 1. In the ineffective model, retain a checked
   distinction between the label-1 and label-0 endpoint observations despite
   their identical fiber action. These are applications of the same source
   derivation, not independent target-only proofs.
3. An ordinary source reindexing specialization for the result under a typed
   substitution, retaining its substituted endpoints and certificate. Any
   comparison with a freshly constructed certificate must state exactly what
   is proved; equality of selected higher witnesses is not assumed.

Statement review will check endpoint order, all quantifiers, the identity level,
assumption satisfiability, general p, correspondence with the declared inverse
operation, and the exact connection from soundness to each consumer. The
nonzero C4 examples check that an interpretation has not silently replaced all
paths by reflexivity. Ordinary groupoid identity fibers are discrete, so these
consumers do not establish faithfulness for arbitrary higher models.

## Public preparation and task-size assessment

Name/variant searches across the frozen repository found no `inv-inv`,
`invInv`, `inverseInverse`, `doubleInverse`, `inverse_inverse`, or source
path-symmetry involution translation. The broader search also inspected
involution and symmetry references and the existing guarded source operation
inventory. General algebraic involution hypotheses and `Equiv.symm_symm`
appear in unrelated applications; neither supplies this source derivation.
The nearby inverse operations in `PathTransport/Two*` are semantic categorical
constructions, not a generated source involution theorem. No prepared
specialization of the selected generated statement was found.

The public #115 material inspected consists of `IdentityPattern`, the
Monodromy/FrozenMemo declarations, HigherWitness, and the inspection report.
Those declarations concern generic J, transport, dependent witnesses, and
monodromy, not double inversion. The frozen reports for #116/#117 describe
surface-design/comparison work and point to bounded elaboration; searches
found no selected-candidate translation in that corpus. Searches alone do not
prove semantic non-equivalence across the entire repository. The independent
scope checker must verify equivalent statements and theorem-specific
preparation across the full permitted corpus before release. A discovered
prepared equivalent is a scope failure, not permission to rename it.

`inv-inv` is different from `tr-concat` and `assoc`, and is neither a renamed
copy nor a reflexive restatement of either. It has one arbitrary path and no
extra dependent argument tail. It is mathematically smaller than the earlier
associativity task, while requiring a new derived operation and an identity at
the path level. Success therefore cannot establish that the repair removed
all of #106's dependent-tail friction or demonstrate a causal productivity gain.

## Frozen capabilities and actual inputs

The full public tree at the exact freeze is allowed. The #107 handoff in
`inputs/handoff-107.json` contains the public capability inventory, separating
repair work from intervening developments. Principal available capabilities:

| Layer | Frozen entry points | Relation to #106 |
| --- | --- | --- |
| Guarded/contextual theory | ContextualRules, TelescopePresentation | Added before resumed repair; absent from original trial boundary |
| Finite-tail authoring | PresentedElimination, PresentedSquares, TelescopeAuthoring, SourcePath, SourcePathArguments | Reusable repair mechanisms |
| Known left-concatenation regressions | LeftConcatenationSubstitution, LeftAssociativity, LeftTransportComposition and GuardedLeft examples | Framework-assisted known work, excluded as candidate |
| Soundness/ordinary models | PresentedSoundness, PathTransport models, GroupoidTransport/GroupoidRoutes | Public semantic interfaces and retained clients |
| Other source/corpus facilities | ReferenceDependentCalculus, bounded elaboration, higher/cubical source examples, Agda inspection corpus | Distinct later capabilities; no general importer promised |

Actual code inspected so far: `DerivedPaths.lean`, `ReferenceDerived.lean`,
`PresentedSoundness.lean`, and `Examples/GuardedLeftConcatenation.lean`; declaration
and search excerpts from the authoring/source-path/presented-elimination modules
and broader corpus. The generic C4 consumer was read as a public application
example. Actual documentation inputs: repository instructions/README, skills
and standards recorded in the log, guarded repair report, #106 protocol/log/
category summary, Agda frontend and internal-retention reports. Some large
batched output was truncated; no claim is made to have read every byte of those
batched files. Targeted searches and reads established the facts used here.
All actual upstream bytes are pinned and retained under `inputs/upstream/`.
Full live #108 and #106 responses and the exact #107 handoff were saved before
selection. The #106 archive was checked unchanged against commit `429c7cc`.

## Budget, phase boundary and archive

The cap is 40 substantive cycles total, starting with the setup/protocol
investigation already logged. Retain #106's exact definition: “A cycle consists
of one recorded investigation or one logically grouped edit followed by its
targeted check. Multiple checks within a cycle are recorded separately.”
Categories are dependency investigation, proof translation, helper writing,
debugging, application, and validation. All investigation, translation,
operation/helper work, debugging, and applications consume this budget.
Accounting/reporting infrastructure is recorded separately; it must not hide
proof edits or checks. No budget reset occurs at the phase boundary.

Record a checkpoint at cycle 10 and each later ten-cycle boundary. Preserve
progress at cycle 10 even if no source judgment exists. At most two full fresh
validation invocations are allowed after successful construction; corrections
still count within the original cap. Use normal production resource limits,
the pinned shell/toolchain and full fresh build/exhaustive audit for success.
Failed scratch remains outside the production import closure. This initial
phase adds no production imports and runs no Lean compilation.

Stop early on validated success, a demonstrated unsupported requirement or
required API change, contamination, or an instruction to stop. Stop at cycle
40 otherwise. No theorem weakening/switch, coaching, framework change, budget
extension, or assisted retry may convert this independent attempt to success.
Archive the attempted caller, each failed version, commands/diagnostics, effort
categories, statement review and report with hashes before any feedback,
repair, direct-Lean comparison, or assistance. The evaluator and final
Standards/Spec review are coordinated after archival by the parent; the author
will not spawn nested reviewers. Negative/inconclusive is a valid outcome.

Phase 1 ends here. The independent scope reviewer may return scope/measurement
findings only, with no Lean motive, proof plan, tactic, or helper. The candidate
and prospective protocol will be locked by SHA-256 after that disposition and
before the explicit Phase 2 release. Any substantive scope change before
release must be recorded and independently rechecked.
