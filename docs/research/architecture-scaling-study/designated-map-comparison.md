# Designated maps expose the source/model admission gap

Research and checked controls for [#366](https://github.com/VladimirMarko/conaled/issues/366),
2026-11-08, based on `f6aec438c8e354ac0fe4ab856e3f7b75a45a7109`.

The bounded comparison has a **negative admission outcome**: neither route
implemented here interprets the unchanged quantified dependent source theorem
in both required settings. We constructed the native designated-map argument,
an independent direct/guarded comparison for a smaller action language, and a
groupoid control that rejects a proposed native-identity encoding. These are
usable checked results, but their combination is not the missing interpretation.
The evidence does not choose an architectural winner or refute natural models.

The concrete failure is informative. A native equality between the sole object
of the C4 groupoid and itself cannot retain the chosen gluing label. Actual
groupoid arrows do retain it, and the actual restriction map is still an
equivalence. We should construct the required dependent operations jointly in
a witness-sensitive setting before claiming that this consumer can use either
source interpretation. Adding an equivalence record between endpoint carriers
does not repair the failure.

## Source slice and declaration correspondence

The source is checkpoint 080's
`formalization/src/Orbifolds/Intensional/DerivedAtlasOrbifold.agda`, with
`PushoutLifting.agda` and `Equivalence.agda` in that directory. The exact archive,
source hashes, original consumer reports and existing acceptance receipts are
preserved in the [checkpoint directory](../../history/orbifold/agda-checkpoints/checkpoint-080/README.md).
We read these sources as mathematical evidence. No Agda source was imported
into the production library or translated automatically. This experiment adds
no new Agda acceptance claim.

The selected declarations lie in `Test`, before the later `Theory` module.
The source passes `baseNW` into `Gap`, but `gap` itself depends only on the
boundary, universality and target cocone. The selected argument does not use
`origin`, bounded truncation, or the later weak `FunExt` parameter. Its
`isEquiv` means contractible fibers; it is not merely a proposition asserting
that some equivalence of the endpoints exists.

| Source declaration | Reconstruction and exact boundary |
|---|---|
| `Cocone`, `post-cocone` | `Extensional.Cocone`, `Cocone.post`: two legs and equality of their composites; the latter maps the gluing proof by `congrArg`. Native equality is proof irrelevant. |
| `PushoutBoundary`, `restriction`, `IsPushout` | `Boundary`, `restriction`, `Universal`: the designated restriction, quantified over all `Type u` targets in Lean. Universality is supplied to the general theorem and constructed for the identity-span example. |
| `isEquiv→Equiv`, `equiv→isEquiv` | `toEquiv`, `fromEquiv`: actual forward map and chosen inverse extracted from fiber centers. Both inverse laws are proved. Native fibers are subtypes because their equations are propositions. |
| `Chosen.gap`, `gap-section` | `Boundary.gap`, `gap_section`: inverse of the actual restriction evaluated at the target cocone, with its section law. |
| `mapping-comparison` | `Boundary.mappingComparison`: actual postcomposition with the supplied target cocone. |
| `restriction-naturality`, `comparison-computation` | `Cocone.post_comp` followed by `Boundary.comparison_computation`: postcomposition and the section yield equality of the whole native cocone. The native extensionality lemma does not retain distinct gluing proofs. |
| `homotopy-isEquiv`, `cancel-right-isEquiv` | `homotopy`, `cancelRight`: derived using native `funext`, transport and composition of actual equivalences. These are native reconstructions, not the source's intensional fiber-path derivations. |
| `mapping-square-local` | `Boundary.mapping_square_local`: derives contractible fibers of precomposition by the chosen gap. No field assumes that final conclusion. |

The definitions and proofs are in
[Extensional.lean](../../../SquareKit/Internal/DesignatedMap/Extensional.lean).
The precise argument is

```text
r_Z(h ∘ gap) = post(h, r_SE(gap)) = post(h,c) = m_Z(h).
isEquiv(m_Z), isEquiv(r_Z)  imply  isEquiv(precompose(gap)).
```

The first equality in the source uses composition of action on identity paths,
including the third cocone component. Our native control proves the endpoint
statement with stronger host equality principles. It cannot therefore serve
as an unchanged source derivation in another model.

## What the two interpreters actually interpret

[Interpretations.lean](../../../SquareKit/Internal/DesignatedMap/Interpretations.lean)
contains an independently specified two-sort language: maps and cocones,
variables, map composition, and postcomposition. Its proof language supplies
reflexivity, symmetry, transitivity and the local postcomposition equation.
Its semantic maps are endomaps of one externally selected target `Z`. There
are no object-level dependent binders, universe quantifiers, identity types,
fiber constructions or cancellation proofs in this language.

The direct route recursively interprets these operations and derives
`direct_subst`, `direct_twice` and `direct_sound` by induction. It calls no
guarded soundness theorem. The guarded route has its own operation signature,
typing predicates, invalid value and guarded postcomposition rule. `rule_valid`
proves the local rule. `postCompDerivation` applies that rule with its typed
premises, and `guarded_sound` invokes engine soundness. `encode_eval` connects
the actual syntax translation to direct evaluation; `compare_twice` proves
agreement for arbitrary two well-sorted substitutions.

This is a comparison with the guarded engine's local-rule mechanism, **not**
an extension of the dependent `Reference` interpreter to the full source
slice. The existing
[ReferenceSoundness](../../../SquareKit/Internal/DependentJudgments/ReferenceSoundness.lean)
continues to translate through `TelescopePresentation.model`, including typed
equality operand guards. The new direct interpreter does not secretly call
that theorem. Conversely, its smaller signature does not demonstrate that
replacing the reference calculus would remove dependent constructor costs.

Alongside the action interpreters, `Represented` makes the native model-admission
attempt explicit:

- `Code` packages a small `Type u`, with `pi`, `sigma` and `identity` carrier
  operations. The code object itself is larger. `identity` lifts Lean equality,
  so lifting changes its sort without creating higher identity information.
- `fiberCodeEquiv` connects the constructed Σ/Id fiber code to the native
  fiber, preserving its selected preimage. `applyPi` and the dependent
  `lastFamily` example exercise the Π carrier.
- `represent` reuses `LocalUniverses.Family.comprehensionEquiv` on the decoded
  family. Its naturality and unique pairing construct the representation of
  sections over arbitrary base maps. This avoids duplicating the existing
  Type-family comprehension proof.

These are real semantic operations and representation laws. They are **not**
a constructed presheaf natural transformation with all admitted source rules,
or a theorem interpreting a dependent source derivation. The action syntax
has no binder whose interpretation uses this representation. No code of the
universe, decoding judgment or source quantification over that code object
has been admitted. The native `Universal` theorem quantifies over host types;
that host quantifier must not be presented as the missing object-language one.
An externally indexed family of action interpretations is strictly weaker
than the original `(Z : Set ℓ)` source statement.

## Checked substitutions and selected dependent data

[DesignatedMapComparison.lean](../../../Examples/DesignatedMapComparison.lean)
contains the applications.

The native experiment at parameter `n` uses `Fin(n+2)` for the identity span
and chooses reversal for both target legs. Its actual mapping comparison is
an equivalence, constructed from reversal and the identity-span restriction.
Cancellation yields a fiber center; `selected_inverse` identifies that center
with reversal using the derived fiber contraction. Substitutions `m ↦ m+1`
and `k ↦ 2*k` change the carrier. At `k=2`, the retained inverse sends zero
to 6 in `Fin 7`. Both the preimage and its equation inhabit the actual fiber.
This is a native family computation, not a two-substitution theorem for the
unconstructed quantified source term.

The action-language fixture first computes 8 at input 3, then 14 after one
nonidentity substitution and 7 after the second. `compared` exercises the
general guarded/direct comparison rather than a separate arithmetic proof.
The selected tail is `Fin(output+1)` with its last element. `extended_represents`
connects it to comprehension; `extended_twice` applies representation
naturality to arbitrary two base maps. The nonidentity base substitutions
above select 9 in `Fin 10`, retaining the bound as well as the value.

These controls separate three contracts: syntactic substitution for the
bounded action language, semantic reindexing of a selected dependent family,
and native cancellation of the designated map. There is no theorem connecting
all three as the interpretation of one quantified dependent source term.
The report does not fill that gap by assuming a global preservation field.

## Groupoid gluing and the failed native-identity shortcut

[GroupoidControl.lean](../../../SquareKit/Internal/DesignatedMap/GroupoidControl.lean)
constructs, for any groupoid `G`, the actual functor
`restriction : G ⥤ Arrow G` sending `x` to its identity arrow. This is the
cocone control for the terminal identity span: two selected objects and an
isomorphism between them form an arrow. `universal` constructs its inverse
and natural unit/counit. The counit's right component is exactly the selected
arrow, as `section_right` proves. No nonidentity-gluing obstruction to
universality is assumed.

Postcomposition by `F : G ⥤ H` maps the entire arrow. `section_natural`
retains its commuting square, including the comparison from `F.map_id`.
That comparison cannot be silently replaced by literal equality of the
restriction objects. This is a categorical control with functor arrows and
natural transformations, not an interpretation of the source's internal Π
and `isEquiv` judgments.

Specialize to the one-object groupoid with automorphism group `ZMod 4`.
`selected_section` retains gluing label 1. Postcomposition by multiplication
by 2 sends it to 2, while sending label 0 to 0; `selected_post` distinguishes
them. The independent negation equivalence preserves the endpoint groupoid
but sends gluing 1 to 3. `unrelated_equivalence_changes_glue` therefore rejects
substitution of an arbitrary endpoint equivalence for the designated map.

The attempted shortcut is explicit: decode this groupoid to its object type
and interpret each loop by native equality at the sole object, then attempt
to recover its gluing label. `no_native_glue_observation` quantifies over
**every** such encoding and observation and disproves recovery. Proof
irrelevance identifies the encoded loops 0 and 1, contradicting their required
observations. `Represented.identity` has the same limitation even after its
universe lifts. The failure concerns this native-identity encoding; actual
arrows in the constructed groupoid retain the labels. It does not establish
that a groupoid universe, natural model or weak coherence construction is
impossible.

The existing non-orbifold second-identity observation is retained as a checked
regression through `LocalUniversesBoundary.Witnesses.higher_observation`.
Its imported construction is independent evidence. The C4 model itself has
no nontrivial second identities and cannot discharge #359's stronger task.

## Constructor admission and primary-source applicability

The natural-model alternative remains eligible. Awodey's Definition 1 and
Proposition 2 use a representable natural transformation of presheaves on a
small category with a terminal object to obtain the category-with-families
structure. Type constructors require further structure. Theorem 32 assumes
a closed, stable, factorizing class of maps to obtain Σ, Π and intensional
Id. A representation bijection for native families alone does not establish
those hypotheses for our groupoid interpretation, nor construct the source's
internal universe. [Awodey, v3, §§1–3](https://arxiv.org/html/1406.3219v3).

The weak-model route need not first fill strict incumbent fields. Lumsdaine–Warren
Theorem 3.4.1 requires a **full** comprehension category, condition LF, and
weakly stable constructors. LF requires finite products and the specified
dependent exponentials when the first map is display and the second is
display or a product projection. The theorem supplies strict structure in the
split replacement. It does not supply an internal classifier merely because
its construction uses local universes; its generalization also excludes
arbitrary type-equality conclusions. [Lumsdaine–Warren, v2, Definitions 3.1.2–3.1.3,
Theorem 3.4.1 and §4.1](https://arxiv.org/pdf/1411.1736v2).

For the attempted groupoid admission, the next construction is concrete:
sections of a dependent family must form a groupoid, with natural transformations
as arrows; dependent sums use total groupoids; Id uses arrows with their
conjugation action and contextual elimination. A selected universe must decode
these together, be closed under the admitted operations and support the larger
quantifier over target codes. Both direct and guarded routes must interpret
the same restriction of that universe. One-object C4 arrows alone provide
none of the missing dependent product, classifier or substitution laws.

For a weak-comprehension candidate, instead construct the needed LF hom-set
bijections on actual slice arrows and weak stability of the full constructors.
The [existing coherence assessment](../concrete-dependent-coherence.md) gives
those obligations explicitly. Its historical status must be read alongside
the [later strict higher construction](../strict-two-groupoid-checkpoint.md);
existing higher J evidence still does not by itself admit the Π/Σ/universe
source slice here. We have not constructed this weak package, and absent
code is not a negative theorem about its existence. Allowed equality rules,
including any source universe decoding equations, must be fixed before
applying a strictification theorem.

## Architectural disposition and work accounting

| Work | Constructed or derived here | Remaining obligation and owner |
|---|---|---|
| Native designated-map argument | Actual restriction/gap/comparison, contractible fibers and cancellation; nonconstant family and chosen inverse | Retain as an extensional reference under #289/#290. Do not identify its proof-irrelevant cocones with higher ones. |
| Direct action interpretation | Structural evaluation, substitution and soundness independent of guarded semantics | Retain as a bounded control; #289 owns connecting genuine dependent source binders and constructor rules to representation. |
| Guarded action interpretation | Local rule validity, genuine derivation, engine soundness and actual translation agreement | Retain current guarded/reference guarantees; #289/#290 own admission of the full source fragment rather than inserting the final theorem as an axiom. |
| Groupoid control | Actual categorical restriction equivalence, selected gluing and postcomposition; native-equality encoding rejected | #289 owns joint Π/Σ/Id/universe model admission. #36/#100 own the distinct future joint higher/smooth consumer model. |
| Natural-model and weak-coherence alternatives | Type-family representation reused; exact failed shortcut and missing hypotheses isolated | Investigate under #289. Compare native direct construction with weak stability plus LF on the same chosen fragment; no mandatory incumbent adapter. |
| Institutions and theory publication | No new institution or publication interface needed for these checks | #290/#235 may publish completed fragment interpretations. Publication cannot supply missing model constructors or turn schema substitution into dependent soundness. |

Setup here comprises the native cancellation library, the two-sort syntax,
its two interpreters, local guarded validity, representation reuse, and the
groupoid restriction construction. These costs are not collapsed into a count
of fields in an interface. Recurring action-language clients reuse evaluation
and the arbitrary substitution theorem. New operation constructors still
require clauses in both interpretations, the structural proof cases, guarded
validity and translation agreement. New dependent constructors additionally
need typing, coherence and model admission, which were **not** performed here.

The checked maintenance changes are the two map substitutions and two dependent
base reindexings. Their selected outputs are recorded above. Changing the
selected groupoid gluing from 1 to 0 changes its postcomposition observation;
using the unrelated negation equivalence changes it again. The source's larger
constructor/universe maintenance test remains unperformed. No author trial,
resource measurement or productivity advantage is claimed from this ledger.

## Consequences for #358 and #359

The original acceptance contracts remain in force. #366 does not license
freezing the smaller action schema as their replacement.

- **#358:** do not launch the proposed quantified-source/model author trial
  using these interfaces. First complete and review the dependent fragment
  and matched model admissions, then freeze held-out tasks, budgets and
  stopping rules. Candidate finite scale points remain one/two/four mapping
  stages, successive cocone/fiber/cancellation operations and additional
  genuinely admitted settings. Count initial model admission separately from
  recurring proofs and maintenance. This does not demand the full Myers
  model. Another bounded workload may proceed only if it satisfies #358's
  original dependent-operation, multiple-setting and scaling requirements.
- **#359:** the C4 control does not replace selected higher Id/J, dependent
  action, actual target syntax or an independent computational observation.
  That issue may use the existing higher-model work if its own stronger
  source-to-target connection is constructed. It need not wait for all
  smooth geometry or original Myers model existence. The native comparison
  and smaller action language here do not construct its missing connection.

#289/#290 own the bounded quantified source/model continuation and should
freeze its exact admitted universe before a successor implementation starts.
No full initiality theorem, univalence, resizing, general Agda frontend or
full geometric model has been added as a prerequisite. The external agent
continues the original Myers obstruction investigation. Its code remains
reference evidence requiring conaled's semantic, architectural, validation
and independent review standards before any future integration.

## Validation boundary

The new Lean modules and their examples are public through
`SquareApplications`. Candidate acceptance requires the full build, exhaustive
proof audit and candidate verification recorded by the enclosing workflow.
Focused builds establish only these module dependencies. The comparisons in
this report distinguish checked native/schema/groupoid results from the
unconstructed quantified source interpretation and from primary-paper
conditional results. No new axiom, foreign proof import or changed trust
policy is introduced. Independent Standards and Spec review decides whether
the bounded negative outcome meets #366's explicit alternative acceptance.
