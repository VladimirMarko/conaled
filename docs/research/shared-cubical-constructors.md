# Shared cubical constructors: dependent sums and selected operations

For [#608](https://github.com/VladimirMarko/conaled/issues/608), retain the native
De Morgan and Cartesian APIs and refine the shared-construction proposal before
migration. The checked dependent-sum slice recovers the complete selected filling
operation in both settings. It establishes a common contract and identifies
common proof structure; it does not extract a shared classifier implementation.
A direct identification of their intervals is impossible in the stated direction.
That obstruction does not rule out shared proofs or other interpretation routes.

The baseline is `ff34cf5302adf2e15be132efad51d38fe48532f0`. The
[constructor audit](small-universe-constructor-gap-audit.md) supplies the inventory;
this study checks it against current declarations and adds
[checked specializations](../../Examples/SharedCubicalConstructors.lean).
No existing native API or client changes. Ordinary library users acquire no
new model, chart or interpretation obligations.

## The bounded result

The selected slice is same-level dependent-sum admission and classifier recovery.
For each model, take a lawful local family A and a lawful local family B over
its comprehension. Construct their sum with the native algorithm, classify it,
decode it and extend its local filler back to a global filler.

| Checked declaration | Exact conclusion |
|---|---|
| `Original.sigma_record` | Decoding the classified sum recovers its entire local-family record. |
| `Original.sigma_global` | The recovered global operation is heterogeneously equal to the selected native `sigmaFilling` algorithm; `sigma_record` supplies the family equality. |
| `Original.sigma_selected` | The decoder isomorphism commutes with the whole selected filled section, for every represented cube, Cofibration and fixed-false-cap box. |
| `Target.sigma_record`, `sigma_global`, `sigma_selected` | The corresponding contracts hold for every Cartesian Subcontext and arbitrary cap section r, including its dependent base family. |
| `Target.dependent_sigma_record`, `dependent_sigma_variable` | The target construction handles a Boolean-tagged family with fibers `Fin 1` and `Fin 2`, retaining whole sections at a variable cap. |
| `Target.variableSource_ne_false` | The selected variable cap is not the false endpoint. |
| `Target.sigma_code_comp` | Two substitutions preserve the complete classified code, with endpoint `raisedSub τ ≫ raisedSub σ ≫ code`. |
| `sigmaRestriction` | Actual restriction preserves the underlying dependent sum, pulling B through the inverse comprehension comparison. |
| `no_interval_identification` | An endpoint-preserving isomorphism from the restricted De Morgan interval to the Cartesian interval is impossible. |

These are applications of existing constructor and classification theorems,
not a new model or a replacement proof of their laws. The global equalities
quantify over arbitrary lawful input operations, so they retain choices beyond
vertex observations. The variable-cap specialization quantifies over a supplied
box; it is not a computed example exhibiting two different lawful fillers.
Existing `CartesianSmallFamilyClassification.endpoint_not_whole` and
`endpointGlue_record` retain the proper-face control. Existing native clients
remain integrated in the full build.

The first filler must be lawful even to construct the second box. The second
filler needs lawfulness to establish the sum's laws. Both native algorithms
fill the first projection, construct the dependent second box over that exact
section and its boundary witness, then fill and pair the results. Both uniformity
proofs compare the subtype consisting of the first section and its witness.
This is substantive shared proof structure. Neither sum algorithm requires
De Morgan connections or reversal.

## Three different architectural choices

**Retain native constructions.** Builders keep their current cap, face and
substitution proofs; callers provide lawful families and use existing constructor
facades. This preserves exact selections and all current reduction behavior,
but retains duplicated proof structure.

**Extract represented classification and dependent filling separately.** A
classification construction should consume a small base category, representables,
generic evaluation, compatible interval charts and substitution-stable local
operation data. It must derive code naturality, decoder comparisons and operation
recovery. Taking an encode/decode equivalence and its round trips as fields would
package existing results without sharing their derivation.

A smaller dependent-filling extraction would consume box projection, dependent
second-box formation, pairing and their substitution equations. It should derive
the selected first-then-second operation and its laws. The box parameters may
retain the original singleton cap choice and the Cartesian arbitrary section.
Neither the final sum law nor preservation of the final selected sum operation
belongs among the assumptions. This is the preferred next bounded experiment;
it has two concrete implementations and the recovery contracts above as tests.

**Construct an explicit model bridge.** This additionally requires a cube route,
context/family/term and comprehension maps, an interval comparison in the needed
direction, cap and face translations, base/tube maps, substitution compatibility,
and preservation of the component selections. The second-stage comparison must
live over the image of the chosen first section. A family isomorphism or a common
proof implementation supplies none of these extra filling laws by itself.

| Native difference | Consequence |
|---|---|
| De Morgan cubes have reversal and connections; Cartesian coordinates are variables or endpoints. | There is no endpoint-preserving natural map from the restricted De Morgan represented interval to the Cartesian interval. |
| Original filling uses Cofibration and false cap; Cartesian filling uses Subcontext and arbitrary r. | A common interface must retain cap/face data and substitution of r. Restricting Cartesian inputs to false caps would weaken its API. |
| Original Π uses De Morgan scaling; Cartesian Π uses a variable target dimension. | The sum comparison does not establish common Π filling or chosen-operation recovery. |
| Original large-context classification takes small fiber presentations; Cartesian contextual classification is at the raised-small-context boundary. | Common large-context admission would require new Cartesian construction, owned by #605. |

The interval rejection specializes the stronger existing
`CartesianWitnessPreservation.no_interval_retraction`: even a natural map with
those endpoint equations is impossible, using naturality at reversal. It says
nothing against a map in the other direction, a larger retained interval,
restricted classes of boxes or relational comparison. In particular it is not
an impossibility proof for a common classification argument.

The composition theorem delivered here concerns native substitution of a
classified sum. It is not a cross-model composition theorem. For future routes
M→N→P, the latter must compare the direct composite box translation with successive
translation, including the comprehension map and first-section witness used to
form each dependent second box. Equal vertex outputs would be insufficient.

## Existing transport and a broader alternative

[#570's construction](kunneth-formalization.md) separates a local canonical-map
argument, an indexed provider, and preservation along a named route.
`AdjointSquareTransport.curry` and its pasting laws already transport actual
transposes with explicit adjunctions and square components. Reuse them when a
cubical comparison has that form. They contain no cap, face, box or filling
selection, and therefore cannot derive the missing filling compatibility merely
from an underlying adjunction. The existing elementwise `sigmaComparison` already
supplies the underlying dependent-sum isomorphism; turning it into a mate is a
coherence option, not a proof of chosen-filler preservation. No properness,
projection-formula or exceptional-operation assumptions are needed for this slice.
The generic transport is not thin, but its thin predicate examples cannot test
alternative interior fillers.

Cavallo, Mörtberg and Swan's
[*Unifying Cubical Models of Univalent Type Theory*](https://drops.dagstuhl.de/storage/00lipics/lipics-vol152-csl2020/LIPIcs.CSL.2020.14/LIPIcs.CSL.2020.14.pdf),
Definition 2, Sections 2.3.1–2.3.2 and Theorem 15, provide a broader candidate:
weak composition retains a cap path and admits a shared dependent-sum construction.
This argues against treating cap differences as a universal obstruction. Adapters
to that formulation would still need to establish recovery of our chosen operations
or state the weaker retained comparisons. No such adapter is implemented here.

Pinned Felix `6f36d28097db7ea5f5df3263db3e8be08f74e490`, inspected in
`Construct/Comma/Homomorphism.agda` and `MakeLawful.agda`, separates operations,
commuting comparisons and transported laws. It supports this separation of
obligations but supplies no cubical chosen-filler theorem.

## Challenge synthesis and disposition

Three fresh-context agents independently assessed [foundations](shared-cubical-constructors/foundations.md),
[implementation and use](shared-cubical-constructors/use.md), and
[alternatives](shared-cubical-constructors/alternatives.md), from the
[neutral brief](shared-cubical-constructors/brief.md). Initial reports were saved
before cross-reading. They inspected source; the coordinator ran the Lean checks.
Their agreement is not independent proof or evidence of model diversity.

All favor retaining native APIs and preserving full selections. They differ in
extraction priority: foundations/use emphasize represented classification;
alternatives recommends the smaller dependent-filling argument first. The latter
has a narrower obligation set and directly matching algorithms, so refine that
proposal first while keeping classification as a separate layer. This does not
adopt an unimplemented common interface. No native defect or mathematical barrier
to proof extraction was established. Adapter cost and current Lean elaboration
are costs to assess, not reasons to reject the mathematics.

- **Adopt:** the checked native recovery contracts and explicit distinction between
  underlying restriction, selected-operation preservation and common proofs.
- **Retain:** model-specific constructor APIs and existing client guarantees.
- **Refine:** a common dependent-sum filling proof, deriving both exact native
  specializations from primitive box laws; #235 owns this extraction decision,
  coordinated with #289. Follow with chart-classification extraction only when
  its decoder/recovery argument is actually shared.
- **Defer:** broad migration and a general selected-filler bridge. #235/#289 retain
  their scope; the interval obstruction constrains candidate routes.
- **Keep separate:** #605 larger-context Cartesian admission, #606 recomputation
  coherence, #607 universal-decoder versus returned-filler equality, and #625's
  total internal structure identity theorem. None follows from the present slice.

The next extraction must recover native filling records, retain variable caps and
proper faces, exercise a genuinely dependent second component, and keep native
callers free of chart proofs. Include composite substitutions and assess changes
to existing reduction-based clients. A route extension must derive compound
preservation from component box/filler compatibility, with explicit endpoints.
No author-productivity result, universal framework adoption or arbitrary model
bridge is claimed. The matroid work in #620 does not depend on this extraction.

## Validation and statement review

The checked module is imported by `SquareApplications`. Its local build passes.
Acceptance requires the isolated candidate's integrated build, exhaustive proof
audit and independent Standards/Spec reviews. The review record retains those
results and exact candidate identities outside the source tree.

Statement review distinguished equality of native records and sections from
underlying-family isomorphism and native homotopy. Global recovery uses the
family equality first, then the proved local/global roundtrip; it does not assume
the selected result. The cap rejection has no extra mathematical hypothesis.
No new axioms, toolchain changes or verification exceptions are introduced.
