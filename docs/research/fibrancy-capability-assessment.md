# Fibrancy requirements at constructor boundaries

Research for [#402](https://github.com/VladimirMarko/conaled/issues/402), inspecting
`78540f8f30ed8cb1afa7dc799a96dac65fec1458`. The existing split between operations,
laws and certified families already expresses the main capability distinction.
Retain it. The missing work is admission of new families and verification of
source-specific rules, not another universal `Fibrant` wrapper.

## Existing operations and closure

All paths below are under [the cubical implementation](../../SquareKit/Internal/Cubical/).
These are inspected declarations, not builds rerun for this report.

| Boundary | Existing declaration | Actual requirement |
|---|---|---|
| Presheaf family | `Presheaf.lean`, `Family` | Restriction maps and their laws; no filling is implicit. |
| Filling | `Filling.lean`, `Filling` | A chosen operation for every context map, face and open box. |
| Filler correctness | `Filling.Lawful` | Cap/tube equations and uniformity under arbitrary reindexing. |
| Composition | `Filling.comp`, `hcomp` | Observe the endpoint of that chosen filler; boundary and reindex laws use lawfulness. |
| Restricted transport | `RestrictedTransport.lean`, `Filling.transp` | Selected filler plus `RestrictedConstancy` on the designated face. |
| Certified family | `FamilyData.lean`, `LawfulFamily` | Family, selected filler and lawfulness; reindexing retains the selection. |
| Dependent sum | `SumFilling.lean`, `sigmaFilling_lawful` | Fill the first component, then the second over the actual first filler. |
| Dependent product | `FunctionFilling.lean`, `piComposition_lawful`, `piFilling_lawful` | Lawful domain filling and codomain composition/filling, respectively. |
| Dependent Path | `PathFilling.lean`, `pathFilling_lawful` | Lawful body filling and both endpoint sections. |
| Marked identity/J | `FamilyData.lean`, `LawfulFamily.identity`; `ContextualModel.lean`, `model_j_beta` | Normalized identity filling and the contextual adapter, retaining strict reflexive computation. |
| Providers | `discreteFilling_lawful`; `CocycleFilling.lean` | Constructed discrete and cocycle instances, not evidence for every presheaf. |

The source layer already contains `transp_valid`, `transpBoundary_valid` and
substitution rules in `Judgments/`. Those validate its provider-annotated
operations; they are not an operational semantics for arbitrary Cubical Agda.
Several semantic constructors are `noncomputable`, including `piFilling` and
`pathFilling`. An operational claim therefore needs a separate realization.

## Which source laws matter

[CCHM v1, §§4 and 8](https://arxiv.org/html/1611.02108v1) uses uniform composition
on families; semantic closure retains that structure under substitution.
The interval participates in contexts without thereby being a fibrant type.
[Computational Higher Type Theory I, v2, §4](https://arxiv.org/pdf/1604.08873v2)
defines a type from a cubical pretype satisfying uniform Kan conditions involving
coercion and homogeneous composition. Its simple theory has Boolean negation
as a type line, not the later full universe construction.
The [Cartesian theory, CSL 2018, §§3–5](https://doi.org/10.4230/LIPIcs.CSL.2018.6)
separately admits non-fibrant types and exact equality. These are source-specific
conditions; a local family with `Filling.Lawful` is not automatically a model
of their operational PER judgments.

A crucial mismatch is the meaning of uniformity. Local `Filling.Lawful.uniform`
is a Lean equation between reindexed semantic sections. The computational theory
requires coherent cubical aspects of evaluated programs. A proof of the former
does not establish a step-by-step simulation of the latter.

## Composition test and unsupported input

Proposed combined client: for a lawful family `A` and a lawful family `B` over
its comprehension, form `Σ a : A, B a`, then the family of functions into that
sum, and a dependent path between two such functions. Invoke sum, product and
path closure in that order. Reindex along two composable maps and compare with
one reindex along their composite, retaining the actual selected fillers.
The demand is one composed theorem using existing closure/substitution lemmas,
not new individual closure theorems. A model client should supply only the
primitive family providers and endpoints.

The negative fixture removes the filler from `B`: a bare `Family` must not be
accepted as the codomain capability. Another fixture keeps a box filler but
omits its uniformity law: it must not pass certified source admission. These
are proposed interface rejection checks, not newly executed Lean tests or a
claim that the particular family mathematically lacks any filler. Similarly,
using the interval as an ordinary fibrant family requires additional evidence;
its occurrence in context extension provides none.

## Continuation

Do not open a separate abstraction redesign based only on this inventory.
Attach the composition test to admission of Glue and the circle in the
[universe milestone](cubical-universe-glue-milestone.md) and
[retained consumer](computational-higher-inductive-consumers.md).
A genuine defect would be a constructor that cannot retain its chosen filler
under dependent substitution, or a consumer forced to supply unrelated universe
structure for an existing discrete specialization. Either warrants a focused
change, with the existing native clients retained.

For a new universe provider, the test must include a code-valued dependent
family: the current closures operate on external families and do not classify
them internally. [Compatibility](cubical-judgment-compatibility.md) separates
that gap from differences in dimension algebra. Ordinary Lean users may keep
using the existing operations directly; no new syntax layer is prescribed.
