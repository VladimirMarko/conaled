# Nested internal settings under substitution

The #319 specialization constructs two successive settings from internal
presentation data. The second construction can depend on the first generic
model. Both constructions commute with base substitution, including selected
dependent values. This supports making setting construction available inside
an interpreted argument's context. It does not justify requiring every model
to carry a universal category of settings or selecting a higher foundation.

The [prospective fixture](internal-setting-fixture.md) was committed before the
implementation at `8ad581f`, with its source/host boundary clarified at `285383d`.
The implementation is [NestedSetting](../../SquareKit/Internal/NestedSetting.lean),
with [checked client and failure cases](../../Examples/NestedSetting.lean).

## What is internal in this construction

The existing finite geometric scheme has predicates p and q, coverage,
disjointness, and a bound p implies r. `FiniteSetting.Formula`, `Sequent`,
`axioms` and `Formula.eval` provide its syntax and interpretation. Its parameter
is a predicate in the base context, not an externally supplied category or model.
For P over X, the constructed classifier object is

```
A(x) = PLift(P.parameter x) + Unit
Total(P) = Sigma x:X, A(x)
```

The existing [finite classifier comparison](../../SquareKit/Internal/FiniteClassifierComparison.lean)
proves the coproduct universal property in Set/X and connects the interpreted
models to sections of this object. S(P) is the slice at that object. The new
`settingEquivalence` identifies this slice with Set/Total(P), using Mathlib's
iterated-slice equivalence on objects and morphisms.

Inside S(P), a second parameter Q may depend on the first generic element
`a : Total(P)`. Apply the same formation to Q. Its slice is equivalent to
Set/Total(Q). The checked example takes X=Nat, P(n)=(0<n), and
Q(n,a)=(a.isLeft=true). At the same positive n, changing a changes which second
left summands are permitted. Supplying an external family of unrelated models
would not construct this dependence, its generic interpretation, or its
substitution comparison.

The Nat predicate and tag inspection are Lean-hosted expressions in this
Set-family base. There is no new arithmetic syntax or object-language term
returning a category. Slice formation is a metatheoretic construction that
interprets the internal geometric presentation. This distinction matters:
the result demonstrates an internal presentation and dependent use of its
constructed setting, not an internal universe of all type theories.

## Universal interpretation and selected data

`Argument P Q` consists of a section of A followed by a section of the second
family over that selected first section. `argumentEquiv` constructs a two-sided
equivalence with maps into Total(Q) over X. `argumentOverEquiv` gives the
correspondence over any substitution into X. Its inverse transports the whole
dependent pair along the equation over the base; it does not choose unrelated
representatives for the two components.

`argumentOfModels` interprets two successive models of the finite geometric
scheme. `first_model_recovery` and `second_model_recovery` recover both model
records through the existing model/section equivalence. Independently,
`first_generic_recovery` and `second_generic_recovery` recover both selected
interpretations by pulling back the actual generic models along the classifying
map. Together with the inverse laws, these establish the universal section
interpretation used here. This is not a new arbitrary-source geometric-morphism
classification theorem; the repository's wider classifier results have their
own categorical hypotheses.

The concrete selected argument chooses the first left summand at successors
and right at zero, then makes the corresponding dependent second choice. Its
tags are `(false,false)` at zero and `(true,true)` at successors. A further
payload has type `Fin(n+2)` when the second choice is left and `Fin(1)` when it
is right. The selected value is respectively n+1 or 0. This payload checks that
transport preserves a nonconstant data type and its selected value, beyond
proposition-valued evidence.

## Two representations and their comparison

| Representation | Constructed evidence | Remaining obligation outside this specialization |
| --- | --- | --- |
| Split families and selected sections | Explicit formation, strict reindexing by composition, dependent pair classification, and identity/composition equations | A general authoring syntax or higher interpretation needs its own construction and adequacy proof. |
| Display objects and slice categories | Actual coproduct classifier objects, slice equivalences, categorical pullback of the nested total, inverse-image functors and natural identity/composition comparisons | A different category needs the stated closure and preservation properties; arbitrary chosen pullbacks are not claimed definitionally equal. |

These are different representations of the same client, not different
mathematical capabilities. Awodey's representable-map account relates types
and terms in context to display maps and their universal property. Proposition 2
assumes a context category with terminal object when identifying this with a
CwF; it does not claim every current project model already has that structure.
The present proof constructs the particular Set pullback directly.
[Natural models, §1 and Proposition 2](https://arxiv.org/html/1406.3219v4)

The slice interpretation has a separate categorical justification. The Stacks
Project proves that a slice of a sheaf topos is a topos and identifies its
localization inverse image. Here the category is Set, and the checked code uses
actual Mathlib slices and their iterated equivalence. The cited general theorem
is context for the representation; no unformalized theorem from the reference
is a Lean dependency. [Stacks Project, Lemma 7.30.1](https://stacks.math.columbia.edu/tag/04GY)

A third candidate, mode-indexed judgments, answers another question. MTT's
locks act contravariantly on contexts; its variable and substitution rules
control access across modes. Its mode theory and modal model structure are
supplied separately. Those mechanisms do not themselves construct this
context-varying P or the second presentation using its generic model. This
client uses unrestricted ordinary Set substitutions and requires no modal
lock. A future modal version must state its access rules in addition to the
internal construction contract. [Gratzer et al., §§2, 4–5 and Figure 3](https://www.danielgratzer.com/papers/multimodal-dependent-type-theory.pdf)

Mathlib's pinned implementation supplies the categorical representation:
[`Over.iteratedSliceEquiv`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Comma/Over/Basic.lean)
and [`Over.pullbackId`/`Over.pullbackComp`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Comma/Over/Pullback.lean).
Their explicit isomorphisms support comparison rather than equality of chosen
slice presentations.

## Coherence is constructed

`reindex` substitutes into Q along the map of the constructed first total.
`map_comp` and `reindex_comp` prove both stages compose. `Pullback` retains a
base point, an original nested value, and their base equation. `comparison`
constructs an equivalence with forming after substitution. Its base and original
projection equations establish an actual categorical pullback in
`formed_isPullback`. `comparison_id`, `comparison_comp`, `rebase_id` and
`rebase_comp` establish identity and composition, including the equation
certificate and both dependent components.

`typeSub` and `termSub` admit an arbitrary dependent Type-valued family over
the nested total. `type_comparison` identifies its fiber; `term_comparison`
uses precisely that equality to transport its selected term.
`dependent_comparison_comp` retains the entire dependent value after two
substitutions. `settingSub` provides actual inverse image on slice objects and
morphisms. `setting_term_twice` applies the existing canonical pullback
comparison to arbitrary slice sections, whose dependent types are the
corresponding pullback families. The inherited [Family coherence](../../SquareKit/FamilyCoherence.lean)
proves unit and associativity equations for these canonical comparisons.

The second construction needs no additional law field in this specialization.
It uses the same finite scheme in the constructed first context. Closure under
sums, dependent totals and pullbacks is available in Set. This conclusion is
about this operation and representation; it is not a theorem that arbitrary
setting constructors are admissible without new hypotheses.

For the frozen substitutions sigma(n)=n+1 and tau(n)=2*n, the original index is
2*n+1. The connected payload example yields 6 at n=2. At n=0, the two orders
yield 2 and 3, so the test detects reversing composition. Generic laws quantify
over all base substitutions and all second predicates; these numerical cases
check their intended interpretation rather than replacing their quantifiers.

## Failure, statement review and architectural consequence

The checked `erase` map replaces both selected summands by right and preserves
the base point. It is a valid deliberately lossy map. `erase_fails` shows it
violates the promised tag observations. `no_second_left` and
`cannot_repair_second` prove that no second value over the erased first choice
can preserve the old second-left observation. The dependence therefore affects
which repairs are possible, rather than merely adding an annotation cast.

During implementation, transporting the first component separately left the
second component in the old fiber. Normalizing the whole pair resolved this
Lean obligation. That failed attempt was an encoding error, not evidence that
the mathematics needs a new axiom or that a categorical theorem fails.

Statement review checked that the comparison is an equivalence over the base,
that Q ranges over arbitrary predicates on the first total, and that term
transport uses its type comparison. All equality is native extensional equality;
proposition witnesses are proof irrelevant, while summands and finite payloads
are retained as data. The concrete example demonstrates satisfiable premises
and nonconstant dependence. Its selected right branch at zero does not make P
constant. Existing classical model-to-section extraction is disclosed through
`argumentOfModels`; the concrete selected sections and comparison maps do not
require deciding an arbitrary predicate. The full inherited audit remains the
acceptance check for permitted axioms.

**Adopt the constructed nested comparison as a checked specialization.**
For #314, this is evidence that useful laws can be derived from existing
formation and universal properties without strengthening every model. For
#315, internal construction requires the interpretation and comparison
contracts to mention the constructed context and allow the next presentation
to depend on its generic data. Keeping model construction entirely outside
judgments would miss this client. Authors provide P, Q and the selected argument;
the comparison layer supplies normalization and compositional transport once.
No author trial in this ticket establishes ergonomic benefit.

**Investigate broader admission with #317 and #36/#235.** A different setting
constructor must state its closure and preservation obligations; a replacement
foundation remains eligible. **Defer higher adoption to the #321/#322 continuations identified by
[#316](dependent-higher-identity.md)**. Native proof-irrelevant identity cannot
serve as the requested higher model.
The result does not resume #107, prepare #108's theorem, activate #260, or
settle #297's independent modal-context question.

The [component acceptance record](dependent-foundations-validation/reviews/319-review.md)
retains the exact reviewed candidate, both independent reports and matching
validation evidence. Final orchestration acceptance is a separate gate.
