# Alternatives assessment: local universes beyond weak units

Retain the two weak-unit routes and test dependent products next. The smallest credible extraction is the dependent-input parameter representation shared by Type-family Σ and a proposed Type-family Π, followed by a separate groupoid test. The current evidence supports this bounded experiment, not adoption of a general local-universes foundation. A direct split model and a comprehension-category replacement remain genuine competitors; neither must first implement an adapter to the present weak-unit module.

I inspected revision `e80c51d968925be3809ba3acc3259de7041b504b` in the pinned checkout. I had no prior involvement in this work and received only the assigned brief and repository guidance. I have not read another assessor's report. This uses the same model family as the coordinating assessment; fresh context does not provide model diversity.

## What is worth retaining

`Applications/LocalUniverses/WeakUnit.lean` constructs the arrow map by conjugation (`conjugate`, line 33; `direct`, line 79). `direct_projection` and `direct_beta` assert equality of complete functors. `direct_substitution` handles arbitrary functors between groupoid contexts. There is no split-composition field in `NormalizedLifts` (line 52), and `Examples/WeakGroupoidUnit.lean:100`, `fails_composition`, supplies a concrete nonsplit choice. Strengthening the lift interface would exclude useful evidence without solving a demonstrated problem.

The parameter route has substantive independent content: `representation` (line 377) supplies both inverses, `name_substitution` (line 314) supplies naturality, and `parameter_substitution` (line 341) derives stability by precomposition. `instantiated_agreement` (line 330) compares the actual selected functors when the generic filler uses the same lifts. The C2 controls (`distinct_fillers`, `fixes_whole_branch`, `swaps`) prevent replacing this observation with equality of object functions or an unspecified isomorphism.

There is also useful existing reuse outside weak unit. `SquareKit/LocalUniverses.lean:68`, `Family.sigma`, represents dependent inputs by `(a : A.Parameters) × (A.fiber a → B.Parameters)`. `sigma_reindex` is proved by reduction. `displayCurry` and `displayCurry_natural` (lines 109–119) construct a section-representation equivalence with arbitrary base maps. `SquareKit/Internal/DesignatedMap/Interpretations.lean:39`, `Represented.represent`, consumes `Family.comprehensionEquiv`; `represent_natural` and `pair_unique` use its full representing property. These are assets to preserve through any broader design.

## Concrete next constructor: dependent products

For the existing Type-family input pair `A : Family Γ`, `B : Family A.Comprehension`, consider the following proposed construction, not a checked addition:

```text
P(A,B) := Σ a : A.Parameters, (A.fiber a → B.Parameters)
name γ := (A.name γ, λ x, B.name (γ,x))
Πfiber (a,b) := (x : A.fiber a) → B.fiber (b x)
```

This reuses precisely the parameter object and name formula of `Family.sigma`; only the generic fiber changes. An extracted helper could expose this parameter type, evaluation and name, with naturality. It should not require callers to supply final Π-substitution laws. The existing `displayCurry` supplies the immediate abstraction/section comparison, and the existing `DependentSquares.piTy`, `lam`, `app`, `pi_beta`, `pi_subst`, `lam_subst`, and `app_subst` give the direct comparator (`Dependent.lean:98–164`). Retain any available η law as a separately named part of this Type specialization, without making η a prerequisite for every future Π provider.

The direct comparator already has substitution by reduction. Consequently this Type experiment can justify factoring duplicated dependent-input machinery, but cannot by itself show that local universes make coherence easier. It can lose the author-effort comparison honestly: if helpers add wrappers while the direct proofs stay one line, keep the direct client interface and the extraction local.

The intended positive client is an abstracted version of the existing dependent tail: `A(n)=Fin(n+1)` and a result family depending on the selected first value, using `Examples/LocalUniverses.lean`'s `DependentTail.first`, `second`, `shift`, and `double`. Test abstraction and application after these two nonidentity substitutions, with independently calculated values. Keep a family whose second name changes with its first argument; a constant tail misses the reason for the parameter object.

## Where generalization incurs real obligations

The Type formula uses native dependent function and pair types, function extensionality where needed, and the already constructed comprehension pairing. Its parameters and fibers stay in the declared `Type u`; the record of families itself is larger. There is no requirement to classify all small families by one small code type, no internal univalence, and no choice of fillers in this construction.

For a groupoid Π experiment, a set of objectwise fiber functions is insufficient. One must represent dependent functorial data, including transport and arrow equations, and establish evaluation and currying on complete functors. With a display `pA : EA → VA` and another parameter groupoid `VB`, the specific ambient operation needed to represent dependent names is the dependent exponential along `pA` of the product projection `EA × VB → EA`. Its representing property must hold against arbitrary base maps into `VA`, not merely sections at the identity map. The corresponding generic dependent motive must be a legitimate display after pullback. Constructing Π as a display and supplying application/abstraction and computation is a further logical-constructor obligation; parameter representability alone does not provide it. This is my proposed obligation breakdown, not an implemented groupoid Π theorem.

For the broader foundation comparison, the primary source says LF requires finite products and dependent exponentials for `Z →g Y →f X`, where `f` is display and `g` is display or a product projection. These categorical exponentials need not themselves be displays. Lemma 3.4.2.4 assumes weakly stable dependent products as well as LF. Weak stability retains the substituted Π/application pair while allowing an appropriate abstraction operation after substitution. Separately, Lemma 2.4.2 obtains strict structure on the other split replacement from pseudo-stable structure. [Lumsdaine–Warren, arXiv:1411.1736v2, §§2.4, 3.1, 3.4.2](https://arxiv.org/html/1411.1736v2)

Thus an ambient comprehension-category implementation must provide its fibration and comprehension/cartesian structure, identify its display maps, construct the particular dependent exponentials, and establish the constructor's weak stability. A citation to LF or the existence of a `pi` field cannot discharge these Lean obligations. For small-groupoid implementations, record object and arrow universe levels of the representing objects, and prove the required closure at those levels. Fixed finite examples do not establish that closure. Supplied generic choices and classically selected generic choices should remain distinguishable inputs.

## Alternatives and their discriminating costs

| Approach | What it buys | What must be demonstrated |
|---|---|---|
| Direct split families | Immediate computation and short strict substitution proofs in Type; constructor formulas can preserve arrow information in groupoids. | Each new constructor's coherence and interpretation contract. Current weak-unit success is not an all-constructor proof. |
| Local parameter helpers | Reuses naming, evaluation and representation while preserving direct public operations. | A second constructor must actually consume the helpers and reduce repeated obligations. Sharing a slogan is insufficient. |
| General local-universes replacement | Makes generic choice independent of the later context. | Comprehension, representation and the particular ambient closure operations, plus each constructor's logical hypotheses. |
| Other split replacement with pseudo-stable operations | A real alternative when coherent comparisons are available. | The requisite coherent action and laws in the intended model. A weak-unit automorphism example does not by itself refute this route. |
| Chosen classifier/universe presentation | A candidate common naming interface if the intended model has suitable codes. | Classification scope, closure and universe levels. Do not infer these from `Family.present` or from naming one fixed motive. |

A replacement foundation can be evaluated directly on a common semantic workload without first encoding itself as `WeakUnit.Parameter`. The workload must retain selected-arrow observations, dependent result families, repeated substitution and the chosen computation laws. A comparison using only isomorphism of results answers a different question and should be reported separately.

There is no established soundness defect in the inspected routes. The main risk is treating the fixed-product weak-unit representation as if it represented arbitrary dependent telescopes already. The open question is how much of parameter construction and naturality can be reused once the shape of the dependent domain varies. The Type Π candidate gives a cheap, concrete test; the groupoid Π obligation tests the stronger claim.

## Discriminating experiment and acceptance evidence

First implement the Type Π comparator in an isolated experiment, connecting the existing dependent-tail client to both routes. Count new mathematical obligations separately from equality-transport repairs and generic infrastructure. Require decoding agreement, β, the selected η contract, and formation/abstraction/application stability after two substitutions. Preserve `PresentationFailure.presentation_ne`: equal decoded families do not imply identical presentations.

Then test a groupoid dependent product with nontrivial domain transport and nonidentity arrows in the result groupoid. Require a full natural representing equivalence, a generic constructor, and stability on arrow maps. Include an intentionally object-only candidate that fails an arrow equation. Let the experiment stop at a concrete missing dependent-exponential or display-closure obligation instead of hiding it in a field claiming final strict stability. Compare against a direct construction under explicitly matched hypotheses. An alternative with different foundational input may still win; report the difference rather than disqualifying it for lacking an incumbent adapter.

Promote shared machinery only if both actual constructors consume it with preserved contracts and reduced repeated work. Adopt a broader strategy only after a model-level experiment accounts for its foundation obligations and gains. No current result warrants changing the Type-family comparison callers, designated-map comprehension consumers, or separate higher/descent contracts. I inspected the comparison boundary declarations but did not exhaustively audit descent implementations; preservation there remains a required regression check, not a verified conclusion of this assessment.

## Validation and limits

This assessment used source inspection, declaration-level proof reading and the primary paper's named definitions and lemmas. The Π construction and foundation breakdown above are paper proposals. No new Lean theorem, executable experiment, build, proof audit or productivity measurement was run. The pinned checkout's revision was verified; no target files or issues were changed. The full paper theorem was not reconstructed, and this is not an exhaustive comparison with cubical, simplicial or syntactic foundations. No report from another perspective informed these conclusions.
