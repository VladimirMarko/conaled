# Bounded audit of semantic statements

The [#432](https://github.com/VladimirMarko/conaled/issues/432) first pass found
**no new defect in its selected contracts**. It inspected substitution under
binders, selected dependent descent, numerical error composition and selected
least-fixed-point transport. Several apparently strong premises are necessary
for their specified observations. This is a bounded source and statement
assessment, not a repository-wide semantic certificate or a new proof audit.

The [prospective inventory](semantic-statement-audit-selection.md) was committed
as `c0b5a8f76e3ad50a4830f2f3aea576c6e000214a` and
[published on #432](https://github.com/VladimirMarko/conaled/issues/432#issuecomment-6747897589)
before detailed assessment. Its pending-status text is preserved as historical
checkpoint evidence. The sample was fixed at
`0b9a72f58d8fd7476eff6676f88b2690491b5051`. Integration of #115 produced
audit checkout `bc5f3785f2a41c4b638f8de898540a7e9374428c`; the sampled sources
and associated contracts are unchanged from the selected revision.
Sources were inspected on 2026-11-09, using Lean 4.35.0 and Mathlib
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

The author did not write the sampled Lean code. Prior #431 work had inspected
the descent interface; that familiarity is disclosed rather than counted as
independent acceptance. The coordinator's path suggestions were candidates,
not findings. Standards and Spec review belongs to the enclosing workflow,
separate from this audit author's assessment.

## Coverage and independent contracts

| Stratum | Inspected declarations and immediate dependencies | Independent intended contract |
|---|---|---|
| Substitution/induction | All definitions and proofs in [`FirstOrderSubstitution.lean`](../../SquareKit/FirstOrderSubstitution.lean), including private lift helpers; `Ty`, `Var`, `Term`, `lookup`, `eval` in [`FirstOrder.lean`](../../FirstOrder.lean); staging specialization/substitution definitions and the open-let example | [#214](https://github.com/VladimirMarko/conaled/issues/214): substitute static syntax while retaining arbitrary runtime inputs and capture avoidance. Derive simultaneous substitution from the source grammar and independently assigned variable values. |
| Semantic transport | All definitions and proofs in [`Descent.lean`](../../SquareKit/RepresentationExtension/Descent.lean); `Dependent` examples in [`RepresentationExtension`](../../Examples/RepresentationExtension.lean) | [#291 item 4](https://github.com/VladimirMarko/conaled/issues/291), the [frozen fixture](all-model-representation-fixture.md), and the [earlier paper construction](representation-extension-comparison.md#dependent-witness-descent-with-explicit-fiber-comparisons): construct a quotient family and recover the chosen section through coherent fiber equivalences. |
| Quantitative composition | All definitions and proofs in [`Numerical/Error.lean`](../../SquareKit/Numerical/Error.lean); affine, enclosure and rejection declarations in [`NumericalError`](../../Examples/NumericalError.lean) | [#372](https://github.com/VladimirMarko/conaled/issues/372) and the [fixed affine fixture](ordered-quantitative-observations.md#client-and-observations-fixed-before-adaptation): bound selected outputs by `6e+3df+dg`, with domain obligations at each stage. Re-derive the estimate from triangle inequality and local sensitivity. |
| Fixed-point selection | All definitions and proofs in [`SelectedFixedPoint.lean`](../../SquareKit/SelectedFixedPoint.lean) and [`IndexedPartialComputation`](../../Examples/IndexedPartialComputation.lean) | [#346](https://github.com/VladimirMarko/conaled/issues/346) and the [countdown graph](context-dependent-partial-computation.md#contract-fixed-before-either-construction): enabled inputs return the specified value and entire trace; disabled inputs denote bottom; two reindexings retain that record. |

The numerical disk-motion theorem was read as a use of the shared bound; its
underlying trajectory, Euler and analytic-error development was not audited.
The parser adapter, general extension logic, higher-order substitution,
weak-machine simulation, smooth/sheaf descent, current #107 work and internal
SDT provider are outside the completed sample. Reading their references does
not extend coverage to them. There is no percentage-of-repository claim.

Primary checks used the pinned Mathlib
[Lipschitz API](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Topology/MetricSpace/Lipschitz.lean)
and [ω-cpo implementation](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Order/OmegaCompletePartialOrder.lean).
The former's `lipschitzOnWith_iff_dist_le_mul` requires two points in the stated
domain. The latter's `ContinuousHom` bundles monotonicity and preservation of
increasing-chain suprema; `ωSup_iterate_le_prefixedPoint` proves comparison
with prefixed points. These facts identify what the local proofs can reuse.

[Abramsky–Jung, *Domain Theory*, Definition 2.1.17, Theorem 2.1.19 and Lemma
2.1.21](https://www.cs.ox.ac.uk/people/samson.abramsky/handbook.pdf) supplies the
pointed-dcpo fixed-point and strict continuous intertwining results. Local
code only needs increasing countable chains, using Mathlib's ω-cpo results;
the source's full dcpo hypothesis is not silently inferred from that class.
[Davies's introduction](https://www.cs.cmu.edu/Groups/fox/people/fp/courses/15816-s10/papers/Davies96.pdf)
supports staging as residualization, but is not a substitution theorem for
this repository's grammar. [Barrett–Halvorson §§4.1–4.2](https://arxiv.org/html/1506.04675)
concerns Morita sort expansions; the audited dependent descent is the report's
separate set-theoretic argument. No dependent theorem is attributed to that
source, and no broader literature survey is claimed.

## Substitution includes the actual binder use

Independently assign values ρ to source variables and τ to target variables.
For a fixed syntax substitution s, require `eval(s(v),τ)=lookup(v,ρ)` for each
typed variable v. The intended conclusion is the corresponding equality for
every term. The variable case needs precisely this obligation; products,
projections and primitive application extend it by congruence. A let initializer
is itself a term, and its body is in the extended context.

The formal `eval_subst` has these quantifiers and the full seven-constructor
grammar. Its let case relates initializer values before applying the body
induction hypothesis to extended environments and lifted substitution.
`liftSub` leaves the newly bound variable alone and weakens replacements for
old variables. `liftSub_agrees` invokes renaming with the extra value, so no
closedness restriction is smuggled into that case. `eval_single` permits free
runtime variables in both replacement and body. `specialize_correct` retains
every runtime valuation; static substitution additionally compares syntax.

**AUD-432-FP1, dismissed suspicion:** environment agreement resembles the
conclusion but concerns only variables; the theorem derives the composite-term
result. Identity substitution satisfies it under the same valuation. The
retained `underLet` example replaces a variable by an open runtime variable
and obtains 4 beneath a let-bound 99. The positive case uses `eval_single`;
the separate captured expression yields 99 and is rejected. Thus the premise
is useful and satisfiable, not a disguised whole-client theorem. The result
does not claim normalization or a syntactic equality decision procedure.

## Descent separates fibers from chosen sections

Independently quotient pairs `(a,e)` by R together with
`transport(a,b,e)=f`. Identity and composition make this an equivalence
relation. Insertion into the fiber over `[a]` is injective by identity transport
and surjective by transporting a representative back to a. No inhabitation
of E(a) is needed. These are the steps in `totalSetoid`, `insert_eq_iff` and
`insert_surjective`.

R is Prop-valued: proof irrelevance identifies proofs of the same relatedness,
matching the specified thin-relation restriction. `fiberEquiv` uses
`Equiv.ofBijective`, hence a noncomputable inverse in Lean; the implementation
report already distinguishes this from a representative selector. No arbitrary
higher loop action or proof-object identity is promised by this contract.

For one supplied `w : ∀a, E(a)`, equivariance makes `[(a,w(a))]` independent
of representative. `section_descends_iff` asks for one descended function with
all pullback equations; it does not replace `∃s,∀a` with separate pointwise
witnesses. Comparing total-space values suffices for the subtype fibers,
whose remaining field is a proposition. `recover` returns precisely w(a).

**AUD-432-FP2, dismissed suspicion:** equivariance is equivalent to existence
with exact recovery, but is an appropriate local condition for a factorization
criterion. The construction derives the descended object instead of assuming
it. The three-point example has two distinct indices in one class and only
zero in the other, and recovers zero through `recover`. For universal R on
Bool with identity transport, `w(a)=a` would force false=true after descent.
`no_selected_descent` rejects that guarantee through the public iff theorem.
Changing transport changes the contract. Empty fibers are allowed in the
family theorem; requiring w in the selected-section theorem does not infer
global choice from pointwise inhabitation.

## Numerical composition needs both intermediate domains

Let `y=f(x)` and `ŷ=fhat(xhat)`. Triangle inequality and the first certificate
give `dist(ŷ,y) ≤ Lf*e+df`, using local error at xhat and sensitivity between
xhat and x. Applying the same reasoning to g gives
`dist(ghat(ŷ),g(y)) ≤ Lg*(Lf*e+df)+dg`, provided both y and ŷ lie in the
second domain. This independently recovers the order in `Bound.comp`.

`estimate` gets this orientation by distance symmetry around `propagate`.
`compose` uses `closed hx` and `closedHat hh` for those two points;
`compose_three` retains both closures at the next boundary. Associativity
changes grouping, not stage order. Maps remain explicit parameters, so equal
bounds do not identify implementations. Pseudometric spaces suffice because
the theorem never turns zero distance into equality of points.

**AUD-432-FP3, dismissed suspicion:** negative real radii and empty domains
can make premises unusable, but do not undermine the advertised clients.
An actual input pair with `dist ≤ e` entails `0 ≤ e`. The affine example
supplies concrete uniform bounds and nonzero input uncertainty; `amplification`
calculates error 1/2 against the false additive estimate 3/10. A two-sided
interval encloses outputs without asserting every enclosed value is produced
by the chosen implementation. `same_error_distinct_outputs` rejects identifying
two selected values by their equal errors.

These additional **paper controls**, not new Lean theorems, isolate each
closure premise. All spaces are real with ordinary distance, `s=t={0}`,
`xhat=x=0`, `e=0`, first bound `(Lf,df)=(0,1)` and second bound `(Lg,dg)=(0,0)`:

| Omitted condition | Maps | Failure of the weakened guarantee |
|---|---|---|
| Approximate closure | `f(z)=0`, `fhat(z)=1`, `g(z)=0`; `ghat(z)=100` if `z=1`, otherwise 0 | f maps s to t. The actual intermediate is 1 outside t; final distance is 100 against composed bound 0. |
| Exact closure | `f(z)=1`, `fhat(z)=0`; `g(z)=100` if `z=1`, otherwise 0; `ghat(z)=0` | fhat maps s to t. The exact intermediate is 1 outside t; final distance is again 100 against bound 0. |

Each exact map has sensitivity zero on its singleton domain. In both rows
the first local distance is 1 and the second local distance at zero is 0, so
all other premises hold. Four constant-zero maps give a positive case with
both closures. These calculations reject weakening the existing theorem;
they do not find an error in it. The existing `domain_membership_needed`
declaration provides a checked control for the related single-stage boundary.

## Least-solution selection is stronger than fixedness

The independent iteration starts at bottom and repeatedly applies f.
Monotonicity makes it increasing; continuity proves the supremum fixed.
Induction places every approximant below any prefixed point. The local
`solution_le` thus compares against prefixed points without assuming uniqueness
of arbitrary solutions. A strict continuous h intertwining f and g maps each
approximant to its counterpart, then preserves their supremum.
`map_approximants` and `map_solution` implement those distinct steps.

The countdown's independent result is value `size γ` and trace `[k,…,0]`.
Its approximants are defined exactly when enabled and `k<fuel`. The supremum
proof uses approximant `k+1` for each coordinate, not a common finite fuel
for all k. It produces one function of γ,k. Reindexing precomposes arguments
and is strict, continuous and intertwining; `two_reindexings` applies the
general theorem twice before identifying 4 : Fin 5 and `[2,1,0]`. The observation
map intentionally forgets the trace through its own admitted strict map.
That different specification does not require maximal witness retention.

**AUD-432-FP4, dismissed suspicion:** f and g need not preserve bottom.
Strictness belongs to h; requiring it of f would exclude the enabled zero
case. Conversely the retained constant h to `Part.some true` intertwines
identity endomaps but sends their least point bottom to a nonbottom result.
This rejection isolates selection from fixedness. Bool negation separately
rejects unrestricted total fixed points. Fuel 2 at enabled countdown 2 yields
bottom although the full denotation succeeds, so exhaustion is not divergence
evidence. No runtime adequacy or uniform realizability follows from these
external set-based statements.

## Calibration, dispositions and further scope

**AUD-432-CAL1, calibration only:** the [known first-wave repair](semantic-traditions-first-wave.md#a-recurring-decision-check)
now uses induction over open mixed terms in the
[control argument](classical-control-selected-search.md), including `walk`
and `test` with open continuation parameter k. It explicitly covers initializer
`walk(k,L,0,[])`; saved continuations instead contain closed stacks. The
retrospective accurately records the previous domain mismatch. This audit
inspected that corrected passage, not the entire simulation or its later Lean
formalization. It is neither a new defect nor newly checked simulation evidence.

| Disposition | Result |
|---|---|
| New incorrect exposition, insufficient theorem strength or erroneous paper argument in the selected contracts | None identified. No weaker true Lean theorem is called a kernel failure. |
| Suspected circularity, vacuity or missing hypotheses | FP1–FP4 dismissed with the reasons and controls above. |
| Known historical defect | CAL1 used only as calibration. |
| Repairs or exact successor issues needed | None: no unresolved in-scope gap was found and no specification was weakened. |

Do not introduce a semantic-certification lint from this sample. A premise
resembling a conclusion would falsely flag variable agreement and equivariance;
demanding strict endomaps would reject the intended countdown; flagging every
real-valued radius would confuse impossible inputs with vacuous advertised uses.
The initializer lesson warrants a review prompt: enumerate intermediate forms
and compare them with the induction domain. A detector would need explicit
grammar/consumer data and both actual mismatches and valid extensions. This
pass establishes no such detector for arbitrary Lean or prose, so adds none.

For the next audit, #235 should consider excluded higher-order and weak-machine
substitution consumers, where intermediate runtime forms make the calibrated
failure plausible, and separately analytic domain closures in numerical
execution. These are recommendations to scope another pass, not findings or
scheduled implementation. Fix the sample and independent contracts before
expanding coverage.

## Validation limits

No formal files or examples changed. Existing statements and proof bodies were
read; only `FirstOrder.lean` and `SquareKit/FirstOrderSubstitution.lean` received
a fresh focused Lean source check. It compiled into a new private temporary
directory, using the pinned direnv environment and private `LEAN_PATH` with
the freshly built FirstOrder module. It shares no writable Lake build output
and is not an integrated build or exhaustive axiom audit. Other selected Lean
results were inspected, not rebuilt. The two additional numerical controls
remain paper calculations. No execution or productivity measurement was made.

Documentation validation covers local links, fences and whitespace. No Lean,
dependency, Nix or build-tool change requires a production build for this report.
Exact check commands and candidate-matched validation are retained by the
coordinator. Independent review outcomes must not be inferred from this audit's
absence of findings.
