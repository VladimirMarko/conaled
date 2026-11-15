# Categorical systems, interconnection and approximate transport

Research assessment for [#392](https://github.com/VladimirMarko/conaled/issues/392),
under [#235](https://github.com/VladimirMarko/conaled/issues/235), 2026-11-09.
Code inspection baseline: `68c85372b1754658786614bf2cc295ea9ec1293a`.
This document specifies an experiment; it adds no Lean declarations and reports
no new checked approximation theorem.

The bounded discrete follow-up is now recorded in
[Finite approximate transport through feedback wiring](approximate-wiring-experiment.md).
It retains this assessment as the research specification and states the
implemented comparison and remaining continuous-flow boundary separately.

Myers provides a useful exact account of systems, their interfaces and behavior
composition. Adopt that account as a design test, and extend the existing finite
wiring experiment with a separate quantitative comparison. Do not retrofit all
preservation contracts into a systems-theory interface. The approximation lead
in the book remains a research obligation, and the local code already supplies
more exact interconnection structure than a sequential-contract comparison would
suggest.

## Sources and reproducibility

The primary sources inspected are David Jaz Myers's
[author-hosted draft PDF](https://www.davidjaz.com/Papers/DynamicalBook.pdf),
marked September 3, 2023, and the source tree at
[`8e662c5c7f7dae0eb39fb5858af9f0c295403178`](https://github.com/DavidJaz/DynamicalSystemsBook/tree/8e662c5c7f7dae0eb39fb5858af9f0c295403178).
That revision was also the repository HEAD at retrieval. The downloaded PDF's
SHA-256 is
`ef1266986be540eb0ee71c96aaac968e34774f4922e204358ae6096756141c8e`.
Reproduce the source identity with:

```sh
curl -L --fail https://www.davidjaz.com/Papers/DynamicalBook.pdf -o DynamicalBook.pdf
sha256sum DynamicalBook.pdf
git clone https://github.com/DavidJaz/DynamicalSystemsBook
git -C DynamicalSystemsBook checkout 8e662c5c7f7dae0eb39fb5858af9f0c295403178
```

The PDF URL is mutable: a different checksum means a different artifact. The
2022 source revision and the PDF's 2023 date do not prove textual agreement.
The targeted passages were compared by content: the Euler proof and approximation
remark, change-of-theory functoriality, and representable behavior/tautness
statements occur in both. No whole-document equivalence or reproducible PDF
build was established. Numbered references below use the PDF; source labels
and files give a second locator where numbering may change.

| Material | PDF locator | Pinned source locator and status |
|---|---|---|
| Lenses and wiring | §1.3, especially §§1.3.1–1.3.2 | [C1-.tex](https://github.com/DavidJaz/DynamicalSystemsBook/blob/8e662c5c7f7dae0eb39fb5858af9f0c295403178/book/C1-.tex), `def.lens`, `def.lens_composition`, `def.lens_parallel`: definitions and exact laws. |
| Indexed and monadic lenses | §2.6 | [C2-.tex](https://github.com/DavidJaz/DynamicalSystemsBook/blob/8e662c5c7f7dae0eb39fb5858af9f0c295403178/book/C2-.tex), `sec.wiring_together_non_det`: generalized lens prerequisites. |
| Behaviors and charts | §§3.2–3.5 | [C3-.tex](https://github.com/DavidJaz/DynamicalSystemsBook/blob/8e662c5c7f7dae0eb39fb5858af9f0c295403178/book/C3-.tex), `def.chart_discrete`, `def.behavior_discrete`, `eqn.behavior_discrete`: interfaces, dynamics equations and double-category organization. |
| Changes of theory | Definition 4.5.1.2; Proposition 4.5.1.11; Remark 4.5.1.12; Theorem 4.5.2.2 | [C4-.tex](https://github.com/DavidJaz/DynamicalSystemsBook/blob/8e662c5c7f7dae0eb39fb5858af9f0c295403178/book/C4-.tex), `def.change_of_doctrine`, `eqn:euler.affine.map`, `sec:functoriality.of.sys`: proof arguments for the exact claims; the approximation remark proposes further work. |
| Composition and recovery | Theorems 5.3.2.1 and 5.3.3.1 | [C5-.tex](https://github.com/DavidJaz/DynamicalSystemsBook/blob/8e662c5c7f7dae0eb39fb5858af9f0c295403178/book/C5-.tex), `thm.representable_discrete`, `thm:representables.taut`: proofs supplied. The abstract representable construction requires the horizontal factor condition (`defn:spanlike`, `thm:representable.lax.doubly.indexed.functors`). |

These are proofs in a draft, not machine-checked results in this repository.
Example 5.3.3.2 has an unfinished worked wiring passage (PDF printed p. 249).
That omission must not be treated as an implemented trajectory example. The
approximation remark gives no general metric, error-composition law, domain
invariance argument or stability theorem. The proposed experiment below supplies
its own explicit obligations.

## Exact interfaces and laws

Here is an unpacking in ordinary deterministic sets; dependent interfaces use
reindexing in the indexed category. An interface has outputs `O` and inputs `I`
(possibly a family over `O`). A system has state `S`, readout `r : S → O`, and
update `u : S × I → S`. Differential systems replace the next-state target by
the appropriate tangent object. A theory packages an indexed category
`A : Cᵒᵖ → Cat` and a section `T` specifying allowable changes of state.

A lens `w : (I,O) → (J,P)` has `wout : O → P` and
`win : O × J → I`. Wiring substitutes the supplied inputs:

```text
r[w](s)   = wout(r(s))
u[w](s,j) = u(s, win(r(s),j)).
```

For a second lens `v`, composition substitutes
`win(o, vin(wout(o),k))`; its output map is `vout ∘ wout`.
Identity and associativity follow from substitution. Independent components
combine by product states and componentwise updates/readouts, before wiring.
The monoidal/product hypotheses enabling this parallel composition must be
present; an arbitrary indexed functor need not preserve the chosen products.

A chart has a covariant input map, unlike a lens's backward input map. For a
probe system `P`, a behavior in `S` consists of a state map `b` and a chart
`(c, cin)` satisfying

```text
rS(b(p)) = c(rP(p))
uS(b(p), cin(rP(p),i)) = b(uP(p,i)).
```

The differential version uses `Db` on the probe velocity. Time, fixed-point,
and clock probes select trajectories, steady states and periodic behaviors.
The chart retains the input/output trace; behavior is not just the terminal
output. Arenas form a double category with lenses, charts and compatible
squares. Horizontal/vertical composition and interchange explain why behavior
maps and rewiring fit together. The doubly indexed category of systems keeps
this interface information separate from the systems over it (Chapter 4,
including Definition 4.3.0.2 and the vertical-slice construction in §4.4).

A change of theory consists of an indexed functor `(F,Fbar)` and a transformation
of sections `phi : Fbar T1 → T2 F`. Its naturality square must commute for every
admitted state map, with the indexed functor's reindexing comparison understood.
It changes the update by applying `Fbar` and then `phi`, and the readout by `F`.
Theorem 4.5.2.2 makes this construction functorial on systems and their behavior
maps. Thus interpretation commutes with rewiring and with successive changes
of theory through the specified comparisons. For a parallel family the desired
law is, schematically,

```text
F(wire(w, parallel(Si))) ≅ wire(F(w), parallel(F(Si))).
```

The parallel part additionally needs compatible product/monoidal structure.
In the Euclidean Euler example those comparisons are the ordinary product
ones. These exact equalities are not bounds on the difference between Euler
samples and a continuous solution.

Theorem 5.3.2.1 supplies a *lax* behavior comparison: compatible component
behaviors and their wiring data give composite behaviors. Laxness does not
assert that every composite behavior comes from such data. Theorem 5.3.3.1
makes the rewiring comparison invertible when the **probe's** readout is an
isomorphism. It is not a condition that the modeled system expose all its
state. The inverse retains the matching chart/wiring witnesses. For trajectory
probes this reconstructs compatible component trajectories from a full composite
behavior; it does not reconstruct hidden states from an externally observed
output trace. Steady-looking behavior with hidden probe state fails that general
recovery claim (Remark 3.2.2.5). The abstract representable theorem also needs a
spanlike double category, or the relevant horizontal factor condition; it is
not a theorem about every arbitrary double category.

## What the local code supplies

The following claims are based on declarations at the recorded baseline,
including the linked examples, rather than on the older inventory alone.

| Current contract | Evidence | Adapter or mathematical gap |
|---|---|---|
| Exact interconnection | [Wiring](../../Applications/OpenSystems/Wiring.lean): `Routing.supply_comp`, `System.wire_comp`, `parallel`, `Smooth.wire`, `Smooth.parallel`. [OpenSystemWiring](../../Examples/OpenSystemWiring.lean): `hierarchy`, `dynamics_conjugacy`, `hierarchy_reverse`, `flatten_left`. | Real scalar ports and state-only readouts; certified `Wiring` requires a finite no-passing port bijection. `System.wire` itself accepts the broader `Routing`, without that certificate. No generalized indexed theory, behavior-probe functor or quantitative rewiring comparison is implemented here. Smoothness is not existence or stability of solutions. |
| Ordered transfer and combination | [PreservationBounds](../../SquareKit/PreservationBounds.lean): `Interaction.Refines.bound`, `comparison_comp`, `combine`. | Target coverage and observation comparison are explicit. `combine` is not restricted to sequential costs: it accepts arbitrary source/target operations with monotonicity and compatibility. But the caller must prove that the chosen operation bounds the actual composite. It does not derive coupling gains or solve feedback. |
| Exact engine/reference alignment and conditional progress | [FRP Engine](../../Applications/FRP/Engine.lean): `step_refines`, `run_refines`, `response_honest`, `eventual_response`. | Alignment retains silent command positions; honest source relations connect responses to truth. Progress requires delivery, fairness, processing and advancing-prefix assumptions. An open-system adapter must preserve these temporal/environmental obligations. Neither lens composition nor numerical closeness implies fairness or delivery. |
| Exact probability interpretation | [FiniteKernel](../../Applications/Probability/FiniteKernel.lean): `Table.kernel_comp`, `tableMeaning_laws`, `table_steps_meaning`, `invariant_comp`. | Rational stochastic tables preserve the entire kernel, including mass. Stationarity composition assumes a shared invariant measure. Wiring stochastic components needs a joint-law/coupling choice; marginal errors alone cannot preserve correlation. There is no stochastic feedback/error theorem in these declarations. |
| Approximation with successful execution and domains | [NumericalExecution](../../Applications/Orbifold/NumericalExecution.lean): `run_correct`, `run_append`, `run_error`, `run_interval_correct`. | Successful `Option` runs retain endpoint relations and domain validity; `errorAfter` iterates command-specific budgets. Feedback-dependent controls and approximate theory changes need new compatibility proofs. Rational arithmetic does not introduce or bound floating-point roundoff. |

The [contract inventory](preservation-contract-inventory.md) also records
indexed witnesses, path labels and probability correlation. Those contracts
cannot be recovered by replacing everything with a distance on final values.
An exact interpretation preserves its selected semantic equality; a refinement
can discard possibilities with explicit coverage; an approximation compares
selected observations with a budget. None automatically reflects source
behavior or reconstructs witnesses. This agrees with
[ADR 0002](../adr/0002-relations-and-synchronization.md), while challenging any
assumption that relation composition alone discharges every wiring obligation.

## Euler's affine restriction and the missing approximate law

Proposition 4.5.1.11 uses `E_h(s,v) = s + h v`, for `h > 0`, as the section
comparison from affine-restricted Euclidean differential systems to deterministic
Euclidean systems. For an affine state map `f`,

```text
f(s + h v) = f(s) + h Df(s)v.
```

The affine restriction concerns admitted maps, including the behavior and chart
maps in §4.5.2; it does not mean that every component vector field is linear.
Euler preserves wiring in this setting and preserves affine behaviors such as
steady states. General solution curves are usually not affine, so the exact
change-of-theory theorem does not transport them as exact Euler trajectories.

For a nonlinear `C²` map, a second-derivative bound `H` on the segment from `s`
to `s+h v` yields a defect at most `H h² ‖v‖² / 2` by Taylor's remainder.
This is an analytic obligation added here, not a proved theorem in Remark
4.5.1.12. A useful approximate comparison also needs bounds on velocities,
transport of inputs/readouts, the target update's Lipschitz gain, and preservation
of the region where those bounds hold. A further interpretation with gain `K`
amplifies an earlier defect `δ` to `K δ` before adding its own defect. A sum of
unweighted component budgets misses this dependence.

State-only readouts make feedback substitution explicit at the current state.
For smooth vector fields, a separate local existence/uniqueness argument still
needs its analytic hypotheses; global or finite-horizon existence needs more.
Input-dependent instantaneous readouts can instead create algebraic equations
with zero, one or many solutions. Contractive feedback could be a separate
admissible construction with its own gain denominator. No arbitrary feedback
solver follows from lens composition or from a budget-combination lemma.

## Bounded experiment: the existing three-component feedback circuit

Use the actual `A`, `B`, `C`, `ab`, `bc`, `close` and `flat` fixture in
[OpenSystemWiring](../../Examples/OpenSystemWiring.lean). Its equations are

```text
x' = -x + u + z      y' = -2y + x      z' = -3z + y
observable = z.
```

The wires connect A to B, B to C, and one C output back to A; C's other
output remains exposed. Two distinct C ports carry the same state readout,
so this does not reuse a supplier in the certified wiring. This is an actual
feedback interconnection, not a list of sequential commands.

Freeze constant external input `u=0`, state domain `R³`, max norm, step `h>0`,
and finite horizon `N h ≤ T`. Require every Euler component to read the same
pre-step state. Specify these deliverables for a separately scoped experiment:

1. **Exact baseline.** Reuse the checked reassociation `coordinates` and the
   two wiring hierarchies. Define Euler next state from the field, prove that
   discretizing the wired field equals wiring the discretized components, and
   prove that `coordinates` commutes with their Euler updates. Retain the whole
   field/readout contract and identity/rewiring laws, not just output equality.
   The continuous solution is independently `s(t)=exp(t M)s(0)`, where
   `M=[[-1,0,1],[1,-2,0],[0,1,-3]]`; its existence and derivative equation are
   separate analytic proof obligations.
2. **Approximate transport.** Replace only A's state coordinate by
   `q=g(x)=x+x³`, with readout `g⁻¹(q)`. The derivative `1+3x²` is positive;
   `g` is a global smooth bijection and its inverse is 1-Lipschitz. Set
   `Phi(x,y,z)=(g(x),y,z)` and target field
   `G(Phi(s))=DPhi(s) M s`. Prove this identity componentwise before wiring.
   B and C are unchanged and consume the decoded A readout, so the continuous
   systems remain conjugate with the same external observable. Euler in the
   two coordinates does not commute exactly.
3. **Local defect and propagation.** For `v=-x+z`, compute the defect exactly:
   `Phi(s+h M s) - (Phi(s)+h G(Phi(s))) = (3x h²v²+h³v³,0,0)`.
   On `‖s‖∞≤R`, it is bounded by
   `δ=12R³h²+8R³h³`, since `|v|≤2R`. For source Euler states `s_n` and target
   Euler states `q_n`, let `e_n=‖Phi(s_n)-q_n‖∞`. Supply a convex target region
   containing both sequences and a bound `L_G` for `G` there. Then prove
   `e_(n+1)≤(1+h L_G)e_n+δ` and its finite sum bound
   `e_N≤(1+h L_G)^N e_0+δ Σ_(j<N)(1+h L_G)^j`.
   Coordinate bounds and domain membership are premises to discharge, not
   consequences of an unexplained big-O estimate. Since the external output
   is the third coordinate, its discrepancy is at most `e_n`.
4. **Independent flow error.** Also compare source Euler with the continuous
   solution, rather than using the other Euler route as ground truth. If
   `‖s''(t)‖∞≤M₂` on `[0,T]`, the local flow defect is at most `M₂h²/2`.
   The raw norm bound `‖M‖∞≤4` gives the analogous recurrence with factor
   `1+4h`. Combine that bound with the transport bound for sampled observations.
   For full transformed states, account for `Phi`'s Lipschitz constant
   `1+3R²` on a containing box. Exact arithmetic is assumed; roundoff would
   require another error term and domain check.

For the original linear circuit, `0<h≤1/3` makes all diagonal Euler coefficients
nonnegative, and its row sums are `1`, `1-h`, `1-2h`. Thus source Euler is
nonexpansive in the max norm and preserves the box `‖s‖∞≤R` for `u=0`.
This is a concrete route to discharging one domain premise. It does not prove
that target-coordinate Euler preserves `Phi` of that box. Prove a suitable
larger invariant region or bound a finite horizon with a guard; if a guard
fails, report failure and keep the error theorem conditional on success.
For the continuous linear source, existence is global and an exponential
norm bound can bound `M₂`; these facts still need checked analytic proofs in
an implementation. No uniform-in-time error follows from the finite sum above.

Derive gains from component contracts and routing before applying a general
ordered bound lemma. With absolute component errors, the source Euler comparison
uses the nonnegative matrix

```text
B_h = [[|1-h|, 0, h], [h, |1-2h|, 0], [0, h, |1-3h|]].
```

The off-diagonal entries are the wiring-induced input sensitivities. In the
transformed circuit, A's decoded output error feeds B, B feeds C, and C feeds
A; bound those sensitivities on the selected domain. Showing that `combine`
can consume the resulting bound is useful, but supplying that matrix as an
unexplained premise would fail this experiment's composition objective.

### Negative cases and acceptance decision

At `s=(1,0,0)` and `h=1/4`, the transport defect in the first coordinate is
`11/64`, so a purported exact nonlinear Euler transport law must fail. Output
`z` alone initially hides that defect, but the feedback circuit propagates
state discrepancies through later updates. Compare full state relations and
sampled outputs over the horizon.

Changing the feedback to `x'=-x+kz`, leaving the other equations unchanged,
gives characteristic polynomial `(λ+1)(λ+2)(λ+3)-k`. For `k>6` it has a positive
real root (negative at zero and positive for sufficiently large positive λ).
Thus stable isolated components do not justify a stable interconnection or a
uniform error budget. Even in the original circuit, `h=1` gives Euler matrix
trace `-3`; if all three eigenvalues had modulus strictly less than one, its
trace would have modulus less than three. A blanket assertion of strict Euler
stability for all positive steps is therefore false.

Keep the checked `feedthrough_feedback_unsolvable` and `fanout_rejected` cases
as admission regressions. An algebraic feedback `i=i+1` has no solution; using
a routing that violates the certified bijection silently changes the supported
wiring class. Also retain a behavior-recovery test with a hidden-state probe:
an output quotient must not receive the invertibility guarantee of Theorem
5.3.3.1 merely because its forward behavior comparison exists.

Acceptance requires component-derived gains, exact baseline laws, the nonzero
defect, a conditional finite-horizon observation theorem, and explicit treatment
of domain failure. Compare direct native proofs against a reusable quantitative
adapter on these same obligations. Record repeated author work, hypotheses and
conversion overhead. If the adapter only repackages an entire composite bound
proved independently, it has not demonstrated reuse. If it forces exact maps,
erases intermediate domain failures or assumes all probes recoverable, it is
insufficient. Successful finite-horizon transport still would not settle a
general approximate change-of-theory theorem.

## Recommendation and follow-up ownership

Keep `Wiring`'s exact substitution laws and existing domain APIs. Add a separately
scoped experiment pairing a chosen interconnection with state/readout comparisons,
local defects, gains and admissibility evidence. This may become an optional
quantitative extension, or a separate construction if its hypotheses do not fit
the existing preservation families. The book's double-category organization
could eventually replace repeated hand-built compatibility diagrams; assess it
on actual reused proofs before deciding that every client should migrate.

| Proposed owner | Bounded next work and retained guarantees |
|---|---|
| [#235](https://github.com/VladimirMarko/conaled/issues/235), coordinated with [#200](https://github.com/VladimirMarko/conaled/issues/200) | Own the experiment and choose native extension versus separate comparison construction. Require composition across wiring and interpretation, not merely sequential iteration. Keep `Refines.bound` coverage and `combine` compatibility explicit. Reassess shared interfaces only after evidence of reuse. |
| [#34](https://github.com/VladimirMarko/conaled/issues/34) | Numerical consumer: test component-dependent controls and domain guards. Retain `Approx`, endpoint correspondence, possible failure and symmetry/witness contracts. A new circuit theorem must not be advertised as a theorem about the existing disk-motion integrator. |
| [#27](https://github.com/VladimirMarko/conaled/issues/27) | FRP consumer: assess a discrete state-only adapter that retains command alignment, event positions and environmental fairness. Do not infer progress from quantitative closeness. |
| [#200](https://github.com/VladimirMarko/conaled/issues/200), with the probability library consumer | Before stochastic adoption, specify joint kernels/couplings and the metric or observation being approximated. Retain full-law interpretation and shared-invariant hypotheses; support-only or marginal comparisons cannot replace them. |
| [#290](https://github.com/VladimirMarko/conaled/issues/290) and [#36](https://github.com/VladimirMarko/conaled/issues/36) | Assess whether the section/naturality and probe requirements can be exposed as reusable author requirements. Carry indexed charts and comparison witnesses. This research does not supply an importer or universal internal language. |

These are scoped follow-up proposals, not newly opened issues or an approved
whole-book port. Existing consumers remain direct usable specializations. Any
later retrofit must recheck exact kernel interpretation, FRP response/progress
hypotheses and successful numerical-run contracts alongside the new wiring
client; weakening these contracts is not an acceptable migration strategy.

## Claim review and validation

Statement review separated the book's exact proof claims, its unfinished example,
its proposed approximation extension, the current Lean declarations and the
unimplemented experiment obligations. The probe-readout hypothesis was checked
against Theorem 5.3.3.1; Euler's map restriction against Proposition 4.5.1.11 and
its §4.5.2 behavior discussion. Formula review checked the cubic defect,
nonnegative Euler row sums, gain matrix and unstable-feedback polynomial.
The distinction between full behavior recovery and external observability is
part of the proposed negative test.

Validation is documentation/source inspection, local-link checking and
`git diff --check`. No Lean or tooling files change, so no new build or proof
audit is claimed. Independent Standards and Spec review belongs to the parent
implementation workflow and must finish before acceptance.
