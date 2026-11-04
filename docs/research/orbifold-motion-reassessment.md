# Orbifold motion: representations and mathematical settings

Assessment dated 2026-11-04. This revisits the choices in
[#33](https://github.com/VladimirMarko/conaled/issues/33), rather than treating
its first implementation as the final architecture. Literature results below
are paper results, not newly checked Lean theorems. Proposed comparisons and
experiments are explicitly recommendations.

## What we already investigated

The [gyrovector assessment](gyrovector-generalizations.md) contains a real
literature comparison: Isabelle's AFP gyrovector development; Nguyen's SPD
and Grassmann constructions; Kikkawa's geodesic local loops; double
exponentials for general affine connections; post-Lie integration with
parallel curvature and torsion; and orthonormal frame development on effective
orbifolds. It distinguishes their hypotheses instead of assuming that every
curved space has a gyrovector algebra. Lorentz representations were proposed,
but were not implemented or compared numerically there.

The record also contains our own mathematical comparisons. The note derives a framed-path
contract, compares independent disk pose and matrix formulas, records a
variable-curvature counterexample to homogeneous assumptions, and records
reproducible numerical probes. Subsequent Lean results include the failure of
independent-representative point addition and agreement of the implemented
disk representations. The note distinguishes those checked results from its
mathematical calculations and floating-point observations.

The source set substantially follows the leads in the imported discussion;
the record does not establish a separate broad discovery pass before choosing
the first slice. That evidence supports the chosen first slice. It does not establish that
framed paths are the best general interface. In the geometry notes inspected
for this assessment, there is no developed comparison with transport functors
over stacks, Lie-groupoid variational mechanics, or nonassociative loopoids.
There is also no comparative Lorentz/Clifford implementation or measured
representation ranking. These are gaps in the recorded investigation, not
claims that nobody previously considered those subjects.

## Alternatives worth comparing

### Transport functors and bundles with connection over stacks

Schreiber and Waldorf characterize parallel transport through smooth functors
with local trivializations and descent data. This provides an alternative
description of bundles with connection, not just an encoding of a chosen
matrix action. [Parallel Transport and Functors, v5](https://arxiv.org/abs/0705.0452v5).

Collier, Lerman and Wolbert extend the correspondence to stacks. Their
Theorem 4.1 establishes the manifold equivalence; Theorem 5.4 promotes
holonomy to an equivalence of stacks; Theorem 6.4 obtains the corresponding
equivalence for bundles with connection over a stack. The underlying paths
use thin homotopy, which preserves connection holonomy; arbitrary homotopy
does not. [Parallel Transport on Principal Bundles over Stacks, §§2, 4–6](https://arxiv.org/html/1509.05000v1).

Assessment: this is the most directly relevant missing comparison for our
general motion semantics. It could replace presentation-specific transport
bookkeeping with a bundle/transport interface whose descent is proved once.
We must still supply the metric or connection, physical controls, and
existence domains. A transport observation can forget elapsed time, so it
cannot replace a timed simulator trace without a separate observation map.
An orbifold presentation groupoid's arrows identify descriptions; they must
not be confused with the paths describing physical motion.

### Cartan development and rolling

The earlier note already proposes controlled development on a frame space
using the solder and connection forms. This is a substantive geometric
alternative to point addition, not merely a disk representation. A further
comparison is intrinsic rolling: Chitour and Kokkonen formulate rolling
against space forms through a control system and relate controllability to
the associated connection and holonomy.
[Rolling manifolds on space forms](https://www.numdam.org/item/AIHPC_2012__29_6_927_0/).

Assessment: compare a control-and-development interface with transport-only
semantics. The former determines how a command produces a path; the latter
describes what transport along a supplied path does. The orbifold extension,
including ineffective isotropy and changes of presentation, still needs its
own argument. Neither paper-level manifold rolling nor the local disk
implementation establishes it.

### Variational mechanics on Lie groupoids

Marrero, Martín de Diego and Martínez derive discrete Euler–Lagrange equations
on Lie groupoids and a preserved symplectic structure. Their framework
includes ordinary discrete mechanics and reduced Euler–Poincaré and
Lagrange–Poincaré cases. The journal records a corrigendum; any theorem-level
adoption must check the corrected statements.
[Revised preprint](https://arxiv.org/abs/math/0506299v2),
[journal record and correction link](https://doi.org/10.1088/0951-7715/19/6/006).

Assessment: this offers a different starting point when motion should follow
a mechanical law, with discrete variational structure guiding integration.
It is not a drop-in proof that an Euler step preserves that structure. Nor
does choosing the orbifold's étale presentation groupoid automatically
produce physical dynamics: its source fibers are discrete and its Lie
algebroid, defined from the tangent spaces of source fibers at units, has zero
rank. This is our structural observation, not a claim that the paper implements
orbifold mechanics. The relevant dynamical configuration and transition
groupoid, or a stack-level construction descending from charts, must be
identified. That distinction is a mathematical prerequisite for this route.

### Nonassociative loopoids

Grabowski and Ravanpak develop smooth loopoids and quasiloopoids, their
infinitesimal structures, and discrete mechanics without associative
multiplication. [Nonassociative analogs of Lie groupoids, v2](https://arxiv.org/abs/2101.07258v2).

Assessment: this is a candidate if the desired interface should retain local
displacement arithmetic rather than enlarge states until composition is
associative. The earlier geodesic-loop survey does not settle this option.
We have not established an orbifold instance, a gyrogroup comparison, or a
benefit over framed paths. A trial must state admissibility domains and
isotropy behavior rather than weaken away the requirements that motivated
the simulator.

### Lorentz and Clifford realizations

The earlier assessment proposed a real Lorentz realization with sheet and
orientation restrictions, distinct from the existing complex projective
model. Sokolov studies projectivized Clifford algebra for hyperbolic spaces
in dimensions one through three. Gunn compares projective and conformal
geometric algebra for Euclidean primitives and kinematics.
[Sokolov](https://arxiv.org/abs/1602.08562v1),
[Gunn](https://arxiv.org/abs/1411.6502v4).

Assessment: these are plausible alternative realizations for constant-curvature
motions and geometric primitives. Neither cited result supplies a general
variable-curvature orbifold motion law. Compare them on common point/frame
semantics, composition, valid domains, and executable workloads before
choosing one.

Numerical superiority cannot be inferred from exact equivalence. Mishne and
coauthors find different floating-point tradeoffs for Lorentz and Poincaré
representations, including a distinction between representing points and
optimization behavior. Their workload is representation learning, not this
simulator; their results motivate a simulator-specific comparison rather
than settle it. [The Numerical Stability of Hyperbolic Representation Learning](https://proceedings.mlr.press/v202/mishne23a.html).

## What a Myers-style setting could improve

Myers defines orbifolds as microlinear types with properly finite
identification types. Maps are functions; isotropy is self-identification.
The tangent fiber is defined by pointed maps from the infinitesimal interval,
and isotropy acts on it through its dependence on the base point. Microlinearity
provides coherent module structure on tangent fibers, including for higher
types. These are mathematical simplifications of constructions and their
compatibility laws. [Myers, Definition 1.1.2, Definition 4.1.8,
Remark 4.1.10 and Theorem 4.2.19](https://arxiv.org/html/2205.15887v1).

Schreiber's differential cohesive framework also treats connections and
higher bundles intrinsically and supplies models. This gives evidence that
synthetic settings can organize differential geometry beyond the definition
of orbifolds. [Differential cohomology in a cohesive infinity-topos](https://arxiv.org/abs/1310.7930v1).

There are more focused sources for the motion laws. Kock develops affine
and bundle connections from infinitesimal neighbor relations, then groupoid
connections, holonomy and the Bianchi identity. His ambient category is a
topos with a suitable ring object and infinitesimal axioms, using constructive
reasoning. [Synthetic Geometry of Manifolds, §§2.3–2.5, 5.2–5.8 and 6.4](https://users-math.au.dk/~kock/SGM-final.pdf).
Bunge and Sawyer relate synthetic connections, connection maps, geodesics
and sprays. Their comparisons require additional hypotheses, including
short path lifting and appropriate existence of exponential maps; they
start with vector bundles whose total and base objects are infinitesimally
linear. [On connections, geodesics and sprays in synthetic differential
geometry, introduction and §1](https://www.numdam.org/article/CTGDC_1984__25_3_221_0.pdf).

Assessment: these supply candidate synthetic formulations for connection
and curvature proofs, beyond quotient and tangent definitions. Extending
their hypotheses and constructions to our higher orbifold setting, and
interpreting them in the constructed model, remains work. The cited sources
do not themselves certify that bridge.

Assessment: a Myers-style development could make the motion theory itself
neater. The promising gain is expressing tangent, frame and connection
constructions uniformly over an orbifold, with presentation changes handled
by the model. This should be compared with the external stack/transport route,
which offers another way to make those obligations reusable. There is no
evidence here that only one route can achieve that goal.

The required distinctions remain:

- Identity transport handles identifications, including isotropy. Transport
  along a physical smooth path depends on a connection. An identity type is
  not automatically the simulator's type of trajectories, and identity
  elimination alone is not a Levi-Civita transport construction.
- Internal microlinear geometry requires an appropriate smooth line and
  higher/differential structure. Writing the same syntax over ordinary Lean
  real numbers does not supply that setting. The existing
  [Myers assessment](myers-orbifold-assessment.md) records this model boundary.
- Changing settings does not turn the existing failed representative-wise
  point formula into a well-defined operation, eliminate curvature-dependent
  holonomy, select a metric, or establish global flow existence.
- Exact internal constructions still need a realization and numerical
  contract before they yield executable simulation. Smaller proofs are a
  plausible benefit to test; smaller runtime or rounding error does not
  follow from them.

These are reasons to compare settings on an actual motion theorem. They do
not justify dismissing the synthetic route as merely a prettier description.

## What later workstreams change

This comparison uses source at `2525b12052e4c85c57f9050dbf18f7a36ba2ef19`
and GitHub issue bodies/states read on 2026-11-04. Entries marked as proposals
are recommendations of this assessment, not integrations performed here.

| Work and evidence | Application to orbifold motion | Boundary and decision |
| --- | --- | --- |
| Checked arrow-sensitive composition: [GroupoidTransportRoutes](../../SquareKit/GroupoidTransportRoutes.lean), especially `Route.comp`, `transport`, `transport_concat`, `reindex_comp` | Reuse composition of a base functor and natural fibre map when comparing symmetry actions and tangent families. | Adopt where these hypotheses fit. These are set-valued families over categories; they supply neither arbitrary smooth restriction/descent nor connection transport along physical paths. #103 still requires its source-to-smooth-model proof. |
| Checked pullback coherence: [FamilyCoherence](../../SquareKit/FamilyCoherence.lean), and the open [#292 comparison](https://github.com/VladimirMarko/conaled/issues/292) | Compare the repeated dependent substitution obligations of #107 with local universes or a different representation of contexts and substitution. | Investigate through #292/#289. Its approved discovery stage permits replacement architectures. Lumsdaine–Warren [Theorem 3.4.1](https://arxiv.org/html/1411.1736v2) requires a full comprehension category, condition LF and the appropriate weakly stable constructors. Neither the current helpers nor the paper alone discharge our syntax/annotation correspondence. |
| Checked exact observer descent: [ObservationExtension](../../SquareKit/ObservationExtension.lean), `descend`, `no_factor`; [#267 record](observation-extension-contracts.md) | Organize which observations survive forgetting a frame, choosing a quotient, or changing a representation. A distinguishing pair can refute a proposed coarse observation contract. | Adopt for exact set-valued observations. The setoid API must not replace isotropy arrows or moving tangent fibres. Recovering position observations does not recover the full orbifold. |
| [#287 representation-extension assessment](representation-extension-comparison.md), with [#291](https://github.com/VladimirMarko/conaled/issues/291) still open | Make witness descent and the impossibility of a natural representative selector explicit when comparing representations. | Use as a design constraint. Its paper construction uses thin equivalence-relation groupoids; its Morita terminology does not establish Morita equivalence of orbifold presentations. No completed all-model Lean extension or orbifold descent integration is inferred. |
| Checked [structured linear realizations and costs](structured-linear-implementation.md), #265 | Reuse the distinction between geometry, coordinates, storage and algorithms, and the measured-work/whole-workload comparison machinery for new matrix or factored motion backends. | Investigate an adapter for the actual operation. Matrix-vector application is not certified projective motion composition; closure, form preservation, projective decoding and frame agreement remain required. Small disk matrices do not automatically benefit from sparse storage. The cost model excludes scalar bit complexity, so it does not resolve rational growth in #49. |
| Checked [bounded FRP driver](frp-driver.md), #233; [finite-circuit indefinite service](indefinite-reactive-service.md), #234 | Reuse pure transition/IO separation, bounded decoding, replay and explicit failure contracts when implementing #49's command runner. | Adopt the applicable architecture, investigate actual API reuse. The existing driver serves a different lifecycle. #234's fixed Boolean circuits do not establish bounded memory or per-step work for rational-valued simulation. Interactive controls need not wait for a universal FRP runtime. |
| Open [#299 quantitative composition](https://github.com/VladimirMarko/conaled/issues/299) | The existing recurrence `e' = (1 + 13*d)*e + 39*d^2` is a concrete numerical client for comparing relational, ordered and metric accounts. | Investigate if it reduces recurring proof obligations. It is not nonexpansive, does not give an intrinsic-distance bound, and supplies no rounding term. Keep #49's rational-growth feasibility check. |
| Open [#297 modal contexts/higher identity](https://github.com/VladimirMarko/conaled/issues/297), [#294 theory reuse](https://github.com/VladimirMarko/conaled/issues/294), and [#293 requirement discovery](https://github.com/VladimirMarko/conaled/issues/293) | Separate the differential, identity and context-restriction principles used by a synthetic geometry argument, then compare reusable presentations. | Coordinate with #36/#100; these are research tasks, not already constructed Myers semantics. Modal context control and preservation of nontrivial identity data are different requirements. |

The [language direction](../language-direction.md#selecting-research-by-semantic-requirements)
now explicitly asks discovery to consider approaches that could replace the
current architecture. The existing #107 repair is therefore one bounded route,
not the ceiling on geometric authoring. Its independent #108 retest remains a
gate for the particular #103 implementation; it is not a mathematical dependency
of every possible synthetic geometry investigation. No gate is changed here.

## Proposed comparisons and existing owners

The recommended next investigation is a matched mathematical comparison of
three presentations: current explicit groupoids and framed paths, connection
transport over differentiable stacks, and synthetic infinitesimal geometry in
a higher smooth setting. This is a proposal, not a migration or implementation
started by this assessment. Coordinate geometry under #32/#34 and model/source
interpretation under #36/#100, with #292 owning the dependent-coherence
comparison. Keep the numerical runner under #49 independently actionable.

Use the same cases across routes:

1. **Quarter-turn cone with a chosen connection.** Retain all four origin
   automorphisms, the regular-point case, the tangent action `v ↦ i*v`, and an
   ineffective action with distinct arrows acting identically. Compare how each
   route constructs these facts and handles a change of presentation.
2. **Path-dependent frame transport.** Retain the existing curved loop and its
   closing symmetry separately, plus the variable-curvature example. Require
   composition and coordinate/presentation comparison. This tests whether a
   candidate actually improves motion mathematics beyond quotient formation.
3. **One executable observation.** Recover position, frame, elapsed time and the
   existing coordinate-error contract from a finite move/turn/hold run. Charge
   conversion and arithmetic requirements separately. A neater geometric theory
   need not itself be the execution representation.

Compare the mathematical assumptions and author obligations before selecting
a Lean encoding. Record what a model builder proves once, what every geometry
author repeats, what an interpretation preserves, and what the numerical backend
must still establish. A paper derivation can establish mathematical economy;
checked interpretations establish semantic reuse; an independent author trial
can test usability. None substitutes for the others.

Keep Lorentz or Clifford/spin realizations as competing concrete candidates,
not as prerequisites for this foundation comparison. If one is pursued, compare
it with the current gyro and projective implementations on identical operations,
frame observations, conversion costs and conditioning/error obligations. An
extra coordinate formula alone would not answer the question about a better
mathematical setting.

## Approved investigations and authoring requirement

On 2026-11-04 the owner approved the three-presentation comparison and
investigation of all the alternatives above. The following research issues
are native children of [#34](https://github.com/VladimirMarko/conaled/issues/34):

| Issue | Scope |
| --- | --- |
| [#310](https://github.com/VladimirMarko/conaled/issues/310) | Compare explicit frames, differentiable-stack transport and synthetic geometry on the same motion problem; include Cartan development/rolling and the Myers/Kock connection literature. |
| [#311](https://github.com/VladimirMarko/conaled/issues/311) | Investigate variational mechanics on Lie groupoids, its physical configuration and descent requirements. |
| [#312](https://github.com/VladimirMarko/conaled/issues/312) | Investigate loopoids and local displacement arithmetic, including domains, nonassociativity and quotient obstructions. |
| [#313](https://github.com/VladimirMarko/conaled/issues/313) | Compare Lorentz and Clifford realizations against current exact point/frame semantics, computation costs and numerical behavior. |

These are authorized research tasks, not completed comparisons or authorization
for a wholesale migration. Their issue bodies own acceptance criteria. They
can begin independently; #310 integrates the foundation comparison while the
other investigations retain distinct dynamics and realization questions.

The owner reports that #292 is being finished. #310 must consume its final
reviewed findings when available and verify their exact scope. This does not
assume that #107 is repaired or that a higher smooth interpretation exists.

The owner also identified proficiency in an embedded language or a new
frontend as an unwanted burden. The research must begin with the mathematical
argument and its required principles, without making mastery of an encoding
an entry condition. Separate the model builder's work from recurring geometry
author obligations. Assess whether the interface absorbs syntax, annotations,
substitution and casts, rather than requiring authors to become implementers
of the internal calculus. No frontend is prescribed as a prerequisite, and a
new mathematical setting need not imply a new host language. Any claim that
these burdens have been removed needs concrete author evidence; this assessment
does not claim that the current interfaces already achieve that goal.

## Evidence scope

This was a targeted primary-source search, not an exhaustive literature
review. Search topics included Cartan development and rolling, parallel
transport over differentiable stacks, Lie-groupoid discrete mechanics,
nonassociative loopoids, hyperbolic Clifford algebra, Lorentz numerical
stability, and synthetic connections/geodesics. The Myers and stack-transport
claims were checked against full text, and the synthetic connection sources
against their introductions and relevant section inventory. The variational,
loopoid and representation sources were screened through their author
abstracts and publication records; detailed theorem adoption remains a
follow-up. No numerical benchmark or Lean implementation was added in this
reassessment.
