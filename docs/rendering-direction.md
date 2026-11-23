# Rendering direction

Agreed with the project owner on 2026-11-23. Rendering is a capability goal:
visualize and move through at least three-dimensional orbifold worlds. The
foundations must support other dimensions and geometric settings through
explicit assumptions. Specialized 3D implementations and optimizations are
welcome. The architecture and the order of experiments remain revisable as
working examples expose requirements.

[Simulator #34](https://github.com/VladimirMarko/conaled/issues/34) owns the
rendering milestones and their current status. This document records direction,
not an implemented renderer or a final interface. The
[preserved source chat](history/rendering/README.md) supplies motivation and
research leads; its claims require verification before adoption.

## World, observation and presentation

Keep these choices distinguishable:

- The world contains the scene and supplies the geometric structure used by a
  construction. Its dimension and presentation are not fixed globally.
- An observation specifies what an observer measures, including its sampling
  footprint and relevant camera, illumination, and time parameters.
- A presentation turns the selected observation into a displayed image or
  another output, with its own realization contract.

A two-dimensional display does not require a three-dimensional world. Projection,
slicing and other observations of higher-dimensional worlds are choices to
investigate. A global Euclidean embedding must not be required by the common
scene interface. Merely replacing a fixed dimension by a natural-number parameter
would leave that geometric restriction intact.

The initial optical-response proposal should admit exact geometry, fields and
statistical descriptions as scene meanings. It must expose enough information
for the intended composition. A distribution, an expectation and one persistent
random realization answer different questions; preserve their distinctions and
any dependence needed across views, components, times and resolutions.

Require additional capabilities where used: measures for integration, geometric
transport for comparing attached data, differentiability for AD, and quantitative
regularity for finite approximation bounds. A primitive need not support every
capability. Generality should come from reusable constructions and justified
specializations, not a maximal record of every proposed feature.

## Existing starting points and gaps

The following source inspection is relative to `d682f8ca`; it is not a new build
or an audit of every claim in the chat.

| Existing component | Relevant contract | Rendering work still needed |
| --- | --- | --- |
| [Numerical error composition](../SquareKit/Numerical/Error.lean) | `Bound` composes sensitivity and local error; `compose` requires exact and approximate intermediate values in the next domain. | Select observation distances and derive usable scene, camera and numerical bounds. |
| [Relational squares](../SquareKit/Relations.lean), [ADR 0002](adr/0002-relations-and-synchronization.md) | Preservation of specified relations, with composition and a witness-square presentation. | Define the rendering realization relations and prove their primitive obligations. |
| [Local second-order AD](../Applications/AD/SecondOrderAt.lean) | Derivative composition at admitted points. | Establish quantitative bounds over a query region; a derivative at an anchor does not certify finite reuse. |
| [Charted transport](../Applications/Orbifold/ChartedTransport.lean) | Agreement across witnessed chart subdivisions for the selected disk paths. | Connect observations to transport and extend to the chosen 3D orbifold scene; this is not general orbifold rendering. |
| [Exact memoization](../Applications/Memoization/Cache.lean) | Populated entries equal the specified value at their key; repeated hits reuse that value. | Retain and evaluate approximate local responses under explicit domains and dependency invariants. |
| [Executable disk motion](research/numerical-motion.md) | Rational motion with stated coordinate error and domain checks. | Connect motion error to rendering observations and supply the selected 3D motion realization. |

Reuse the library's distinctions between operations, equivalence and laws, and
its [shared language direction](language-direction.md). Compiler interpretations
should follow demonstrated reusable operations. A first renderer need not wait
for a universal language, a complete orbifold theory, or a general FRP runtime.

## Milestones and evidence

These are revisable milestones, not a requirement to complete all mathematics
before producing an image. The executable path should develop alongside the
semantic experiments.

1. **Small semantics with contrasting clients.** Begin by investigating simple
   emission/transmission responses and a selected observation. Establish their
   composition laws and checked specializations in different dimensions. Include
   a correlated statistical case that detects unjustified multiplication of
   marginal means. Compare distinct geometric presentations as a separate test:
   changing dimension and changing presentation exercise different requirements.
   Choose the first concrete scene and observation before freezing interfaces.
2. **Visible 3D execution.** Produce images and a camera sequence for a small
   three-dimensional world. State the optical model, numerical assumptions and
   the boundary between proved contracts and external execution. A Euclidean
   scene can establish this path; it does not complete the orbifold milestone.
3. **A genuinely 3D orbifold scene.** Select and document the supported class and
   scene. Demonstrate camera motion and relevant representative changes, frame
   transport and isotropy behavior, with observation compatibility under the
   selected presentations. Retain appropriate witnesses rather than silently
   replacing the world with its orbit set. Existing disk cases can guide the
   work but cannot discharge this three-dimensional goal.
4. **Certified local reuse.** For a tractable response, prove that substitution
   by a cached approximation meets the selected observation bound throughout
   its admitted query region and through an explicit surrounding computation.
   Include a visibility or newly revealed information case that forces a larger
   bound or fresh evaluation. If retained data cannot certify the requested
   tolerance, reject reuse; include a case requiring fresh evaluation to satisfy
   the request. Cache dependencies must account for relevant scene,
   illumination, realization and camera changes. AD is one possible construction;
   exact transport or a conservative non-differentiable bound may be preferable.
5. **Measured optimization.** Measure concrete costs before choosing specialized
   spatial structures, 3D kernels or storage formats. Connect replacements to
   their semantic contracts, retain comparison examples and distinguish modeled
   costs from runtime measurements.

The next bounded implementation should address milestone 1 with an accompanying
plan for the first executable observation. Its acceptance evidence is a reusable
composition result consumed by contrasting clients, a dependence-sensitive
statistical example, a presentation-compatibility case, and a record of missing
capabilities. These tests may revise or reject the initial response interface.
They do not claim that simple layered composition handles interreflection or all
light transport. The selected construction must state what it excludes.

## Questions to settle through the work

- Which response information is sufficient for each composition, including
  feedback from multiple scattering? Associative layering alone does not answer
  that question.
- Which observation and error relation support the intended use? Screen-space
  displacement, image error and operator error need distinct connecting results.
- Which changes of presentation preserve the response, including attached frame
  and isotropy data? Endpoint agreement alone may omit needed transport data.
- Which query regions admit useful error bounds, and how are domain membership
  and numerical error established by an executable realization?
- Which statistical information remains coherent when the camera reveals new
  detail? Rendering accuracy relative to a chosen model does not bound the
  model's discrepancy from an unknown physical scene.

The chat's finite-distance formulas, hyperbolic-infinity calculation and external
rendering references remain research leads. Check their assumptions, derivations
and primary sources before building contracts on them. No particular treatment
of infinity, global boundary, mesh hierarchy or differentiation method is adopted
here.

At each milestone, reassess the interfaces against the retained clients and the
visible-rendering goal. Record the benefit, remaining assumptions and next scope
in #34 or a linked issue; preserve useful mathematics when revising a design.
