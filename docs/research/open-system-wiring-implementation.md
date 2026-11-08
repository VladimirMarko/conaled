# Checked scalar-port open-system wiring

Issue [#376](https://github.com/VladimirMarko/conaled/issues/376) implements the
bounded comparison proposed in [the wiring report](open-system-wiring-comparison.md).
The [library](../../Applications/OpenSystems/Wiring.lean) and
[checked cases](../../Examples/OpenSystemWiring.lean) retain both the vector field
and the state-only readout. They do not select a trajectory, time domain,
discretization, runtime schedule, or steady-state hiding operation.

## Source and inspected interfaces

The primary source is Vagner, Spivak and Lerman,
[*Algebras of Open Dynamical Systems on the Operad of Wiring Diagrams*,
arXiv:1408.1598v2](https://arxiv.org/html/1408.1598v2), Definitions 3.1, 3.8, 4.2
and Proposition 4.5. Its port bijection has domain `X_in + Y_out` and codomain
`X_out + Y_in`; external outputs cannot connect to external inputs. Its system
semantics combine a smooth field with a state-only smooth output. Composition
substitutes those outputs into component inputs. The published theorem concerns
a lax monoidal functor on manifold-typed ports. The present code establishes a
restricted construction directly; it does not import that theorem as a premise.

Inspection started at conaled `7e4b55480123ef55958104cd63d13d8c378cf430`, with
Lean 4.35.0 and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
`SquareKit.WireCorelation` supplies equality constraints and boundary behavior,
not vector fields. `Progress.Feedback` supplies initialized discrete steps;
`Progress.CoupledFeedback` selects an update order. Neither contract is the
simultaneous field in this experiment. `Applications.AD.DMap.ofSmooth` derives
a derivative from Mathlib smoothness; the wiring fragment uses those same
Mathlib analytic foundations directly, without requiring an AD adapter.

## Contract and checked derivation

All ports in this fragment have the fixed type `ℝ`. Their finite index types
record distinct ports; this is the constant-real specialization of typed ports,
not an implementation of arbitrary manifold-valued type assignments. State
spaces in the cases are products of `ℝ`. The generic smoothness lemmas work in
normed real vector spaces, with velocity in the same space as the state.

`Routing` holds local input/output selections. Its output map targets internal
outputs, so passing wires cannot be represented. `Admissible` requires the
combined map to be bijective, and `Wiring` bundles that proof with finite ports.
`equivalence` converts the proof to a Mathlib `Equiv`. The unbundled operations
also make sense for nonbijective routing; that larger operational domain does
not admit those maps as source wiring diagrams. `comp_admissible` proves closure
from the two component bijections. `Wiring.comp` uses that theorem.

`System` holds a velocity function and a state-only output function. `parallel`
uses product states and disjoint input/output ports. `wire` substitutes selected
suppliers. `supply_comp` and `read_comp` prove local substitution laws;
`wire_comp` derives equality of the complete systems from them. Identity leaves
both functions unchanged. `Smooth.wire` and `Smooth.parallel` derive analytic
closure from component smoothness, using Mathlib composition, products and
finite function spaces. No field of a record assumes the desired global
preservation theorem.

The report's A, B and C remain separate definitions. C has two ports carrying
the same state value: duplication occurs in its readout. The four local
hierarchical diagrams and the flat five-wire diagram carry checked bijections.
`left_field`, `right_native`, `hierarchy`, `left_native`, and `flatten_left`
connect local substitution to the independently frozen native functions

```text
F((x,y,z),u) = (-x + u + z, -2*y + x, -3*z + y)
r(x,y,z) = z.
```

`coordinates` is Mathlib's real linear isometric product reassociation.
`coordinate_derivative` proves its actual Fréchet derivative;
`dynamics_conjugacy` applies that derivative to the velocity.
`hierarchy_reverse` proves the reverse comparison using its inverse, and
`initial_coordinates` retains the zero initialization. The comparison therefore
preserves and reflects the complete field/readout across these coordinates;
it is not an output-only or selected-state test. Quantification covers every
state and input valuation. `hierarchies_smooth` reuses the generic closure laws.

The second case swaps AB's boundary inputs and changes the closing diagram to
match. `swapped_composition` invokes `wire_comp`; its composite certificate
uses `comp_admissible`. `swapped_field` checks the exposed port order before
closing, and `second_hierarchy` checks that the compensated wiring retains both
functions. This case changes an actual finite permutation, not just a name.

Negative controls reject implicit fanout by injectivity and reject `q=i+1`
as a state-only output. Its feedback equation has no real solution.
`readout_is_insufficient` retains the report's state `(0,0,1)`: changing the
feedback sign alters velocity while the output remains one. These controls
prevent importing arbitrary feedthrough solvability or output-only correctness.

## Reuse and recurring obligations

| Item | Reused construction or checked law | Remaining per-client work |
| --- | --- | --- |
| Finite bijection and type correctness | Mathlib `Sum`, `Fin`, `Fintype`, `Equiv`; `Wiring` fixes the scalar type | Choose port indices, write selections, establish bijectivity for new diagrams |
| Admissible composition | `Routing.comp_admissible`, `Wiring.comp` | Supply two accepted diagrams; no new composition proof |
| Full system substitution | `supply_comp`, `read_comp`, `System.wire_comp`, `wire_identity` | Define component meanings and boundary diagrams |
| Product state and smoothness | `System.parallel`, `Smooth.parallel`, `Smooth.wire`; Mathlib `ContDiff` | Prove primitive field/readout smoothness |
| Coordinate change | Mathlib `LinearIsometryEquiv.prodAssoc` and continuous-linear-map derivative | State the intended state relation; establish its derivative for other coordinates |
| This native comparison | `left_field`, `right_native`, `hierarchy`, `left_native` | New independent fields still require a comparison calculation |
| Second wiring | `swapped_composition` reuses the composition law; `second_hierarchy` checks the closing | Changed port boundaries require new wiring data and certificates |
| Existing conaled semantics | Native functions, equality-wire and discrete-feedback clients retained | No conversion to the compiler engine or discrete runtime is supplied |

The setup includes routing certificates, semantic operations, smoothness closure,
and the admissible composition proof. Native functions need none of that setup
to state this particular field. Both routes still need independent component
contracts and coordinate bookkeeping. No timing study or controlled author trial
was performed; source length is not evidence of productivity. The reusable gain
shown here is the invocation of named laws in the second wiring and smoothness
proofs, not a measured reduction in effort.

## Statement review and next obligations

Statement review checked each declaration family against the report and source:
port bijectivity includes both injectivity and surjectivity; output selections
cannot pass external inputs; composition order feeds the outer boundary into
the inner diagram; all readouts are state-only; smoothness covers the jointly
input-dependent field and the whole output function. Product reassociation acts
on velocities as its actual derivative. Every system comparison retains field
and readout, and the zero initial state is checked separately. The examples
establish satisfiable hypotheses, while the fanout and feedthrough cases expose
failed premises. No new axiom or admission is introduced.

The first checked obligations were the report's component substitutions and
native field equality. Missing connections were the local routing laws,
product-state construction and coordinate derivative, not a changed target
field. The retained cases consume those public operations and laws. Compilation
and the exhaustive project audit are recorded for the immutable candidate by
the orchestration handoff; this document does not claim unrun checks.

Adopt this bounded experimental interface for the checked cases. Defer a general
operad and heterogeneous manifold ports: this example does not demonstrate a
consumer need for either. For #235/#36, the next obligation is a second client
whose nonconstant port types or nonlinear coordinate maps require extending this
interface, with its independent denotation retained. For a numerical or hardware
consumer under #27, first specify its discretization or schedule and the exact
comparison to this simultaneous field. An ODE client must select an input
regularity class and solution notion before trajectory transport is meaningful.
These are distinct contracts; no solver, stability, approximation, scheduling,
or steady-state claim follows here.

One remaining shared blind spot is scaling of explicit port certificates and
coordinate bookkeeping in larger networks. The present finite cases establish
correctness and concrete law reuse, not that the representation remains usable
at that scale. This is evidence to collect with a client, not an architectural
blocker for the bounded comparison. #107, #108 and #260 are unaffected.
