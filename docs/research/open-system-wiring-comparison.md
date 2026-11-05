# Open-system wiring and native denotations

Issue [#300](https://github.com/VladimirMarko/conaled/issues/300), within
[#235](https://github.com/VladimirMarko/conaled/issues/235). This paper experiment
compares two decompositions of one independently specified vector field.
**Investigate** a wiring interface when an open-system client needs reusable
port substitution; **defer** a general library now. The native functions below
already express this experiment faithfully. The wiring account supplies a
composition theorem with explicit admissibility conditions, not an execution
engine or an unrestricted feedback solver.

Local inspection: `36e102788d74268710bfd94e4f29b147bafbb885`. This report adds
no Lean definitions or checked claims. Published results, the paper calculation,
and proposed implementation work are distinguished below. The source trail is
[D6 of the language comparison](external-language-comparison.md); its primary
wiring source was inspected before selecting the comparison theorem.

## Published theorem and applicability

The primary source is Vagner, Spivak and Lerman,
[*Algebras of Open Dynamical Systems on the Operad of Wiring Diagrams*,
arXiv:1408.1598v2](https://arxiv.org/html/1408.1598v2), specifically
Definitions 3.1, 3.8, 4.2 and Proposition 4.5 with its proof.
Boxes have finite manifold-typed input and output ports. A wiring is a typed
bijection `X_in + Y_out ≅ X_out + Y_in` with no passing wires:
external outputs connect to internal outputs. Thus it neither duplicates a wire
nor passes an external input straight to an external output.
A system has a state manifold, a smooth input-dependent tangent vector at that
state, and a smooth **state-only** output map. Proposition 4.5 makes these
systems a lax monoidal functor: product-state parallel composition and wiring
substitution respect diagram composition. These hypotheses permit feedback
through state readouts without solving an instantaneous input/output equation.
The proposition establishes composition of system descriptions; it does not
assert global existence of trajectories or an executable scheduler.

For this experiment all port and component state manifolds are `ℝ`. All maps
are linear, hence smooth; the usual tangent trivialization identifies a vector
at `s ∈ ℝⁿ` with its velocity in `ℝⁿ`. The tangent base point is always `s`.
We use no cartesian closed structure, function-space object, or global choice
of solutions. The applicability check includes the port bijection, rather than
assuming that every drawn network is an admissible diagram.

## Frozen independent meaning

The following is a constructed test system, not an empirical device model.
For state `s = (x,y,z)` and external input `u ∈ ℝ`, fix the independent meaning

```text
F((x,y,z),u) = (-x + u + z, -2*y + x, -3*z + y)
r(x,y,z)     = z
s₀          = (0,0,0).
```

The observable mathematical object is the entire vector field and readout,
with initial state retained if a trajectory is later requested. Equality of
`r` alone is insufficient. A trajectory interpretation would ask for
`d s(t)/dt = F(s(t),u(t))`, `s(0)=s₀`, and output `r(s(t))`. This report compares
fields at every state/input; it does not select a time domain, input regularity
class, ODE solution theorem, or numerical solver.

Freeze these component contracts before choosing a hierarchy:

| Component | State | Input ports | Output ports | Velocity | Readout |
| --- | --- | --- | --- | --- | --- |
| A | x | u, v | a | `-x + u + v` | `a=x` |
| B | y | a | b | `-2*y + a` | `b=y` |
| C | z | b | f, o | `-3*z + b` | `(f,o)=(z,z)` |

Port names are local to each box. Wire external `u` to `A.u`, `C.f` to `A.v`,
`A.a` to `B.a`, `B.b` to `C.b`, and `C.o` to external `r`.
There are four internal input ports and one external output, matched bijectively
to four internal output ports and one external input. Each port occurs once;
all types match; no external output receives an external input. Duplication is
in C's explicit smooth readout `z ↦ (z,z)`, not a split wire. Substituting these
contracts yields precisely `F` and `r` above.

The cycle A → B → C → A is permitted because each supplied readout depends
only on its component state. At a fixed joint state the supplied values are
already determined. No equation must be solved to find the instantaneous input
values. This says nothing about a discretization's update order.

## Two hierarchical decompositions

These calculations are paper derivations. Both use the same component contracts
and the same five outer/internal connections after flattening.

First compose A with B along `A.a → B.a`. The composite AB has state `(x,y)`,
inputs `(u,v)`, output `b=y`, and velocity

```text
F_AB((x,y),(u,v)) = (-x + u + v, -2*y + x).
```

Its boundary has two input ports and one output port. The local wiring matches
three internal inputs plus one boundary output against two internal outputs
plus two boundary inputs. Compose AB with C, supplying `C.f` to `AB.v`,
`AB.b` to `C.b`, external `u` to `AB.u`, and `C.o` to external `r`:

```text
F_1(((x,y),z),u) = ((-x + u + z, -2*y + x), -3*z + y)
r_1(((x,y),z))   = z.
```

Alternatively compose B with C along `B.b → C.b`. BC has state `(y,z)`, input
`a`, outputs `(f,o)=(z,z)`, and velocity

```text
F_BC((y,z),a) = (-2*y + a, -3*z + y).
```

Its local wiring matches two internal inputs plus two boundary outputs against
three internal outputs plus one boundary input. Compose A with BC, supplying
`A.a` to `BC.a`, `BC.f` to `A.v`, external `u` to `A.u`, and `BC.o` to `r`:

```text
F_2((x,(y,z)),u) = (-x + u + z, (-2*y + x, -3*z + y))
r_2((x,(y,z)))   = z.
```

The outer wiring in each case also has four demand and four supply ports, each
used once, with no passing wire. Define the state diffeomorphism
`h(((x,y),z)) = (x,(y,z))`. Its derivative rebrackets velocity coordinates.
The displayed formulas establish

```text
D h_s (F_1(s,u)) = F_2(h(s),u)
r_1(s) = r_2(h(s))
h(((0,0),0)) = (0,(0,0)).
```

Flattening either state space to `ℝ³` gives the independent `F` exactly.
This is equality of the full dynamics under a named coordinate isomorphism,
not merely equality of one output. Proposition 4.5 explains the reusable
substitution law behind the calculations. The calculations also expose the
coordinate bookkeeping that a concrete encoding must discharge.

## Native route and existing boundaries

A native representation can retain a state type, input type, output type,
velocity function and state readout. For this finite-dimensional example,
ordinary product functions implement the displayed formulas directly. Product
reassociation proves the comparison; a general operad implementation is not
needed to state it. A future Lean formalization should reuse Mathlib's real
vector spaces, smooth maps and derivatives for the tangent interpretation,
rather than introduce competing analysis foundations. No Mathlib theorem is
claimed checked by this report.

The local [initialized feedback module](../../Applications/Progress/Feedback.lean)
defines a different mathematical object: a total discrete step
`A × S → B × S` and initial state. Its `Solution` retains the entire state
recurrence and outputs; `existsUnique_solution` proves uniqueness by recursion.
Its `transport` requires an initial relation and a one-step relation preserving
both output and next state. These interfaces offer a useful comparison pattern,
but none turns the continuous field here into a chosen discrete step.

The [coupled feedback module](../../Applications/Progress/CoupledFeedback.lean)
proves `factorization` for a specified schedule: the left update reads the old
right state, then the right update reads the new left state. That is not the
simultaneous field substitution above. Even an Euler-style interpretation would
need a separately specified discretization and a comparison theorem; borrowing
its factorization by matching diagram shape would change the meaning.

Likewise, [guarded streams](modular-guarded-streams.md) derive solution transport
with a guarded coordinate discipline and target uniqueness. State-only smooth
readouts do not supply that discrete guardedness premise. These existing results
remain useful in their stated domains. This report does not reopen
[#285's higher-order comparison](higher-order-extensional-comparison.md) or build an FRP
runtime. It uses first-order ports with a fixed finite state space throughout.

For an exact native preservation square, keep both velocity and readout in the
specification, with the state relation induced by `h` and the tangent map
`D h`. A square observing only `r` loses the property being compared. Selected
state maps, initial states, port types and the full input quantification are
part of the contract; they cannot be erased during representation transfer.

## Cases that reject an overextended route

1. **Implicit fanout.** Replace C's two output ports by one output port, then
   connect it both to A and the exterior. The source's typed bijection fails:
   one supplier would be used twice. The frozen explicit duplicated readout
   repairs this particular example; it does not prove the wiring category
   supports arbitrary copying.
2. **Instantaneous feedthrough.** Allow a component with output `q=i+1` and
   connect that output to its own input. The required equation `i=i+1` has no
   real solution. This violates the state-only readout hypothesis. Thus the
   selected construction cannot be extended to arbitrary feedthrough feedback
   by invoking Proposition 4.5. The failure concerns the altered contract,
   not the permitted cycle in the frozen example.
3. **Erased dynamics.** Change A's feedback contribution from `+v` to `-v`.
   At state `(0,0,1)` and input `0`, the original field is `(1,0,-3)` and the
   changed field is `(-1,0,-3)`. Both readouts are `1`. A returned-value-only
   observer would accept this point while the specified field comparison
   rejects it. It does not preserve the system's independent meaning.

## Reusable laws, costs and ownership

The paper experiment supports reuse of typed port substitution, parallel
product-state composition, identity wiring and associative hierarchical
composition, with explicit coordinate isomorphisms. It does not establish
trajectory existence, uniqueness, stability, a causal stream interpreter,
finite-precision accuracy, bounded execution time or a hardware schedule.
Those require their own input regularity, numerical and timing contracts.
For example, proving an ODE trajectory comparison would first choose a solution
notion and establish suitable existence/uniqueness hypotheses; a numerical
client would additionally choose a step scheme and error criterion.

The implementation tradeoff is concrete. Native functions require two local
substitution calculations and one product reassociation for this example.
A reusable wiring library must encode finite typed ports, admissible bijections,
product-state bookkeeping, smooth tangent maps and readouts, and prove the
substitution laws once. It also needs rejection examples for inadmissible
wiring and feedthrough. No timing or proof-size measurements were made, and
no existing open-system client has been demonstrated here to need that cost.

| Decision | Scope and residual owner |
| --- | --- |
| Adopt | Retain full vector-field/readout meaning and explicit port and feedback hypotheses in future open-system comparisons. #235 owns this comparison criterion. |
| Investigate | When a client needs repeated hierarchical rewiring, #235 coordinates #27/#36 and the relevant numerical or hardware consumer to decide whether typed wiring substitution should become a library interface. This report supplies the first paper case, not that client's requirements. |
| Defer | General wiring/operad formalization, ODE solver integration and runtime implementation until such a client supplies its denotation and required operations. The requesting consumer owns the missing execution/analysis contract. |
| Reject | Arbitrary instantaneous feedback solvability and output-only substitutes for vector-field preservation under the present theorem. A consumer needing feedthrough must supply a different admissibility/solution theory. |

The result is a successful matched paper comparison for the restricted system,
with explicit failures outside its hypotheses. It creates no dependency on
cartesian closed structure, new kernel axioms or a universal syntax. Scheduling
priority remains separate from mathematical dependencies; no unrelated research
or implementation gate is advanced by this calculation.
