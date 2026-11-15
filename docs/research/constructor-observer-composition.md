# Constructor and observer extension of the vector client

Issue [#278](https://github.com/VladimirMarko/conaled/issues/278) connects the
observation-extension contract to the shared indexed composition theorem.
The [checked client](../../Examples/ConstructorObserverExtension.lean) extends
the existing finite-vector example with scalar shift and a sum observer.
The independent meaning remains a function `Fin n → Nat`.

## Contracts and local interactions

The original client builds vectors with nil, cons, and pointwise doubling;
it observes a head and requests a tail at decreasing lengths. Its complete
coordinate contract identifies two terms when their vector meanings agree at
every coordinate. An empty vector has no coordinate request. The enriched
coalgebra returns a pair: the original head (Unit at length zero, Nat otherwise)
and the sum of all remaining coordinates. Requests and their result lengths
are unchanged. The sum is defined independently by finite recursion on vectors.

The added constructor shifts every coordinate by a natural number. A positive
length has a `shift` node; at length zero the public helper returns the original
term because shifting an empty vector is the identity. `fold_shift` checks that
this helper has the intended meaning at every length.

All interactions have explicit local obligations:

| Constructor | Old head observation | New sum observation | Tail request |
|---|---|---|---|
| nil | Unit | 0 | No request exists |
| cons a | a | a + child sum | Original child |
| double | Twice child head, or Unit at zero | Twice child sum | Double child successor |
| shift a | Child head + a | Child sum + n × a | Shift child successor; at length one the resulting empty child is retained unchanged |

Here n in the shift sum equation is the vector's positive length. `total_double`
and `total_shift` prove the nontrivial sum equations against native functions.
`compatible` discharges the entire table, with one explicit parameter:
`ShiftSumLaw` is the obligation for the supplied new-constructor/new-observer
cell. It quantifies only over actual vectors at positive lengths. No composite
correctness result is assumed as a local condition.

## Reusing the native client and comparing extension orders

`embed` includes every original term without rewriting its leaves. `fold_embed`
proves equality of its independent vector meaning. `old_client` reuses the
existing public `Vectors.correct` theorem with the original term and coordinate;
its premises are unchanged. `embedded_client` additionally proves preservation
of every original coordinate through the enriched coalgebra after forgetting
the sum component. The direct native vector API remains usable.

`correct` uses the shared `Rule.fold_morphism` for arbitrary mixed finite terms
and every typed observation path. A term that inserts 7 and 11, shifts both by
3, then doubles them has head 20 and sum 48. After one tail request it has head
28 and sum 28. Both checked calculations use the general theorem.

Two construction orders can fill the table differently. Adding the constructor
first leaves its sum cell to the observer extension. Adding the observer first
leaves the same cell to the constructor extension. The checked completions use
`sum + n*a` and `n*a + sum`, respectively. The original constructors and sum
cells are already fixed; both completions must validate the remaining cross
cell against the same independent meaning. `old_cells` shows that merely
agreeing on old-constructor cells says nothing about this remaining condition.
`old_head_cells` also recovers the original rule's head interface directly.

The reusable [comparison theorem](../../SquareKit/ObservationComposition.lean)
compares any two rules compatible with the same algebra and native coalgebra.
It derives equality of finite observations through their two fold morphisms.
`order_comparison` instantiates it when each completion supplies `ShiftSumLaw`;
the selected completions discharge that law by reflexivity and addition
commutativity. Their syntax comparison is identity on the common named
signature. This is a comparison of two completed local tables, not a general
operation claiming that arbitrary extensions commute or that unrelated
signature presentations are definitionally equal.

## Accepted and rejected observations

`sum_square` connects the implemented sum observer to the independently defined
vector sum using the all-term theorem. `sum_compatible` then uses
`ObservationExtension.compatible_of_factor` to show that it respects the old
coordinate setoid. `enriched_iff` proves that adding this observer leaves exactly
the old equality. A checked `descend_mk` application supplies its value on the
old quotient.

Two failure cases keep different obligations separate:

- `incompatibleRule` leaves every old cell unchanged but returns the child sum
  for shift. On the one-element zero vector shifted by one, its required
  `Compatible.output` sum equation is 1 = 0. `failed_sum_law` and `incompatible`
  prove the failure. The mixed example still reports head 20 but gives sum 36,
  exposing the lost shift contribution.
- The proposed `constructors` observer counts syntax nodes. A plain leaf holding
  7 and a zero-shift node around it have identical vector meaning but counts
  0 and 1. `constructors_incompatible` rejects its old-equivalence law;
  `constructors_no_factor` rules out every map from the old quotient that could
  recover it, including noncomputable maps.

The second failure is not a contradiction in the original theory. Existing
coordinate theorems continue to have their original meaning and premises;
`old_client` and `embedded_client` remain valid. The structural observer can be
studied with a finer representation-sensitive equality, but cannot be installed
as an exact-valued observer of the old quotient. This distinction matches the
separate selected-witness descent boundary of #287; this experiment adds no
semantic types or claim about expansion of every model.

## Author obligations and scope

A direct client can implement shift and sum as ordinary vector functions and
prove their equations without any syntax wrapper. An author wanting shared
finite composition supplies the indexed signature, algebra, rule templates and
local table laws. The shared theorem then covers all mixtures and observation
paths; observation compatibility and quotient descent reuse the existing
`ObservationExtension` interface. There is additional encoding work but no
second induction over each mixed program or extension order.

The example has length-dependent head results and request targets, retained
without erasure. It has no ambiguous parse witnesses; no claim about preserving
selected parser witnesses follows from this vector result. It establishes
semantic preservation and a conditional comparison of extension orders, not
consistency, normalization, execution cost or productivity. Broader extension
interfaces and any dependent witness transport remain with
[#235](https://github.com/VladimirMarko/conaled/issues/235), coordinated with
#262 and the separately completed #287 assessment. Independent author effort
is assessed by #279 rather than inferred from this implementation.
