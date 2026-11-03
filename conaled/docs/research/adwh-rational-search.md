# Static rational-cost search (#159)

`Applications.Search.RationalCost` interprets finite rational edge costs through
existing Nat search. Its independent graph uses `WithTop ℚ`: finite entries are
traversable edges and infinity is blocked. Rational walks accumulate finite
costs independently of the encoding or search implementation. Goals retain the
same vertices and Boolean predicate throughout transport.

`Scale` contains a positive natural denominator. `encode` takes the natural
floor after multiplication; `Fits` requires that this operation is exact.
`fits_of_integral` discharges that requirement from an explicit natural
multiple. `decode` divides by the same denominator. No rounding-error or
approximate-shortest-path claim is made. A nonintegral scaled cost is rejected
by the laws, even though the raw encoding function is total.

Operations, exactness laws and instance finiteness are separate. `Compatible`
requires exact encoding of finite edges and heuristic values. `FiniteCosts`
certifies an explicit finite list containing those values and strictly positive
finite edges, and supplies `Compatible`. The transport theorems need only the
exactness laws; they also work for exactly representable zero-cost edges.
The scale is supplied and checked, rather than synthesized by a denominator
search. The examples choose 6 and 4 from their displayed cost collections.

`adjacency` filters infinity entries without sorting. `adjacency_order` proves
that retained vertex occurrences form a sublist of the original successor
list. `edge_iff`, `walk_iff` and `walk_scaled` give both directions, including
`Nat cost = rational cost * denominator`. `optimistic_iff`, `monotonic_iff`
and `distance_iff` transport the corresponding mathematical contracts.
A distance is minimal over all rational walks to any goal, including cyclic
walks; it is not defined as the search's answer. Completed failure means that
no finite-cost goal walk exists. A route containing infinity is not an
alternative with a very large finite cost.

`distanceSquare` composes `Search.Heuristic.distanceSquare` with
`decodeDistance` using `Relational.compose`. Thus the actual search, independent
Nat optimum, and rational minimum-distance observation share the existing
consumer. `distanceSquare_apply` exposes its executable observation, while
`distanceSquare_correct` proves its independent specification. Budget
exhaustion remains outside `Completed`; it cannot be mistaken for an
unreachable goal. `completed_exists` reuses Nat termination with an explicitly
chosen finite vertex list and closure only for traversable edges from that
list. Blocked destinations need not belong to the list. Graph/heuristic
exactness laws describe the supplied graph globally; a finite subtype can
restrict the graph to a chosen valid domain.

## Heuristics, ties and checked cases

Exact Nat encoding requires nonnegative heuristic values. Signed rational
heuristics are supported by the explicit normalization `max 0 h`.
`normalize_optimistic` and `normalize_monotonic` preserve the respective
premises when edge costs are nonnegative. This normalization may change priority
ordering and path selection. For already nonnegative, exactly encoded
heuristics, `priority_le_iff` and `priority_eq_iff` preserve cost-plus-heuristic
comparisons and ties. Queue implementations still choose among equal
priorities according to their own policies; no identical-selected-path theorem
is asserted.

`Examples.RationalSearch` retains these checked uses:

- `diamond`: costs 1/2, 1/3 and 2/3, scale 6, nonzero optimistic monotone
  heuristic. Both two-edge alternatives have rational cost 1. A direct
  infinity edge is omitted. `diamond_distance` uses the composed consumer;
  the two walk proofs, scaled empty walk, finite-domain termination and
  priority-tie proof use the public transports.
- `cycle`: costs 3/4 and 1/4, scale 4, zero heuristic. Vertex 1 has minimum
  cost 3/4; vertex 2 is unreachable behind an infinity entry. Both conclusions
  use the composed consumer. The terminating domain is `[0,1]`, deliberately
  excluding the blocked destination 2.
- The constant signed heuristic -1/3 is optimistic and monotone on `cycle`.
  Its normalization satisfies the rational and encoded Nat premises via the
  public normalization and scaling results.
- `fifth_not_supported` proves that adding a cost 1/5 invalidates scale 4.

The first development obligation was to connect the diamond's independently
calculated rational distance 1 to the existing Nat consumer. The original
interfaces only returned Nat costs. The missing connection led to separate
rational walks, exact scaling laws and the decoding square. The cycle and
blocked-destination examples then checked failure and finite closure; signed
heuristics exposed the need for normalization rather than silently requiring
all input heuristics to be nonnegative.

Statement review covered all new claims. The walk relation uses only finite
entries from the original graph. Empty walks cost zero. Scaling preserves
endpoints, so goals need no additional correspondence premise. Every
finite-cost source walk has a target witness, and every target walk decodes
to a source walk; cost minimization therefore quantifies over the same
alternatives. Exactness is checked per edge and heuristic, not assumed for
an arbitrary desired optimum. Positive denominator assumptions justify order
reflection and division. Finite-domain closure and positivity are not imposed
on unrelated vertices or blocked edges by the termination theorem. Two
satisfiable concrete `FiniteCosts` certificates prevent vacuous use of the
encoding laws. Kernel reduction checks computed outputs after application of
the public consumer theorem; it does not replace that theorem.

## Provenance and update boundary

The [source ledger](adwh-rational-search-provenance.tsv) records selected
contracts from `adwh-checkpoint-233`, member hashes and declaration names.
Those Nat contracts were already reconstructed under #155 and are reused
unchanged. Rational walks, `WithTop` filtering, exact scale transport,
normalization and the decoding consumer are new local mathematics. This
extension does not claim another source module wholly reconstructed. The
remaining source declarations and migration scope stay in the
[static-search record](adwh-static-search.md).

[#111](https://github.com/VladimirMarko/conaled/issues/111) owns retained-state
repair. Its patches must preserve the finite domain and predecessor/successor
agreement, positivity of finite edges, and exact encoding of every new edge
and normalized heuristic value. A fixed scale is valid only while those
invariants hold. Changing the scale needs a separate transport of retained
`g`/`rhs` values, infinity markers, queue priorities/keys and stale entries,
plus preservation of local consistency and the repair algorithm's invariants.
A static rescaling theorem establishes none of that state correspondence.
Heuristic optimism or monotonicity must be re-established for the patched
graph; old validity does not survive an arbitrary cost decrease. Repair
termination must retain a justified well-founded measure. Rational order
alone admits infinite descending sequences. Initialization, patch processing,
queue repair and improvement/resource bounds remain #111/#113 work.

Targeted validation uses `direnv exec . lake build Examples.RationalSearch`.
The public entrypoint imports the examples for the fresh full build and
exhaustive audit. Independent reviews and full integration checks are the
coordinating session's acceptance gates.
