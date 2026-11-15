# Shared table-observation preparation

Status: bounded cross-cutting draft, outside the integrated library. No Maps,
SearchTree, ADT, Redblack or Trie chapter is declared implemented or accepted.
Prepared under the main task's explicit cross-cutting exception, 2026-11-02.

## Source evidence and scope

Read against the pinned VFA 2.1 source inventory:

- `Maps.v`: `total_map`, `t_empty`, `t_update`, the six total-update laws,
  `examplemap`, and partial maps with `None` versus `Some v`.
- `ADT.v`, `Table` (lines 50–87): empty/default, get-after-same-write,
  get-after-distinct-write. `FunTable` and the `ListsTable` exercise provide
  the two simple realizations used by this preparation.
- `ADT.v`, `ETable` (lines 375–414): `rep_ok`, explicit `bound`, and
  invariant-dependent elements soundness/completeness. Its failed first
  attempt demonstrates why a representation invariant cannot be erased from
  the elements specification.
- `ADT.v`, `ETableAbs` (lines 806–847): `Abs : table -> partial_map V`,
  get and bound consistency, update refinement and elements abstraction.
- `SearchTree.v`, `map_of_list`/`find`/`map_bound` (lines 986–1020): lists
  are interpreted with first-binding precedence; partial observations expose
  `Option`, while `find` uses the caller-supplied default.
- `Trie.v`: the trie table stores a default and its abstraction is a *total*
  map. The chapter does not thereby supply explicit-binding enumeration.

No tree, trie, balancing, enumeration, or extraction algorithm was prototyped.
The material here does not discharge all source declarations in any chapter.

## Existing interfaces inspected

`Applications/Sequences/AbstractFIFO.lean` keeps operations separate from
simulation laws and composes ordinary clients through `RelSquare`.
`Applications/Dijkstra/Store.lean` supplies a bounded Vector realization and
`lookup_write`; it is not a generic finite-binding map.
`SquareKit/ListFusion.lean` supplies `foldl_reachable` and `foldr_reachable` for
future batch clients, so a new generic word executor is unnecessary.

At the time of the initial draft, the main checkout had no cached
`SquareKit.ListFusion` module. This preparation was restricted to focused
checking without building project dependencies, so it used cached Mathlib
function/list basics and a bounded two-write client. A later authorized
resource build supplied the ListFusion module. Any later arbitrary
update-history client should reuse ListFusion; this preparation does not
duplicate its fold induction.

## Design and preserved distinctions

`TableObservations.lean` provides operation-only `Ops`, separate `Laws`, and
the ordinary pointwise `ObservedEq` relation. These are a small prototype,
not a new container hierarchy. `Valid` is an explicit argument to the laws;
empty and set preserve it. The function and association-list instances need
no representation restriction (`Valid := True`). Future trees can supply their
actual invariant without imposing tree constructors on clients. Source
`Table` itself has unconditional laws, recovered by the `True` instance.

The generic key parameter does not itself transport Trie operations between
positive and natural keys. That chapter must establish its actual conversion
bijection. Mathlib's `Function.update_comp_eq_of_injective` is an existing
reindexing law to reuse once the relevant injectivity hypothesis is proved;
this draft assumes or claims no positive/natural conversion theorem.

The function instance uses existing `Function.update`. The association-list
instance prepends a binding and uses first-match lookup, retaining duplicates
as shadowed entries. `Laws.observe_set` identifies its *total observation*
with `Function.update`; `Laws.set_observed` and `twoWrites_equivalent` prove
that one ordinary client works with both representations. No equality of raw
list and function carriers is claimed. Key ordering and value equality are
unnecessary; executable updates/lookups require only decidable key equality.

`withDefault` is explicitly a forgetful operation from partial observations.
It preserves setting a key to `Some v`, but cannot recover whether a default
value was explicitly stored. `binding_iff` shows that a separate bound bit plus
the total lookup value does recover a *particular* optional binding. The checked
false/default example and universal noninjectivity theorem prevent treating
total observational equality as equality of partial maps.

Raw shadowing-list membership cannot implement ETable's elements specification:
an old shadowed `(key,value)` pair can remain in the raw list even when get
returns a newer value. The draft retains a checked counterexample. A future
ETable list adapter needs canonicalization or an invariant/removal operation;
no elements field or law was added here. Likewise arbitrary functions need not
have finite support or enumerable keys, so enumeration cannot be derived from
the total-table laws.

## Example-driven development and statement review

The starting obligation was a missing connection from the same two-write/get
client to both actual realizations, not a claim that concrete values were
unprovable by reduction. Expectations were fixed independently from the source
contract: the later same-key write wins; unrelated keys retain the default;
Boolean keys need no numeric ordering; explicit false and absence both return
false but have different bound observations; a shadowed raw list member is not
the current binding. Checked cases consume the public client/refinement results
where those results are the intended connection.

| Claims | Statement review |
| --- | --- |
| `Laws.observe_set` | Equality of lookup functions for every query, under the input invariant. Uses `Function.update`; query/write key direction was checked explicitly. |
| `Laws.empty_observed`, `set_observed` | Both sides use the same default and key/value types, with their own invariant evidence. Set preserves observation, not state shape. No injective decoder assumption. |
| `twoWrites_equivalent` | Writes execute in displayed order. Each side's intermediate validity is established using its law, rather than assumed at the conclusion. |
| `twoWrites_latest`, `twoWrites_first`, `twoWrites_other` | Latest key returns latest value even when both write keys coincide. The first write is retained when the second key differs. Other-key result requires the query differ from *both* writes. The exact Boolean `Maps.examplemap` observations at 0, 1, 2 and 3 instantiate all three laws. |
| `functionLaws`, `associationLaws` | Both `True` invariants are inhabited and preserved. All three source Table observation laws hold for every represented state, including duplicate list keys. |
| `withDefault_update`, `lookup_cons_update` | Optional insertion uses `Some v`, retaining explicit binding; the default appears only at the observation boundary. |
| `binding_iff` | The bound bit is required even when the observed value equals the default. The statement makes no finite-support or enumeration claim. |
| `forget_default_not_injective` | Requires an actual key and default value, constructs distinct partial functions, and proves equality only after forgetting absence. No vacuous empty-key-domain claim. |

Standard total-map algebra should be reused directly from
`Mathlib.Logic.Function.Basic`: `Function.update_self`, `update_of_ne`,
`update_eq_self`, `update_idem`, and `update_comm`. This draft does not add
renamed copies solely to restate Mathlib.

## Validation and integration boundary

Only focused `lake env lean` checking is authorized for this preparation; use
the pinned environment commands in `../../environment.md` with
`LEAN_NUM_THREADS=1`. No `lake build`, project cache write, chapter acceptance,
independent chapter review, or integrated proof-audit claim is made here.
The final focused-check outcome is recorded in `validation.txt`.

Root may select this seam for integration at the appropriate chapter gate.
Names and placement remain provisional; a source-to-Lean chapter map and full
candidate build/audit/review are still required at that point.
