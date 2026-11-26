# Shared immutable lists: a persistence prerequisite

This is a bounded cross-cutting development for the
[PFDS reconstruction](pfds-reconstruction.md), grounded in the inspected
publisher excerpt, printed pages 7–11. It supplies a cell model needed to state
persistence and sharing precisely. It does not establish complete coverage of
Chapter 1 or 2, the search-tree material, lazy evaluation, or persistent
amortization. The subsequently available complete chapter and its additional
developments are tracked in [the Chapter 2 record](pfds-persistence.md).

## Representation and assumptions

[`SharedList.Basic`](../../Applications/Sequences/SharedList/Basic.lean) uses the
existing `Durability.Heap`, `Extends`, `put` and `extends_put` algebra. Their
reuse here requires no crash or durable-write assumption. A store has a heap
and a fresh-allocation frontier. A root is either null or a natural address;
each element cell contains a value and one tail root.

`Represents` relates a root to a finite ordered list. Its live links point to
strictly smaller addresses; this premise ensures finite traversals bounded by
the frontier. It does not constrain unrelated cells to be valid lists.
`Represents.unique` gives unique list observation, while `Represents.mono`
preserves every old valid root under heap extension. Equal lists need not have
equal roots, and neither root equality nor list equality models the logical
persistent identity of an abstract structure across versions.

`allocate` writes one fresh cell. `allocate_extends` reuses the existing heap
extension theorem, and `allocate_retains` applies it to an arbitrary old root,
including roots unrelated to the new tail. `allocate_represents` proves the
new list interpretation when the supplied tail is valid. Initialization through
`load` constructs valid instances for every finite input list; validity
premises are therefore usable, not an assumed impossible condition.

The model assumes a supply of fresh addresses. A finite-capacity target must
add a capacity/failure contract. Abstract heap access and frontier arithmetic
are not proved constant-time operations of Lean's runtime or of a device.
Payload representation, allocator metadata, reclamation and physical retention
are separate obligations. This is an ordinary Lean type/heap interpretation;
it does not transport list induction to another mathematical setting.

## Actual traversals and explicit failures

[`SharedList.Copy`](../../Applications/Sequences/SharedList/Copy.lean) follows
heap links for append and indexed replacement. It does not first decode a list
and rebuild it. The raw functions have fuel to totalize malformed inputs; the
public functions use the frontier. `Represents.length_le_next` proves that this
choice is sufficient for represented inputs. Raw operations reject encountered
missing cells and insufficient fuel at non-null roots; they are not validators
of an untraversed right root or tail. Correctness requires both input relations
where the theorem states them.

All measurements use the existing `Resources.Measured` pair. A structural
visit counts one reached list-cell/null case. Exhausted fuel at a non-null root
reports failure with no further visit. A null case still takes one visit, even
with zero fuel. Allocation is independently recorded by the exact change
in the frontier. These observations are an explicit model, not elapsed time.

| Operation and public result | Value contract | Sharing and resource contract |
| --- | --- | --- |
| `head_correct`, `tail_cons`, `tail_empty` | Optional head; empty tail fails, but a singleton has a successful null tail. | No new cells. `none` and `some none` have different meanings. |
| `appendRun_correct` | Valid roots for `xs` and `ys` produce a root for `xs ++ ys`. | All old cells are retained; exactly `xs.length` fresh cells; `xs.length + 1` visits; following the copied prefix reaches the exact original right root. |
| `updateRun_success` | For `i < xs.length`, the result represents `xs.set i x`. | All old cells are retained; exactly `i + 1` fresh cells and visits; roots reached after `i + 1` links are equal before and after the update. |
| `updateRun_failure` | For `xs.length ≤ i`, replacement fails. | It visits `xs.length + 1` cases and returns no new store. The result is not an out-of-range `List.set` no-op. |
| `suffixesRun_correct` | Returned roots represent `xs.tails` in order, including the empty suffix. | The same element heap is observed throughout; `n + 1` visits and root-list entries, exactly `n` distinct non-null element roots, and `2*n + 1` shared result cells. |

The suffix implementation in
[`SharedList.Suffixes`](../../Applications/Sequences/SharedList/Suffixes.lean)
returns references to the original tails. Its distinctness proof uses the
address-order invariant; every represented suffix still has an independent
standard `List.tails` observation. `suffixesRunFuel_chain` additionally proves
that the roots follow the actual tail fields. Its closure result underlies
`suffixesRun_reachable`, which identifies all reachable element cells with
the returned non-null roots, and `nonnull_nodup` proves that enumeration has no
duplicates. These results justify interpreting `sharedSpace` as reachable
element cells plus new root-list cells. Value observation and distinct roots
alone are insufficient: equal suffix values could be represented by different
unshared cells. The count excludes traversal stack space and payload size. Standard asymptotic
statements in [`Resources.SharedList`](../../Applications/Resources/SharedList.lean)
for the exact visit and shared-space functions use the existing
`Resources.isBigO_of_nat_bound`; they make the unit-cost model explicit.

## Composition and checked applications

[`SharedList.Observation`](../../Applications/Sequences/SharedList/Observation.lean)
provides ordinary `RelSquare` adapters. Optional results preserve the
success/failure distinction, without choosing a decoder for invalid heaps.
`appendHeadSquare` composes the append and head contracts; `updateRun_head_correct`
composes partial replacement with optional head observation. Such observation
can forget a distinction (for example, failure and a successful empty list both
have no head) without equating the underlying representations.

[`Examples.SharedList`](../../Examples/SharedList.lean) uses the public results:

- A new `[2,3]` version retains the original `[3]` root and both heads.
- Appending `[1,2]` and `[3,4]` retains both inputs, allocates two cells and
  reaches the original right root after two links. The composed head client
  returns `1`.
- Replacing index `1` in `[1,2,3]` yields `[1,9,3]`, retains the original and
  shares the tail after two links. Index `3` explicitly fails.
- The three-element suffix example returns four distinct roots observing all
  suffixes, with three shared element cells and seven result cells in total.
- Empty-tail failure, successful singleton-tail removal and insufficient fuel
  remain distinct checked cases.
- A counterexample has distinct roots with correct suffix values but an extra
  reachable cell omitted from the root list. It fails the closure condition,
  demonstrating why value correctness alone cannot justify the storage count.

The examples exercise universal theorems rather than proving only unrelated
literal evaluations. `SquareApplications` imports them, bringing all four
semantic modules into the normal integrated build and exhaustive audit; the
separate resource module is also imported by the public entrypoint.

## Statement review and remaining scope

The allocation and traversal results quantify over arbitrary payload types,
valid represented roots and independent old roots. They require no payload
equality or ordering. Allocation is globally fresh, so the extension result
preserves every previously occupied address. Value uniqueness does not assert
representation uniqueness. Fuel bounds use the represented chain length,
which is bounded by the frontier even when unrelated cells exist.

Append's sharing conclusion is equality of an actual reached root. Update's
domain check is strict, including index equal to length as a failure, and its
sharing conclusion retains the untouched suffix. The suffix theorem retains
order, duplicates among payloads and the null final suffix; distinct roots do
not imply distinct payload values. Complexity claims concern counted visits
and result cells. They assume neither a particular compiler optimization nor
safe repeated spending of potential across branches.

This prerequisite does not supply the book's full abstract-stack/custom-stack
correspondence, search trees, their exercises, reclamation, mutable sharing,
memoization or a target compiler refinement. Those remain explicit obligations
of the relevant chapter tickets. Checkpoint review and validation records own
acceptance status; this document describes the statements and their boundaries.
