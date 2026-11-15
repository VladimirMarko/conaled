# Local #10013: cross-cutting shared persistence foundation

Version 2 (raw traversal failures clarified; no validator requirement). Base: `cbb1e27d18c69ce2e0c35ef1cb492483b5ca0833`.
Parent: full user task in `REQUEST.md`; user explicitly permits cross-cutting work.

Chapter 1 and Chapter 2 source gates remain open. This prerequisite supplies
shared immutable-cell reasoning required by the inspected lists material and
later persistent data-structure work. It does not accept or skip a chapter.

## Expected checked cases and intended contracts

1. Allocate a cell for value 3, then allocate value 2 pointing to it. Reading
   the old root must still yield [3], and the new root [2,3]. The frontier grows
   by two. This must use a generic old-root-preservation theorem, not merely
   reduction of the chosen example.
2. Build [1,2] and [3,4], append their roots, and observe [1,2,3,4]. Both inputs
   remain valid. Following exactly two links from the result must reach the
   original [3,4] root, and exactly two cells must be allocated by append.
3. Update index 1 of [1,2,3] with 9. Observe [1,9,3] and the unchanged original.
   Exactly two new cells are allocated; the tail root after two links is shared.
   An index equal to length fails, and failure must not be disguised as List.set's
   out-of-range no-op. Empty head and tail fail, while a singleton has a successful
   empty tail (`some none`).
4. Enumerate suffix roots of [1,2,3]. Their observations must be
   [[1,2,3],[2,3],[3],[]], ending in the null root. The operation retains the same
   element heap, uses one step per visited suffix and creates length+1 root-list
   entries. Distinguish this shared representation from unfolded nested lists.

The initial gap is the absent explicit root/cell model and public correctness
theorems connecting these cases. Existing append/list-value lemmas do not
discharge pointer equality or physical/allocation-model obligations. No fabricated
syntax failure is used as mathematical evidence.

## Implementation and acceptance

Reuse `Durability.Heap`, `Extends`, `put`, `extends_put` and `Resources.Measured`.
Keep fresh allocation, validity and list observation separate. Use total raw
operations with explicit failure for insufficient fuel at non-null roots and
encountered missing cells, without requiring validation of untraversed roots; prove that
the actual public fuel choice succeeds on represented finite inputs. Correctness
must connect actual root traversals, not a decode/re-encode shortcut.

State abstract-memory/resource assumptions; no Lean runtime, reclamation,
arbitrary branching amortization, or crash-durability claim. Preserve the existing
public module entrypoint and exhaustive axiom audit. Every new claim requires
statement review and connected uses. Isolated exact candidate validation and
both independent review axes are required for this prerequisite's acceptance.
