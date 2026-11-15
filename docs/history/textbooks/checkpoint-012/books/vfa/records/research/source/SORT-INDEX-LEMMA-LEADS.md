# Sort optional-index API leads

Prospective source reconnaissance only, recorded 2026-11-04. No new Lean proof
was written or compiled. Use after Preface/Perm acceptance, within local #1003.
Candidate c988f183887896c00b09aaff9077a6ea7fb8d68f and pinned Lean4.35.0 / Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679. The independent advisor inspected all
APIs below; root additionally read the exact lookup declarations and insertion
membership theorem in their pinned primary sources.

## Old Nat-index witnesses without payload equality decisions

`Init/Data/List/Lemmas.lean` supplies, for arbitrary payload type:

- `List.getElem?_of_mem (h : a ∈ l) : ∃ i : Nat, l[i]? = some a`.
- `List.mem_of_getElem? (e : l[i]? = some a) : a ∈ l`.
- `List.mem_iff_getElem? : a ∈ l ↔ ∃ i : Nat, l[i]? = some a`.

No DecidableEq or BEq payload assumption is required. Combine these with
`List.mem_orderedInsert (r) : a ∈ orderedInsert r b l ↔ a = b ∨ a ∈ l`
in Mathlib/Data/List/Sort.lean, whose relation assumptions here are only the
operation's DecidableRel. This is enough to expose the lookup-origin obligation
without using any sortedness theorem. The direct source-to-orderedInsert bridge
must first be proved by the future chapter implementation.

## Shift successful optional lookups through cons

The same core file has:

- `List.getElem?_cons_zero : (a :: l)[0]? = some a` (rfl; not tagged simp).
- `List.getElem?_cons_succ : (a :: l)[i + 1]? = l[i]?` (simp; rfl).
- `List.getElem?_nil : ([] : List α)[i]? = none` (simp; rfl).

Retain the some premises; no auxiliary bounded/default lookup replacement is
needed for these positional cases. Init/Data/Nat/Basic.lean supplies
`Nat.succ_lt_succ` and `Nat.succ_lt_succ_iff`; Init/Prelude.lean supplies
`Nat.zero_lt_succ` / `Nat.succ_pos` for head-versus-tail comparisons.

## False insertion comparison

For a generic total relation, Init/Core.lean's class field is
`Std.Total.total [Std.Total r] : ∀ a b, r a b ∨ r b a`.
Mathlib/Order/Defs/Unbundled.lean exposes `total_of r a b` with that conclusion.
`Or.resolve_left` can eliminate the false forward relation. Neither this step
nor the lookup APIs needs antisymmetry or decidable payload equality.
Transitivity remains a separate requirement when composing comparisons in the
stopping branch. Init/Data/Nat/Basic.lean's `Nat.le_of_not_le` is the direct Nat
specialization, with premise not(b≤a) and conclusion a≤b.

These are source/API leads, not the independent optional proof itself. Its
actual insertion induction must remain positional as required in §6 of
specs/1003-Sort.md. Do not transport insertion sortedness through Pairwise,
IsChain or the staged sortedness equivalences to discharge that method-specific
exercise. No chapter or source claim is accepted by this note.
