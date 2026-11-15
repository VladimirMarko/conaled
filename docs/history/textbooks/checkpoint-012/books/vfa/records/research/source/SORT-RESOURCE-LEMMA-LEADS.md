# Sort resource lemma leads

**Prospective, source-only, uncompiled. Use only after local #1002 Perm is
accepted.** This is bounded reconnaissance for `specs/1003-Sort.md`, not Sort
implementation, validation, or acceptance. No new Lean proof was elaborated.

## Inspected identities (2026-11-04)

- conaled: `c988f183887896c00b09aaff9077a6ea7fb8d68f`.
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`, matching the
  conaled `lake-manifest.json` pin (`v4.35.0`).
- Lean toolchain: `leanprover/lean4:v4.35.0`.
- `Mathlib/Data/List/Sort.lean` SHA-256:
  `bc2fe8a7888a1298dc605ce769915c7bd5cefcb5db7de9cad5215d898d21abd9`.

Paths below identify primary sources at those pins. The inspected Mathlib
checkout is `vfa-validation/.lake/packages/mathlib` under the recovery root;
the active validation checkout links to it. Core `Init/...` files were read
under the installed toolchain's `src/lean`. Project paths are relative to
`conaled`. Recheck identities when implementation becomes authorized.

## Range, reverse, and membership

`Init/Data/List/Range.lean`, namespace `List`:

- `range_succ {n : Nat} : range (succ n) = range n ++ [n]`.
- `length_range {n : Nat} : (range n).length = n`.

`Init/Data/List/Lemmas.lean`, namespace `List`:

- `reverse_append {as bs : List α} : (as ++ bs).reverse = bs.reverse ++ as.reverse`.
- `reverse_singleton {a : α} : [a].reverse = [a]`.
- `length_reverse {as : List α} : as.reverse.length = as.length`.
- `mem_reverse {x : α} {as : List α} : x ∈ reverse as ↔ x ∈ as`.

`Init/Data/List/Nat/Range.lean`:

- `List.mem_range {m n : Nat} : m ∈ range n ↔ m < n`.

These give the descending-family step
`(range (n + 1)).reverse = n :: (range n).reverse`, its length, and strict
membership bounds. The step is a prospective derivation, not a checked lemma.

## Insertion after every old element

`Mathlib/Data/List/Sort.lean` has explicit `r : α → α → Prop` and
`[DecidableRel r]`. Its recurrence is exactly the planned source adapter:

- `List.orderedInsert_nil (a : α) : [].orderedInsert r a = [a]`.
- `List.orderedInsert_of_not_le {a b : α} (l : List α) (h : ¬ r a b) :
  orderedInsert r a (b :: l) = b :: orderedInsert r a l`.
- `List.insertionSort_cons (a : α) (l : List α) :
  (a :: l).insertionSort r = orderedInsert r a (insertionSort r l)`.
- `List.length_insertionSort (l : List α) :
  (insertionSort r l).length = l.length`.

Prospective helper: under `∀ b ∈ xs, ¬ r a b`, prove that insertion gives
`xs ++ [a]` by list induction using the nil and false-cons equations above.
No sortedness, transitivity, or totality is required. For Nat `≤`, strict
`b < a` supplies the false branch through `Nat.not_le_of_gt`; equality would
stop insertion early. That theorem is in `Init/Data/Nat/Basic.lean`:
`Nat.not_le_of_gt {n m : Nat} (h : n > m) : ¬ n ≤ m`.

A value-only alternative uses `List.orderedInsert_eq_take_drop` in the same
Sort file and `List.takeWhile_eq_self_iff` / `List.dropWhile_eq_nil_iff` in
`Mathlib/Data/List/TakeWhile.lean`. Direct induction is better aligned with
proving that the measured recurrence performs exactly `xs.length` comparisons.

## Triangular arithmetic

`Mathlib/Data/Nat/Choose/Basic.lean` provides the exact successor identity:

`Nat.triangle_succ (n : ℕ) :
  (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n`.

It includes the zero boundary and avoids rediscovering truncated-subtraction
and division algebra.

For bounds, `Init/Data/Nat/Basic.lean` provides
`Nat.add_le_add {a b c d : Nat} (h₁ : a ≤ b) (h₂ : c ≤ d) : a + c ≤ b + d`.
`Init/Data/Nat/Div/Basic.lean` provides
`Nat.le_div_iff_mul_le (k0 : 0 < k) : x ≤ y / k ↔ x * k ≤ y`.
At `k = 2`, this converts to the permitted division-free bound after commuting
multiplication. No parity argument is needed for this inequality conversion.

## Prospective proof dependencies

1. Instrument the actual source recursion. Prove insertion erasure, comparison
   count at most input length, and exact input-length count when all tests fail.
   The latter induction also gives the append-value helper above.
2. For arbitrary sorting input, use tail-first sequencing, insertion's bound,
   erasure and `length_insertionSort`. Combine inequalities with `Nat.add_le_add`
   and close the length-successor step with `Nat.triangle_succ`.
3. For descending ranges, induct on size using the reverse-range step. The
   sorted tail is `range n`; `mem_range` forces every insertion test for `n`
   to fail. The output is `range n ++ [n] = range (n + 1)`.
4. The same witness induction adds exactly `n` comparisons. Apply
   `Nat.triangle_succ` for exact triangular cost.

Reuse `Applications/Resources/Measured.lean` (`Measured`, `bind_value`,
`bind_erases`) for the value seam. Cost facts must still follow from the
instrumented recurrence; value equality alone proves no cost equality.

## Additional prospective literal-cons identity

During checkpoint057 recovery, root identified a useful algebraic consequence
of the already specified literal-cons model. This is planning only, uncompiled,
and must not be credited before #1003 implements and proves its actual measured
recurrence. It changes no chapter ordering or current candidate.

With nil insertion charged (0 comparisons, 1 cons), a stopping cons charged
(1 comparison, 2 cons), and a recursive cons charged (1 comparison, 1 cons)
plus the tail result, the proposed identity is:

- literal insertion cons requests = insertion comparisons + 1;
- literal sort cons requests = sort comparisons + input length.

The insertion induction has an exact base and stopping case. In the recursive
case both coordinates gain one, preserving their difference. The sort induction
adds one insertion to the measured tail, so the differences add to list length.
No totality, transitivity or payload equality decision is needed for this
accounting identity; a decidable relation suffices to run the recurrence.

This could derive a literal-cons bound from the separately proved comparison
bound, and connect the four-comparison/five-cons source example to the generic
model. It is not an identity for a suffix-reusing allocation model, a count of
nil constructors, an input-allocation count, or a statement about physical heap
allocation. Value erasure and the actual cost recurrence still need independent
Lean proofs. The intended public API should expose only useful results after
those proofs and connected examples have been checked.
