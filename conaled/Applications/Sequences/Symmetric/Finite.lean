import Applications.Sequences.Symmetric.Prefixes

/-! Finite representation classification, offline prefixes and indexed fold observations.
Source provenance and statement review: `docs/research/adwh-symmetric-lists.md`. -/

namespace Sequences.Symmetric
universe u v
variable {α : Type u} {β : Type v}

theorem representation_front (s : SymList α) : (fromSL s).take s.1.length = s.1 := by
  simp [fromSL]

theorem representation_back (s : SymList α) :
    ((fromSL s).drop s.1.length).reverse = s.2 := by
  simp [fromSL]

/-- All invariant-respecting representations, not just three witnesses. -/
theorem representations_four (a b c d : α) (s : SymList α) :
    Inv s ∧ fromSL s = [a, b, c, d] ↔
      s = ([a], [d, c, b]) ∨ s = ([a, b], [d, c]) ∨ s = ([a, b, c], [d]) := by
  constructor
  · rintro ⟨hi, hv⟩
    have ht : s.1.length + s.2.length = 4 := by
      have h := congrArg List.length hv
      simpa [fromSL] using h
    have hf : s.1.length ≠ 0 := by
      intro h
      have hb := hi.1 (List.length_eq_zero_iff.mp h)
      omega
    have hb : s.2.length ≠ 0 := by
      intro h
      have hf := hi.2 (List.length_eq_zero_iff.mp h)
      omega
    have choices : s.1.length = 1 ∨ s.1.length = 2 ∨ s.1.length = 3 := by omega
    have hfront := representation_front s
    have hback := representation_back s
    rw [hv] at hfront hback
    rcases choices with h | h | h
    · left
      apply Prod.ext
      · simpa [h] using hfront.symm
      · simpa [h] using hback.symm
    · right; left
      apply Prod.ext
      · simpa [h] using hfront.symm
      · simpa [h] using hback.symm
    · right; right
      apply Prod.ext
      · simpa [h] using hfront.symm
      · simpa [h] using hback.symm
  · rintro (rfl | rfl | rfl) <;> simp [Inv, fromSL]

theorem four_foldl_snoc (a b c d : α) :
    [a, b, c, d].foldl (fun s x => snocSL x s) nilSL = ([a], [d, c, b]) := rfl

theorem four_foldr_cons (a b c d : α) :
    [a, b, c, d].foldr consSL nilSL = ([a, b, c], [d]) := rfl

theorem four_mixed (a b c d : α) :
    consSL a (snocSL d ([b, c].foldr consSL nilSL)) = ([a, b], [d, c]) := rfl

theorem inits_bridge (xs : List α) : inits xs = xs.inits := rfl

theorem tails_append_singleton (xs : List α) (x : α) :
    (xs ++ [x]).tails = xs.tails.map (· ++ [x]) ++ [[]] := by simp

def offlineInits (xs : List α) : List (List α) := xs.reverse.tails.reverse.map List.reverse

theorem offlineInits_value (xs : List α) : offlineInits xs = xs.inits := by
  simpa [offlineInits, List.map_reverse] using (List.inits_eq_tails xs).symm

def finitePrefix (σ : Nat → α) (n : Nat) : List α := (List.range n).map σ

theorem prefix_succ (σ : Nat → α) (n : Nat) :
    finitePrefix σ (n + 1) = finitePrefix σ n ++ [σ n] := by
  simp [finitePrefix, List.range_succ]

/-- Checkpoint recurrence, retained privately to certify its finite-fold meaning. -/
private def sourceScanState (f : β → α → β) (e : β) (σ : Nat → α) : Nat → β
  | 0 => e
  | n + 1 => sourceScanState f (f e (σ 0)) (fun k => σ (k + 1)) n

private theorem sourceScanState_succ (f : β → α → β) (e : β) (σ : Nat → α) (n : Nat) :
    sourceScanState f e σ (n + 1) = f (sourceScanState f e σ n) (σ n) := by
  induction n generalizing e σ with
  | zero => rfl
  | succ n ih => exact ih (f e (σ 0)) (fun k => σ (k + 1))

private theorem sourceScanState_eq_foldl (f : β → α → β) (e : β) (σ : Nat → α) (n : Nat) :
    sourceScanState f e σ n = (finitePrefix σ n).foldl f e := by
  induction n with
  | zero => rfl
  | succ n ih => rw [sourceScanState_succ, prefix_succ, List.foldl_append, ih]; rfl

/-- The source's shift recurrence, expressed entirely with standard finite folds. -/
theorem finitePrefix_foldl_shift (f : β → α → β) (e : β) (σ : Nat → α) (n : Nat) :
    (finitePrefix σ (n + 1)).foldl f e =
      (finitePrefix (fun k => σ (k + 1)) n).foldl f (f e (σ 0)) := by
  rw [← sourceScanState_eq_foldl, ← sourceScanState_eq_foldl]
  rfl

theorem scanState_symmetric_inv (σ : Nat → α) (n : Nat) :
    Inv ((finitePrefix σ n).foldl (fun s x => snocSL x s) nilSL) := by
  induction n with
  | zero => exact inv_nilSL
  | succ n _ => simp only [prefix_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]; exact inv_snocSL _ _

theorem scanState_symmetric_value (σ : Nat → α) (n : Nat) :
    fromSL ((finitePrefix σ n).foldl (fun s x => snocSL x s) nilSL) = finitePrefix σ n := by
  have fusion := SquareKit.ListFusion.foldl_reachable
    (fun s x => snocSL x s) (fun ys x => ys ++ [x]) fromSL Inv nilSL inv_nilSL
    (fun s x _ => inv_snocSL x s) (fun s x h => fromSL_snocSL x s h) (finitePrefix σ n)
  simpa [← List.flatMap_def] using fusion

theorem scanState_reverse_value (σ : Nat → α) (n : Nat) :
    ((finitePrefix σ n).foldl (fun ys x => x :: ys) []).reverse = finitePrefix σ n := by
  simp

end Sequences.Symmetric
