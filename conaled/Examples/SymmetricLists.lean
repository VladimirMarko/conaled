import Applications.Sequences.Symmetric.Observation

/-! Boundary cases through finite sequence contracts and composed consumers. -/
namespace Examples.SymmetricLists
open Sequences.Symmetric

example : headSL (nilSL : SymList Nat) = none :=
  (headSL_eq_none_iff _).mpr rfl

example (s : SymList Nat) (hs : s = ([7], []) ∨ s = ([], [7])) :
    headSL s = some 7 ∧ lastSL s = some 7 ∧ fromSL (tailSL s) = [] ∧
      fromSL (initSL s) = [] := by
  have h : Inv s := by rcases hs with rfl | rfl <;> simp [Sequences.Symmetric.Inv]
  rw [headSL_eq_head _ h, lastSL_eq_getLast _ h, fromSL_tailSL _ h, fromSL_initSL _ h]
  rcases hs with rfl | rfl <;> simp [fromSL]

example (a b c d : α) (s : SymList α) (h : Inv s) (he : fromSL s = [a,b,c,d]) :
    s = ([a],[d,c,b]) ∨ s = ([a,b],[d,c]) ∨ s = ([a,b,c],[d]) :=
  (representations_four a b c d s).mp ⟨h, he⟩

example (a b c d x : α) :
    (editHead x).impl ([a,b,c,d].foldl (fun s y => snocSL y s) (nilSL : SymList α)) = some b := by
  exact (congrArg (editHead x).impl (four_foldl_snoc a b c d)).trans
    (by simpa [fromSL] using editHead_correct x ([a],[d,c,b]) (by simp [Sequences.Symmetric.Inv]))

example (a b c d x : α) :
    (editHead x).impl ([a,b,c,d].foldr consSL (nilSL : SymList α)) = some b := by
  exact (congrArg (editHead x).impl (four_foldr_cons a b c d)).trans
    (by simpa [fromSL] using editHead_correct x ([a,b,c],[d]) (by simp [Sequences.Symmetric.Inv]))

example (a b c d x : α) :
    (editHead x).impl (consSL a (snocSL d ([b,c].foldr consSL nilSL))) = some b := by
  rw [four_mixed]
  simpa [fromSL] using editHead_correct x ([a,b],[d,c]) (by simp [Sequences.Symmetric.Inv])

example (s : SymList Nat) :
    Inv s ∧ fromSL s = [1,1,1,1] ↔
      s = ([1],[1,1,1]) ∨ s = ([1,1],[1,1]) ∨ s = ([1,1,1],[1]) :=
  representations_four _ _ _ _ _

example : fromSL (tailSL (nilSL : SymList Nat)) = [] :=
  fromSL_tailSL _ inv_nilSL
example : fromSL (initSL (nilSL : SymList Nat)) = [] :=
  fromSL_initSL _ inv_nilSL
example : fromSL (splitSL [1,2,3,4,5]) = [1,2,3,4,5] := fromSL_splitSL _
example : Inv (splitSL [1,2,3,4]) := inv_splitSL _

example : Inv ([1], [6,5,4,3,2]) ∧
    fromSL (tailSL ([1],[6,5,4,3,2])) = [2,3,4,5,6] := by
  have h : Inv ([1], [6,5,4,3,2]) := by simp [Sequences.Symmetric.Inv]
  exact ⟨h, by simpa [fromSL] using fromSL_tailSL _ h⟩

example : tailSL ([1], [5,4,3,2]) = ([2,3],[5,4]) := rfl
example : tailSL ([1], [6,5,4,3,2]) = ([2,3,4],[6,5]) := rfl
example : initSL ([1,2,3,4,5], [6]) = ([1,2],[5,4,3]) :=
  initSL_singleton_back _ _
example : fromSL (initSL ([1,2,3,4,5], [6])) = [1,2,3,4,5] := by
  simpa [fromSL] using fromSL_initSL ([1,2,3,4,5],[6]) (by simp [Sequences.Symmetric.Inv])

example : ¬ Inv (([], [1,2]) : SymList Nat) := by simp [Sequences.Symmetric.Inv]
example : fromSL (snocSL 3 ([], [1,2])) ≠ fromSL ([], [1,2]) ++ [3] := by decide
example : Inv (snocSL 3 ([], [1,2])) := inv_snocSL _ _
example : lengthSL (tailSL ([], [1,2])) < lengthSL ([], [1,2]) :=
  tailSL_length_lt _ (by decide)

example : fromSL (dropWhileSL (fun _ => false) ([1],[4,3,2])) = [1,2,3,4] := by
  simpa [fromSL] using fromSL_dropWhileSL (fun _ => false) ([1],[4,3,2]) (by simp [Sequences.Symmetric.Inv])
example : fromSL (dropWhileSL (fun _ => true) ([1],[4,3,2])) = [] := by
  simpa [fromSL] using fromSL_dropWhileSL (fun _ => true) ([1],[4,3,2]) (by simp [Sequences.Symmetric.Inv])
example : fromSL (dropWhileSL (fun n => n < 4) ([1],[5,4,3,2])) = [4,5] := by
  simpa [fromSL] using fromSL_dropWhileSL (fun n : Nat => n < 4) ([1],[5,4,3,2]) (by simp [Sequences.Symmetric.Inv])

example : ([1,2].scanl (fun s x => snocSL x s) ([9],[])).map fromSL =
    [[9],[9,1],[9,1,2]] := by
  simpa [inits, fromSL] using scanl_snocSL_refinement [1,2] ([9],[]) (by simp [Sequences.Symmetric.Inv])

example : Inv ((finitePrefix (fun n => n + 10) 3).foldl (fun s x => snocSL x s) nilSL) :=
  scanState_symmetric_inv _ _

example : initsViaSL [1,2,1] = [[],[1],[1,2],[1,2,1]] := initsViaSL_eq_inits _
example : initsReverseScan [1,2,1] = [[],[1],[1,2],[1,2,1]] := initsReverseScan_eq_inits _
example : offlineInits [1,2,1] = [[],[1],[1,2],[1,2,1]] := offlineInits_value _
example : (fromSL (initsSL (toSL [1,2,1]))).map fromSL = [[],[1],[1,2],[1,2,1]] := by
  rw [fromSL_initsSL _ (inv_toSL _), fromSL_toSL]; rfl
example : Inv (initsSL (toSL [1,2,1])) ∧
    ∀ t ∈ fromSL (initsSL (toSL [1,2,1])), Inv t :=
  ⟨inv_initsSL _, initsSL_members_valid _ (inv_toSL _)⟩
example : ((prefixLengths (α := Nat)).impl (toSL [1,2,1])).down = [0,1,2,3] := by
  rw [prefixLengths_correct _ (inv_toSL _), ← length_fromSL, fromSL_toSL]; rfl
example : ((prefixLengths (α := Nat)).impl nilSL).down = [0] :=
  prefixLengths_correct _ inv_nilSL

example : fromSL ((finitePrefix (fun n => n + 10) 0).foldl (fun s x => snocSL x s) nilSL) = [] :=
  scanState_symmetric_value _ _
example : fromSL ((finitePrefix (fun n => n + 10) 3).foldl (fun s x => snocSL x s) nilSL) = [10,11,12] :=
  scanState_symmetric_value _ _
example : ((finitePrefix (fun n => n + 10) 3).foldl (fun ys x => x :: ys) []).reverse = [10,11,12] :=
  scanState_reverse_value _ _
example (f : β → α → β) (e : β) (σ : Nat → α) :
    (finitePrefix σ 3).foldl f e = (finitePrefix (fun k => σ (k+1)) 2).foldl f (f e (σ 0)) :=
  finitePrefix_foldl_shift _ _ _ _

end Examples.SymmetricLists
