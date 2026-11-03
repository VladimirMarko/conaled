import Applications.Resources.RandomAccess.Cycles

/-! Finite end-operation accounting from checkpoint 233.
Provenance, source domains and statement review:
`docs/research/adwh-random-access-end-costs.md`. -/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RandomAccessCosts
open RandomAccess
universe u
variable {α : Type u}

/-- Exercise 3.9's explicit error label, retaining the checked lookup algorithm. -/
def fetchRAError (k : Nat) (ds : RAList α) : Except String α :=
  match fetchRA k ds with
  | none => .error "index too large"
  | some x => .ok x

theorem fetchRAError_nil (k : Nat) : fetchRAError (α := α) k [] = .error "index too large" := rfl

theorem fetchRAError_refinement {r : Nat} {ds : RAList α} (h : Valid r ds) (k : Nat) :
    fetchRAError k ds =
      match (fromRA ds)[k]? with
      | none => .error "index too large"
      | some x => .ok x := by
  rw [fetchRAError, fetchRA_refinement h]

theorem fetchRAError_error_iff {r : Nat} {ds : RAList α} (h : Valid r ds) (k : Nat) :
    fetchRAError k ds = .error "index too large" ↔ (fromRA ds).length ≤ k := by
  constructor
  · intro he
    have hn : fetchRA k ds = none := by
      cases hf : fetchRA k ds with
      | none => rfl
      | some x => simp [fetchRAError, hf] at he
    rw [fetchRA_refinement h] at hn
    exact List.getElem?_eq_none_iff.mp hn
  · intro hk
    have hn : fetchRA k ds = none := by
      rw [fetchRA_refinement h]
      exact List.getElem?_eq_none hk
    simp [fetchRAError, hn]

theorem fetchRAError_ok_iff {r : Nat} {ds : RAList α} (h : Valid r ds) (k : Nat) (x : α) :
    fetchRAError k ds = .ok x ↔ (fromRA ds)[k]? = some x := by
  rw [fetchRAError_refinement h]
  cases (fromRA ds)[k]? <;> simp

/-- The source tree builder produces exactly the tree used in pp50–51. -/
theorem four_element_tree (a b c d : α) :
    tree [a, b, c, d] = some (node (node (.leaf a) (.leaf b)) (node (.leaf c) (.leaf d))) := by
  simp [tree]

/-- Every intermediate borrow state from the printed four-element derivation. -/
theorem four_element_borrow_derivation (a b c d : α) :
    let ab := node (.leaf a) (.leaf b)
    let cd := node (.leaf c) (.leaf d)
    let t := node ab cd
    unconsT [.one t] = some (t, []) ∧
      unconsT [.zero, .one t] = some (ab, [.one cd]) ∧
      unconsT [.zero, .zero, .one t] = some (.leaf a, [.one (.leaf b), .one cd]) ∧
      unconsTRun [.zero, .zero, .one t] =
        (some (.leaf a, [.one (.leaf b), .one cd]), 3) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Decode every reachable bulk-update state, preserving order and the initial seed. -/
theorem bulk_scan_refinement {r : Nat} {ds : RAList α} (h : Valid r ds)
    (us : List (Nat × α)) :
    (us.scanl (fun ys p => updateRA p.1 p.2 ys) ds).map fromRA =
      us.scanl (fun xs p => xs.set p.1 p.2) (fromRA ds) :=
  SquareKit.ListFusion.scanl_reachable _ _ fromRA (Valid r) ds h
    (fun _ p hy => valid_updateRA hy p.1 p.2)
    (fun _ p hy => updateRA_refinement hy p.1 p.2) us

/-- Answer 3.12's full ordered state trace, including the overwritten index 2. -/
theorem bulk_answer_intermediate_states :
    (([(1, 7), (2, 3), (3, 4), (2, 8)] : List (Nat × Nat)).scanl
      (fun ds p => updateRA p.1 p.2 ds) (toRA [0, 1, 2, 3])).map fromRA =
      [[0, 1, 2, 3], [0, 7, 2, 3], [0, 7, 3, 3], [0, 7, 3, 4], [0, 7, 8, 4]] := by
  rw [bulk_scan_refinement (inv_toRA _), fromRA_toRA]
  rfl

theorem bulk_answer_final_state :
    fromRA (bulk (toRA [0, 1, 2, 3]) [(1, 7), (2, 3), (3, 4), (2, 8)]) =
      [0, 7, 8, 4] := by
  rw [bulk_refinement (inv_toRA _), fromRA_toRA]
  rfl

end Resources.RandomAccessCosts
