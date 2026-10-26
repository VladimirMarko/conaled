import Applications.Sequences.RandomAccess.Representation

/-! Public List refinements, binary carries/borrows and invariant boundaries. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.RandomAccessLists
open RandomAccess

example : fetchRA 0 (toRA ([] : List Nat)) = none := by
  rw [fetchRA_toRA]
  rfl

example : nullRA (toRA ([] : List Nat)) = true :=
  (nullRA_refinement (inv_toRA [])).mpr (fromRA_toRA [])

example : headRA (toRA ["only"]) = some "only" := by
  rw [headRA_refinement (inv_toRA _), fromRA_toRA]
  rfl

example : (tailRA (toRA ([] : List String))).map fromRA = none :=
  tailRA_refinement (inv_toRA [])

example : tailRA (toRA ["only"]) = some [] := by
  change (unconsRA (consRA "only" [])).map Prod.snd = some []
  rw [unconsRA_consRA _ (Valid.nil 0)]
  rfl

example : fetchRA 0 (toRA ([4, 4, 2] : List Nat)) = some 4 ∧
    fetchRA 2 (toRA ([4, 4, 2] : List Nat)) = some 2 := by
  constructor <;> rw [fetchRA_toRA] <;> rfl

example : fetchRA 3 (toRA ([4, 4, 2] : List Nat)) = none ∧
    fetchRA 9 (toRA ([4, 4, 2] : List Nat)) = none := by
  constructor <;> apply (fetchRA_none_iff (inv_toRA _) _).mpr <;>
    rw [fromRA_toRA] <;> decide

example : (updateQuery 1 "new" 1).impl (encode ["a", "b", "a"]) = some "new" :=
  updateQuery_same _ _ _ (by simp [encode, fromRA_toRA])

example : (updateQuery 1 "new" 2).impl (encode ["a", "b", "a"]) = some "a" := by
  rw [updateQuery_other _ _ _ _ (by decide)]
  exact fetchRA_toRA 2 _

example : (updateQuery 8 "new" 1).impl (encode ["a", "b"]) = some "b" := by
  rw [updateQuery_refinement]
  simp only [encode, fromRA_toRA]
  rfl

example : updateRA 3 9 (toRA ([4, 4, 2] : List Nat)) = toRA [4, 4, 2] ∧
    updateRA 8 9 (toRA ([4, 4, 2] : List Nat)) = toRA [4, 4, 2] := by
  constructor <;> apply updateRA_out_of_range (inv_toRA _) <;>
    rw [fromRA_toRA] <;> decide

example : fromRA (updateRA 2 9 (toRA ([4, 4, 2] : List Nat))) = [4, 4, 9] :=
  updateRA_toRA 2 9 _

example : (updateSquare 0 "new").impl (encode ([] : List String)) = encode [] :=
  updateSquare_encode [] 0 "new"

example : (updateSquare 0 "new").impl (encode ["only"]) = encode ["new"] :=
  updateSquare_encode ["only"] 0 "new"

example : (updateQuery 0 9 0).impl (encode ([4, 4, 2] : List Nat)) = some 9 :=
  updateQuery_same _ _ _ (by simp [encode, fromRA_toRA])

def seven : Carrier Nat := encode [1, 2, 3, 4, 5, 6, 7]
def eight : Carrier Nat := (consSquare 0).impl seven

def block (a b c d : Nat) : Tree Nat := node (node (.leaf a) (.leaf b)) (node (.leaf c) (.leaf d))

theorem seven_digits : seven.val =
    [.one (.leaf 1), .one (node (.leaf 2) (.leaf 3)), .one (block 4 5 6 7)] := by decide +kernel

theorem carry_digits : eight.val = [.zero, .zero, .zero, .one (node (block 0 1 2 3) (block 4 5 6 7))] := by
  decide +kernel

theorem carry_order : fromRA eight.val = [0, 1, 2, 3, 4, 5, 6, 7] := by
  change fromRA (consRA 0 seven.val) = _
  rw [fromRA_consRA]
  exact congrArg (0 :: ·) (fromRA_toRA _)

example : Inv eight.val := eight.property

-- Borrowing through the three zero digits returns the exact original state.
theorem borrow_exact : unconsRA eight.val = some (0, seven.val) :=
  unconsRA_consRA 0 seven.property

example : (pushPop 0).impl seven = some (0, seven) := pushPop_exact seven 0

example : (unconsRepresentation Nat).decode ((pushPop 0).impl seven) =
    some (0, [1, 2, 3, 4, 5, 6, 7]) := by
  rw [pushPop_refinement]
  exact congrArg (fun xs => some (0, xs)) (fromRA_toRA _)

example : Inv seven.val ∧ fromRA seven.val = [1, 2, 3, 4, 5, 6, 7] :=
  ⟨unconsRA_valid eight.property borrow_exact, fromRA_toRA _⟩

example : encode ((representation Nat).decode eight) = eight := encode_decode eight

-- The historical shallow-check false positive is kept verbatim in meaning.
theorem weak_check_accepts_bad_tree :
    invRA [.one (.node 1 (.leaf 10) (.leaf 20))] = true := rfl

theorem bad_tree_lookup_mismatch :
    fetchRA 0 [.one (.node 1 (.leaf 10) (.leaf 20))] = some 20 ∧
      (fromRA [.one (.node 1 (.leaf 10) (.leaf 20))])[0]? = some 10 := by
  constructor <;> rfl

theorem bad_tree_not_valid : ¬Inv [.one (.node 1 (.leaf 10) (.leaf 20))] := by
  intro h
  have he := fetchRA_refinement h 0
  rw [bad_tree_lookup_mismatch.1, bad_tree_lookup_mismatch.2] at he
  contradiction

theorem trailing_zero_boundary : invRA ([.zero] : RAList Nat) = true ∧
    fromRA ([.zero] : RAList Nat) = [] ∧ nullRA ([.zero] : RAList Nat) = false := by
  decide +kernel

example : ¬Inv ([.zero] : RAList Nat) := by
  intro h
  have he := (nullRA_refinement h).mpr trailing_zero_boundary.2.1
  rw [trailing_zero_boundary.2.2] at he
  contradiction

def unbalanced : Tree Nat := .node 3 (.node 2 (.leaf 10) (.leaf 20)) (.leaf 30)

theorem unbalanced_cached : Cached unbalanced := ⟨rfl, ⟨rfl, trivial, trivial⟩, trivial⟩

theorem cached_not_balanced : fetchT 1 unbalanced = some 30 ∧
    (fromT unbalanced)[1]? = some 20 := by constructor <;> rfl

example (rank : Nat) : ¬Perfect rank unbalanced := by
  intro h
  have he := fetchT_refinement h 1
  rw [cached_not_balanced.1, cached_not_balanced.2] at he
  contradiction

example : size unbalanced = Bracketing.size (erase unbalanced) :=
  cached_size_erasure _ unbalanced_cached

example : (tree ([] : List Nat)).map fromT = none := tree_abstraction []

theorem builder_three : ∃ t, tree ([10, 20, 30] : List Nat) = some t ∧
    fromT t = [10, 20, 30] ∧ Cached t := tree_spec _ (by decide)

example : ∃ t, tree ([10, 20, 30] : List Nat) = some t ∧
    Bracketing.fringeSpec (erase t) = [10, 20, 30] ∧ size t = 3 := by
  obtain ⟨t, ht, hf, hc⟩ := builder_three
  refine ⟨t, ht, (fromT_eq_fringe t).symm.trans hf, ?_⟩
  rw [cached_size_refinement t hc, hf]
  rfl

theorem builder_four : ∃ t, tree (["a", "b", "b", "d"] : List String) = some t ∧
    Perfect 2 t := tree_perfect 2 _ rfl

example : ∃ t, tree (["a", "b", "b", "d"] : List String) = some t ∧
    fetchT 2 t = some "b" := by
  obtain ⟨t, ht, hp⟩ := builder_four
  obtain ⟨s, hs, hf, _⟩ := tree_spec (["a", "b", "b", "d"] : List String) (by decide)
  have he : t = s := Option.some.inj (ht.symm.trans hs)
  subst s
  refine ⟨t, ht, ?_⟩
  rw [fetchT_refinement hp, hf]
  rfl

end Examples.RandomAccessLists
