import Applications.Trees.Rotations.Mixed
import Applications.Trees.Rotations.Bounds
import Mathlib.Data.Nat.Find

/-!
# Minimum mixed rotation distance

For labelled trees the connected domain is equality of the complete inorder
list. The minimum is taken over every successful mixed trace, using the existing
normalizing route only to establish nonemptiness and an upper bound. Unit labels
then give a transparent fixed-size shape interface without a connectedness input.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.Rotations
universe u
variable {α : Type u}

/-- The established right-normalization / left-recovery route as mixed moves. -/
def connectionMoves (s t : BinaryTree α) : List RotationMove :=
  directedMoves .right (rightPositions s) ++
    directedMoves .left (rightPositions t).reverse

theorem apply_connectionMoves {s t : BinaryTree α} (same : inorder s = inorder t) :
    applyMoves? (connectionMoves s t) s = some t := by
  rw [connectionMoves, applyMoves?_append, applyMoves?_directedMoves]
  have recovery : applyMoves? (α := α) (directedMoves .left (rightPositions t).reverse) =
      applyAts? rotateLeft? (rightPositions t).reverse :=
    funext (applyMoves?_directedMoves .left _)
  rw [recovery]
  exact connect_equal_inorder same

theorem connectionMoves_length_le {s t : BinaryTree α} (same : inorder s = inorder t) :
    (connectionMoves s t).length ≤ 2 * s.numNodes - 2 := by
  simpa only [connectionMoves, List.length_append, directedMoves_length, List.length_reverse]
    using connection_length_le same

/-- The inorder observation exactly characterizes the connected labelled domain. -/
theorem exists_moves_iff {s t : BinaryTree α} :
    (∃ moves, applyMoves? moves s = some t) ↔ inorder s = inorder t := by
  constructor
  · rintro ⟨moves, run⟩
    exact (applyMoves?_inorder moves run).symm
  · intro same
    exact ⟨connectionMoves s t, apply_connectionMoves same⟩

private theorem exists_trace_length {s t : BinaryTree α} (same : inorder s = inorder t) :
    ∃ n : Nat, ∃ moves : List RotationMove,
      applyMoves? moves s = some t ∧ moves.length = n :=
  ⟨(connectionMoves s t).length, connectionMoves s t, apply_connectionMoves same, rfl⟩

/-- The least length of any legal mixed trace, defined only on connected labelled pairs. -/
noncomputable def distance (s t : BinaryTree α) (same : inorder s = inorder t) : Nat := by
  classical
  exact Nat.find (exists_trace_length same)

/-- The minimum is attained by an actual successful trace. -/
theorem distance_spec {s t : BinaryTree α} (same : inorder s = inorder t) :
    ∃ moves : List RotationMove,
      applyMoves? moves s = some t ∧ moves.length = distance s t same := by
  classical
  exact Nat.find_spec (exists_trace_length same)

/-- Every legal trace, not just the selected normalizing route, bounds the minimum. -/
theorem distance_le_length {s t : BinaryTree α} (same : inorder s = inorder t)
    {moves : List RotationMove} (run : applyMoves? moves s = some t) :
    distance s t same ≤ moves.length := by
  classical
  exact Nat.find_min' (exists_trace_length same) ⟨moves, run, rfl⟩

/-- An uncosted certificate characterization; no representation or runtime bound is asserted. -/
theorem distance_le_iff {s t : BinaryTree α} (same : inorder s = inorder t) (k : Nat) :
    distance s t same ≤ k ↔
      ∃ moves : List RotationMove, applyMoves? moves s = some t ∧ moves.length ≤ k := by
  constructor
  · intro bound
    obtain ⟨moves, run, length⟩ := distance_spec same
    exact ⟨moves, run, length ▸ bound⟩
  · rintro ⟨moves, run, bound⟩
    exact (distance_le_length same run).trans bound

@[simp] theorem distance_self (t : BinaryTree α) : distance t t rfl = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact distance_le_length rfl (applyMoves?_nil t)

theorem distance_eq_zero_iff {s t : BinaryTree α} (same : inorder s = inorder t) :
    distance s t same = 0 ↔ s = t := by
  constructor
  · intro zero
    obtain ⟨moves, run, length⟩ := distance_spec same
    have empty : moves = [] := List.eq_nil_of_length_eq_zero (length.trans zero)
    subst moves
    exact Option.some.inj run
  · rintro rfl
    exact distance_self s

theorem distance_symm {s t : BinaryTree α} (same : inorder s = inorder t) :
    distance s t same = distance t s same.symm := by
  apply Nat.le_antisymm
  · obtain ⟨moves, run, length⟩ := distance_spec same.symm
    calc
      distance s t same ≤ (inverseMoves moves).length :=
        distance_le_length same (applyMoves?_undo moves run)
      _ = distance t s same.symm := by simpa only [inverseMoves_length] using length
  · obtain ⟨moves, run, length⟩ := distance_spec same
    calc
      distance t s same.symm ≤ (inverseMoves moves).length :=
        distance_le_length same.symm (applyMoves?_undo moves run)
      _ = distance s t same := by simpa only [inverseMoves_length] using length

theorem distance_triangle {r s t : BinaryTree α}
    (first : inorder r = inorder s) (second : inorder s = inorder t) :
    distance r t (first.trans second) ≤ distance r s first + distance s t second := by
  obtain ⟨ms, runMS, lengthMS⟩ := distance_spec first
  obtain ⟨ns, runNS, lengthNS⟩ := distance_spec second
  have run : applyMoves? (ms ++ ns) r = some t := by
    rw [applyMoves?_append, runMS, Option.bind_some, runNS]
  calc
    distance r t (first.trans second) ≤ (ms ++ ns).length :=
      distance_le_length (first.trans second) run
    _ = distance r s first + distance s t second := by
      rw [List.length_append, lengthMS, lengthNS]

/-- Natural subtraction makes the elementary bound valid also at the empty tree. -/
theorem distance_le_two_mul_numNodes_sub_two {s t : BinaryTree α}
    (same : inorder s = inorder t) : distance s t same ≤ 2 * s.numNodes - 2 :=
  (distance_le_length same (apply_connectionMoves same)).trans (connectionMoves_length_le same)

/-- For subsingleton labels, node count already determines the inorder list. -/
theorem inorder_eq_of_numNodes_eq [Subsingleton α] {s t : BinaryTree α}
    (same : s.numNodes = t.numNodes) : inorder s = inorder t := by
  apply List.ext_getElem
  · simpa only [inorder_length] using same
  · intro i hs ht
    exact Subsingleton.elim _ _

/-- A tree shape with exactly `n` nonempty nodes, using the existing tree carrier. -/
abbrev Shape (n : Nat) := {t : BinaryTree Unit // t.numNodes = n}

namespace Shape
variable {n : Nat}

theorem inorder_eq (s t : Shape n) : inorder s.val = inorder t.val :=
  inorder_eq_of_numNodes_eq (s.property.trans t.property.symm)

/-- Finite minimum rotation distance on every pair of shapes of a common size. -/
noncomputable def distance (s t : Shape n) : Nat :=
  Trees.Rotations.distance s.val t.val (inorder_eq s t)

theorem distance_spec (s t : Shape n) :
    ∃ moves : List RotationMove,
      applyMoves? moves s.val = some t.val ∧ moves.length = distance s t :=
  Trees.Rotations.distance_spec (inorder_eq s t)

theorem distance_le_length (s t : Shape n) {moves : List RotationMove}
    (run : applyMoves? moves s.val = some t.val) : distance s t ≤ moves.length :=
  Trees.Rotations.distance_le_length (inorder_eq s t) run

theorem distance_le_iff (s t : Shape n) (k : Nat) :
    distance s t ≤ k ↔
      ∃ moves : List RotationMove, applyMoves? moves s.val = some t.val ∧ moves.length ≤ k :=
  Trees.Rotations.distance_le_iff (inorder_eq s t) k

@[simp] theorem distance_self (t : Shape n) : distance t t = 0 :=
  Trees.Rotations.distance_self t.val

theorem distance_eq_zero_iff (s t : Shape n) : distance s t = 0 ↔ s = t := by
  rw [distance, Trees.Rotations.distance_eq_zero_iff]
  exact Subtype.val_inj

theorem distance_symm (s t : Shape n) : distance s t = distance t s :=
  Trees.Rotations.distance_symm (inorder_eq s t)

theorem distance_triangle (r s t : Shape n) : distance r t ≤ distance r s + distance s t :=
  Trees.Rotations.distance_triangle (inorder_eq r s) (inorder_eq s t)

/-- The canonical `2*n-2` bound, with the natural-subtraction extension to `n = 0`. -/
theorem distance_le_two_mul_sub_two (s t : Shape n) : distance s t ≤ 2 * n - 2 := by
  simpa only [distance, s.property] using
    Trees.Rotations.distance_le_two_mul_numNodes_sub_two (inorder_eq s t)

theorem distance_empty (s t : Shape 0) : distance s t = 0 :=
  Nat.eq_zero_of_le_zero (distance_le_two_mul_sub_two s t)

theorem distance_singleton (s t : Shape 1) : distance s t = 0 :=
  Nat.eq_zero_of_le_zero (distance_le_two_mul_sub_two s t)

end Shape
end Trees.Rotations
