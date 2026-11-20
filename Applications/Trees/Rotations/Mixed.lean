import Applications.Trees.Rotations.Position

/-!
# Mixed partial rotation traces

A move records the rotation direction separately from its subtree position.
Every position is interpreted in the result of the preceding move. Successful
traces preserve the complete inorder list and are undone by reversing the moves
and swapping their directions.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.Rotations
open Search.SharedTree (Branch)
universe u
variable {α : Type u}

/-- The direction of a root rotation, as opposed to a branch in a subtree path. -/
inductive RotationDirection where
  | left
  | right
  deriving DecidableEq, Repr

namespace RotationDirection

def opposite : RotationDirection → RotationDirection
  | .left => .right
  | .right => .left

@[simp] theorem opposite_opposite (d : RotationDirection) : d.opposite.opposite = d := by
  cases d <;> rfl

/-- Dispatch to the existing partial root operation; an illegal rotation fails. -/
def apply? : RotationDirection → BinaryTree α → Option (BinaryTree α)
  | .left => rotateLeft?
  | .right => rotateRight?

theorem apply?_inorder (d : RotationDirection) {s t : BinaryTree α}
    (run : d.apply? s = some t) : inorder t = inorder s := by
  cases d with
  | left => exact rotateLeft?_inorder run
  | right => exact rotateRight?_inorder run

theorem apply?_undo (d : RotationDirection) {s t : BinaryTree α}
    (run : d.apply? s = some t) : d.opposite.apply? t = some s := by
  cases d with
  | left => exact rotateRight?_undo run
  | right => exact rotateLeft?_undo run

end RotationDirection

/-- A direction and a path, with no assumed legality or endpoint. -/
structure RotationMove where
  direction : RotationDirection
  position : List Branch
  deriving DecidableEq, Repr

namespace RotationMove

/-- The inverse uses the same subtree position in the reached state. -/
def opposite (move : RotationMove) : RotationMove :=
  ⟨move.direction.opposite, move.position⟩

@[simp] theorem opposite_opposite (move : RotationMove) :
    move.opposite.opposite = move := by
  cases move
  simp [opposite]

end RotationMove

def applyMove? (move : RotationMove) (t : BinaryTree α) : Option (BinaryTree α) :=
  applyAt? move.direction.apply? move.position t

theorem applyMove?_inorder (move : RotationMove) {s t : BinaryTree α}
    (run : applyMove? move s = some t) : inorder t = inorder s :=
  applyAt?_inorder move.direction.apply? move.direction.apply?_inorder move.position run

theorem applyMove?_undo (move : RotationMove) {s t : BinaryTree α}
    (run : applyMove? move s = some t) : applyMove? move.opposite t = some s :=
  applyAt?_undo move.direction.apply? move.direction.opposite.apply?
    move.direction.apply?_undo move.position run

/-- Ordinary sequential partial execution; the tail consumes the preceding result. -/
def applyMoves? (moves : List RotationMove) (t : BinaryTree α) : Option (BinaryTree α) :=
  moves.foldlM (fun current move => applyMove? move current) t

@[simp] theorem applyMoves?_nil (t : BinaryTree α) : applyMoves? [] t = some t := rfl

@[simp] theorem applyMoves?_cons (move : RotationMove) (moves : List RotationMove)
    (t : BinaryTree α) :
    applyMoves? (move :: moves) t = (applyMove? move t).bind (applyMoves? moves) := rfl

/-- Includes propagation of failure from either component. -/
theorem applyMoves?_append (first second : List RotationMove) (t : BinaryTree α) :
    applyMoves? (first ++ second) t = (applyMoves? first t).bind (applyMoves? second) := by
  exact List.foldlM_append

theorem applyMoves?_inorder (moves : List RotationMove) {s t : BinaryTree α}
    (run : applyMoves? moves s = some t) : inorder t = inorder s := by
  induction moves generalizing s t with
  | nil => cases run; rfl
  | cons move moves ih =>
      cases first : applyMove? move s with
      | none => simp [first] at run
      | some s' =>
          simp only [applyMoves?_cons, first, Option.bind_some] at run
          exact (ih run).trans (applyMove?_inorder move first)

theorem applyMoves?_numNodes (moves : List RotationMove) {s t : BinaryTree α}
    (run : applyMoves? moves s = some t) : t.numNodes = s.numNodes :=
  numNodes_eq_of_inorder_eq (applyMoves?_inorder moves run)

/-- Reverse the actual operations, retaining each position and swapping its direction. -/
def inverseMoves (moves : List RotationMove) : List RotationMove :=
  moves.reverse.map RotationMove.opposite

@[simp] theorem inverseMoves_nil : inverseMoves [] = [] := rfl

@[simp] theorem inverseMoves_cons (move : RotationMove) (moves : List RotationMove) :
    inverseMoves (move :: moves) = inverseMoves moves ++ [move.opposite] := by
  simp [inverseMoves]

@[simp] theorem inverseMoves_length (moves : List RotationMove) :
    (inverseMoves moves).length = moves.length := by
  simp [inverseMoves]

@[simp] theorem inverseMoves_inverseMoves (moves : List RotationMove) :
    inverseMoves (inverseMoves moves) = moves := by
  simp [inverseMoves, List.map_reverse, List.map_map, Function.comp_def]

theorem applyMoves?_undo (moves : List RotationMove) {s t : BinaryTree α}
    (run : applyMoves? moves s = some t) : applyMoves? (inverseMoves moves) t = some s := by
  induction moves generalizing s t with
  | nil => cases run; rfl
  | cons move moves ih =>
      cases first : applyMove? move s with
      | none => simp [first] at run
      | some s' =>
          simp only [applyMoves?_cons, first, Option.bind_some] at run
          rw [inverseMoves_cons, applyMoves?_append, ih run, Option.bind_some]
          simp only [applyMoves?_cons, applyMove?_undo move first, Option.bind_some,
            applyMoves?_nil]

/-- Embed an existing fixed-direction position schedule without changing its positions. -/
def directedMoves (d : RotationDirection) (positions : List (List Branch)) :
    List RotationMove := positions.map (fun p => ⟨d, p⟩)

@[simp] theorem directedMoves_length (d : RotationDirection) (positions : List (List Branch)) :
    (directedMoves d positions).length = positions.length := by
  simp [directedMoves]

/-- The mixed interpreter agrees with the existing fixed-direction interpreter. -/
theorem applyMoves?_directedMoves (d : RotationDirection) (positions : List (List Branch))
    (t : BinaryTree α) :
    applyMoves? (directedMoves d positions) t = applyAts? d.apply? positions t := by
  induction positions generalizing t with
  | nil => rfl
  | cons p positions ih =>
      simp only [directedMoves, List.map_cons, applyMoves?_cons, applyMove?, applyAts?_cons]
      cases first : applyAt? d.apply? p t with
      | none => rfl
      | some t' => exact ih t'

end Trees.Rotations
