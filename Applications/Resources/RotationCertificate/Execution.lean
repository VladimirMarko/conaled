import Applications.Trees.Rotations.Mixed
import Applications.Resources.CallCount

/-!
# Measured partial rotation execution and structural equality

The tariff charges one entry per primitive, one per constructed node, Option
constructor or Boolean literal, and zero for projections, packaging and reuse.
Each reached callback supplies its actual result; reconstruction consumes it.
The position tail is not traversed after a missing node. Shape equality is an
actual left-first short-circuit program on Unit trees, not a whole-tree oracle.
These source-event observations do not assert machine time or NP membership.
Correspondence: `docs/research/fdsa-rotation-certificate-preparation.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RotationCertificate
open Search.SharedTree (Branch)
open Trees.Rotations (RotationDirection RotationMove)
universe u
variable {α : Type u}

/-- Execute a legal root rewrite, binding both newly constructed nodes. -/
def rotateRun : RotationDirection → BinaryTree α → Measured (Option (BinaryTree α)) Nat
  | .left, .node a A (.node b B C) =>
      CallCount.tick (bind (.node a A B, 1) (fun left =>
        bind (.node b left C, 1) (fun result => (some result, 1))))
  | .right, .node b (.node a A B) C =>
      CallCount.tick (bind (.node b B C, 1) (fun right =>
        bind (.node a A right, 1) (fun result => (some result, 1))))
  | _, _ => (none, 2)

@[simp] theorem rotateRun_left (a b : α) (A B C : BinaryTree α) :
    rotateRun .left (.node a A (.node b B C)) =
      (some (.node b (.node a A B) C), 4) := rfl

@[simp] theorem rotateRun_right (a b : α) (A B C : BinaryTree α) :
    rotateRun .right (.node b (.node a A B) C) =
      (some (.node a A (.node b B C)), 4) := rfl

@[simp] theorem rotateRun_nil (d : RotationDirection) :
    rotateRun d (.nil : BinaryTree α) = (none, 2) := by cases d <;> rfl

theorem rotateRun_value (d : RotationDirection) (t : BinaryTree α) :
    (rotateRun d t).1 = d.apply? t := by
  cases d with
  | left => cases t with
    | nil => rfl
    | node a l r => cases r <;> rfl
  | right => cases t with
    | nil => rfl
    | node a l r => cases l <;> rfl

theorem rotateRun_cost_of_some (d : RotationDirection) (s t : BinaryTree α)
    (returned : (rotateRun d s).1 = some t) : (rotateRun d s).2 = 4 := by
  cases d with
  | left => cases s with
    | nil => cases returned
    | node a l r => cases r with
      | nil => cases returned
      | node b B C => rfl
  | right => cases s with
    | nil => cases returned
    | node a l r => cases l with
      | nil => cases returned
      | node b A B => rfl

theorem rotateRun_cost_of_none (d : RotationDirection) (s : BinaryTree α)
    (returned : (rotateRun d s).1 = none) : (rotateRun d s).2 = 2 := by
  cases d with
  | left => cases s with
    | nil => rfl
    | node a l r => cases r with
      | nil => rfl
      | node b B C => cases returned
  | right => cases s with
    | nil => rfl
    | node a l r => cases l with
      | nil => rfl
      | node b A B => cases returned

theorem rotateRun_cost_le (d : RotationDirection) (s : BinaryTree α) :
    (rotateRun d s).2 ≤ 4 := by
  cases returned : (rotateRun d s).1 with
  | none => rw [rotateRun_cost_of_none d s returned]; decide
  | some t => rw [rotateRun_cost_of_some d s t returned]

/-- Follow one actual path, reconstructing only successful ancestors. -/
def applyAtRun (fRun : BinaryTree α → Measured (Option (BinaryTree α)) Nat) :
    List Branch → BinaryTree α → Measured (Option (BinaryTree α)) Nat
  | [], t => CallCount.tick (fRun t)
  | _ :: _, .nil => (none, 2)
  | .left :: p, .node a l r =>
      CallCount.tick (bind (applyAtRun fRun p l) (fun result =>
        match result with
        | none => (none, 1)
        | some child => bind (.node a child r, 1) (fun rebuilt => (some rebuilt, 1))))
  | .right :: p, .node a l r =>
      CallCount.tick (bind (applyAtRun fRun p r) (fun result =>
        match result with
        | none => (none, 1)
        | some child => bind (.node a l child, 1) (fun rebuilt => (some rebuilt, 1))))

@[simp] theorem applyAtRun_root
    (fRun : BinaryTree α → Measured (Option (BinaryTree α)) Nat) (t : BinaryTree α) :
    applyAtRun fRun [] t = ((fRun t).1, (fRun t).2 + 1) := rfl

@[simp] theorem applyAtRun_nil_cons
    (fRun : BinaryTree α → Measured (Option (BinaryTree α)) Nat)
    (d : Branch) (p : List Branch) : applyAtRun fRun (d :: p) .nil = (none, 2) := rfl

theorem applyAtRun_left
    (fRun : BinaryTree α → Measured (Option (BinaryTree α)) Nat)
    (p : List Branch) (a : α) (l r : BinaryTree α) :
    applyAtRun fRun (.left :: p) (.node a l r) =
      let actual := applyAtRun fRun p l
      match actual.1 with
      | none => (none, actual.2 + 2)
      | some child => (some (.node a child r), actual.2 + 3) := by
  simp only [applyAtRun, CallCount.tick, bind]
  cases h : (applyAtRun fRun p l).1 <;> rfl

theorem applyAtRun_right
    (fRun : BinaryTree α → Measured (Option (BinaryTree α)) Nat)
    (p : List Branch) (a : α) (l r : BinaryTree α) :
    applyAtRun fRun (.right :: p) (.node a l r) =
      let actual := applyAtRun fRun p r
      match actual.1 with
      | none => (none, actual.2 + 2)
      | some child => (some (.node a l child), actual.2 + 3) := by
  simp only [applyAtRun, CallCount.tick, bind]
  cases h : (applyAtRun fRun p r).1 <;> rfl

theorem applyAtRun_value
    (fRun : BinaryTree α → Measured (Option (BinaryTree α)) Nat)
    (f : BinaryTree α → Option (BinaryTree α)) (p : List Branch) (t : BinaryTree α)
    (values : ∀ s, (fRun s).1 = f s) :
    (applyAtRun fRun p t).1 = Trees.Rotations.applyAt? f p t := by
  induction p generalizing t with
  | nil => exact values t
  | cons d p ih =>
      cases t with
      | nil => rfl
      | node a l r =>
          cases d with
          | left =>
              simp only [applyAtRun_left, Trees.Rotations.applyAt?_left, ← ih l]
              cases h : (applyAtRun fRun p l).1 <;> rfl
          | right =>
              simp only [applyAtRun_right, Trees.Rotations.applyAt?_right, ← ih r]
              cases h : (applyAtRun fRun p r).1 <;> rfl

/-- Success adds exactly three events for each reconstructed ancestor. -/
theorem applyAtRun_cost_of_some
    (fRun : BinaryTree α → Measured (Option (BinaryTree α)) Nat)
    (p : List Branch) (s t : BinaryTree α) (C : Nat)
    (callback : ∀ a b, (fRun a).1 = some b → (fRun a).2 = C)
    (returned : (applyAtRun fRun p s).1 = some t) :
    (applyAtRun fRun p s).2 = 3 * p.length + C + 1 := by
  induction p generalizing s t with
  | nil =>
      have cost := callback s t returned
      change (fRun s).2 + 1 = 3 * 0 + C + 1
      omega
  | cons d p ih =>
      cases s with
      | nil => cases returned
      | node a l r =>
          cases d with
          | left =>
              simp only [applyAtRun_left] at returned ⊢
              cases child : (applyAtRun fRun p l).1 with
              | none => simp only [child] at returned; cases returned
              | some left =>
                  have cost := ih l left child
                  simp only [List.length_cons]
                  omega
          | right =>
              simp only [applyAtRun_right] at returned ⊢
              cases child : (applyAtRun fRun p r).1 with
              | none => simp only [child] at returned; cases returned
              | some right =>
                  have cost := ih r right child
                  simp only [List.length_cons]
                  omega

def applyMoveRun (move : RotationMove) (t : BinaryTree α) :
    Measured (Option (BinaryTree α)) Nat :=
  applyAtRun (rotateRun move.direction) move.position t

theorem applyMoveRun_value (move : RotationMove) (t : BinaryTree α) :
    (applyMoveRun move t).1 = Trees.Rotations.applyMove? move t :=
  applyAtRun_value (rotateRun move.direction) move.direction.apply? move.position t
    (rotateRun_value move.direction)

private theorem rotate_depth_le (d : RotationDirection) (s t : BinaryTree α)
    (run : d.apply? s = some t) : 2 ≤ s.numNodes := by
  cases d with
  | left =>
      obtain ⟨a, b, A, B, C, rfl, rfl⟩ :=
        (Trees.Rotations.rotateLeft?_eq_some_iff s t).1 run
      simp only [BinaryTree.numNodes]
      omega
  | right =>
      obtain ⟨a, b, A, B, C, rfl, rfl⟩ :=
        (Trees.Rotations.rotateRight?_eq_some_iff s t).1 run
      simp only [BinaryTree.numNodes]
      omega

private theorem applyAtRotate_depth_le (d : RotationDirection) (p : List Branch)
    (s t : BinaryTree α) (run : Trees.Rotations.applyAt? d.apply? p s = some t) :
    p.length + 2 ≤ s.numNodes := by
  induction p generalizing s t with
  | nil => exact rotate_depth_le d s t run
  | cons branch p ih =>
      cases s with
      | nil => cases run
      | node a l r =>
          cases branch with
          | left =>
              cases child : Trees.Rotations.applyAt? d.apply? p l with
              | none =>
                  simp only [Trees.Rotations.applyAt?_left, child, Option.map_none] at run
                  cases run
              | some left =>
                  have depth := ih l left child
                  simp only [List.length_cons, BinaryTree.numNodes]
                  omega
          | right =>
              cases child : Trees.Rotations.applyAt? d.apply? p r with
              | none =>
                  simp only [Trees.Rotations.applyAt?_right, child, Option.map_none] at run
                  cases run
              | some right =>
                  have depth := ih r right child
                  simp only [List.length_cons, BinaryTree.numNodes]
                  omega

/-- A legal root needs two nodes beyond the actually traversed ancestors. -/
theorem applyMove_depth_le (move : RotationMove) (s t : BinaryTree α)
    (run : Trees.Rotations.applyMove? move s = some t) :
    move.position.length + 2 ≤ s.numNodes :=
  applyAtRotate_depth_le move.direction move.position s t run

theorem applyMoveRun_depth_le (move : RotationMove) (s t : BinaryTree α)
    (returned : (applyMoveRun move s).1 = some t) :
    move.position.length + 2 ≤ s.numNodes :=
  applyMove_depth_le move s t ((applyMoveRun_value move s).symm.trans returned)

theorem applyMoveRun_cost_of_some (move : RotationMove) (s t : BinaryTree α)
    (returned : (applyMoveRun move s).1 = some t) :
    (applyMoveRun move s).2 = 3 * move.position.length + 5 := by
  simpa only [applyMoveRun, Nat.add_assoc, Nat.reduceAdd] using
    applyAtRun_cost_of_some (rotateRun move.direction) move.position s t 4
      (rotateRun_cost_of_some move.direction) returned

private theorem applyAtRotate_cost_le (d : RotationDirection) (p : List Branch)
    (s : BinaryTree α) : (applyAtRun (rotateRun d) p s).2 ≤ 3 * s.numNodes + 3 := by
  induction p generalizing s with
  | nil =>
      cases s with
      | nil => simp only [applyAtRun_root, rotateRun_nil, BinaryTree.numNodes]; decide
      | node a l r =>
          have bound := rotateRun_cost_le d (.node a l r)
          simp only [applyAtRun_root, BinaryTree.numNodes]
          omega
  | cons branch p ih =>
      cases s with
      | nil => simp only [applyAtRun_nil_cons, BinaryTree.numNodes]; decide
      | node a l r =>
          cases branch with
          | left =>
              have bound := ih l
              simp only [applyAtRun_left, BinaryTree.numNodes]
              cases child : (applyAtRun (rotateRun d) p l).1 <;> dsimp <;> omega
          | right =>
              have bound := ih r
              simp only [applyAtRun_right, BinaryTree.numNodes]
              cases child : (applyAtRun (rotateRun d) p r).1 <;> dsimp <;> omega

/-- Includes arbitrary overlong positions, which stop when a node is missing. -/
theorem applyMoveRun_cost_le (move : RotationMove) (s : BinaryTree α) :
    (applyMoveRun move s).2 ≤ 3 * s.numNodes + 3 :=
  applyAtRotate_cost_le move.direction move.position s

theorem applyMoveRun_numNodes (move : RotationMove) (s t : BinaryTree α)
    (returned : (applyMoveRun move s).1 = some t) : t.numNodes = s.numNodes :=
  Trees.Rotations.numNodes_eq_of_inorder_eq
    (Trees.Rotations.applyMove?_inorder move ((applyMoveRun_value move s).symm.trans returned))

theorem applyMoveRun_undo (move : RotationMove) (s t : BinaryTree α)
    (returned : (applyMoveRun move s).1 = some t) :
    (applyMoveRun move.opposite t).1 = some s := by
  rw [applyMoveRun_value]
  exact Trees.Rotations.applyMove?_undo move ((applyMoveRun_value move s).symm.trans returned)

/-- Compare left first, returning the actual right result only after left success. -/
def eqTreeRun : BinaryTree Unit → BinaryTree Unit → Measured Bool Nat
  | .nil, .nil => (true, 2)
  | .node _ l r, .node _ l' r' =>
      CallCount.tick (bind (eqTreeRun l l') (fun equal =>
        if equal then eqTreeRun r r' else (false, 1)))
  | _, _ => (false, 2)

@[simp] theorem eqTreeRun_nil_nil : eqTreeRun .nil .nil = (true, 2) := rfl
@[simp] theorem eqTreeRun_nil_node (l r : BinaryTree Unit) :
    eqTreeRun .nil (.node () l r) = (false, 2) := rfl
@[simp] theorem eqTreeRun_node_nil (l r : BinaryTree Unit) :
    eqTreeRun (.node () l r) .nil = (false, 2) := rfl

theorem eqTreeRun_node (l r l' r' : BinaryTree Unit) :
    eqTreeRun (.node () l r) (.node () l' r') =
      if (eqTreeRun l l').1 then
        ((eqTreeRun r r').1, (eqTreeRun l l').2 + (eqTreeRun r r').2 + 1)
      else (false, (eqTreeRun l l').2 + 2) := by
  simp only [eqTreeRun, CallCount.tick, bind]
  split <;> rfl

theorem eqTreeRun_of_left_false (l r l' r' : BinaryTree Unit)
    (left : (eqTreeRun l l').1 = false) :
    eqTreeRun (.node () l r) (.node () l' r') = (false, (eqTreeRun l l').2 + 2) := by
  rw [eqTreeRun_node, left]
  rfl

theorem eqTreeRun_value (s t : BinaryTree Unit) :
    (eqTreeRun s t).1 = decide (s = t) := by
  induction s generalizing t with
  | nil => cases t <;> rfl
  | node a l r ihl ihr =>
      cases a
      cases t with
      | nil => rfl
      | node b l' r' =>
          cases b
          rw [eqTreeRun_node]
          by_cases left : l = l'
          · subst l'
            simp [ihl, ihr]
          · simp [ihl, left]

/-- Work is bounded by the source size even when the target is much larger. -/
theorem eqTreeRun_cost_le (s t : BinaryTree Unit) :
    (eqTreeRun s t).2 ≤ 3 * s.numNodes + 2 := by
  induction s generalizing t with
  | nil => cases t <;> exact Nat.le_refl 2
  | node a l r ihl ihr =>
      cases a
      cases t with
      | nil => simp only [eqTreeRun_node_nil, BinaryTree.numNodes]; omega
      | node b l' r' =>
          cases b
          have left := ihl l'
          have right := ihr r'
          rw [eqTreeRun_node]
          simp only [BinaryTree.numNodes]
          split <;> dsimp <;> omega

theorem eqTreeRun_self_cost (t : BinaryTree Unit) :
    (eqTreeRun t t).2 = 3 * t.numNodes + 2 := by
  induction t with
  | nil => rfl
  | node a l r ihl ihr =>
      cases a
      have same : (eqTreeRun l l).1 = true :=
        (eqTreeRun_value l l).trans (decide_eq_true rfl)
      rw [eqTreeRun_node, same]
      change (eqTreeRun l l).2 + (eqTreeRun r r).2 + 1 =
        3 * (l.numNodes + r.numNodes + 1) + 2
      omega

end Resources.RotationCertificate
