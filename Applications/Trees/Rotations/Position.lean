import Applications.Trees.Rotations.Basic

/-!
# Partial subtree edits and sequential rotation traces

An empty path calls the callback even at an empty tree. Nonempty paths must
traverse nodes. Each schedule position is interpreted in the preceding result;
`List.foldlM` supplies the ordinary sequential interpreter and failure behavior.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.Rotations
open Search.SharedTree (Branch)
universe u
variable {α : Type u}

/-- Apply a partial edit at a position, retaining all unselected constructors. -/
def applyAt? (f : BinaryTree α → Option (BinaryTree α)) :
    List Branch → BinaryTree α → Option (BinaryTree α)
  | [], t => f t
  | _ :: _, .nil => none
  | .left :: p, .node a l r => (applyAt? f p l).map (fun l' => .node a l' r)
  | .right :: p, .node a l r => (applyAt? f p r).map (fun r' => .node a l r')

@[simp] theorem applyAt?_root (f : BinaryTree α → Option (BinaryTree α))
    (t : BinaryTree α) : applyAt? f [] t = f t := rfl

@[simp] theorem applyAt?_nil_cons (f : BinaryTree α → Option (BinaryTree α))
    (d : Branch) (p : List Branch) : applyAt? f (d :: p) .nil = none := rfl

@[simp] theorem applyAt?_left (f : BinaryTree α → Option (BinaryTree α))
    (p : List Branch) (a : α) (l r : BinaryTree α) :
    applyAt? f (.left :: p) (.node a l r) =
      (applyAt? f p l).map (fun l' => .node a l' r) := rfl

@[simp] theorem applyAt?_right (f : BinaryTree α → Option (BinaryTree α))
    (p : List Branch) (a : α) (l r : BinaryTree α) :
    applyAt? f (.right :: p) (.node a l r) =
      (applyAt? f p r).map (fun r' => .node a l r') := rfl

/-- The first position acts on the current tree, then the tail acts on its result. -/
def applyAts? (f : BinaryTree α → Option (BinaryTree α))
    (ps : List (List Branch)) (t : BinaryTree α) : Option (BinaryTree α) :=
  ps.foldlM (fun current p => applyAt? f p current) t

@[simp] theorem applyAts?_nil (f : BinaryTree α → Option (BinaryTree α))
    (t : BinaryTree α) : applyAts? f [] t = some t := rfl

@[simp] theorem applyAts?_cons (f : BinaryTree α → Option (BinaryTree α))
    (p : List Branch) (ps : List (List Branch)) (t : BinaryTree α) :
    applyAts? f (p :: ps) t = (applyAt? f p t).bind (applyAts? f ps) := rfl

/-- The action law is unconditional, including failure of either component. -/
theorem applyAts?_append (f : BinaryTree α → Option (BinaryTree α))
    (ps qs : List (List Branch)) (t : BinaryTree α) :
    applyAts? f (ps ++ qs) t = (applyAts? f ps t).bind (applyAts? f qs) := by
  exact List.foldlM_append

/-- Lift an arbitrary partial callback schedule beneath a right child. -/
theorem applyAts?_map_right (f : BinaryTree α → Option (BinaryTree α))
    (ps : List (List Branch)) (a : α) (l r : BinaryTree α) :
    applyAts? f (ps.map (Branch.right :: ·)) (.node a l r) =
      (applyAts? f ps r).map (fun r' => .node a l r') := by
  induction ps generalizing r with
  | nil => rfl
  | cons p ps ih =>
      cases h : applyAt? f p r with
      | none => simp [h]
      | some r' => simp [h, ih]

theorem applyAt?_inorder (f : BinaryTree α → Option (BinaryTree α))
    (preserve : ∀ {s t : BinaryTree α}, f s = some t → inorder t = inorder s)
    (p : List Branch) {s t : BinaryTree α} (h : applyAt? f p s = some t) :
    inorder t = inorder s := by
  induction p generalizing s t with
  | nil => exact preserve h
  | cons d p ih =>
      cases s with
      | nil => simp at h
      | node a l r =>
          cases d with
          | left =>
              cases hs : applyAt? f p l with
              | none => simp [hs] at h
              | some l' =>
                  simp only [applyAt?_left, hs, Option.map_some, Option.some.injEq] at h
                  subst t
                  simp only [inorder_node, ih hs]
          | right =>
              cases hs : applyAt? f p r with
              | none => simp [hs] at h
              | some r' =>
                  simp only [applyAt?_right, hs, Option.map_some, Option.some.injEq] at h
                  subst t
                  simp only [inorder_node, ih hs]

theorem applyAts?_inorder (f : BinaryTree α → Option (BinaryTree α))
    (preserve : ∀ {s t : BinaryTree α}, f s = some t → inorder t = inorder s)
    (ps : List (List Branch)) {s t : BinaryTree α} (h : applyAts? f ps s = some t) :
    inorder t = inorder s := by
  induction ps generalizing s t with
  | nil => cases h; rfl
  | cons p ps ih =>
      cases hs : applyAt? f p s with
      | none => simp [hs] at h
      | some s' =>
          simp only [applyAts?_cons, hs, Option.bind_some] at h
          exact (ih h).trans (applyAt?_inorder f preserve p hs)

/-- Pointwise partial inverse laws lift through every successfully traversed path. -/
theorem applyAt?_undo (f g : BinaryTree α → Option (BinaryTree α))
    (undo : ∀ {s t : BinaryTree α}, f s = some t → g t = some s)
    (p : List Branch) {s t : BinaryTree α} (h : applyAt? f p s = some t) :
    applyAt? g p t = some s := by
  induction p generalizing s t with
  | nil => exact undo h
  | cons d p ih =>
      cases s with
      | nil => simp at h
      | node a l r =>
          cases d with
          | left =>
              cases hs : applyAt? f p l with
              | none => simp [hs] at h
              | some l' =>
                  simp only [applyAt?_left, hs, Option.map_some, Option.some.injEq] at h
                  subst t
                  simp only [applyAt?_left, ih hs, Option.map_some]
          | right =>
              cases hs : applyAt? f p r with
              | none => simp [hs] at h
              | some r' =>
                  simp only [applyAt?_right, hs, Option.map_some, Option.some.injEq] at h
                  subst t
                  simp only [applyAt?_right, ih hs, Option.map_some]

/-- Successful traces carry sufficient information to recover the original tree. -/
theorem applyAts?_undo (f g : BinaryTree α → Option (BinaryTree α))
    (undo : ∀ {s t : BinaryTree α}, f s = some t → g t = some s)
    (ps : List (List Branch)) {s t : BinaryTree α} (h : applyAts? f ps s = some t) :
    applyAts? g ps.reverse t = some s := by
  induction ps generalizing s t with
  | nil => cases h; rfl
  | cons p ps ih =>
      cases hs : applyAt? f p s with
      | none => simp [hs] at h
      | some s' =>
          simp only [applyAts?_cons, hs, Option.bind_some] at h
          rw [List.reverse_cons, applyAts?_append, ih h]
          simp only [Option.bind_some, applyAts?_cons,
            applyAt?_undo f g undo p hs, applyAts?_nil]

theorem applyAt?_right_nil (p : List Branch) :
    applyAt? rotateRight? p (.nil : BinaryTree α) = none := by
  cases p <;> rfl

theorem no_right_rotation_of_isList {t : BinaryTree α} (h : IsList t)
    (p : List Branch) : applyAt? rotateRight? p t = none := by
  induction p generalizing t with
  | nil =>
      cases t with
      | nil => rfl
      | node a l r => rcases h with ⟨rfl, _⟩; rfl
  | cons d p ih =>
      cases t with
      | nil => rfl
      | node a l r =>
          rcases h with ⟨rfl, hr⟩
          cases d with
          | left => simp only [applyAt?_left, applyAt?_right_nil, Option.map_none]
          | right => simp only [applyAt?_right, ih hr, Option.map_none]

theorem isList_of_no_right_rotation (t : BinaryTree α)
    (h : ∀ p, applyAt? rotateRight? p t = none) : IsList t := by
  induction t with
  | nil => trivial
  | node a l r _ ihr =>
      cases l with
      | nil =>
          refine ⟨rfl, ihr ?_⟩
          intro p
          have hr := h (.right :: p)
          cases hp : applyAt? rotateRight? p r with
          | none => rfl
          | some s => simp [hp] at hr
      | node b A B =>
          have hr := h []
          simp only [applyAt?_root, rotateRight?_node] at hr
          cases hr

/-- This quantifies all positions, not just the current root. -/
theorem isList_iff_no_right_rotation (t : BinaryTree α) :
    IsList t ↔ ∀ p, applyAt? rotateRight? p t = none :=
  ⟨no_right_rotation_of_isList, isList_of_no_right_rotation t⟩

end Trees.Rotations
