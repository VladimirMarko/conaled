import Applications.Trees.Cached

/-! A source maximum cache stores a raw annotation at each nonempty node.
The reader and smart constructor act locally on that representation. Explicit
adapters connect it to the existing optional-summary cache, whose validity
and fold laws supply correctness. No order laws are needed in this module;
greatest-element semantics belongs to MaximumCacheObservations.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Trees.MaximumCache
universe u
variable {α : Type u}

/-- Read only the constructor and the root's raw annotation. -/
def mx : BinaryTree (α × α) → Option α
  | .nil => none
  | .node (_, b) _ _ => some b

@[simp] theorem mx_nil : mx (.nil : BinaryTree (α × α)) = none := rfl

@[simp] theorem mx_node (a b : α) (l r : BinaryTree (α × α)) :
    mx (.node (a, b) l r) = some b := rfl

/-- Nonempty raw caches always return a stored value, even when invalid. -/
theorem mx_eq_none_iff (t : BinaryTree (α × α)) : mx t = none ↔ t = .nil := by
  cases t <;> simp [mx]

/-- Embed each raw annotation as a present optional annotation. -/
def lift (t : BinaryTree (α × α)) : BinaryTree (α × Option α) :=
  t.map (fun ab => (ab.1, some ab.2))

/-- The fallback is the node's own key, never an invented default label. -/
def project (t : BinaryTree (α × Option α)) : BinaryTree (α × α) :=
  t.map (fun ab => (ab.1, ab.2.getD ab.1))

@[simp] theorem lift_nil : lift (.nil : BinaryTree (α × α)) = .nil := rfl

@[simp] theorem lift_node (a b : α) (l r : BinaryTree (α × α)) :
    lift (.node (a, b) l r) = .node (a, some b) (lift l) (lift r) := rfl

@[simp] theorem project_nil : project (.nil : BinaryTree (α × Option α)) = .nil := rfl

@[simp] theorem project_node (a : α) (b : Option α)
    (l r : BinaryTree (α × Option α)) :
    project (.node (a, b) l r) = .node (a, b.getD a) (project l) (project r) := rfl

theorem project_lift (t : BinaryTree (α × α)) : project (lift t) = t := by
  unfold project lift
  rw [← BinaryTree.comp_map]
  exact BinaryTree.id_map t

theorem erase_lift (t : BinaryTree (α × α)) :
    Cached.erase (lift t) = Cached.erase t := by
  unfold Cached.erase lift
  rw [← BinaryTree.comp_map]
  rfl

theorem erase_project (t : BinaryTree (α × Option α)) :
    Cached.erase (project t) = Cached.erase t := by
  unfold Cached.erase project
  rw [← BinaryTree.comp_map]
  rfl

theorem read_lift (t : BinaryTree (α × α)) : Cached.read none (lift t) = mx t := by
  cases t <;> rfl

section Max
variable [Max α]

/-- Start with the actual key, then incorporate each present child summary. -/
def localMax (l : Option α) (a : α) (r : Option α) : α :=
  let leftMax := l.elim a (max a)
  r.elim leftMax (max leftMax)

def combine (l : Option α) (a : α) (r : Option α) : Option α :=
  some (localMax l a r)

/-- An independent key fold; no stored annotations are consulted. -/
def summary (t : BinaryTree α) : Option α := Trees.fold none combine t

@[simp] theorem summary_nil : summary (.nil : BinaryTree α) = none := rfl

@[simp] theorem summary_node (a : α) (l r : BinaryTree α) :
    summary (.node a l r) = combine (summary l) a (summary r) := rfl

/-- Read the two child roots and construct one raw annotated root. -/
def nodeMx (l : BinaryTree (α × α)) (a : α) (r : BinaryTree (α × α)) :
    BinaryTree (α × α) := .node (a, localMax (mx l) a (mx r)) l r

@[simp] theorem mx_nodeMx (l : BinaryTree (α × α)) (a : α)
    (r : BinaryTree (α × α)) :
    mx (nodeMx l a r) = combine (mx l) a (mx r) := rfl

theorem erase_nodeMx (l : BinaryTree (α × α)) (a : α)
    (r : BinaryTree (α × α)) :
    Cached.erase (nodeMx l a r) = .node a (Cached.erase l) (Cached.erase r) := rfl

/-- Every stored maximum must satisfy the local equation, including descendants. -/
def Valid : BinaryTree (α × α) → Prop
  | .nil => True
  | .node (a, b) l r =>
      Valid l ∧ Valid r ∧ b = localMax (mx l) a (mx r)

@[simp] theorem valid_nil : Valid (.nil : BinaryTree (α × α)) := trivial

@[simp] theorem valid_node (a b : α) (l r : BinaryTree (α × α)) :
    Valid (.node (a, b) l r) ↔
      Valid l ∧ Valid r ∧ b = localMax (mx l) a (mx r) := Iff.rfl

theorem lift_nodeMx (l : BinaryTree (α × α)) (a : α)
    (r : BinaryTree (α × α)) :
    lift (nodeMx l a r) = Cached.smartNode none combine (lift l) a (lift r) := by
  simp only [nodeMx, lift_node, Cached.smartNode, read_lift, combine]

/-- Representation transport, independent of any greatest-element law. -/
theorem valid_iff_valid_lift (t : BinaryTree (α × α)) :
    Valid t ↔ Cached.Valid none combine (lift t) := by
  induction t with
  | nil => rfl
  | node ab l r ihl ihr =>
      rcases ab with ⟨a, b⟩
      simp only [valid_node, lift_node, Cached.valid_node, read_lift, combine,
        Option.some.injEq, ihl, ihr]

/-- Generic constructor validity transports back to the raw representation. -/
theorem nodeMx_valid_iff (l : BinaryTree (α × α)) (a : α)
    (r : BinaryTree (α × α)) : Valid (nodeMx l a r) ↔ Valid l ∧ Valid r := by
  rw [valid_iff_valid_lift, lift_nodeMx, Cached.smartNode_valid_iff,
    ← valid_iff_valid_lift, ← valid_iff_valid_lift]

theorem nodeMx_valid (l : BinaryTree (α × α)) (a : α)
    (r : BinaryTree (α × α)) (hl : Valid l) (hr : Valid r) :
    Valid (nodeMx l a r) := (nodeMx_valid_iff l a r).mpr ⟨hl, hr⟩

/-- Use the generic cached-fold theorem instead of another correctness induction. -/
theorem mx_eq_summary (t : BinaryTree (α × α)) (ht : Valid t) :
    mx t = summary (Cached.erase t) := by
  calc
    mx t = Cached.read none (lift t) := (read_lift t).symm
    _ = Trees.fold none combine (Cached.erase (lift t)) :=
      Cached.read_eq_fold none combine _ ((valid_iff_valid_lift t).mp ht)
    _ = summary (Cached.erase t) := by rw [erase_lift]; rfl

/-- Generic validity is sufficient for this inverse law, not necessary. -/
theorem lift_project (t : BinaryTree (α × Option α))
    (ht : Cached.Valid none combine t) : lift (project t) = t := by
  induction t with
  | nil => rfl
  | node ab l r ihl ihr =>
      rcases ab with ⟨a, b⟩
      rcases ht with ⟨hl, hr, hb⟩
      have hb_some : some (b.getD a) = b := by
        rw [hb]
        rfl
      change BinaryTree.node (a, some (b.getD a)) (lift (project l)) (lift (project r)) =
        BinaryTree.node (a, b) l r
      rw [hb_some, ihl hl, ihr hr]

theorem project_valid (t : BinaryTree (α × Option α))
    (ht : Cached.Valid none combine t) : Valid (project t) := by
  apply (valid_iff_valid_lift _).mpr
  rw [lift_project t ht]
  exact ht

theorem mx_project (t : BinaryTree (α × Option α))
    (ht : Cached.Valid none combine t) : mx (project t) = Cached.read none t := by
  rw [← read_lift, lift_project t ht]

/-- A full generic annotation pass followed by a full representation projection.
This client makes no one-pass or local-work claim. -/
def annotate (t : BinaryTree α) : BinaryTree (α × α) :=
  project (Cached.annotate none combine t)

theorem annotate_valid (t : BinaryTree α) : Valid (annotate t) :=
  project_valid _ (Cached.annotate_valid none combine t)

theorem erase_annotate (t : BinaryTree α) : Cached.erase (annotate t) = t :=
  (erase_project _).trans (Cached.erase_annotate none combine t)

theorem mx_annotate (t : BinaryTree α) : mx (annotate t) = summary t :=
  (mx_project _ (Cached.annotate_valid none combine t)).trans
    (Cached.read_annotate none combine t)

theorem lift_annotate (t : BinaryTree α) :
    lift (annotate t) = Cached.annotate none combine t :=
  lift_project _ (Cached.annotate_valid none combine t)

end Max
end Trees.MaximumCache
