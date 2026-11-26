import Applications.Trees.HeightBalance.SetRefinement
import Applications.Search.IntervalTree.Search
import Applications.Search.IntervalSet.Contract

/-!
# Balanced interval trees with complete height and maximum annotations

The existing height-balanced rotations and updates maintain both coordinates
through their local smart constructor. The maximum-only projection is used in
proofs; the executable overlap query reads the product tree directly and follows
one branch. Source correspondence: `docs/research/fdsa-balanced-interval-tree.md`.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.IntervalTree.Balanced
universe u v
variable {α : Type u} {κ : Type v}

/-- Forget stored heights, retaining the shape, keys and even malformed maxima. -/
def maximumTree (t : BinaryTree (κ × (Nat × α))) : BinaryTree (κ × α) :=
  t.map (fun binding => (binding.1, binding.2.2))

@[simp] theorem maximumTree_nil :
    maximumTree (.nil : BinaryTree (κ × (Nat × α))) = .nil := rfl

@[simp] theorem maximumTree_node (a : κ) (h : Nat) (m : α)
    (l r : BinaryTree (κ × (Nat × α))) :
    maximumTree (.node (a, (h, m)) l r) =
      .node (a, m) (maximumTree l) (maximumTree r) := rfl

@[simp] theorem erase_maximumTree (t : BinaryTree (κ × (Nat × α))) :
    Trees.Cached.erase (maximumTree t) = Trees.Cached.erase t := by
  unfold Trees.Cached.erase maximumTree
  rw [← BinaryTree.comp_map]
  rfl

theorem maximumTree_eq_nil_iff (t : BinaryTree (κ × (Nat × α))) :
    maximumTree t = .nil ↔ t = .nil := by
  cases t <;> simp [maximumTree, BinaryTree.map]

/-- Read just the stored maximum; the empty-tree value is the endpoint bottom. -/
def maxHi [Bot α] (t : BinaryTree (κ × (Nat × α))) : α :=
  (Trees.Cached.read (0, ⊥) t).2

@[simp] theorem maxHi_nil [Bot α] :
    maxHi (.nil : BinaryTree (κ × (Nat × α))) = ⊥ := rfl

@[simp] theorem maxHi_node [Bot α] (a : κ) (h : Nat) (m : α)
    (l r : BinaryTree (κ × (Nat × α))) :
    maxHi (.node (a, (h, m)) l r) = m := rfl

@[simp] theorem maxHi_maximumTree [Bot α] (t : BinaryTree (κ × (Nat × α))) :
    IntervalTree.maxHi (maximumTree t) = maxHi t := by
  cases t <;> rfl

section Annotation
variable [LE α] [Max α] [Bot α]

/-- The complete algebra used by the existing local balancing programs. -/
def annotation (iv : κ → IntervalKey α) : Trees.HeightBalance.HeightAnnotation κ (Nat × α) where
  empty := (0, ⊥)
  combine l a r := (max l.1 r.1 + 1, IntervalTree.combine iv l.2 a r.2)
  height := Prod.fst
  height_empty := rfl
  height_combine _ _ _ := rfl

theorem maximumTree_node_smart (iv : κ → IntervalKey α)
    (l : BinaryTree (κ × (Nat × α))) (a : κ) (r : BinaryTree (κ × (Nat × α))) :
    maximumTree (Trees.HeightBalance.node (annotation iv) l a r) =
      IntervalTree.node iv (maximumTree l) a (maximumTree r) := by
  change BinaryTree.node (a, IntervalTree.combine iv (maxHi l) a (maxHi r))
    (maximumTree l) (maximumTree r) = _
  simp only [IntervalTree.node_eq, IntervalTree.max3, maxHi_maximumTree]

/-- Complete annotation validity supplies the maximum invariant at every node. -/
theorem cacheValid_maximumTree (iv : κ → IntervalKey α)
    {t : BinaryTree (κ × (Nat × α))}
    (valid : Trees.HeightBalance.CacheValid (annotation iv) t) :
    IntervalTree.CacheValid iv (maximumTree t) := by
  induction t with
  | nil => exact IntervalTree.cacheValid_nil iv
  | node binding l r ihl ihr =>
      rcases binding with ⟨a, h, m⟩
      rcases (Trees.HeightBalance.cacheValid_node (annotation iv) a (h, m) l r).mp valid
        with ⟨hl, hr, equation⟩
      apply (IntervalTree.cacheValid_node iv a m (maximumTree l) (maximumTree r)).mpr
      refine ⟨ihl hl, ihr hr, ?_⟩
      simpa only [annotation, IntervalTree.max3, maxHi_maximumTree, maxHi] using
        congrArg Prod.snd equation

/-- The selected AVL implementation is the existing tolerance-one update program. -/
abbrev deleteOps [LT κ] [DecidableLT κ] (iv : κ → IntervalKey α) :
    AbstractSet.DeleteOps κ (BinaryTree (κ × (Nat × α))) :=
  Trees.HeightBalance.deleteOps (annotation iv) 1

/-- Actual shape balance, complete annotation validity, and strict key ordering. -/
abbrev Valid [LT κ] (iv : κ → IntervalKey α) (t : BinaryTree (κ × (Nat × α))) : Prop :=
  Trees.HeightBalance.SetValid (annotation iv) 1 t

/-- All seven ordinary set laws are inherited without re-proving rotations. -/
theorem setLaws [LinearOrder κ] (iv : κ → IntervalKey α) :
    AbstractSet.DeleteLaws (deleteOps iv)
      (fun t => Trees.setTree (Trees.Cached.erase t)) (Valid iv) :=
  Trees.HeightBalance.setLaws (annotation iv) 1 (by decide)

end Annotation

section RawSearch
variable [LE α] [Bot α] [DecidableLE α]

/-- Direct one-branch query; no tree projection is executed. -/
def search (iv : κ → IntervalKey α) : BinaryTree (κ × (Nat × α)) → IntervalKey α → Bool
  | .nil, _ => false
  | .node (a, _) l r, query =>
      if IntervalKey.Overlap query (iv a) then true
      else match l with
        | .nil => search iv r query
        | .node _ _ _ =>
            if query.low ≤ maxHi l then search iv l query else search iv r query

@[simp] theorem search_nil (iv : κ → IntervalKey α) (query : IntervalKey α) :
    search iv .nil query = false := rfl

/-- The raw programs agree even when height, maximum or ordering is malformed. -/
theorem search_eq (iv : κ → IntervalKey α) (t : BinaryTree (κ × (Nat × α)))
    (query : IntervalKey α) :
    search iv t query = IntervalTree.search iv (maximumTree t) query := by
  induction t with
  | nil => rfl
  | node binding l r ihl ihr =>
      rcases binding with ⟨a, h, m⟩
      cases l with
      | nil =>
          change (if IntervalKey.Overlap query (iv a) then true else search iv r query) =
            (if IntervalKey.Overlap query (iv a) then true
              else IntervalTree.search iv (maximumTree r) query)
          rw [ihr]
      | node binding ll lr =>
          rcases binding with ⟨b, hl, ml⟩
          change (if IntervalKey.Overlap query (iv a) then true
            else if query.low ≤ ml then search iv (.node (b, (hl, ml)) ll lr) query
              else search iv r query) =
            (if IntervalKey.Overlap query (iv a) then true
              else if query.low ≤ ml then
                IntervalTree.search iv (maximumTree (.node (b, (hl, ml)) ll lr)) query
                else IntervalTree.search iv (maximumTree r) query)
          rw [ihl, ihr]

/-- A returned hit supplies an original key, with no invariant hypotheses. -/
theorem search_sound (iv : κ → IntervalKey α) {t : BinaryTree (κ × (Nat × α))}
    {query : IntervalKey α} (found : search iv t query = true) :
    ∃ a ∈ Trees.setTree (Trees.Cached.erase t), IntervalKey.Overlap (iv a) query := by
  rw [search_eq] at found
  simpa only [erase_maximumTree] using IntervalTree.search_sound iv found

end RawSearch

section Correctness
variable [LinearOrder α] [OrderBot α]

/-- Attainment and upper bounds need valid maxima, independently of stored heights. -/
theorem maxHi_spec (iv : κ → IntervalKey α) {t : BinaryTree (κ × (Nat × α))}
    (valid : IntervalTree.CacheValid iv (maximumTree t)) (nonempty : t ≠ .nil) :
    (∃ a ∈ Trees.setTree (Trees.Cached.erase t), (iv a).high = maxHi t) ∧
      ∀ a ∈ Trees.setTree (Trees.Cached.erase t), (iv a).high ≤ maxHi t := by
  have ne : maximumTree t ≠ .nil := fun h => nonempty ((maximumTree_eq_nil_iff t).mp h)
  simpa only [erase_maximumTree, maxHi_maximumTree] using IntervalTree.maxHi_spec iv valid ne

/-- Maximum validity and weak low order suffice; no height or key-order premise. -/
theorem search_correct (iv : κ → IntervalKey α) {t : BinaryTree (κ × (Nat × α))}
    (valid : IntervalTree.CacheValid iv (maximumTree t))
    (ordered : (Trees.inorder (Trees.Cached.erase t)).Pairwise
      (fun a b => (iv a).low ≤ (iv b).low)) (query : IntervalKey α) :
    search iv t query = true ↔
      ∃ a ∈ Trees.setTree (Trees.Cached.erase t), IntervalKey.Overlap (iv a) query := by
  rw [search_eq]
  have ordered' : IntervalTree.LowOrdered iv (maximumTree t) := by
    simpa only [IntervalTree.LowOrdered, erase_maximumTree] using ordered
  simpa only [erase_maximumTree] using IntervalTree.search_correct iv valid ordered' query

theorem search_correct_of_strict [LT κ] (iv : κ → IntervalKey α)
    (compatible : ∀ a b, a < b → (iv a).low ≤ (iv b).low)
    {t : BinaryTree (κ × (Nat × α))}
    (valid : IntervalTree.CacheValid iv (maximumTree t))
    (strict : (Trees.inorder (Trees.Cached.erase t)).Pairwise (· < ·))
    (query : IntervalKey α) :
    search iv t query = true ↔
      ∃ a ∈ Trees.setTree (Trees.Cached.erase t), IntervalKey.Overlap (iv a) query :=
  search_correct iv valid (strict.imp (fun h => compatible _ _ h)) query

/-- Complete balanced set semantics, including overlap of noninjective images. -/
theorem intervalSetLaws [LinearOrder κ] (iv : κ → IntervalKey α)
    (compatible : ∀ a b, a < b → (iv a).low ≤ (iv b).low) :
    IntervalSet.Laws (deleteOps iv) (search iv) iv
      (fun t => Trees.setTree (Trees.Cached.erase t)) (Valid iv) where
  toDeleteLaws := setLaws iv
  overlap t valid query :=
    (search_correct_of_strict iv compatible (cacheValid_maximumTree iv valid.1.2)
      valid.2 query).trans
      (IntervalSet.hasOverlap_image_iff iv (Trees.setTree (Trees.Cached.erase t)) query).symm

end Correctness
end Search.IntervalTree.Balanced
