import Applications.Matroid.Presentations

/-! # Finite matroids from submodular rank

The cardinality bound and submodularity derive the local increment laws used by
`RankPresentation`. Both presentations recover the same labelled matroid.
-/
set_option autoImplicit false
set_option warningAsError true

open Set

namespace Applications.Matroid

/-- Natural-valued submodular rank on a finite labelled ground, normalized on all
ambient subsets. The cardinality bound uses the ground portion even when the
ambient set is infinite. -/
structure SubmodularRankPresentation (α : Type*) where
  ground : Set α
  finite_ground : ground.Finite
  rank : Set α → ℕ
  empty : rank ∅ = 0
  inter_ground : ∀ X, rank (X ∩ ground) = rank X
  mono : Monotone rank
  rank_le : ∀ X, rank X ≤ (X ∩ ground).ncard
  submodular : ∀ X Y, rank (X ∩ Y) + rank (X ∪ Y) ≤ rank X + rank Y

namespace SubmodularRankPresentation
variable {α : Type*} (R : SubmodularRankPresentation α)

@[ext] theorem ext {S : SubmodularRankPresentation α}
    (hground : R.ground = S.ground) (hrank : R.rank = S.rank) : R = S := by
  cases R
  cases S
  cases hground
  cases hrank
  rfl

/-- Submodularity and the singleton cardinality bound give unit increments. -/
theorem insert_le (e : α) (X : Set α) : R.rank (insert e X) ≤ R.rank X + 1 := by
  have h := R.submodular X {e}
  have hs := (R.rank_le {e}).trans (ncard_singleton_inter e R.ground)
  rw [union_singleton] at h
  omega

/-- Zero increments persist under inclusion, by submodularity. -/
theorem persist {X Y : Set α} {e : α} (hXY : X ⊆ Y)
    (h : R.rank (insert e X) = R.rank X) : R.rank (insert e Y) = R.rank Y := by
  by_cases he : e ∈ Y
  · rw [insert_eq_of_mem he]
  have hi : insert e X ∩ Y = X := by
    ext x
    simp only [mem_inter_iff, mem_insert_iff]
    constructor
    · rintro ⟨rfl | hx, hy⟩
      · exact False.elim (he hy)
      · exact hx
    · intro hx
      exact ⟨Or.inr hx, hXY hx⟩
  have hu : insert e X ∪ Y = insert e Y := by rw [insert_union, union_eq_self_of_subset_left hXY]
  have hs := R.submodular (insert e X) Y
  rw [hi, hu, h] at hs
  have hm := R.mono (subset_insert e Y)
  omega

/-- Construct the existing local-rank presentation without extra exchange premises. -/
def toRank : RankPresentation α where
  ground := R.ground
  finite_ground := R.finite_ground
  rank := R.rank
  empty := R.empty
  inter_ground := R.inter_ground
  mono := R.mono
  insert_le := R.insert_le
  persist := R.persist

noncomputable def matroid : _root_.Matroid α := R.toRank.matroid
instance : R.matroid.Finite := R.toRank.instFiniteMatroid

@[simp] theorem matroid_ground : R.matroid.E = R.ground := rfl
@[simp] theorem matroid_eRk (X : Set α) : R.matroid.eRk X = R.rank X := R.toRank.matroid_eRk X

private theorem native_ne_top (M : _root_.Matroid α) [M.Finite] (X : Set α) :
    M.eRk X ≠ ⊤ := _root_.Matroid.eRk_ne_top_iff.mpr (M.isRkFinite_set X)

/-- Every finite native matroid supplies the standard rank axioms. -/
noncomputable def ofMatroid (M : _root_.Matroid α) [M.Finite] :
    SubmodularRankPresentation α where
  ground := M.E
  finite_ground := M.ground_finite
  rank := fun X ↦ (M.eRk X).toNat
  empty := by simp
  inter_ground := fun X ↦ by rw [M.eRk_inter_ground]
  mono := (RankPresentation.ofMatroid M).mono
  rank_le := by
    intro X
    have h := M.eRk_le_encard (X ∩ M.E)
    rw [M.eRk_inter_ground, ← (M.ground_finite.subset inter_subset_right).cast_ncard_eq] at h
    simpa using ENat.toNat_le_toNat h (by simp)
  submodular := by
    intro X Y
    have h := ENat.toNat_le_toNat (M.eRk_inter_add_eRk_union_le X Y)
      (show M.eRk X + M.eRk Y ≠ ⊤ by simp)
    simpa only [ENat.toNat_add (native_ne_top M _) (native_ne_top M _)] using h

@[simp] theorem ofMatroid_toRank (M : _root_.Matroid α) [M.Finite] :
    (ofMatroid M).toRank = RankPresentation.ofMatroid M := rfl

@[simp] theorem ofMatroid_matroid (M : _root_.Matroid α) [M.Finite] :
    (ofMatroid M).matroid = M := RankPresentation.ofMatroid_matroid M

@[simp] theorem matroid_ofMatroid : ofMatroid R.matroid = R := by
  apply ext (ofMatroid R.matroid) (S := R) rfl
  funext X
  change (R.matroid.eRk X).toNat = R.rank X
  rw [R.matroid_eRk, ENat.toNat_natCast]

/-- The familiar submodular and local-increment axiom systems are interchangeable. -/
noncomputable def rankEquiv : SubmodularRankPresentation α ≃ RankPresentation α where
  toFun := toRank
  invFun P := ofMatroid P.matroid
  left_inv := matroid_ofMatroid
  right_inv P := by rw [ofMatroid_toRank, P.matroid_ofMatroid]

/-- Relabel the entire ambient carrier while retaining the ground and all ranks. -/
noncomputable def relabel {β : Type*} (f : α ≃ β) : SubmodularRankPresentation β :=
  ofMatroid (R.matroid.mapEquiv f)

@[simp] theorem relabel_matroid {β : Type*} (f : α ≃ β) :
    (R.relabel f).matroid = R.matroid.mapEquiv f := ofMatroid_matroid _

@[simp] theorem relabel_ground {β : Type*} (f : α ≃ β) :
    (R.relabel f).ground = f '' R.ground := rfl

@[simp] theorem relabel_rank {β : Type*} (f : α ≃ β) (X : Set α) :
    (R.relabel f).rank (f '' X) = R.rank X := by
  change ((R.matroid.mapEquiv f).eRk (f '' X)).toNat = _
  rw [Applications.Matroid.relabel_rank, R.matroid_eRk, ENat.toNat_natCast]

/-- Evaluate on arbitrary target subsets, not only explicitly written images. -/
theorem rank_relabel {β : Type*} (f : α ≃ β) (Y : Set β) :
    (R.relabel f).rank Y = R.rank (f.symm '' Y) := by
  simpa only [Equiv.image_symm_image] using R.relabel_rank f (f.symm '' Y)

@[simp] theorem relabel_refl : R.relabel (Equiv.refl α) = R := by
  apply ext (R.relabel (Equiv.refl α)) (S := R)
  · simp
  · funext X
    simp [rank_relabel]

/-- Successive carrier changes agree on the entire presentation. -/
theorem relabel_trans {β γ : Type*} (f : α ≃ β) (g : β ≃ γ) :
    (R.relabel f).relabel g = R.relabel (f.trans g) := by
  apply ext ((R.relabel f).relabel g) (S := R.relabel (f.trans g))
  · simp [image_image]
  · funext X
    simp [rank_relabel, image_image]

end SubmodularRankPresentation

namespace FiniteMatroid
variable {α : Type*}

/-- Submodular ranks join the existing presentation hub and its route-agreement law. -/
noncomputable def submodularRankEquiv : FiniteMatroid α ≃ SubmodularRankPresentation α :=
  rankEquiv.trans SubmodularRankPresentation.rankEquiv.symm

end FiniteMatroid
end Applications.Matroid
