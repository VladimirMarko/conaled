import Applications.Matroid.Closure
import Mathlib.Combinatorics.Matroid.Rank.ENat

/-! # Finite rank presentations via local increments

Rank is natural-valued, normalized outside the ground. A single insertion raises
rank by at most one. An insertion that raises no rank continues to raise no rank
in larger sets. These local axioms construct closure with exchange.
-/
set_option autoImplicit false
set_option warningAsError true

open Set

namespace Applications.Matroid

/-- Local rank axioms on a finite labelled ground set. -/
structure RankPresentation (α : Type*) where
  ground : Set α
  finite_ground : ground.Finite
  rank : Set α → ℕ
  empty : rank ∅ = 0
  inter_ground : ∀ X, rank (X ∩ ground) = rank X
  mono : Monotone rank
  insert_le : ∀ e X, rank (insert e X) ≤ rank X + 1
  persist : ∀ {X Y e}, X ⊆ Y → rank (insert e X) = rank X →
    rank (insert e Y) = rank Y

namespace RankPresentation
variable {α : Type*} (R : RankPresentation α)

def cl (X : Set α) : Set α := {e | e ∈ R.ground ∧ R.rank (insert e X) = R.rank X}

theorem subset_cl {X : Set α} (hX : X ⊆ R.ground) : X ⊆ R.cl X := by
  intro e he
  exact ⟨hX he, by rw [insert_eq_of_mem he]⟩

theorem cl_mono : Monotone R.cl :=
  fun _ _ h _ he ↦ ⟨he.1, R.persist h he.2⟩

theorem rank_union_eq {X S : Set α} (hS : S.Finite) (h : S ⊆ R.cl X) :
    R.rank (X ∪ S) = R.rank X := by
  induction S, hS using Set.Finite.induction_on with
  | empty => simp
  | @insert e S _ _ ih =>
    rw [union_insert, R.persist (subset_union_left : X ⊆ X ∪ S) (h (mem_insert _ _)).2]
    exact ih (fun x hx ↦ h (mem_insert_of_mem _ hx))

theorem rank_cl (X : Set α) : R.rank (R.cl X) = R.rank X := by
  have h := R.rank_union_eq (R.finite_ground.subset (fun _ h ↦ h.1)) (Subset.rfl : R.cl X ⊆ R.cl X)
  apply le_antisymm ((R.mono subset_union_right).trans h.le)
  rw [← R.inter_ground X]
  exact R.mono (fun e he ↦ ⟨he.2, by rw [insert_eq_of_mem he.1]⟩)

theorem cl_inter_ground (X : Set α) : R.cl (X ∩ R.ground) = R.cl X := by
  ext e
  simp only [cl, mem_ofPred_eq]
  apply and_congr_right
  intro he
  rw [← insert_inter_of_mem he, R.inter_ground, R.inter_ground]

/-- Rank axioms give closure axioms, including exchange. -/
def toClosure : ClosurePresentation α where
  ground := R.ground
  finite_ground := R.finite_ground
  cl := R.cl
  subset_ground := fun _ _ h ↦ h.1
  inter_ground := R.cl_inter_ground
  extensive := fun X e he ↦ ⟨he.2, by rw [insert_eq_of_mem he.1]⟩
  mono := R.cl_mono
  idempotent := by
    intro X
    rw [← R.cl_inter_ground X]
    apply Subset.antisymm
    · intro e he
      refine ⟨he.1, le_antisymm ?_ (R.mono (subset_insert _ _))⟩
      calc
        R.rank (insert e (X ∩ R.ground)) ≤ R.rank (insert e (R.cl (X ∩ R.ground))) :=
          R.mono (insert_subset_insert (R.subset_cl inter_subset_right))
        _ = R.rank (R.cl (X ∩ R.ground)) := he.2
        _ = R.rank (X ∩ R.ground) := R.rank_cl _
    · exact R.subset_cl (fun _ h ↦ h.1)
  exchange := by
    intro X x y hx
    have hxE := hx.1.1
    have hxne : R.rank (insert x X) ≠ R.rank X := fun h ↦ hx.2 ⟨hxE, h⟩
    have hxstep := R.insert_le x X
    have hxmono := R.mono (subset_insert x X)
    have hyE : y ∈ R.ground := by
      by_contra hy
      have heq : R.cl (insert y X) = R.cl X := by
        rw [← R.cl_inter_ground (insert y X), insert_inter_of_notMem hy, R.cl_inter_ground]
      exact hx.2 (heq ▸ hx.1)
    refine ⟨hyE, ?_⟩
    have hyne : R.rank (insert y X) ≠ R.rank X := by
      intro h
      have hz := R.persist (subset_insert x X) h
      rw [insert_comm] at hz
      have hm := hx.1.2
      omega
    have hystep := R.insert_le y X
    have hymono := R.mono (subset_insert y X)
    have hm := hx.1.2
    rw [insert_comm]
    omega

noncomputable def matroid : _root_.Matroid α := R.toClosure.matroid
instance : R.matroid.Finite := R.toClosure.instFiniteMatroid

@[simp] theorem matroid_ground : R.matroid.E = R.ground := rfl
@[simp] theorem matroid_closure (X : Set α) : R.matroid.closure X = R.cl X :=
  R.toClosure.matroid_closure X

/-- Agreement with native rank, including sets containing outside elements. -/
@[simp] theorem matroid_eRk (X : Set α) : R.matroid.eRk X = R.rank X := by
  have hfinite : ∀ S, S.Finite → S ⊆ R.ground → R.matroid.eRk S = R.rank S := by
    intro S hS
    induction S, hS using Set.Finite.induction_on with
    | empty => simp [R.empty]
    | @insert e S he hS ih =>
      intro hE
      have ih' := ih ((subset_insert e S).trans hE)
      by_cases h : R.rank (insert e S) = R.rank S
      · have hc : e ∈ R.matroid.closure S := by
          rw [R.matroid_closure]; exact ⟨hE (mem_insert _ _), h⟩
        rw [← R.matroid.eRk_closure_eq (insert e S),
          _root_.Matroid.closure_insert_eq_of_mem_closure hc, R.matroid.eRk_closure_eq, ih', h]
      · have hc : e ∉ R.matroid.closure S := by
          rw [R.matroid_closure]; exact fun hc ↦ h hc.2
        rw [_root_.Matroid.eRk_insert_eq_add_one ⟨hE (mem_insert _ _), hc⟩, ih']
        have hle := R.insert_le e S
        have hmono := R.mono (subset_insert e S)
        have heq : R.rank (insert e S) = R.rank S + 1 := by omega
        simp [heq]
  rw [← R.matroid.eRk_inter_ground X, matroid_ground,
    hfinite _ (R.finite_ground.subset inter_subset_right) inter_subset_right, R.inter_ground]

private theorem native_ne_top (M : _root_.Matroid α) [M.Finite] (X : Set α) :
    M.eRk X ≠ ⊤ := _root_.Matroid.eRk_ne_top_iff.mpr (M.isRkFinite_set X)

private theorem native_zero_iff (M : _root_.Matroid α) [M.Finite] {e : α}
    {X : Set α} (he : e ∈ M.E) :
    (M.eRk (insert e X)).toNat = (M.eRk X).toNat ↔ e ∈ M.closure X := by
  constructor
  · intro h
    by_contra hc
    rw [_root_.Matroid.eRk_insert_eq_add_one ⟨he, hc⟩,
      ENat.toNat_add (native_ne_top M X) (by simp)] at h
    simp at h
  · intro hc
    rw [← M.eRk_closure_eq (insert e X),
      _root_.Matroid.closure_insert_eq_of_mem_closure hc, M.eRk_closure_eq]

/-- Recover the local rank axioms from any finite native matroid. -/
noncomputable def ofMatroid (M : _root_.Matroid α) [M.Finite] : RankPresentation α where
  ground := M.E
  finite_ground := M.ground_finite
  rank := fun X ↦ (M.eRk X).toNat
  empty := by simp
  inter_ground := by intro X; rw [M.eRk_inter_ground]
  mono := fun _ Y h ↦ ENat.toNat_le_toNat (M.eRk_mono h) (native_ne_top M Y)
  insert_le := by
    intro e X
    have h := ENat.toNat_le_toNat (M.eRk_insert_le_add_one e X)
      (show M.eRk X + 1 ≠ ⊤ by simp [native_ne_top M X])
    rw [ENat.toNat_add (native_ne_top M X) (show (1 : ℕ∞) ≠ ⊤ by simp)] at h
    simpa using h
  persist := by
    intro X Y e hXY h
    by_cases he : e ∈ M.E
    · exact (native_zero_iff M he).mpr
        (M.closure_subset_closure hXY ((native_zero_iff M he).mp h))
    · rw [M.eRk_insert_of_notMem_ground Y he]

@[simp] theorem ofMatroid_matroid (M : _root_.Matroid α) [M.Finite] :
    (ofMatroid M).matroid = M := by
  apply _root_.Matroid.ext_closure
  intro X
  rw [matroid_closure]
  ext e
  change (e ∈ M.E ∧ (M.eRk (insert e X)).toNat = (M.eRk X).toNat) ↔ _
  exact ⟨fun h ↦ (native_zero_iff M h.1).mp h.2,
    fun h ↦ ⟨M.closure_subset_ground X h,
      (native_zero_iff M (M.closure_subset_ground X h)).mpr h⟩⟩

@[simp] theorem matroid_ofMatroid : ofMatroid R.matroid = R := by
  cases R
  simp only [ofMatroid, matroid_ground]
  congr
  funext X
  rw [matroid_eRk, ENat.toNat_natCast]

end RankPresentation
end Applications.Matroid
