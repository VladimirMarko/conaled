import SquareKit.Internal.Cubical.CartesianFilling
import Mathlib.CategoryTheory.Sites.Sieves.Basic
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.EquivFin

/-! Finite presentations of Cartesian sieves by equality patterns. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory

instance (n : ℕ) : Fintype (Dim n) := Fintype.ofEquiv (Bool ⊕ Fin n) {
  toFun := fun x => match x with | .inl b => .endpoint b | .inr i => .var i
  invFun := fun x => match x with | .endpoint b => .inl b | .var i => .inr i
  left_inv := by intro x; cases x <;> rfl
  right_inv := by intro x; cases x <;> rfl }

instance (I J : Cube) : Fintype (I ⟶ J) :=
  inferInstanceAs (Fintype (Fin J.dimension → Dim I.dimension))

namespace Cube
/-- A finite alphabet suffices even when the source has arbitrarily many variables.
Unused slots are padded with zero; mutual factorization preserves sieve membership. -/
theorem finite_pattern {I J : Cube} (f : J ⟶ I) :
    ∃ (p : J ⟶ I) (i : I ⟶ I) (s : I ⟶ J), p ≫ i = f ∧ s ≫ f = i := by
  classical
  let rep (v : Fin J.dimension) (h : ∃ j, f j = .var v) := h.choose
  let s : I ⟶ J := fun v => if h : ∃ j, f j = .var v then .var (rep v h) else .endpoint false
  let p : J ⟶ I := fun j => match f j with | .var v => .var v | .endpoint _ => .endpoint false
  refine ⟨p, s ≫ f, s, ?_, rfl⟩
  funext j
  change Dim.subst p (Dim.subst s (f j)) = f j
  cases hj : f j with
  | endpoint b => rfl
  | var v =>
    have h : ∃ j, f j = .var v := ⟨j, hj⟩
    have hr : f (rep v h) = .var v := h.choose_spec
    simp only [Dim.subst, s, dite_eq_left h]
    change (match f (rep v h) with | .var w => Dim.var w | .endpoint _ => Dim.endpoint false) = Dim.var v
    rw [hr]

/-- Enumerating exactly the used variables gives a split projection, including k = 0. -/
theorem split_variable_factorization {I J : Cube} (f : J ⟶ I) :
    ∃ (k : ℕ) (_ : k ≤ I.dimension) (p : J ⟶ (⟨k⟩ : Cube))
      (i : (⟨k⟩ : Cube) ⟶ I) (s : (⟨k⟩ : Cube) ⟶ J),
      s ≫ p = 𝟙 (⟨k⟩ : Cube) ∧ p ≫ i = f ∧ s ≫ f = i := by
  classical
  let Used := {v : Fin J.dimension // ∃ j, f j = .var v}
  let e : Used ≃ Fin (Fintype.card Used) := Fintype.equivFin Used
  let p : J ⟶ (⟨Fintype.card Used⟩ : Cube) := fun j => .var (e.symm j).val
  let s : (⟨Fintype.card Used⟩ : Cube) ⟶ J := fun v =>
    if h : ∃ j, f j = .var v then .var (e ⟨v, h⟩) else .endpoint false
  let representative : Used → Fin I.dimension := fun v => v.property.choose
  have hr (v : Used) : f (representative v) = .var v.val := v.property.choose_spec
  have hinj : Function.Injective representative := by
    intro v w h
    apply Subtype.ext
    exact Dim.var.inj ((hr v).symm.trans ((congrArg f h).trans (hr w)))
  have hcard : Fintype.card Used ≤ I.dimension := by
    simpa using Fintype.card_le_of_injective representative hinj
  refine ⟨Fintype.card Used, hcard, p, s ≫ f, s, ?_, ?_, rfl⟩
  · funext j
    change s (e.symm j).val = .var j
    have h := (e.symm j).property
    simp only [s, dite_eq_left h]
    exact congrArg Dim.var (e.apply_symm_apply j)
  · funext j
    change Dim.subst p (Dim.subst s (f j)) = f j
    cases hj : f j with
    | endpoint b => rfl
    | var v =>
      have h : ∃ j, f j = .var v := ⟨j, hj⟩
      simp only [Dim.subst, s, dite_eq_left h]
      change Dim.var (e.symm (e ⟨v, h⟩)).val = Dim.var v
      rw [e.symm_apply_apply]
end Cube

namespace Face
variable {n : ℕ}
def all (ps : List (Face n)) : Face n := ps.foldr Face.meet .top
def any (ps : List (Face n)) : Face n := ps.foldr Face.join .bot

theorem all_holds {m : ℕ} (ps : List (Face n)) (f : Fin n → Dim m) :
    ((all ps).subst f).Holds ↔ ∀ p ∈ ps, (p.subst f).Holds := by
  induction ps with
  | nil => simp [all, subst, Holds]
  | cons p ps ih => simp [all, subst, Holds, ← ih]

theorem any_holds {m : ℕ} (ps : List (Face n)) (f : Fin n → Dim m) :
    ((any ps).subst f).Holds ↔ ∃ p ∈ ps, (p.subst f).Holds := by
  induction ps with
  | nil => simp [any, subst, Holds]
  | cons p ps ih => simp [any, subst, Holds, ← ih]

/-- Constants and repeated outputs characterize factorization through a tuple. -/
def pattern {I J : Cube} (i : I ⟶ J) : Face J.dimension :=
  all ((List.ofFn fun j : Fin J.dimension => match i j with
    | .endpoint b => eq (.var j) (.endpoint b)
    | .var _ => top) ++
    (List.ofFn fun j : Fin J.dimension => all (List.ofFn fun k : Fin J.dimension =>
      if i j = i k then eq (.var j) (.var k) else top)))

theorem pattern_holds {I J K : Cube} (i : I ⟶ J) (f : K ⟶ J) :
    ((pattern i).subst f).Holds ↔ ∃ g : K ⟶ I, g ≫ i = f := by
  classical
  have characterization : ((pattern i).subst f).Holds ↔
      (∀ j b, i j = .endpoint b → f j = .endpoint b) ∧
      (∀ j k, i j = i k → f j = f k) := by
    simp only [pattern, all_holds, List.forall_mem_append, List.mem_ofFn,
      forall_exists_index, forall_apply_eq_imp_iff]
    constructor
    · intro h
      constructor
      · intro j b hj
        have hh := h.1 j
        simpa [hj, subst, Holds, Dim.subst] using hh
      · intro j k hjk
        have hk := h.2 j k
        simpa [hjk, subst, Holds, Dim.subst] using hk
    · rintro ⟨hc, hv⟩
      constructor
      · intro j
        cases hj : i j with
        | endpoint b => exact hc j b hj
        | var v => trivial
      · intro j k
        by_cases h : i j = i k
        · simpa [h, subst, Holds, Dim.subst] using hv j k h
        · simp [h, subst, Holds]
  rw [characterization]
  constructor
  · rintro ⟨hc, hv⟩
    let g : K ⟶ I := fun v => if h : ∃ j, i j = .var v then f h.choose else .endpoint false
    refine ⟨g, ?_⟩
    funext j
    cases hj : i j with
    | endpoint b =>
      change Dim.subst g (i j) = f j
      rw [hj]
      exact (hc j b hj).symm
    | var v =>
      have h : ∃ j, i j = .var v := ⟨j, hj⟩
      change Dim.subst g (i j) = f j
      rw [hj]
      simp only [Dim.subst, g, dite_eq_left h]
      exact hv _ j (h.choose_spec.trans hj.symm)
  · rintro ⟨g, rfl⟩
    constructor
    · intro j b hj; change Dim.subst g (i j) = _; rw [hj]; rfl
    · intro j k hjk; change Dim.subst g (i j) = Dim.subst g (i k); rw [hjk]

/-- Every sieve is a finite union of principal equality patterns. -/
noncomputable def ofSieve {I : Cube} (S : Sieve I) : Face I.dimension := by
  classical
  exact any ((Finset.univ.filter fun i : I ⟶ I => S i).toList.map pattern)

theorem ofSieve_holds {I J : Cube} (S : Sieve I) (f : J ⟶ I) :
    ((ofSieve S).subst f).Holds ↔ S f := by
  classical
  simp only [ofSieve, any_holds, List.mem_map, Finset.mem_toList, Finset.mem_filter,
    Finset.mem_univ, true_and, exists_exists_and_eq_and]
  constructor
  · rintro ⟨i, hi, h⟩
    obtain ⟨g, rfl⟩ := (pattern_holds i f).mp h
    exact S.downward_closed hi g
  · intro hf
    obtain ⟨p, i, s, hpi, hsi⟩ := Cube.finite_pattern f
    refine ⟨i, ?_, (pattern_holds i f).mpr ⟨p, hpi⟩⟩
    rw [← hsi]
    exact S.downward_closed hf s
end Face
end SquareKit.Cubical.Cartesian
