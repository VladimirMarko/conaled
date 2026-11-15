import SquareKit.Internal.Cubical.IdentityContraction
import SquareKit.Internal.Cubical.IdentityFaces

/-! The identity singleton context and its actual connection contraction. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

namespace IdentitySingleton
variable {Γ : Context.{u}} (A : Family Γ) (a : Term A)

abbrev fiber : Family (total A) := identity (reindex A (projection A)) (a.reindex (projection A)) (generic A)
abbrev context : Context := total (fiber A a)
abbrev base : context A a ⟶ Γ := projection (fiber A a) ≫ projection A
abbrev endpoint : Term (reindex A (base A a)) := (generic A).reindex (projection (fiber A a))

def witness : Term (identity (reindex A (base A a)) (a.reindex (base A a)) (endpoint A a)) :=
  Term.map (identityReindex (reindex A (projection A)) (a.reindex (projection A)) (generic A)
    (projection (fiber A a))) (generic (fiber A a))

def introduce {Δ : Context.{u}} (σ : Δ ⟶ Γ) (t : Term (reindex A σ))
    (p : Term (identity (reindex A σ) (a.reindex σ) t)) : Δ ⟶ context A a :=
  pair (pair σ t)
    (Term.map (identityReindexIso (reindex A (projection A)) (a.reindex (projection A)) (generic A)
      (pair σ t)).inv p)

def reflexivity : Γ ⟶ context A a := introduce A a (𝟙 Γ) a (identityRefl a)

def contraction : total (interval (context A a)) ⟶ context A a :=
  introduce A a (projection (interval (context A a)) ≫ base A a)
    (IdentityContraction.point (witness A a)) (IdentityContraction.contract (witness A a))

theorem introduce_congr {Δ : Context.{u}} (σ : Δ ⟶ Γ) {t t' : Term (reindex A σ)}
    (ht : t = t') {p : Term (identity (reindex A σ) (a.reindex σ) t)}
    {p' : Term (identity (reindex A σ) (a.reindex σ) t')} (hp : HEq p p') :
    introduce A a σ t p = introduce A a σ t' p' := by
  cases ht
  cases hp
  rfl

theorem introduce_reindex {Δ Θ : Context.{u}} (σ : Δ ⟶ Γ) (t : Term (reindex A σ))
    (p : Term (identity (reindex A σ) (a.reindex σ) t)) (τ : Θ ⟶ Δ) :
    τ ≫ introduce A a σ t p = introduce A a (τ ≫ σ) (t.reindex τ)
      (Term.map (identityReindex (reindex A σ) (a.reindex σ) t τ) (p.reindex τ)) := by
  unfold introduce
  rw [pair_reindex]
  apply congrArg (pair (pair (τ ≫ σ) (t.reindex τ)))
  apply Term.map_injective_of_iso
    (identityReindexIso (reindex A (projection A)) (a.reindex (projection A)) (generic A)
      (pair (τ ≫ σ) (t.reindex τ)))
  have h := congrArg (fun s => Term.map (identityReindex (reindex A σ) (a.reindex σ) t τ)
    (s.reindex τ)) (Term.map_iso_roundtrip
      (identityReindexIso (reindex A (projection A)) (a.reindex (projection A)) (generic A)
        (pair σ t)).symm p)
  exact h.trans (Term.map_iso_roundtrip
    (identityReindexIso (reindex A (projection A)) (a.reindex (projection A)) (generic A)
      (pair (τ ≫ σ) (t.reindex τ))).symm _).symm

theorem reflexivity_base : reflexivity A a ≫ base A a = 𝟙 Γ := rfl

theorem contraction_base : contraction A a ≫ base A a = projection (interval (context A a)) ≫ base A a := rfl

theorem introduce_generic : introduce A a (base A a) (endpoint A a) (witness A a) = 𝟙 (context A a) := by
  have h := Term.map_iso_roundtrip
    (identityReindexIso (reindex A (projection A)) (a.reindex (projection A)) (generic A)
      (projection (fiber A a))) (generic (fiber A a))
  exact congrArg (pair (projection (fiber A a))) h

theorem contraction_zero :
    endpointSub (context A a) false ≫ contraction A a = base A a ≫ reflexivity A a := by
  have hc := introduce_reindex A a (projection (interval (context A a)) ≫ base A a)
    (IdentityContraction.point (witness A a)) (IdentityContraction.contract (witness A a))
    (endpointSub (context A a) false)
  have he := introduce_congr A a (base A a) (IdentityContraction.point_zero (witness A a))
    ((Term.convert_heq _ _).symm.trans (heq_of_eq (IdentityContraction.atZero_refl (witness A a))))
  exact hc.trans (he.trans (introduce_reindex A a (𝟙 Γ) a (identityRefl a) (base A a)).symm)

theorem contraction_one : endpointSub (context A a) true ≫ contraction A a = 𝟙 (context A a) := by
  have hc := introduce_reindex A a (projection (interval (context A a)) ≫ base A a)
    (IdentityContraction.point (witness A a)) (IdentityContraction.contract (witness A a))
    (endpointSub (context A a) true)
  have he := introduce_congr A a (base A a) (IdentityContraction.point_one (witness A a))
    ((Term.convert_heq _ _).symm.trans (heq_of_eq (IdentityContraction.atOne_self (witness A a))))
  exact hc.trans (he.trans (introduce_generic A a))

theorem introduce_full {Δ : Context.{u}} (σ : Δ ⟶ Γ) (t : Term (reindex A σ))
    (p : Term (identity (reindex A σ) (a.reindex σ) t)) (h : ∀ x, (identityFace p).full x) :
    introduce A a σ t p = σ ≫ reflexivity A a := by
  have he := introduce_congr A a σ (identity_full_endpoints p h)
    ((Term.convert_heq _ p).symm.trans (heq_of_eq (identity_full_refl p h)))
  exact he.trans (introduce_reindex A a (𝟙 Γ) a (identityRefl a) σ).symm

abbrev markedFace : Cofibration (context A a) := identityFace (witness A a)

theorem markedFace_reflexivity : (markedFace A a).reindex (reflexivity A a) = Cofibration.top Γ := rfl

theorem contraction_full :
    restrictInclusion ((markedFace A a).reindex (projection (interval (context A a)))) ≫ contraction A a =
      restrictInclusion ((markedFace A a).reindex (projection (interval (context A a)))) ≫
        projection (interval (context A a)) ≫ base A a ≫ reflexivity A a := by
  let τ := restrictInclusion ((markedFace A a).reindex (projection (interval (context A a))))
  have h := introduce_reindex A a (projection (interval (context A a)) ≫ base A a)
    (IdentityContraction.point (witness A a)) (IdentityContraction.contract (witness A a)) τ
  apply h.trans
  apply introduce_full
  intro x
  exact (Cofibration.full_join _ _ _).mpr (Or.inl x.val.property)

end IdentitySingleton
end SquareKit.Cubical.Presheaf
