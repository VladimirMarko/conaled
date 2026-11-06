import SquareKit.Internal.Cubical.LocalIdentity

namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u v

private theorem prod_heq {X Y : Type u} {Z : Type v} {x : X} {y : Y} (h : HEq x y) (z : Z) :
    HEq (x,z) (y,z) := by cases h; rfl

private def identitySubstitutionEquiv {Γ Δ : Context.{u}} (A : Family Γ)
    (a b : Term A) (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    IdentityElement A a b (σ.mapElements.obj x) ≃
      IdentityElement (reindex A σ) (a.reindex σ) (b.reindex σ) x where
  toFun := (identityReindexIso A a b σ).hom.app x
  invFun := (identityReindexIso A a b σ).inv.app x
  left_inv p := congrArg (fun t => t.app x p) (identityReindexIso A a b σ).hom_inv_id
  right_inv p := congrArg (fun t => t.app x p) (identityReindexIso A a b σ).inv_hom_id

theorem identityData_substitution {Γ Δ : Context.{u}} (A : Family Γ)
    (a b : Term A) (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    IdentityData A a b (σ.mapElements.obj x) =
      IdentityData (reindex A σ) (a.reindex σ) (b.reindex σ) x :=
  congrArg (fun X => X × Face.Carrier x.obj.unop.dimension)
    (localPath_substitution (reindex A (projection (interval Γ))) a b σ x)

theorem identityLocalData_substitution {Γ Δ : Context.{u}} (A : Family Γ)
    (a b : Term A) (σ : Δ ⟶ Γ) (x : Δ.Elements)
    (p : IdentityElement A a b (σ.mapElements.obj x)) :
    HEq p.localData (((identityReindex A a b σ).app x p).localData) :=
  prod_heq (pathToLocal_substitution (reindex A (projection (interval Γ))) a b σ x p.path) p.face

theorem localIdentity_substitution {Γ Δ : Context.{u}} (A : Family Γ)
    (a b : Term A) (σ : Δ ⟶ Γ) (x : Δ.Elements) :
    LocalIdentity A a b (σ.mapElements.obj x) =
      LocalIdentity (reindex A σ) (a.reindex σ) (b.reindex σ) x :=
  rangeSubtype_eq (identitySubstitutionEquiv A a b σ x) (identityData_substitution A a b σ x)
    IdentityElement.localData IdentityElement.localData (identityLocalData_substitution A a b σ x)

theorem identityToLocal_substitution {Γ Δ : Context.{u}} (A : Family Γ)
    (a b : Term A) (σ : Δ ⟶ Γ) (x : Δ.Elements)
    (p : IdentityElement A a b (σ.mapElements.obj x)) :
    HEq p.toLocal (((identityReindex A a b σ).app x p).toLocal) := by
  apply (Subtype.heq_iff_coe_heq (identityData_substitution A a b σ x)
    (rangePredicate_heq (identitySubstitutionEquiv A a b σ x) (identityData_substitution A a b σ x)
      IdentityElement.localData IdentityElement.localData (identityLocalData_substitution A a b σ x))).mpr
  exact identityLocalData_substitution A a b σ x p

end SquareKit.Cubical.Presheaf
