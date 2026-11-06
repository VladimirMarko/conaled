import SquareKit.Internal.PathTransport.TwoFamilyEndpoints
import SquareKit.Internal.PathTransport.TwoIdentityTransport
/-! Open identity transport over the actual family of endpoints. The ordinary
functor laws are constructed; assembling the complete higher family remains pending. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Bicategory.Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ, IsGroupoid (F.obj γ)]

/-- Endpoint transport acts on the complete fiber hom-category. -/
noncomputable def openIdMap {x y : Total (endpointFamily F)}
    (p : x ⟶ y) : (x.fiber.1 ⟶ x.fiber.2) ⥤ (y.fiber.1 ⟶ y.fiber.2) := by
  letI : IsIso p.fiber.1 := IsGroupoid.all_isIso (C := (F.obj y.base).carrier) p.fiber.1
  exact TwoIdentityTransport.homTransport (F.map p.base) p.fiber.1 p.fiber.2

theorem openIdMap_id (x : Total (endpointFamily F)) : openIdMap F (𝟙 x) = 𝟭 _ := by
  have hf : (identity (endpointFamily F) x).fiber.1 =
      eqToHom (congrArg (fun H : F.obj x.base ⟶ F.obj x.base => H.obj x.fiber.1) (F.map_id x.base)) := by
    exact CategoryTheory.eqToHom_fst (congrArg
      (fun H : (endpointFamily F).obj x.base ⟶ (endpointFamily F).obj x.base => H.obj x.fiber)
      ((endpointFamily F).map_id x.base))
  have hg : (identity (endpointFamily F) x).fiber.2 =
      eqToHom (congrArg (fun H : F.obj x.base ⟶ F.obj x.base => H.obj x.fiber.2) (F.map_id x.base)) := by
    exact CategoryTheory.eqToHom_snd (congrArg
      (fun H : (endpointFamily F).obj x.base ⟶ (endpointFamily F).obj x.base => H.obj x.fiber)
      ((endpointFamily F).map_id x.base))
  change TwoIdentityTransport.homTransport (F.map (𝟙 x.base))
    (identity (endpointFamily F) x).fiber.1 (identity (endpointFamily F) x).fiber.2 = _
  rw [hf, hg]
  exact TwoIdentityTransport.homTransport_of_eq_id _ (F.map_id x.base) _ _
theorem openIdMap_comp {x y z : Total (endpointFamily F)} (p : x ⟶ y) (q : y ⟶ z) :
    openIdMap F (p ≫ q) = openIdMap F p ⋙ openIdMap F q := by
  let e := congrArg
    (fun H : (endpointFamily F).obj x.base ⟶ (endpointFamily F).obj z.base => H.obj x.fiber)
    ((endpointFamily F).map_comp p.base q.base)
  have hf : (compose (endpointFamily F) p q).fiber.1 =
      eqToHom (congrArg (fun H : F.obj x.base ⟶ F.obj z.base => H.obj x.fiber.1)
        (F.map_comp p.base q.base)) ≫ (F.map q.base).map p.fiber.1 ≫ q.fiber.1 := by
    change (eqToHom e).1 ≫ (F.map q.base).map p.fiber.1 ≫ q.fiber.1 = _
    rw [CategoryTheory.eqToHom_fst]
  have hg : (compose (endpointFamily F) p q).fiber.2 =
      eqToHom (congrArg (fun H : F.obj x.base ⟶ F.obj z.base => H.obj x.fiber.2)
        (F.map_comp p.base q.base)) ≫ (F.map q.base).map p.fiber.2 ≫ q.fiber.2 := by
    change (eqToHom e).2 ≫ (F.map q.base).map p.fiber.2 ≫ q.fiber.2 = _
    rw [CategoryTheory.eqToHom_snd]
  change TwoIdentityTransport.homTransport (F.map (p.base ≫ q.base))
    (compose (endpointFamily F) p q).fiber.1 (compose (endpointFamily F) p q).fiber.2 = _
  rw [hf,hg]
  letI : IsIso p.fiber.1 := IsGroupoid.all_isIso (C := (F.obj y.base).carrier) p.fiber.1
  letI : IsIso q.fiber.1 := IsGroupoid.all_isIso (C := (F.obj z.base).carrier) q.fiber.1
  exact (TwoIdentityTransport.homTransport_congr (F.map_comp p.base q.base)
    ((F.map q.base).map p.fiber.1 ≫ q.fiber.1)
    ((F.map q.base).map p.fiber.2 ≫ q.fiber.2)).trans
      (TwoIdentityTransport.homTransport_comp (F.map p.base) (F.map q.base)
        p.fiber.1 p.fiber.2 q.fiber.1 q.fiber.2)

/-- The underlying identity-family functor on the general endpoint context. -/
noncomputable def openIdUnderlying : Total (endpointFamily F) ⥤ Cat.{w,v} where
  obj x := Cat.of (x.fiber.1 ⟶ x.fiber.2)
  map p := (openIdMap F p).toCatHom
  map_id x := congrArg Functor.toCatHom (openIdMap_id F x)
  map_comp p q := congrArg Functor.toCatHom (openIdMap_comp F p q)
variable [∀ γ, Bicategory.IsLocallyGroupoid (F.obj γ)]
/-- A genuine endpoint-context 2-cell supplies the natural hom comparison. -/
noncomputable def openIdCell {x y : Total (endpointFamily F)} {p q : Hom (endpointFamily F) x y}
    (α : p ⟶ q) : openIdMap F p ⟶ openIdMap F q := by
  letI : IsIso p.fiber.1 := IsGroupoid.all_isIso (C := (F.obj y.base).carrier) p.fiber.1
  letI : IsIso q.fiber.1 := IsGroupoid.all_isIso (C := (F.obj y.base).carrier) q.fiber.1
  exact TwoIdentityTransport.homComparison (F.map₂ α.base) α.fiber.1 α.fiber.2
end SquareKit.Internal.PathTransport.TwoFamily
