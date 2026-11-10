import SquareKit.Internal.PathTransport.GeneratedSectionLift
import SquareKit.Internal.PathTransport.SectionIdentitySquare
import SquareKit.Internal.PathTransport.GeneratedIdentitySetMap

/-! Identity restriction retains the actual included vertical arrow. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C D : Grpd.{u,u}} (R : C ⥤ D)
variable {A : C ⥤ Grpd.{u,u}} {B : D ⥤ Grpd.{u,u}} (α : A ⟶ R ⋙ B)
variable (x y : Section A) (z w : Section (R ⋙ B))

theorem identity_restriction_square (hx : x.familyImage α = z) (hy : y.familyImage α = w)
    (c : C) (p : x.obj c ⟶ y.obj c) :
    (Comparison.totalMap R α).map ((Grothendieck.ι (A ⋙ Grpd.forgetToCat) c).map p) ≫
      eqToHom (congrArg (fun s : Section (R ⋙ B) =>
        (Grothendieck.pre (B ⋙ Grpd.forgetToCat) R).obj (s.lift.obj c)) hy) =
    eqToHom (congrArg (fun s : Section (R ⋙ B) =>
        (Grothendieck.pre (B ⋙ Grpd.forgetToCat) R).obj (s.lift.obj c)) hx) ≫
      (Grothendieck.ι (B ⋙ Grpd.forgetToCat) (R.obj c)).map
        ((directIdentityMap α x y ≫ eqToHom (by rw [hx, hy])).app c p) := by
  subst z; subst w
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
  fapply Grothendieck.ext
  · simp [Comparison.totalMap]
  · simp [Comparison.totalMap, Grothendieck.ι, Grothendieck.map, Grothendieck.pre,
      directIdentityMap, Grpd.forgetToCat]
    change eqToHom _ ≫ (α.app c).map (eqToHom _) ≫ (α.app c).map p =
      eqToHom _ ≫ (α.app c).map p
    simp only [eqToHom_map, eqToHom_trans_assoc]

namespace Comparison
variable (S : Signature.{u})
local notation "L" => Instance.fullModel S.base.left S.leftFiber
local notation "T" => Instance.fullModel S.base.right S.rightFiber

theorem generatedIdentity_included (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hA : Typed.TyDeriv.{u+1} Γ γ F f)
    (hx : Typed.TmDeriv.{u+1} Γ γ F f xx ξ) (hy : Typed.TmDeriv.{u+1} Γ γ F f yy η)
    (c : (show Grpd.{u,u} from γ L)) (p : (ξ L).down.obj c ⟶ (η L).down.obj c) :
    (totalMap (generatedContextMap S hΓ) (generatedFamilyMap S hΓ hA)).map
      ((Grothendieck.ι (f L ⋙ Grpd.forgetToCat) c).map p) ≫
        eqToHom (Functor.congr_obj (generatedSectionLift_commutes S hΓ hA hy) c) =
      eqToHom (Functor.congr_obj (generatedSectionLift_commutes S hΓ hA hx) c) ≫
        (Grothendieck.ι (f T ⋙ Grpd.forgetToCat) ((generatedContextMap S hΓ).obj c)).map
          ((generatedIdentitySetMap S hΓ hA hx hy).app c p) :=
  identity_restriction_square (generatedContextMap S hΓ) (generatedFamilyMap S hΓ hA)
    (ξ L).down (η L).down ((ξ T).down.reindex _) ((η T).down.reindex _)
    (generatedTerm_commutes S hΓ hA hx) (generatedTerm_commutes S hΓ hA hy) c p

/-- The same selected identity arrow after any equal presentation of the total map. -/
theorem generatedIdentity_conjugate (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hA : Typed.TyDeriv.{u+1} Γ γ F f)
    (hx : Typed.TmDeriv.{u+1} Γ γ F f xx ξ) (hy : Typed.TmDeriv.{u+1} Γ γ F f yy η)
    (Q : Extend (f L) ⥤ Extend (f T))
    (hQ : Q = totalMap (generatedContextMap S hΓ) (generatedFamilyMap S hΓ hA))
    (c : (show Grpd.{u,u} from γ L))
    (ex : Q.obj ((ξ L).down.lift.obj c) = (ξ T).down.lift.obj ((generatedContextMap S hΓ).obj c))
    (ey : Q.obj ((η L).down.lift.obj c) = (η T).down.lift.obj ((generatedContextMap S hΓ).obj c))
    (p : (ξ L).down.obj c ⟶ (η L).down.obj c) :
    (Grothendieck.ι (f T ⋙ Grpd.forgetToCat) ((generatedContextMap S hΓ).obj c)).map
        ((generatedIdentitySetMap S hΓ hA hx hy).app c p) =
      eqToHom ex.symm ≫ Q.map ((Grothendieck.ι (f L ⋙ Grpd.forgetToCat) c).map p) ≫ eqToHom ey := by
  subst Q
  have hh := generatedIdentity_included S hΓ hA hx hy c p
  have hh' := congrArg (fun k => eqToHom ex.symm ≫ k) hh
  simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp] using hh'.symm

end Comparison
end SquareKit.Internal.PathTransport.GroupoidModel
