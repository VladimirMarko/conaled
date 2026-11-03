import SquareKit.SplitPiBaseChange

/-! Experimental recovery of ordinary display presentations from split Π. -/
noncomputable section
namespace SquareKit.SplitSheafPi
open CategoryTheory Limits SplitSheaf
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Γ S T : Sheaf J (Type (max u v))}

/-- Reconstruction of an ordinary display as an isomorphism in its slice. -/
def presentation (d : S ⟶ Γ) : Over.mk (p (ofDisplay d)) ≅ Over.mk d :=
  Over.isoMk (SplitSheaf.displayIso d) (SplitSheaf.displayIso_projection d)

theorem presentationSquare (d : S ⟶ Γ) :
    IsPullback (p (ofDisplay d)) (SplitSheaf.displayIso d).hom (𝟙 Γ) d :=
  IsPullback.of_vert_isIso ⟨by rw [Category.comp_id, SplitSheaf.displayIso_projection]⟩

/-- Present an arbitrary dependent result over the reconstructed argument. -/
abbrev resultPresentation (d : S ⟶ Γ) (e : T ⟶ S) : Ty (Ext (ofDisplay d)) :=
  ofDisplay (Family.reindex e (SplitSheaf.displayIso d).hom)

/-- Every earlier ordinary Π consumer can be recovered through this actual iso. -/
def ordinaryPresentation (d : S ⟶ Γ) (e : T ⟶ S) :
    Over.mk (p (pi (ofDisplay d) (resultPresentation d e))) ≅
      (SheafDependentProduct.pi d).obj (Over.mk e) :=
  displayIso (ofDisplay d) (resultPresentation d e) ≪≫
    (SheafDependentProduct.pi (p (ofDisplay d))).mapIso
      (presentation (Family.reindex e (SplitSheaf.displayIso d).hom)) ≪≫
    ((SheafDependentProduct.baseChange d (presentationSquare d)).app (Over.mk e)).symm ≪≫
    Over.pullbackId.app _

/-- The iso acts on actual split fibers, not arbitrary functions of stage fibers. -/
def familyEquiv (P : Ty Γ) (Q : Over Γ) (i : Over.mk (p P) ≅ Q) (x : Γ.obj.Elements) :
    P.family.obj x ≃ {z : Q.left.obj.obj x.obj // Q.hom.hom.app x.obj z = x.val} :=
  (((ElementFamilies.fiberTotalIso Γ.obj P.family).app x).symm.toEquiv).trans
    ((((sheafToPresheaf _ _).mapIso ((SheafSlice.forward Γ).mapIso i)).app (Opposite.op (Opposite.op x))).toEquiv)

end SquareKit.SplitSheafPi
