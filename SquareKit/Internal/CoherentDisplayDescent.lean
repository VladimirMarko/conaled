import SquareKit.SheafDisplayFamilyDescent
import SquareKit.Internal.CoherentSheafOver

/-! Family descent compared with coherent local diagrams on the context's element site. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.CoherentDisplayDescent
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {X : Sheaf J (Type (max u v))} {I : Type (max u v)}
variable {Y : I → Sheaf J (Type (max u v))} (f : ∀ i, Y i ⟶ X)
variable (hf : SheafFamilyCover.JointlyLocallySurjective f)

/-- Coherent local diagrams, actual sheaf displays and family descent data
classify the same objects and all maps. No original-site representability is assumed. -/
def equivalence :
    CoherentSheafOver.Code (ElementSite.topology X.obj J) ≌
      (SplitSheaf.pseudofunctor.{u,v,max u v} (J := J)).DescentData f :=
  (CoherentSheafOver.classification (ElementSite.topology X.obj J)).trans
    ((SheafSlice.equivalence X).symm.trans (SheafDisplayFamilyDescent.overEquivalence f hf))

/-- The recovery comparison is natural in every code map, not only invertible ones. -/
theorem recovery_natural {A B : CoherentSheafOver.Code (ElementSite.topology X.obj J)}
    (h : A ⟶ B) :
    h ≫ (equivalence f hf).unitIso.hom.app B =
      (equivalence f hf).unitIso.hom.app A ≫
        (equivalence f hf).inverse.map ((equivalence f hf).functor.map h) :=
  (equivalence f hf).unitIso.hom.naturality h

end SquareKit.CoherentDisplayDescent
