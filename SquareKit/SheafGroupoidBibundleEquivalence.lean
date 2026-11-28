import SquareKit.SheafGroupoidBibundlePrincipality
import SquareKit.SheafGroupoidBibundleBicategory
import SquareKit.SheafGroupoidBibundleFunctor
import SquareKit.SheafGroupoidAtlasInvariance

/-! Tensor inverses give Mathlib equivalences with the actual bibundle as forward map. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H : SquareKit.SheafGroupoid J} (P : G ⟶ H)

def TensorInverse.bicategoryEquivalence (i : TensorInverse P) :
    Bicategory.Equivalence G H :=
  Bicategory.Equivalence.mkOfAdjointifyCounit
    (f := P) (g := i.inverse) i.evaluation.symm i.coevaluation

@[simp] theorem TensorInverse.bicategoryEquivalence_hom (i : TensorInverse P) :
    (i.bicategoryEquivalence P).hom = P := rfl

def TensorInverse.ofBicategoryEquivalence (e : Bicategory.Equivalence G H)
    (h : e.hom = P) : TensorInverse P where
  inverse := e.inv
  evaluation := (Bicategory.whiskerRightIso (eqToIso h).symm e.inv) ≪≫ e.unit.symm
  coevaluation := (Bicategory.whiskerLeftIso e.inv (eqToIso h).symm) ≪≫ e.counit

theorem tensorInverse_iff_bicategoryEquivalence : Nonempty (TensorInverse P) ↔
    ∃ e : Bicategory.Equivalence G H, e.hom = P := by
  constructor
  · rintro ⟨i⟩
    exact ⟨i.bicategoryEquivalence P, rfl⟩
  · rintro ⟨e,h⟩
    exact ⟨TensorInverse.ofBicategoryEquivalence P e h⟩

theorem leftPrincipal_iff_bicategoryEquivalence : LeftPrincipal P ↔
    ∃ e : Bicategory.Equivalence G H, e.hom = P :=
  (leftPrincipal_iff_tensorInverse P).trans (tensorInverse_iff_bicategoryEquivalence P)

end SquareKit.SheafGroupoid.Bibundle

noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Bibundle
open CategoryTheory Opposite SquareKit SquareKit.SheafGroupoid
open CategoryTheory.Bicategory
open SquareKit.SheafGroupoid.Bibundle
open SquareKit.SheafGroupoid.Bibundle
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H : Operations J} [G.Laws] [H.Laws]
variable (F : G.pseudofunctor ⟶ H.pseudofunctor)
variable (hFF : ∀ X : Sheaf J (Type (max u v)),
  (StackDescentTransformation.component F X).FullyFaithful)
variable (hLG : StackLocalGeneration.LocallyGenerating (SheafCover.topology (J := J)) F)

/-- The actual completion inverse gives two-sided inverses for the balanced tensor. -/
def functorTensorInverse : TensorInverse (functorBibundle F) :=
  TensorInverse.ofStackInverse (functorBibundle F) (Bundle.completeMapInverse F hFF hLG)
    (Bundle.completeMapEquivalenceUnit F hFF hLG ≪≫
      whiskerRightIso (functorStackComparison F).symm (Bundle.completeMapInverse F hFF hLG))
    (whiskerLeftIso (Bundle.completeMapInverse F hFF hLG) (functorStackComparison F) ≪≫
      Bundle.completeMapEquivalenceCounit F hFF hLG)

include hFF hLG in
/-- A fully faithful, locally generating input map has a biprincipal associated bibundle. -/
theorem functor_leftPrincipal : LeftPrincipal (functorBibundle F) :=
  (functorTensorInverse F hFF hLG).leftPrincipal (functorBibundle F)

section Atlas
variable {U V : Sheaf J (Type (max u v))}
variable {p : U ⟶ G.objects} {q : V ⟶ G.objects}
variable (D : Chart G p p) (E : Chart G q q) (r : U ⟶ V) (hr : r ≫ q = p)

theorem atlas_leftPrincipal [Presheaf.IsLocallySurjective J r.hom] :
    LeftPrincipal (atlasBibundle D E r hr) :=
  functor_leftPrincipal (D.representedMap E r hr)
    (D.representedMapFullyFaithful E r hr) (D.representedMapLocallyGenerating E r hr)

/-- Covering the ambient groupoid is enough; the refinement map need not itself be a cover. -/
theorem atlas_leftPrincipal_of_sourceCover [Presheaf.IsLocallySurjective J p.hom] :
    LeftPrincipal (atlasBibundle D E r hr) :=
  functor_leftPrincipal (D.representedMap E r hr)
    (D.representedMapFullyFaithful E r hr)
    (D.representedMapLocallyGenerating_of_sourceCover E r hr)

theorem atlasAmbient_leftPrincipal [Presheaf.IsLocallySurjective J p.hom] :
    LeftPrincipal (atlasAmbientBibundle D) :=
  functor_leftPrincipal D.ambientTransformation D.ambientFullyFaithful D.ambientLocallyGenerating
end Atlas

end SquareKit.SheafGroupoid.Bibundle
