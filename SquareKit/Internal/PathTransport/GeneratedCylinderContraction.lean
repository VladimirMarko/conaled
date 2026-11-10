import SquareKit.Internal.PathTransport.GeneratedCylinderCoherence
import SquareKit.Internal.PathTransport.GeneratedContractionSquares

/-! Selected external comparisons respect the actual generated root/tail
contractions and their chosen counits. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {C D : Grpd.{u,u}} (F : C ⥤ D) (P : C ⥤ Type u)
variable {G : C ⥤ D} (η : F ≅ G)
variable (Q : D ⥤ Type u) (α : P ⟶ F ⋙ Q) (β : P ⟶ G ⋙ Q)
variable (h : α ≫ whiskerRight η.hom Q = β)
local notation "S" => Signature.mk (Context.mk C D F) P Q α
local notation "U" => Signature.mk (Context.mk C D G) P Q β
local notation "L" => Instance.fullModel C P
local notation "R" => Instance.fullModel D Q

theorem contextComparison_rootTail_counit (hΓ : Typed.CtxDeriv.{u+1} Γ γ)
    (hA : Typed.TyDeriv.{u+1} Γ γ A a) (hx : Typed.TmDeriv.{u+1} Γ γ A a t x)
    (hT : Typed.TelDeriv.{u+1} (pathCtx Γ A t) (Typed.pathCode a x) n Δ T) :
    let s := generatedRootTail_square S hΓ hA hx hT
    let q := generatedRootTail_square U hΓ hA hx hT
    let e := (Instance.rootTailEquivalence D Q (a R) (x R).down (T R)).equiv
    let e' := (Instance.rootTailEquivalence C P (a L) (x L).down (T L)).equiv
    let k := contextComparison F P η Q α β h (.telescope (.path hΓ hA hx) hT)
    let l := contextComparison F P η Q α β h (.branch hΓ hA hx hT)
    whiskerLeft _ e.counitInv ≫ eqToHom (congrArg (· ⋙ e.functor) s.inverse) ≫
        whiskerLeft e'.inverse (whiskerRight l.hom e.functor) =
      k.hom ≫ whiskerLeft _ e.counitInv ≫
        eqToHom (congrArg (· ⋙ e.functor) q.inverse) := by
  apply EquivalenceSquare.selectedCounit_square
    (generatedRootTail_square S hΓ hA hx hT) (generatedRootTail_square U hΓ hA hx hT)
  exact contextComparison_substitution F P η Q α β h
    (.telescope (.path hΓ hA hx) hT) (.branch hΓ hA hx hT) (.rootTail hΓ hA hx hT)

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison.SignatureCylinder
