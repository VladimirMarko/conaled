import SquareKit.Internal.Cubical.GlueEquivalence

/-! Boolean transposition exercises the constructed Glue elimination equivalence
on arbitrary faces; the selected center really lies over its requested target. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalGlueEquivalence
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf

variable {Γ : Context.{0}}

def index : Term (constantFamily Γ Unit) where
  val _ := ()
  property _ := rfl

def boolFilling : Filling (constantFamily Γ Bool) := discreteFilling index (fun _ => Bool)
theorem boolFilling_lawful : (boolFilling (Γ := Γ)).Lawful :=
  discreteFilling_lawful index (fun _ => Bool)

def flip : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl

def faceFlip (φ : Cofibration Γ) :
    reindex (constantFamily Γ Bool) (restrictInclusion φ) ≅
      reindex (constantFamily Γ Bool) (restrictInclusion φ) :=
  NatIso.ofComponents (fun _ => flip.toIso) (by intro x y f; rfl)

noncomputable def equivalence (φ : Cofibration Γ) : HomotopyEquivalence
    (Glue.unglue φ (constantFamily Γ Bool)
      (reindex (constantFamily Γ Bool) (restrictInclusion φ)) (faceFlip φ).hom) :=
  Glue.unglueEquivalence φ _ _ _ (HomotopyEquivalence.ofIso (faceFlip φ))
    (boolFilling.reindex (restrictInclusion φ)) (boolFilling_lawful.reindex _)
    boolFilling boolFilling_lawful

/-- The center selected by the general construction returns the requested Boolean,
even though the supplied equivalence reverses it on the full gluing face. -/
theorem center_unglue (φ : Cofibration Γ) :
    Term.map (Functor.whiskerLeft (projection (constantFamily Γ Bool)).mapElements
      (Glue.unglue φ (constantFamily Γ Bool)
        (reindex (constantFamily Γ Bool) (restrictInclusion φ)) (faceFlip φ).hom))
      (genericFiberFst _ (𝟙 _) (equivalence φ).fibers.center) = generic (constantFamily Γ Bool) :=
  discretePath_endpoints (genericFiberPath _ (𝟙 _) (equivalence φ).fibers.center)

end Examples.CubicalGlueEquivalence
