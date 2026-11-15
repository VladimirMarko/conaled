import SquareKit.Internal.Cubical.FaceEndpoints
import SquareKit.Internal.Cubical.Conversion
import SquareKit.Internal.Cubical.PartialSections

/-! Exchange the filling and path dimensions, with their actual endpoint faces. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def swapIntervals (Γ : Context.{u}) :
    total (interval (total (interval Γ))) ⟶ total (interval (total (interval Γ))) where
  app _ := TypeCat.ofHom (fun z => ⟨⟨z.1.1,z.2⟩,z.1.2⟩)
  naturality _ _ _ := rfl

theorem swapIntervals_twice (Γ : Context.{u}) : swapIntervals Γ ≫ swapIntervals Γ = 𝟙 _ := rfl

theorem swapIntervals_endpoint (Γ : Context.{u}) (b : Bool) :
    endpointSub (total (interval Γ)) b ≫ swapIntervals Γ = liftSub (interval (total (interval Γ))) (endpointSub Γ b) := rfl

theorem swapIntervals_lift_endpoint (Γ : Context.{u}) (b : Bool) :
    liftSub (interval (total (interval Γ))) (endpointSub Γ b) ≫ swapIntervals Γ = endpointSub (total (interval Γ)) b := rfl

theorem swapIntervals_natural {Γ Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    swapIntervals Δ ≫ liftSub (interval (total (interval Γ))) (liftSub (interval Γ) σ) =
      liftSub (interval (total (interval Γ))) (liftSub (interval Γ) σ) ≫ swapIntervals Γ := rfl

abbrev intervalFace (Γ : Context.{u}) (b : Bool) : Cofibration (total (interval Γ)) :=
  Cofibration.endpoint (generic (interval Γ)) b

theorem intervalFace_inclusion (Γ : Context.{u}) (b : Bool) :
    (restrictInclusion (intervalFace Γ b) ≫ projection (interval Γ)) ≫ endpointSub Γ b =
      restrictInclusion (intervalFace Γ b) := by
  ext I z
  change (⟨z.val.1,(endpoint Γ b).val (Γ.elementsMk I z.val.1)⟩ :
    (total (interval Γ)).obj I) = z.val
  exact congrArg (fun r => (⟨z.val.1,r⟩ : (total (interval Γ)).obj I))
    (((Cofibration.full_endpoint (generic (interval Γ)) b
      ((total (interval Γ)).elementsMk I z.val)).mp z.property).symm)

def endpointSection {Γ : Context.{u}} (B : Family (total (interval Γ))) (b : Bool)
    (a : Term (reindex B (endpointSub Γ b))) : PartialSection B (intervalFace Γ b) :=
  PartialSection.ofRestricted
    ((a.reindex (restrictInclusion (intervalFace Γ b) ≫ projection (interval Γ))).convert
      (congrArg (fun σ => reindex B σ) (intervalFace_inclusion Γ b)))

theorem endpointSection_val {Γ : Context.{u}} (B : Family (total (interval Γ))) (b : Bool)
    (a : Term (reindex B (endpointSub Γ b))) (x : (total (interval Γ)).Elements)
    (h : (intervalFace Γ b).full x) :
    HEq ((endpointSection B b a).val x h) (a.val ((projection (interval Γ)).mapElements.obj x)) :=
  Term.convert_val_heq _ _ ((restrictContext (intervalFace Γ b)).elementsMk x.obj ⟨x.val,h⟩)

theorem intervalFace_disjoint {Γ : Context.{u}} (x : (total (interval Γ)).Elements)
    (h₀ : (intervalFace Γ false).full x) (h₁ : (intervalFace Γ true).full x) : False := by
  have h := ((Cofibration.full_endpoint (generic (interval Γ)) false x).mp h₀).symm.trans
    ((Cofibration.full_endpoint (generic (interval Γ)) true x).mp h₁)
  have hd := congrArg ULift.down h
  have bad := PartialDimension.sound (fun _ => none) (Quotient.exact hd 0)
  cases bad

theorem endpointSection_reindex {Γ Δ : Context.{u}} (B : Family (total (interval Γ))) (b : Bool)
    (a : Term (reindex B (endpointSub Γ b))) (σ : Δ ⟶ Γ) :
    (endpointSection B b a).reindex (liftSub (interval Γ) σ) =
      endpointSection (reindex B (liftSub (interval Γ) σ)) b (a.reindex σ) := by
  apply PartialSection.ext
  intro x h
  apply eq_of_heq
  exact (endpointSection_val B b a ((liftSub (interval Γ) σ).mapElements.obj x) h).trans
    (endpointSection_val (reindex B (liftSub (interval Γ) σ)) b (a.reindex σ) x h).symm

end SquareKit.Cubical.Presheaf
