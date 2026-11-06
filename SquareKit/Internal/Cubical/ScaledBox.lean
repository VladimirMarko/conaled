import SquareKit.Internal.Cubical.IntervalScaling
import SquareKit.Internal.Cubical.PartialRestriction
import SquareKit.Internal.Cubical.Composition

/-! Scale an open box and add the outer zero face. The new cap and the added
face come from the original cap, with their actual dependent fibers. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem OpenBox.endpoint_compatible {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {φ : Cofibration Γ} (b : OpenBox A φ) :
    b.tube.Compatible (endpointSection A false b.base) := by
  intro x h k
  rcases x with @⟨I,⟨γ,r⟩⟩
  have hr := (Cofibration.full_endpoint (generic (interval Γ)) false
    ((total (interval Γ)).elementsMk I ⟨γ,r⟩)).mp k
  change r = (endpoint Γ false).val (Γ.elementsMk I γ) at hr
  subst r
  apply eq_of_heq
  exact (heq_of_eq (b.boundary (Γ.elementsMk I γ) h)).trans
    (endpointSection_val A false b.base _ k).symm

abbrev scaledFace {Γ : Context.{u}} (φ : Cofibration Γ) : Cofibration (total (interval Γ)) :=
  (φ.reindex (projection (interval Γ))).join (intervalFace Γ false)

theorem scaleInterval_outer_zero {Γ : Context.{u}}
    (x : (total (interval (total (interval Γ)))).Elements)
    (h : ((intervalFace Γ false).reindex (projection (interval (total (interval Γ))))).full x) :
    ((intervalFace Γ false).reindex (scaleInterval Γ)).full x := by
  apply (Cofibration.full_endpoint (generic (interval Γ)) false
    ((scaleInterval Γ).mapElements.obj x)).mpr
  have hr := (Cofibration.full_endpoint (generic (interval Γ)) false
    ((projection (interval (total (interval Γ)))).mapElements.obj x)).mp h
  change x.val.1.2 = ULift.up (Cube.endpoint x.obj.unop false) at hr
  change ULift.up (Cube.meet x.val.1.2.down x.val.2.down) = _
  rw [hr]
  exact congrArg ULift.up (Cube.zero_meet _)

theorem scaleInterval_cap_zero {Γ : Context.{u}} (x : (total (interval Γ)).Elements) :
    ((intervalFace Γ false).reindex (endpointSub (total (interval Γ)) false ≫ scaleInterval Γ)).full x := by
  apply (Cofibration.full_endpoint (generic (interval Γ)) false
    ((endpointSub (total (interval Γ)) false ≫ scaleInterval Γ).mapElements.obj x)).mpr
  exact congrArg ULift.up (Cube.meet_zero _)

def scaledZeroSection {Γ : Context.{u}} {A : Family (total (interval Γ))}
    (a : Term (reindex A (endpointSub Γ false))) :
    PartialSection (reindex A (scaleInterval Γ))
      ((intervalFace Γ false).reindex (projection (interval (total (interval Γ))))) :=
  ((endpointSection A false a).reindex (scaleInterval Γ)).restrict scaleInterval_outer_zero

def scaledBase {Γ : Context.{u}} {A : Family (total (interval Γ))}
    (a : Term (reindex A (endpointSub Γ false))) :
    Term (reindex A (endpointSub (total (interval Γ)) false ≫ scaleInterval Γ)) :=
  ((endpointSection A false a).reindex
    (endpointSub (total (interval Γ)) false ≫ scaleInterval Γ)).toTerm scaleInterval_cap_zero

noncomputable def scaledTube {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {φ : Cofibration Γ} (b : OpenBox A φ) :
    PartialSection (reindex A (scaleInterval Γ))
      ((scaledFace φ).reindex (projection (interval (total (interval Γ))))) :=
  (b.tube.reindex (scaleInterval Γ)).glue (scaledZeroSection b.base)
    (fun x h k => b.endpoint_compatible ((scaleInterval Γ).mapElements.obj x) h
      (scaleInterval_outer_zero x k))

noncomputable def scaledBox {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {φ : Cofibration Γ} (b : OpenBox A φ) :
    OpenBox (reindex A (scaleInterval Γ)) (scaledFace φ) where
  tube := scaledTube b
  base := scaledBase b.base
  boundary x h := by
    let y := (endpointSub (total (interval Γ)) false).mapElements.obj x
    let t := b.tube.reindex (scaleInterval Γ)
    let s := scaledZeroSection b.base
    have hc : t.Compatible s := fun z hp hz =>
      b.endpoint_compatible ((scaleInterval Γ).mapElements.obj z) hp (scaleInterval_outer_zero z hz)
    rcases (Cofibration.full_join _ _ x).mp h with hp | hz
    · exact (glueValue_left t s y h hp).trans
        (b.endpoint_compatible ((scaleInterval Γ).mapElements.obj y) hp (scaleInterval_cap_zero x))
    · exact glueValue_right t s hc y h hz

theorem scaledZeroSection_reindex {Γ Δ : Context.{u}} {A : Family (total (interval Γ))}
    (a : Term (reindex A (endpointSub Γ false))) (σ : Δ ⟶ Γ) :
    (scaledZeroSection a).reindex
      (liftSub (interval (total (interval Γ))) (liftSub (interval Γ) σ)) =
      scaledZeroSection (A := reindex A (liftSub (interval Γ) σ)) (a.reindex σ) := by
  apply PartialSection.ext
  intro x h
  apply eq_of_heq
  exact (endpointSection_val A false a _ _).trans
    (endpointSection_val (reindex A (liftSub (interval Γ) σ)) false (a.reindex σ)
      ((scaleInterval Δ).mapElements.obj x) (scaleInterval_outer_zero x h)).symm

theorem scaledBase_reindex {Γ Δ : Context.{u}} {A : Family (total (interval Γ))}
    (a : Term (reindex A (endpointSub Γ false))) (σ : Δ ⟶ Γ) :
    (scaledBase a).reindex (liftSub (interval Γ) σ) = scaledBase (A := reindex A (liftSub (interval Γ) σ)) (a.reindex σ) := by
  apply Term.ext
  intro x
  apply eq_of_heq
  exact (endpointSection_val A false a _ _).trans
    (endpointSection_val (reindex A (liftSub (interval Γ) σ)) false (a.reindex σ)
      ((endpointSub (total (interval Δ)) false ≫ scaleInterval Δ).mapElements.obj x)
      (scaleInterval_cap_zero x)).symm

theorem scaledBox_reindex {Γ Δ : Context.{u}} {A : Family (total (interval Γ))}
    {φ : Cofibration Γ} (b : OpenBox A φ) (σ : Δ ⟶ Γ) :
    (scaledBox b).reindex (liftSub (interval Γ) σ) = scaledBox (b.reindex σ) := by
  apply OpenBox.ext
  · let τ := liftSub (interval (total (interval Γ))) (liftSub (interval Γ) σ)
    let t := b.tube.reindex (scaleInterval Γ)
    let s := scaledZeroSection b.base
    have hc : t.Compatible s := fun z hp hz =>
      b.endpoint_compatible ((scaleInterval Γ).mapElements.obj z) hp (scaleInterval_outer_zero z hz)
    exact (PartialSection.glue_reindex t s hc τ).trans
      (PartialSection.glue_congr rfl (scaledZeroSection_reindex b.base σ) _
        (fun z hp hz => (b.reindex σ).endpoint_compatible ((scaleInterval Δ).mapElements.obj z)
          hp (scaleInterval_outer_zero z hz)))
  · exact scaledBase_reindex b.base σ

end SquareKit.Cubical.Presheaf
