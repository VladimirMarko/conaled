import SquareKit.Internal.Cubical.CompositionFilling
import SquareKit.Internal.Cubical.FillingTransport

/-! Scaling an open box commutes with a family morphism. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem endpointSection_map {Γ : Context.{u}} {A B : Family (total (interval Γ))}
    (η : A ⟶ B) (v : Bool) (a : Term (reindex A (endpointSub Γ v))) :
    endpointSection B v (Term.map (Functor.whiskerLeft (endpointSub Γ v).mapElements η) a) =
      (endpointSection A v a).map η := by
  apply PartialSection.ext
  intro x hx
  rcases x with @⟨I,⟨γ,r⟩⟩
  have hr := (Cofibration.full_endpoint (generic (interval Γ)) v
    ((total (interval Γ)).elementsMk I ⟨γ,r⟩)).mp hx
  change r = (endpoint Γ v).val (Γ.elementsMk I γ) at hr
  subst r
  have ha := eq_of_heq (endpointSection_val A v a _ hx)
  have hb := eq_of_heq (endpointSection_val B v
    (Term.map (Functor.whiskerLeft (endpointSub Γ v).mapElements η) a) _ hx)
  exact hb.trans (congrArg (η.app _) ha).symm

theorem scaledZeroSection_map {Γ : Context.{u}} {A B : Family (total (interval Γ))}
    (η : A ⟶ B) (a : Term (reindex A (endpointSub Γ false))) :
    scaledZeroSection (Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements η) a) =
      (scaledZeroSection a).map (Functor.whiskerLeft (scaleInterval Γ).mapElements η) := by
  exact congrArg (fun s : PartialSection B (intervalFace Γ false) =>
    (s.reindex (scaleInterval Γ)).restrict scaleInterval_outer_zero) (endpointSection_map η false a)

theorem scaledBase_map {Γ : Context.{u}} {A B : Family (total (interval Γ))}
    (η : A ⟶ B) (a : Term (reindex A (endpointSub Γ false))) :
    scaledBase (Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements η) a) =
      Term.map (Functor.whiskerLeft (endpointSub (total (interval Γ)) false ≫ scaleInterval Γ).mapElements η)
        (scaledBase a) := by
  exact congrArg (fun s : PartialSection B (intervalFace Γ false) =>
    (s.reindex (endpointSub (total (interval Γ)) false ≫ scaleInterval Γ)).toTerm scaleInterval_cap_zero)
      (endpointSection_map η false a)

theorem scaledBox_map {Γ : Context.{u}} {A B : Family (total (interval Γ))}
    (η : A ⟶ B) {φ : Cofibration Γ} (b : OpenBox A φ) :
    scaledBox (b.map η) = (scaledBox b).map (Functor.whiskerLeft (scaleInterval Γ).mapElements η) := by
  apply OpenBox.ext
  · apply PartialSection.ext
    intro x hx
    classical
    by_cases h : ((φ.reindex (projection (interval Γ))).reindex
        (scaleInterval Γ)).full x
    · simp only [scaledBox,scaledTube,OpenBox.map,PartialSection.glue,PartialSection.map,
        glueValue,dite_eq_left h]
      rfl
    · simp only [scaledBox,scaledTube,OpenBox.map,PartialSection.glue,PartialSection.map,
        glueValue,dite_eq_right h]
      rw [scaledZeroSection_map]
      rfl
  · exact scaledBase_map η b.base

end SquareKit.Cubical.Presheaf
