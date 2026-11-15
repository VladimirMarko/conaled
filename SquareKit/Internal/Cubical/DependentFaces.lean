import SquareKit.Internal.Cubical.RestrictedFaces

/-! Dependent face composition. A face on a restricted context extends to its
intersection with the restricting face, naturally under cube substitution. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u
namespace Cofibration
variable {Γ : Context.{u}} (φ : Cofibration Γ) (ψ : Cofibration (restrictContext φ))

def dependentValue (x : Γ.Elements) (ρ : Face.Assignment x.obj.unop.dimension) : Bool :=
  if h : (φ.app x.obj x.val).down.holds ρ = true then
    (ψ.app x.obj (φ.restrictedElement x ρ h).val).down.holds (fun _ => none)
  else false

theorem dependentValue_true (x : Γ.Elements) (ρ : Face.Assignment x.obj.unop.dimension) :
    dependentValue φ ψ x ρ = true ↔
      ∃ h : (φ.app x.obj x.val).down.holds ρ = true, ψ.full (φ.restrictedElement x ρ h) := by
  by_cases h : (φ.app x.obj x.val).down.holds ρ = true
  · simp only [dependentValue,dite_eq_left h]
    exact ⟨fun hp => ⟨h,hp⟩, fun ⟨_,hp⟩ => hp⟩
  · simp only [dependentValue,dite_eq_right h]
    exact ⟨fun hp => (Bool.false_ne_true hp).elim, fun ⟨hp,_⟩ => (h hp).elim⟩

def dependentCarrier (x : Γ.Elements) : Face.Carrier x.obj.unop.dimension where
  holds := dependentValue φ ψ x
  stable ρ τ r h := by
    obtain ⟨hφ,hψ⟩ := (dependentValue_true φ ψ x ρ).mp h
    exact (dependentValue_true φ ψ x τ).mpr
      ⟨(φ.app x.obj x.val).down.stable ρ τ r hφ,
        ψ.full_natural (φ.restrictedRefinement x ρ τ r hφ) hψ⟩

theorem dependentValue_natural {x y : Γ.Elements} (f : x ⟶ y)
    (ρ : Face.Assignment y.obj.unop.dimension) :
    dependentValue φ ψ y ρ = dependentValue φ ψ x (Face.assignmentMap f.hom.unop ρ) := by
  by_cases h : (φ.app y.obj y.val).down.holds ρ = true
  · have hx := (φ.holds_natural f ρ).symm.trans h
    simp only [dependentValue,dite_eq_left h,dite_eq_left hx]
    let τ := Face.assignmentMap f.hom.unop ρ
    let z := φ.restrictedElement x τ hx
    have he₁ := congrArg (fun q : Face.Carrier y.obj.unop.dimension => q.holds (fun _ => none))
      (ψ.value_natural (φ.restrictedArrow f ρ h)).symm
    change (ψ.app y.obj (φ.restrictedElement y ρ h).val).down.holds (fun _ => none) =
      (ψ.app x.obj z.val).down.holds
        (Face.assignmentMap (Cube.comp (Face.restriction ρ) f.hom.unop) (fun _ => none)) at he₁
    rw [Face.assignmentMap_comp,Face.assignmentMap_restriction_none] at he₁
    have he₂ := congrArg (fun q : Face.Carrier x.obj.unop.dimension => q.holds (fun _ => none))
      (ψ.value_natural (φ.restrictedRefinement x τ τ (fun i => Or.inr rfl) hx))
    change (ψ.app x.obj z.val).down.holds
      (Face.assignmentMap (Face.restriction τ) (fun _ => none)) =
        (ψ.app x.obj z.val).down.holds (fun _ => none) at he₂
    rw [Face.assignmentMap_restriction_none] at he₂
    exact he₁.trans he₂
  · have hx : (φ.app x.obj x.val).down.holds (Face.assignmentMap f.hom.unop ρ) ≠ true :=
      fun hp => h ((φ.holds_natural f ρ).trans hp)
    simp only [dependentValue,dite_eq_right h,dite_eq_right hx]

def dependent : Cofibration Γ where
  app I := TypeCat.ofHom (fun x => ⟨dependentCarrier φ ψ (Γ.elementsMk I x)⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply congrArg ULift.up
    apply Face.Carrier.ext
    intro ρ
    exact dependentValue_natural φ ψ (show Γ.elementsMk I x ⟶ Γ.elementsMk J (Γ.map f x) from
      Functor.Elements.homMk f rfl) ρ

theorem restrictedElement_none (x : Γ.Elements) (h : φ.full x) :
    φ.restrictedElement x (fun _ => none) h =
      (restrictContext φ).elementsMk x.obj ⟨x.val,h⟩ :=
  congrArg ((restrictContext φ).elementsMk x.obj) (Subtype.ext (Γ.map_id_apply x.obj x.val))

theorem dependent_full (x : Γ.Elements) :
    (dependent φ ψ).full x ↔ ∃ h : φ.full x,
      ψ.full ((restrictContext φ).elementsMk x.obj ⟨x.val,h⟩) := by
  change dependentValue φ ψ x (fun _ => none) = true ↔ _
  rw [dependentValue_true]
  constructor
  · rintro ⟨h,hψ⟩
    exact ⟨h,(congrArg ψ.full (restrictedElement_none φ x h)).mp hψ⟩
  · rintro ⟨h,hψ⟩
    exact ⟨h,(congrArg ψ.full (restrictedElement_none φ x h)).mpr hψ⟩

theorem ext_full {φ ψ : Cofibration Γ} (h : ∀ x : Γ.Elements, φ.full x ↔ ψ.full x) : φ = ψ := by
  ext I γ
  apply congrArg ULift.up
  apply Face.Carrier.ext
  intro ρ
  apply Bool.eq_iff_iff.mpr
  let x := Γ.elementsMk I γ
  let y := Γ.elementsMk I (Γ.map (Quiver.Hom.op (Face.restriction ρ)) γ)
  let f : x ⟶ y := Functor.Elements.homMk (Quiver.Hom.op (Face.restriction ρ)) rfl
  have hφ := φ.holds_natural f (fun _ => none)
  have hψ := ψ.holds_natural f (fun _ => none)
  change _ = (φ.app I γ).down.holds (Face.assignmentMap (Face.restriction ρ) (fun _ => none)) at hφ
  change _ = (ψ.app I γ).down.holds (Face.assignmentMap (Face.restriction ρ) (fun _ => none)) at hψ
  rw [Face.assignmentMap_restriction_none] at hφ hψ
  change (φ.app I γ).down.holds ρ = true ↔ (ψ.app I γ).down.holds ρ = true
  rw [← hφ,← hψ]
  exact h y

theorem dependent_restrict : (dependent φ ψ).reindex (restrictInclusion φ) = ψ := by
  apply ext_full
  intro x
  rw [full_reindex,dependent_full]
  exact ⟨fun ⟨_,h⟩ => h, fun h => ⟨x.val.property,h⟩⟩

theorem dependent_reindex {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    (dependent φ ψ).reindex σ = dependent (φ.reindex σ) (ψ.reindex (restrictSubstitution φ σ)) := by
  apply ext_full
  intro x
  rw [full_reindex,dependent_full,dependent_full]
  rfl

end Cofibration
end SquareKit.Cubical.Presheaf
