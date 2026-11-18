import Examples.RepresentableClassificationCore
import Examples.SharedCubicalConstructors
import Examples.SharedSigmaFilling
import Examples.CubicalSmallFamilies

/-! Native adapters and dependent substitution controls for the shared production core. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace Examples.SharedRepresentableClassification
open CategoryTheory SquareKit.Cubical
universe u

namespace Original
open Presheaf
def system : SquareKit.RepresentableClassification.System.{u} SquareKit.Cubical.Cube where
  Data := LocalFamily
  restrict := LocalFamily.reindex
  restrict_id := LocalFamily.reindex_id
  restrict_comp := LocalFamily.reindex_comp

/-- The shared construction recovers the entire native code presheaf. -/
theorem codes_native : system.codes = smallFamilyCodes.{u} := rfl
theorem raised_native (Γ : Context.{u}) : SquareKit.RepresentableClassification.raisedContext Γ = raisedContext Γ := rfl
theorem elements_native (Γ : Context.{u}) : SquareKit.RepresentableClassification.raisedElements Γ = raisedElements Γ := rfl

variable {Γ : Context.{u}} (A : LocalFamily Γ)
theorem code_native : system.code A = A.code := rfl

/-- The original code fibers and restriction function still reduce directly. -/
example (I : SquareKit.Cubical.Cubeᵒᵖ) : smallFamilyCodes.{u}.obj I = LocalFamily (representable I.unop) := rfl
example {I J : SquareKit.Cubical.Cubeᵒᵖ} (f : I ⟶ J) (B : SmallFamilyCode.{u} I.unop) :
    smallFamilyCodes.map f B = B.reindex (representableMap f.unop) := rfl
example (I : SquareKit.Cubical.Cubeᵒᵖ) (x : Γ.obj I) :
    A.code.app I ⟨x⟩ = A.reindex (represented (Γ.elementsMk I x)) := rfl

/-- The original component formula determines the whole natural isomorphism. -/
theorem comparison_components (x : Γ.Elements) :
    A.decodeCodeIso.app x = A.family.mapIso (eqToIso (represented_generic_source x)) := by
  apply Iso.ext
  rfl

/-- Maps and identity/inverse components retain the original reduction behavior. -/
example {x y : Γ.Elements} (f : x ⟶ y) (a : (decode A.code).obj x) :
    HEq ((decode A.code).map f a)
      (A.family.map ((represented x).mapElements.map (representableGenericHom f.hom.unop)) a) :=
  cast_heq _ _
example (x : Γ.Elements) : A.decodeCodeIso.inv.app x =
    A.family.map (eqToHom (represented_generic_source x).symm) := rfl

theorem decode_native (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) :
    system.decode universalDecode a = decode a := rfl

theorem decode_substitution {Δ : Context.{u}} (a : raisedContext Γ ⟶ smallFamilyCodes.{u})
    (σ : Δ ⟶ Γ) : decode (raisedSub σ ≫ a) = reindex (decode a) σ :=
  system.decode_reindex universalDecode a σ

theorem evaluation : SquareKit.RepresentableClassification.Evaluation A.family (decode A.code) :=
  ⟨fun _ => rfl, fun _ _ => cast_heq _ _⟩

/-- Derived from the decoder's arrow formula, without the native recovery theorem. -/
def comparison : decode A.code ≅ A.family := (evaluation A).iso

theorem comparison_native : comparison A = A.decodeCodeIso := by
  apply Iso.ext
  ext x a
  rfl

theorem code_substitution {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    (A.reindex σ).code = raisedSub σ ≫ A.code := system.code_reindex A σ

theorem two_substitutions {Δ Θ : Context.{u}} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    ((A.reindex σ).reindex τ).code = raisedSub τ ≫ raisedSub σ ≫ A.code :=
  system.code_reindex_comp A σ τ

theorem identity_substitution : (A.reindex (𝟙 Γ)).code = A.code :=
  congrArg LocalFamily.code (system.restrict_id A)

/-- Recovery of chosen operations remains a native theorem. The shared iso can
replace its comparison without weakening its original box hypotheses. -/
theorem selected {I : SquareKit.Cubical.Cube}
    (p : total (interval (representable.{u} I)) ⟶ Γ)
    (φ : Cofibration (representable.{u} I))
    (b : OpenBox (reindex (decode A.code) p) φ) :
    A.filling.fill p φ (b.map (Functor.whiskerLeft p.mapElements (comparison A).hom)) =
      Term.map (Functor.whiskerLeft p.mapElements (comparison A).hom)
        ((decodedLocalFilling A.code).fill p φ b) := by
  rw [comparison_native]
  exact A.decodeCode_filling p φ b

theorem record_recovery : decodedLocalFamily A.code = A := A.decoded_code
end Original

namespace Target
open Cartesian
def system : SquareKit.RepresentableClassification.System.{u} Cartesian.Cube where
  Data := LocalFamily
  restrict := LocalFamily.reindex
  restrict_id := LocalFamily.reindex_id
  restrict_comp := LocalFamily.reindex_comp

/-- The shared construction recovers the entire native code presheaf. -/
theorem codes_native : system.codes = smallFamilyCodes.{u} := rfl
theorem raised_native (Γ : Context.{u}) : SquareKit.RepresentableClassification.raisedContext Γ = raisedContext Γ := rfl
theorem elements_native (Γ : Context.{u}) : SquareKit.RepresentableClassification.raisedElements Γ = raisedElements Γ := rfl

variable {Γ : Context.{u}} (A : LocalFamily Γ)
theorem code_native : system.code A = A.code := rfl

/-- The original code fibers and restriction function still reduce directly. -/
example (I : Cartesian.Cubeᵒᵖ) : smallFamilyCodes.{u}.obj I = LocalFamily (representable I.unop) := rfl
example {I J : Cartesian.Cubeᵒᵖ} (f : I ⟶ J) (B : SmallFamilyCode.{u} I.unop) :
    smallFamilyCodes.map f B = B.reindex (representableMap f.unop) := rfl
example (I : Cartesian.Cubeᵒᵖ) (x : Γ.obj I) :
    A.code.app I ⟨x⟩ = A.reindex (represented (Γ.elementsMk I x)) := rfl

/-- The original component formula determines the whole natural isomorphism. -/
theorem comparison_components (x : Γ.Elements) :
    A.decodeCodeIso.app x = A.family.mapIso (eqToIso (represented_generic_source x)) := by
  apply Iso.ext
  rfl

/-- Maps and identity/inverse components retain the original reduction behavior. -/
example {x y : Γ.Elements} (f : x ⟶ y) (a : (decode A.code).obj x) :
    HEq ((decode A.code).map f a)
      (A.family.map ((represented x).mapElements.map (representableGenericHom f.hom.unop)) a) :=
  cast_heq _ _
example (x : Γ.Elements) : A.decodeCodeIso.inv.app x =
    A.family.map (eqToHom (represented_generic_source x).symm) := rfl

theorem decode_native (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) :
    system.decode universalDecode a = decode a := rfl

theorem decode_substitution {Δ : Context.{u}} (a : raisedContext Γ ⟶ smallFamilyCodes.{u})
    (σ : Δ ⟶ Γ) : decode (raisedSub σ ≫ a) = reindex (decode a) σ :=
  system.decode_reindex universalDecode a σ

theorem evaluation : SquareKit.RepresentableClassification.Evaluation A.family (decode A.code) :=
  ⟨fun _ => rfl, fun _ _ => cast_heq _ _⟩

/-- Derived from the decoder's arrow formula, without the native recovery theorem. -/
def comparison : decode A.code ≅ A.family := (evaluation A).iso

theorem comparison_native : comparison A = A.decodeCodeIso := by
  apply Iso.ext
  ext x a
  rfl

theorem code_substitution {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    (A.reindex σ).code = raisedSub σ ≫ A.code := system.code_reindex A σ

theorem two_substitutions {Δ Θ : Context.{u}} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    ((A.reindex σ).reindex τ).code = raisedSub τ ≫ raisedSub σ ≫ A.code :=
  system.code_reindex_comp A σ τ

theorem identity_substitution : (A.reindex (𝟙 Γ)).code = A.code :=
  congrArg LocalFamily.code (system.restrict_id A)

/-- Recovery of chosen operations remains a native theorem. The shared iso can
replace its comparison without weakening its original box hypotheses. -/
theorem selected {I : Cartesian.Cube}
    (p : total (interval (representable.{u} I)) ⟶ Γ)
    (φ : Subcontext (representable.{u} I)) (r : Term (interval (representable I)))
    (b : OpenBox (reindex (decode A.code) p) φ r) :
    A.filling.fill p φ r (b.map (Functor.whiskerLeft p.mapElements (comparison A).hom)) =
      Term.map (Functor.whiskerLeft p.mapElements (comparison A).hom)
        ((decodedLocalFilling A.code).fill p φ r b) := by
  rw [comparison_native]
  exact A.decodeCode_filling p φ r b

theorem record_recovery : decodedLocalFamily A.code = A := A.decodeCode_record
end Target

namespace OriginalDependent
open Presheaf Examples.CubicalPresheaf Examples.CubicalSmallFamilies
abbrev A : LocalFamily naturals := decodedLocalFamily selectedCode
example : ((A.reindex successor).reindex twice).code =
    raisedSub twice ≫ raisedSub successor ≫ A.code :=
  Original.two_substitutions A successor twice
example : decode ((A.reindex successor).reindex twice).code ≅
    (A.reindex (twice ≫ successor)).family :=
  Original.comparison ((A.reindex successor).reindex twice)
example : decodedLocalFamily ((A.reindex successor).reindex twice).code =
    A.reindex (twice ≫ successor) := by
  rw [← LocalFamily.reindex_comp]
  exact Original.record_recovery ((A.reindex successor).reindex twice)
example : ¬ Nonempty
    ((decode dependentCode).obj (atArgument 0) ≃ (decode dependentCode).obj (atArgument 1)) :=
  nonconstant_decoded_fibers
theorem successor_ne_id : successor ≠ 𝟙 naturals := by
  intro h
  have hh := congrArg (fun f : naturals ⟶ naturals => f.app (.op ⟨0⟩) (0 : Nat)) h
  contradiction

theorem twice_ne_id : twice ≠ 𝟙 naturals := by
  intro h
  have hh := congrArg (fun f : naturals ⟶ naturals => f.app (.op ⟨0⟩) (1 : Nat)) h
  change 2 = 1 at hh
  omega

theorem composite_ne_id : twice ≫ successor ≠ 𝟙 naturals := by
  intro h
  have hh := congrArg (fun f : naturals ⟶ naturals => f.app (.op ⟨0⟩) (0 : Nat)) h
  contradiction
end OriginalDependent

namespace Dependent
open Cartesian
abbrev base := Examples.SharedSigmaFilling.ctx
abbrev Γ := total (ClassifierExamples.tags base)
abbrev A : LocalFamily Γ := LocalFamily.ofFilling (ClassifierExamples.branch base)
  (bijectiveFilling (ClassifierExamples.branch_restrictions base))
  (bijectiveFilling_lawful (ClassifierExamples.branch_restrictions base))
def σ : Γ ⟶ Γ := liftSub (ClassifierExamples.tags base) Examples.SharedSigmaFilling.σ
def τ : Γ ⟶ Γ := liftSub (ClassifierExamples.tags base) Examples.SharedSigmaFilling.τ

def point (b : Bool) : Γ.Elements :=
  extendObj (ClassifierExamples.tags base) (representableGeneric ⟨3⟩) ⟨b⟩
example : A.family.obj (point false) = ULift (Fin 1) := rfl
example : A.family.obj (point true) = ULift (Fin 2) := rfl

/-- Distinct fiber cardinalities rule out a constant-family-only experiment. -/
theorem fibers_not_equiv : ¬ Nonempty (A.family.obj (point false) ≃ A.family.obj (point true)) := by
  rintro ⟨e⟩
  change ULift (Fin 1) ≃ ULift (Fin 2) at e
  have h := Fintype.card_congr e
  norm_num at h

theorem sigma_ne_id : σ ≠ 𝟙 Γ := by
  intro h
  have hh := congrArg (fun f : Γ ⟶ Γ =>
    ((f.app (.op ⟨3⟩) (point false).val).1.down (0 : Fin 3))) h
  change Dim.var (1 : Fin 3) = Dim.var (0 : Fin 3) at hh
  have := Dim.var.inj hh
  contradiction

theorem tau_ne_id : τ ≠ 𝟙 Γ := by
  intro h
  have hh := congrArg (fun f : Γ ⟶ Γ =>
    ((f.app (.op ⟨3⟩) (point false).val).1.down (1 : Fin 3))) h
  change Dim.var (2 : Fin 3) = Dim.var (1 : Fin 3) at hh
  have := Dim.var.inj hh
  contradiction

theorem composite_ne_id : τ ≫ σ ≠ 𝟙 Γ := by
  intro h
  have hh := congrArg (fun f : Γ ⟶ Γ =>
    ((f.app (.op ⟨3⟩) (point false).val).1.down (0 : Fin 3))) h
  change Dim.var (2 : Fin 3) = Dim.var (0 : Fin 3) at hh
  have := Dim.var.inj hh
  contradiction

example : ((A.reindex σ).reindex τ).code = raisedSub τ ≫ raisedSub σ ≫ A.code :=
  Target.two_substitutions A σ τ
example : (A.reindex (τ ≫ σ)).code = raisedSub (τ ≫ σ) ≫ A.code :=
  Target.code_substitution A (τ ≫ σ)
example : decode ((A.reindex σ).reindex τ).code ≅ (A.reindex (τ ≫ σ)).family :=
  Target.comparison ((A.reindex σ).reindex τ)
example : decodedLocalFamily ((A.reindex σ).reindex τ).code = A.reindex (τ ≫ σ) :=
  Target.record_recovery ((A.reindex σ).reindex τ)

/-- Recovery checks both values in the two-element dependent fiber. -/
example (n : Fin 2) :
    (Target.comparison A).hom.app (point true) ⟨n⟩ = ⟨n⟩ :=
  eq_of_heq ((Target.evaluation A).component_heq (point true) ⟨n⟩)
example : (Target.comparison A).hom.app (point false) ⟨0⟩ = ⟨0⟩ :=
  eq_of_heq ((Target.evaluation A).component_heq (point false) ⟨0⟩)
end Dependent

/-- A shared proof does not supply the obstructed cross-model interval route. -/
example
    (η : Cartesian.inclusion.op ⋙ yoneda.obj (⟨1⟩ : SquareKit.Cubical.Cube) ⟶
      yoneda.obj (⟨1⟩ : Cartesian.Cube))
    (h : ∀ b, η.app (.op ⟨0⟩) (Cube.endpoint ⟨0⟩ b) = Cartesian.Cube.endpoint ⟨0⟩ b) : False :=
  Examples.CartesianWitnessPreservation.no_interval_retraction η h
end Examples.SharedRepresentableClassification
