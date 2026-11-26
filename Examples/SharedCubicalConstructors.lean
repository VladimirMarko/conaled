import SquareKit.Internal.Cubical.SmallFamilyGlue
import SquareKit.Internal.Cubical.SmallFamilyConstructors
import SquareKit.Internal.Cubical.CartesianSmallFamilyClassification
import Examples.CartesianWitnessPreservation
import Examples.CartesianSmallFamilyClassification
import Examples.CartesianClassifier

/-! A bounded comparison of dependent-sum admission. Each classifier recovers
its native selected operation. The underlying restriction comparison is separate
from a comparison of filling structures. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.SharedCubicalConstructors
open CategoryTheory SquareKit.Cubical
universe u

namespace Original
open Presheaf
variable {Γ : Context.{u}} (A : LocalFamily Γ) (B : LocalFamily (total A.family))

theorem sigma_record : decodedLocalFamily (A.sigma B).code = A.sigma B :=
  (A.sigma B).decoded_code

/-- Extending the decoded operation recovers the actual global Sigma algorithm. -/
theorem sigma_global : HEq (decodedLocalFamily (A.sigma B).code).toNative.filling
    (sigmaFilling A.toNative.filling A.toNative.lawful B.toNative.filling) := by
  rw [sigma_record]
  exact heq_of_eq ((sigmaFilling A.toNative.filling A.toNative.lawful
    B.toNative.filling).toLocal_toFilling
      (sigmaFilling_lawful _ A.toNative.lawful _ B.toNative.lawful))

/-- Recovery compares complete output sections, for every admissible face. -/
theorem sigma_selected {I : Cube}
    (p : total (interval (representable.{u} I)) ⟶ Γ)
    (φ : Cofibration (representable.{u} I))
    (b : OpenBox (reindex (decode (A.sigma B).code) p) φ) :
    (A.sigma B).filling.fill p φ
      (b.map (Functor.whiskerLeft p.mapElements (A.sigma B).decodeCodeIso.hom)) =
    Term.map (Functor.whiskerLeft p.mapElements (A.sigma B).decodeCodeIso.hom)
      ((decodedLocalFilling (A.sigma B).code).fill p φ b) :=
  (A.sigma B).decodeCodeIso_fill p φ b
end Original

namespace Target
open Cartesian
variable {Γ : Context.{u}} (A : LocalFamily Γ) (B : LocalFamily (total A.family))

/-- Assemble from the actual Cartesian Sigma algorithm and its proved laws. -/
def sigmaFamily : LocalFamily Γ :=
  LocalFamily.ofFilling (sigma A.family B.family)
    (sigmaFilling A.toFilling A.toFilling_lawful B.toFilling)
    (sigmaFilling_lawful A.toFilling A.toFilling_lawful B.toFilling B.toFilling_lawful)

theorem sigma_record : decodedLocalFamily (sigmaFamily A B).code = sigmaFamily A B :=
  (sigmaFamily A B).decodedLocalFamily_code

/-- Global recovery retains the chosen dependent algorithm, not just its laws. -/
theorem sigma_global : HEq (decodedLocalFamily (sigmaFamily A B).code).toFilling
    (sigmaFilling A.toFilling A.toFilling_lawful B.toFilling) := by
  rw [sigma_record]
  exact heq_of_eq ((sigmaFilling A.toFilling A.toFilling_lawful B.toFilling).toLocal_toFilling
    (sigmaFilling_lawful _ A.toFilling_lawful _ B.toFilling_lawful))

/-- The starting section is arbitrary, including a genuine dimension variable. -/
theorem sigma_selected {I : Cartesian.Cube}
    (p : total (interval (representable.{u} I)) ⟶ Γ)
    (φ : Subcontext (representable.{u} I)) (r : Term (interval (representable I)))
    (b : OpenBox (reindex (decode (sigmaFamily A B).code) p) φ r) :
    (sigmaFamily A B).filling.fill p φ r
      (b.map (Functor.whiskerLeft p.mapElements (sigmaFamily A B).decodeCodeIso.hom)) =
    Term.map (Functor.whiskerLeft p.mapElements (sigmaFamily A B).decodeCodeIso.hom)
      ((decodedLocalFilling (sigmaFamily A B).code).fill p φ r b) :=
  (sigmaFamily A B).decodeCodeIso_fill p φ r b

/-- Classification commutes with two successive substitutions as complete codes. -/
theorem sigma_code_comp {Δ Θ : Context.{u}} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    (((sigmaFamily A B).reindex σ).reindex τ).code =
      raisedSub τ ≫ raisedSub σ ≫ (sigmaFamily A B).code := by
  rw [LocalFamily.code_reindex, LocalFamily.code_reindex]

/-- A variable cap is not the fixed false endpoint. -/
theorem variableSource_ne_false :
    CartesianSmallFamilyClassification.variableSource ≠
      endpoint (representable ⟨1⟩) false := by
  intro h
  have e := congrArg (fun t => t.val (representableGeneric ⟨1⟩)) h
  have e' := congrArg (fun d => d.down 0) e
  cases e'
/-- A genuinely dependent pair: the second fiber has one or two elements. -/
noncomputable def tags (Γ : Context.{u}) : LocalFamily Γ :=
  LocalFamily.ofFilling (Cartesian.ClassifierExamples.tags Γ)
    (Cartesian.ClassifierExamples.tagFilling Γ) (Cartesian.ClassifierExamples.tagFilling_lawful Γ)

noncomputable def branches (Γ : Context.{u}) : LocalFamily (total (tags Γ).family) :=
  LocalFamily.ofFilling (Cartesian.ClassifierExamples.branch Γ)
    (bijectiveFilling (Cartesian.ClassifierExamples.branch_restrictions Γ))
    (bijectiveFilling_lawful (Cartesian.ClassifierExamples.branch_restrictions Γ))

theorem dependent_sigma_record (Γ : Context.{u}) :
    decodedLocalFamily (sigmaFamily (tags Γ) (branches Γ)).code =
      sigmaFamily (tags Γ) (branches Γ) := sigma_record _ _

/-- The dependent example retains whole selected sections at the variable cap. -/
theorem dependent_sigma_variable {Γ : Context.{0}}
    (p : total (interval (representable ⟨1⟩)) ⟶ Γ)
    (φ : Subcontext (representable ⟨1⟩))
    (b : OpenBox (reindex (decode (sigmaFamily (tags Γ) (branches Γ)).code) p) φ
      CartesianSmallFamilyClassification.variableSource) :
    (sigmaFamily (tags Γ) (branches Γ)).filling.fill p φ
      CartesianSmallFamilyClassification.variableSource
      (b.map (Functor.whiskerLeft p.mapElements
        (sigmaFamily (tags Γ) (branches Γ)).decodeCodeIso.hom)) =
    Term.map (Functor.whiskerLeft p.mapElements
      (sigmaFamily (tags Γ) (branches Γ)).decodeCodeIso.hom)
      ((decodedLocalFilling (sigmaFamily (tags Γ) (branches Γ)).code).fill p φ
        CartesianSmallFamilyClassification.variableSource b) :=
  sigma_selected _ _ p φ _ b

end Target

/-- Restriction preserves the underlying dependent sum, with the dependent
second family pulled across the actual comprehension comparison. -/
def sigmaRestriction {Γ : Presheaf.Context.{u}} (A : Presheaf.Family Γ)
    (B : Presheaf.Family (Presheaf.total A)) :
    Cartesian.restrictFamily (Presheaf.sigma A B) ≅
      Cartesian.sigma (Cartesian.restrictFamily A)
        ((Cartesian.totalComparison A).inv.mapElements ⋙ Cartesian.restrictFamily B) :=
  Cartesian.sigmaComparison A B

/-- An endpoint-preserving interval identification would already contradict
naturality at reversal. This does not prohibit weaker comparison routes. -/
theorem no_interval_identification
    (i : Cartesian.inclusion.op ⋙ yoneda.obj (⟨1⟩ : Cube) ≅
      yoneda.obj (⟨1⟩ : Cartesian.Cube))
    (h : ∀ b, i.hom.app (.op ⟨0⟩) (Cube.endpoint ⟨0⟩ b) =
      Cartesian.Cube.endpoint ⟨0⟩ b) : False :=
  CartesianWitnessPreservation.no_interval_retraction i.hom h

end Examples.SharedCubicalConstructors
