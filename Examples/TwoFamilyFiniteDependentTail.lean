import SquareKit.Internal.PathTransport.TwoFamilyFiniteDependentTailBeta
import SquareKit.Internal.PathTransport.TwoFamilyPathContractionReflexive
import SquareKit.Internal.PathTransport.TwoFamilyFiniteDependentTail
import Examples.TwoStrongInverse
noncomputable section
namespace Examples.TwoFamilyFiniteDependentTail
open CategoryTheory Bicategory SquareKit SquareKit.Internal.PathTransport
open Examples.TwoOpenIdentityHigher Examples.TwoFamilyPathContext
open TwoFamily TwoFamily.FiniteDependentTail
local instance : IsGroupoid B where
  all_isIso f := by
    obtain ⟨g, h, k⟩ := DoubleDelooping.one_inverse (Multiplicative ℤ) f
    exact ⟨⟨g, h, k⟩⟩
local instance : ∀x, IsGroupoid (integerFamily.obj x) := fun _ => inferInstanceAs (IsGroupoid B)
local instance : ∀x, IsLocallyGroupoid (integerFamily.obj x) := fun _ => inferInstanceAs (IsLocallyGroupoid B)

abbrev motive := TwoFamilyPathJBeta.motive

def initial : ContractionPresentation ⟨PathContext integerFamily⟩ where
  source := ⟨Total integerFamily⟩
  sourceObjects := inferInstance
  sourceCells := inferInstance
  inclusion := pathReflexivity integerFamily
  retraction := pathFirst integerFamily
  homotopy := pathContraction integerFamily

/-- The second extension is the identity type of the endpoints in the first extension. -/
def dependentTail : FiniteDependentTail ⟨PathContext integerFamily⟩ 2 ⟨PathContext motive⟩ :=
  let one : FiniteDependentTail ⟨PathContext integerFamily⟩ 1 ⟨Total (endpointFamily motive)⟩ :=
    (FiniteDependentTail.nil (Γ := ⟨PathContext integerFamily⟩)).snoc (endpointFamily motive)
      (fun _ => inferInstance) (fun _ => inferInstance)
  one.snoc (openIdHigher motive) (fun _ => inferInstance) (fun _ => inferInstance)

universe uM vM wM
/-- Both dependent extensions admit every higher motive and its selected reflexive branch. -/
def eliminate (E : Family.{0,0,0,uM,vM,wM} (PathContext motive))
    (d : Section (reindex (dependentTail.liftSplit initial).inclusion E)) : Section E :=
  dependentTail.eliminate initial E d
/-- The starting presentation carries the actual whole reflexive normalization. -/
example : HEq (strongPrecomp initial.homotopy initial.inclusion)
    (Pseudofunctor.StrongTrans.id initial.inclusion.toPseudofunctor) :=
  pathContraction_reflexive integerFamily

/-- Generic contraction computation recovers the selected higher branch exactly. -/
example : (retractionJ initial.inclusion initial.retraction initial.homotopy motive
    TwoFamilyPathJBeta.branch).reindex motive initial.inclusion = TwoFamilyPathJBeta.branch :=
  retractionJ_beta _ _ _ (pathReflexivity_first integerFamily)
    (pathContraction_reflexive integerFamily) motive TwoFamilyPathJBeta.branch
theorem initial_normalized : initial.Normalized :=
  ⟨pathReflexivity_first integerFamily, pathContraction_reflexive integerFamily⟩

/-- Every chosen branch returns unchanged after both genuinely dependent extensions. -/
theorem recovered_branch (E : Family.{0,0,0,uM,vM,wM} (PathContext motive))
    (d : Section (reindex (dependentTail.liftSplit initial).inclusion E)) :
    (eliminate E d).reindex E (dependentTail.liftSplit initial).inclusion = d :=
  dependentTail.eliminate_beta initial initial_normalized E d

abbrev selectedMotive := reindex (pathFirst motive) (reindex (projectionHigher motive) motive)
def selectedSection : Section selectedMotive :=
  (variableSection motive).reindex (reindex (projectionHigher motive) motive) (pathFirst motive)
def selectedBranch : Section (reindex (dependentTail.liftSplit initial).inclusion selectedMotive) :=
  selectedSection.reindex selectedMotive (dependentTail.liftSplit initial).inclusion

/-- A concrete higher generic-variable section is recovered as selected data, not mere existence. -/
example : (eliminate selectedMotive selectedBranch).reindex selectedMotive
    (dependentTail.liftSplit initial).inclusion = selectedBranch :=
  recovered_branch selectedMotive selectedBranch
end Examples.TwoFamilyFiniteDependentTail
