import Examples.TwoFamilyFiniteDependentTail
import SquareKit.Internal.PathTransport.TwoFamilyFiniteDependentTailSubstitution
import SquareKit.Internal.PathTransport.TwoFamilyPathContractionReindex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 500000
namespace Examples.TwoFamilyFiniteDependentTailSubstitution
open CategoryTheory Bicategory SquareKit SquareKit.Internal.PathTransport
open TwoFamily TwoFamily.FiniteDependentTail
open Examples.TwoOpenIdentityHigher Examples.TwoFamilyFiniteDependentTail
local instance : IsGroupoid B where
  all_isIso f := by
    obtain ⟨g, h, k⟩ := DoubleDelooping.one_inverse (Multiplicative ℤ) f
    exact ⟨⟨g, h, k⟩⟩
local instance : ∀x, IsGroupoid (integerFamily.obj x) := fun _ => inferInstanceAs (IsGroupoid B)
local instance : ∀x, IsLocallyGroupoid (integerFamily.obj x) := fun _ => inferInstanceAs (IsLocallyGroupoid B)

def presentation (F : Family.{0,0,0,0,0,0} B)
    [∀x, IsGroupoid (F.obj x)] [∀x, IsLocallyGroupoid (F.obj x)] :
    ContractionPresentation ⟨PathContext F⟩ where
  source := ⟨Total F⟩
  sourceObjects := inferInstance
  sourceCells := inferInstance
  inclusion := pathReflexivity F
  retraction := pathFirst F
  homotopy := pathContraction F

def pathMap (F : Family.{0,0,0,0,0,0} B)
    [∀x, IsGroupoid (F.obj x)] [∀x, IsLocallyGroupoid (F.obj x)] (σ : StrictPseudofunctor B B) :
    ContractionMap (presentation F) (presentation (reindex σ F)) (pathReindex F σ) :=
  ⟨reindexHigher F σ⟩
theorem pathMap_lawful (F : Family.{0,0,0,0,0,0} B)
    [∀x, IsGroupoid (F.obj x)] [∀x, IsLocallyGroupoid (F.obj x)] (σ : StrictPseudofunctor B B) :
    (pathMap F σ).Lawful :=
  ⟨pathReindex_reflexivity F σ, (pathReindex_first F σ).symm, pathContraction_reindex F σ⟩

variable (σ τ : StrictPseudofunctor B B)
def once := dependentTail.reindexTail (Δ := ⟨PathContext (reindex σ integerFamily)⟩) (pathReindex integerFamily σ)
def branchOnce := dependentTail.reindexBranch initial (presentation (reindex σ integerFamily))
  (pathReindex integerFamily σ) (pathMap integerFamily σ) (pathMap_lawful integerFamily σ)
  selectedMotive selectedBranch
def motiveOnce := reindex (once σ).substitution selectedMotive
def resultOnce := (once σ).tail.eliminate (presentation (reindex σ integerFamily))
  (motiveOnce σ) (branchOnce σ)

theorem selected_substitution :
    (dependentTail.eliminate initial selectedMotive selectedBranch).reindex selectedMotive
      (once σ).substitution = resultOnce σ :=
  dependentTail.eliminate_reindex initial (presentation (reindex σ integerFamily))
    (pathReindex integerFamily σ) (pathMap integerFamily σ) (pathMap_lawful integerFamily σ)
    selectedMotive selectedBranch

def twice := (once σ).tail.reindexTail (Δ := ⟨PathContext (reindex τ (reindex σ integerFamily))⟩) (pathReindex (reindex σ integerFamily) τ)
def branchTwice := (once σ).tail.reindexBranch (presentation (reindex σ integerFamily))
  (presentation (reindex τ (reindex σ integerFamily))) (pathReindex (reindex σ integerFamily) τ)
  (pathMap (reindex σ integerFamily) τ) (pathMap_lawful (reindex σ integerFamily) τ)
  (motiveOnce σ) (branchOnce σ)
def resultTwice := (twice σ τ).tail.eliminate (presentation (reindex τ (reindex σ integerFamily)))
  (reindex (twice σ τ).substitution (motiveOnce σ)) (branchTwice σ τ)

/-- The selected branch survives two independently chosen context substitutions. -/
theorem selected_two_substitutions :
    ((dependentTail.eliminate initial selectedMotive selectedBranch).reindex selectedMotive
      (once σ).substitution).reindex (motiveOnce σ) (twice σ τ).substitution = resultTwice σ τ := by
  have h1 := congrArg (fun s : Section (motiveOnce σ) => s.reindex _ (twice σ τ).substitution)
    (selected_substitution σ)
  have h2 := (once σ).tail.eliminate_reindex (presentation (reindex σ integerFamily))
    (presentation (reindex τ (reindex σ integerFamily))) (pathReindex (reindex σ integerFamily) τ)
    (pathMap (reindex σ integerFamily) τ) (pathMap_lawful (reindex σ integerFamily) τ)
    (motiveOnce σ) (branchOnce σ)
  exact h1.trans h2
end Examples.TwoFamilyFiniteDependentTailSubstitution
