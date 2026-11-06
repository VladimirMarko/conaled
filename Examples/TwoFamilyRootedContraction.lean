import SquareKit.Internal.PathTransport.TwoFamilyRootedComponent
import SquareKit.Internal.PathTransport.TwoFamilyRootedNaturality
import Examples.TwoFamilyRootedPath
namespace Examples.TwoFamilyRootedContraction
open CategoryTheory Bicategory SquareKit SquareKit.Internal.PathTransport
open Examples.TwoFamilyEndpointSections Examples.TwoFamilyStructuralModel
open TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
local instance : IsLocallyGroupoid (Total Examples.TwoOpenIdentityHigher.integerFamily) :=
  inferInstanceAs (IsLocallyGroupoid Examples.TwoFamilyModelData.integers.total)
local instance : ∀ γ, IsGroupoid (displayed.obj γ) := display.groupoid
local instance : ∀ γ, IsLocallyGroupoid (displayed.obj γ) := display.locallyGroupoid
noncomputable def inclusion := rootedReflexivity displayed selected
noncomputable def retraction := rootedRetraction displayed selected
noncomputable def contraction := rootedContraction displayed selected
noncomputable def motive := reindex retraction displayed

theorem branchFamily : reindex inclusion motive = displayed := by
  unfold motive inclusion retraction
  rw [reindex_comp, rootedReflexivity_retraction, reindex_id]
noncomputable def branch : Section (reindex inclusion motive) := Section.cast branchFamily.symm selected
noncomputable def result : Section motive := retractionJ inclusion retraction contraction motive branch
example : result.reindex motive inclusion = branch :=
  retractionJ_beta inclusion retraction contraction
    (rootedReflexivity_retraction displayed selected) (rootedContraction_reflexive displayed selected) motive branch
example : HEq (strongPostcomp contraction (rootedPathEmbedding displayed selected))
    (strongPrecomp (pathContraction displayed) (rootedPathEmbedding displayed selected)) :=
  rootedContraction_embedding displayed selected

variable (σ τ : StrictPseudofunctor (Total Examples.TwoOpenIdentityHigher.integerFamily)
  (Total Examples.TwoOpenIdentityHigher.integerFamily))
example : HEq (strongPostcomp (rootedContraction (reindex σ displayed) (selected.reindex displayed σ))
    (rootedSubstitution displayed selected σ))
    (strongPrecomp contraction (rootedSubstitution displayed selected σ)) :=
  rootedContraction_reindex displayed selected σ
example : HEq (strongPostcomp
    (rootedContraction (reindex τ (reindex σ displayed)) ((selected.reindex displayed σ).reindex _ τ))
    (rootedSubstitution (reindex σ displayed) (selected.reindex displayed σ) τ))
    (strongPrecomp (rootedContraction (reindex σ displayed) (selected.reindex displayed σ))
      (rootedSubstitution (reindex σ displayed) (selected.reindex displayed σ) τ)) :=
  rootedContraction_reindex (reindex σ displayed) (selected.reindex displayed σ) τ
end Examples.TwoFamilyRootedContraction
