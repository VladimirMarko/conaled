import SquareKit.Internal.PathTransport.TwoFamilyIdentityValueConjugation
import SquareKit.Internal.PathTransport.TwoFamilySourceIdentityFiberAction
import SquareKit.Internal.DependentJudgments.FixedPathBetaSemantics
import Examples.TwoFamilySelectedOrdinaryAction
namespace Examples.TwoFamilySelectedOrdinaryAction
open CategoryTheory Bicategory SquareKit.Internal.PathTransport HigherInterpretation
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open Examples.FrozenMemoStages Examples.SelectedOrdinaryAction
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C D : Context.{u}) (R : SelectedPaths (structuralModel C D))
local notation "M" => fullModel C D
local notation "I" => pathType M R
local notation "T" => transport M R
noncomputable def SelectedIdentityFiberAction : Prop :=
 IdentityFiberValueFormula R.family R.x.down R.y.down R.p.down R.p'.down (T).down
  (ordinaryActionFamily C D I R.p.down R.p'.down (T).down)
  (fun h => (ordinaryApValue M I I ⟨(T).down⟩ ⟨R.p.down⟩ ⟨R.p'.down⟩ ⟨h⟩).down)
noncomputable def SelectedSourceConjugation : Prop :=
 IdentityFiberValueConjugationAt R.family R.x.down R.y.down R.p.down R.p'.down (T).down
  (ordinaryActionFamily C D I R.p.down R.p'.down (T).down)
  (fun h => (ordinaryApValue M I I ⟨(T).down⟩ ⟨R.p.down⟩ ⟨R.p'.down⟩ ⟨h⟩).down)
  (fixedPathBetaSection M R.family R.x R.y).down R.h.down
theorem selectedSourceConjugation_of_action (ha : SelectedIdentityFiberAction C D R) :
 SelectedSourceConjugation C D R :=
 identityFiberValue_conjugation R.family R.x.down R.y.down R.p.down R.p'.down (T).down
  (ordinaryActionFamily C D I R.p.down R.p'.down (T).down)
  (fun h => (ordinaryApValue M I I ⟨(T).down⟩ ⟨R.p.down⟩ ⟨R.p'.down⟩ ⟨h⟩).down)
  (fixedPathBetaSection M R.family R.x R.y).down ha R.h.down
theorem selectedIdentityFiberAction
 [hobj : ∀ γ, Subsingleton ((I).data.obj γ)] : SelectedIdentityFiberAction C D R :=
 @sourceIdentityFiberAction C D _ R.family R.x.down R.y.down R.p.down R.p'.down (T).down hobj
theorem selectedSourceConjugation
 [∀ γ, Subsingleton ((I).data.obj γ)] : SelectedSourceConjugation C D R :=
 selectedSourceConjugation_of_action C D R (selectedIdentityFiberAction C D R)
end Examples.TwoFamilySelectedOrdinaryAction
