import SquareKit.SmoothQuotientGeneratedSectionDescent
import SquareKit.SmoothQuotientGeneratedBaseMatchingRecovery
import Examples.PrimitiveCechMatching

/-! A nontrivial ineffective torsor enters generated matching and is recovered. -/
noncomputable section
namespace Examples.GeneratedNontrivialDescent
open CategoryTheory SquareKit SheafActionQuotient SmoothOpenSite
open Internal.PathTransport GroupoidModel SmoothQuotientGeneratedMatching
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
variable (K : Type) [Group K] (c : K) (A : SplitSheaf.Ty SmoothClutching.base)
local notation "act" => ActionQuotientEvidence.ineffective K
local notation "h₀" => Typed.CtxDeriv.empty
local notation "h₁" => Typed.CtxDeriv.ext h₀ (Typed.TyDeriv.base h₀)

def primitive : SheafActionQuotient.Cech.Datum (a := act) A :=
  SheafActionQuotient.Cech.ofDescent
    (Descent.canonicalDatum A (ActionQuotientEvidence.nontrivialObject K c))

def emptyDatum : Datum act h₀ A :=
  (SmoothQuotientCechLocal.matchingEvaluation act A h₀).obj (Discrete.mk PUnit.unit)

def dependentDatum : (relativeMatchingFamily act h₀ (.base h₀) A).obj (emptyDatum K A) :=
  ((basePrimitiveFamilyIso act h₀ A).inv.app (emptyDatum K A)).obj
    (AsSmall.up.obj (primitive K c A))

/-- This generated datum uses the actual primitive torsor and its overlap. -/
def matching : Datum act h₁ A :=
  (dependentComprehensionEquivalence act h₀ (.base h₀) A).functor.obj
    ⟨emptyDatum K A, dependentDatum K c A⟩

variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

/-- Actual generated restriction recovers the complete matching object. -/
def recovered : (restrictionFunctor act h₁ A).obj
    ((descentEquivalence act A h₁).inverse.obj (matching K c A)) ≅ matching K c A :=
  (descentEquivalence act A h₁).counitIso.app (matching K c A)

/-- Selected generated matching arrows are not collapsed by descent. -/
example (p q : matching K c A ⟶ matching K c A) (hpq : p ≠ q) :
    (descentEquivalence act A h₁).inverse.map p ≠ (descentEquivalence act A h₁).inverse.map q :=
  fun h => hpq ((descentEquivalence act A h₁).inverse.map_injective h)

end Examples.GeneratedNontrivialDescent
