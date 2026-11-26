import SquareKit.Internal.DependentJudgments.Memo
import SquareKit.Internal.DependentJudgments.LiftFunctoriality

/-! The varying certificate section specializes to the original, freshly
constructed formulas. These are source equations, including the selected J
witness; semantic equality is not reflected back into the source theory. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Memo.Parameters
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
noncomputable section
variable {V : Type} {Ω : List (Judgment V)} (F : Parameters Ω)
variable {p : Expression V} (hp : Tm (Ω := Ω) F.Γ F.pathType p)

private def baseTypeAtPath : Equal (Ω := Ω) (subTy F.varying.A (F.atPath p)) F.A :=
  F.xTyping.family.weakenSection hp

private def dependentFamilyAtPath : Equal (Ω := Ω) (subTy F.varying.B (lift F.Γ F.varying.A (F.atPath p))) F.B :=
  F.familyFormation.displayWeakenSection F.xTyping.family hp

private def xAtPath : Equal (Ω := Ω) (subTm F.varying.x (F.atPath p)) F.x := F.xTyping.weakenSection hp
private def yAtPath : Equal (Ω := Ω) (subTm F.varying.y (F.atPath p)) F.y := F.yTyping.weakenSection hp
private def zAtPath : Equal (Ω := Ω) (subTm F.varying.z (F.atPath p)) F.z := F.zTyping.weakenSection hp
private def qAtPath : Equal (Ω := Ω) (subTm F.varying.q (F.atPath p)) F.q := F.qTyping.weakenSection hp
private def uAtPath : Equal (Ω := Ω) (subTm F.varying.u (F.atPath p)) F.u := F.uTyping.weakenSection hp
private def pAtPath : Equal (Ω := Ω) (subTm F.variablePath (F.atPath p)) p := hp.sectionGeneric

private def innerValueAtPath : Equal (Ω := Ω)
    (subTm (transport F.varying.Γ F.varying.A F.varying.B F.varying.x F.varying.y F.variablePath F.varying.u) (F.atPath p))
    (transport F.Γ F.A F.B F.x F.y p F.u) :=
  (Tm.transportSub F.varying.familyFormation F.varying.xTyping F.varying.yTyping F.variablePathTyping F.varying.uTyping hp.section).transitive
    (Equal.transport (.reflexive F.Γ) (baseTypeAtPath F hp) (dependentFamilyAtPath F hp) (xAtPath F hp) (yAtPath F hp) (pAtPath F hp) (uAtPath F hp))

/-- Specializing the varying value reconstructs the original two transports. -/
def valueAtPath : Equal (Ω := Ω) (F.value p)
    (transport F.Γ F.A F.B F.y F.z F.q (transport F.Γ F.A F.B F.x F.y p F.u)) :=
  (Tm.transportSub F.varying.familyFormation F.varying.yTyping F.varying.zTyping F.varying.qTyping
    (Tm.transport F.varying.familyFormation F.varying.xTyping F.varying.yTyping F.variablePathTyping F.varying.uTyping) hp.section).transitive
      (Equal.transport (.reflexive F.Γ) (baseTypeAtPath F hp) (dependentFamilyAtPath F hp) (yAtPath F hp) (zAtPath F hp)
        (qAtPath F hp) (innerValueAtPath F hp))

private def compositePathAtPath : Equal (Ω := Ω)
    (subTm (concat F.varying.Γ F.varying.A F.varying.x F.varying.y F.varying.z F.variablePath F.varying.q) (F.atPath p))
    (concat F.Γ F.A F.x F.y F.z p F.q) :=
  (F.varying.xTyping.concatSub F.varying.yTyping F.varying.zTyping F.variablePathTyping F.varying.qTyping hp.section).transitive
    (Equal.concat (.reflexive F.Γ) (baseTypeAtPath F hp) (xAtPath F hp) (yAtPath F hp) (zAtPath F hp) (pAtPath F hp) (qAtPath F hp))

def compositeValueAtPath : Equal (Ω := Ω) (F.compositeValue p)
    (transport F.Γ F.A F.B F.x F.z (concat F.Γ F.A F.x F.y F.z p F.q) F.u) :=
  (Tm.transportSub F.varying.familyFormation F.varying.xTyping F.varying.zTyping
    (F.varying.xTyping.concat F.varying.yTyping F.varying.zTyping F.variablePathTyping F.varying.qTyping)
    F.varying.uTyping hp.section).transitive
      (Equal.transport (.reflexive F.Γ) (baseTypeAtPath F hp) (dependentFamilyAtPath F hp) (xAtPath F hp) (zAtPath F hp)
        (compositePathAtPath F hp) (uAtPath F hp))

/-- This compares the selected certificate itself, not only its endpoints. -/
def certificateAtPath : Equal (Ω := Ω) (F.certificate p) (eta F.Γ F.A F.B F.x F.y F.z p F.q F.u) :=
  (Tm.etaSub F.varying.familyFormation F.varying.xTyping F.varying.yTyping F.variablePathTyping F.varying.uTyping
    hp.section F.varying.zTyping F.varying.qTyping).transitive
      (Equal.eta (.reflexive F.Γ) (baseTypeAtPath F hp) (dependentFamilyAtPath F hp) (xAtPath F hp) (yAtPath F hp) (zAtPath F hp)
        (pAtPath F hp) (qAtPath F hp) (uAtPath F hp))

def fiberAtPath : Equal (Ω := Ω) (F.fiber p) (subTy F.B (sectionSub F.Γ F.A F.z)) :=
  (F.varying.familyFormation.sectionLift hp.section F.varying.zTyping).symmetric.transitive
    (Equal.subTy (dependentFamilyAtPath F hp) (Equal.sectionSub (.reflexive F.Γ) (baseTypeAtPath F hp) (zAtPath F hp)))

def certificateTypeAtPath : Equal (Ω := Ω) (F.certificateType p)
    (identity (subTy F.B (sectionSub F.Γ F.A F.z))
      (transport F.Γ F.A F.B F.y F.z F.q (transport F.Γ F.A F.B F.x F.y p F.u))
      (transport F.Γ F.A F.B F.x F.z (concat F.Γ F.A F.x F.y F.z p F.q) F.u)) :=
  (F.certificateTypeNormalization hp).transitive
    (Equal.identity (F.fiberAtPath hp) (F.valueAtPath hp) (F.compositeValueAtPath hp))

variable {p' h : Expression V} (hp' : Tm (Ω := Ω) F.Γ F.pathType p')
  (hh : Tm (Ω := Ω) F.Γ (identity F.pathType p p') h)

/-- The first endpoint of dependent action keeps its actual transport in the
varying certificate family; only its selected source value is normalized. -/
def transportedCertificateAtPath : Equal (Ω := Ω) (F.transportedCertificate p p' h)
    (transport F.Γ F.pathType F.certificateFamily p p' h (eta F.Γ F.A F.B F.x F.y F.z p F.q F.u)) :=
  Equal.transport (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _)
    (F.certificateAtPath hp)

def normalizedDependentActionTyping : Tm (Ω := Ω) F.Γ
    (identity
      (identity (subTy F.B (sectionSub F.Γ F.A F.z))
        (transport F.Γ F.A F.B F.y F.z F.q (transport F.Γ F.A F.B F.x F.y p' F.u))
        (transport F.Γ F.A F.B F.x F.z (concat F.Γ F.A F.x F.y F.z p' F.q) F.u))
      (transport F.Γ F.pathType F.certificateFamily p p' h (eta F.Γ F.A F.B F.x F.y F.z p F.q F.u))
      (eta F.Γ F.A F.B F.x F.y F.z p' F.q F.u))
    (F.dependentAction p p' h) :=
  (F.dependentActionTyping hp hp' hh).convert
    (Equal.identity (F.certificateTypeAtPath hp') (F.transportedCertificateAtPath hp) (F.certificateAtPath hp'))

end
end SquareKit.Internal.DependentJudgments.Contextual.Memo.Parameters
