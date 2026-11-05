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

private def A_atPath : Equal (Ω := Ω) (subTy F.varying.A (F.atPath p)) F.A :=
  F.x_typed.family.weakenSection hp

private def B_atPath : Equal (Ω := Ω) (subTy F.varying.B (lift F.Γ F.varying.A (F.atPath p))) F.B :=
  F.B_typed.displayWeakenSection F.x_typed.family hp

private def x_atPath : Equal (Ω := Ω) (subTm F.varying.x (F.atPath p)) F.x := F.x_typed.weakenSection hp
private def y_atPath : Equal (Ω := Ω) (subTm F.varying.y (F.atPath p)) F.y := F.y_typed.weakenSection hp
private def z_atPath : Equal (Ω := Ω) (subTm F.varying.z (F.atPath p)) F.z := F.z_typed.weakenSection hp
private def q_atPath : Equal (Ω := Ω) (subTm F.varying.q (F.atPath p)) F.q := F.q_typed.weakenSection hp
private def u_atPath : Equal (Ω := Ω) (subTm F.varying.u (F.atPath p)) F.u := F.u_typed.weakenSection hp
private def p_atPath : Equal (Ω := Ω) (subTm F.variablePath (F.atPath p)) p := hp.sectionGeneric

private def innerValue_atPath : Equal (Ω := Ω)
    (subTm (transport F.varying.Γ F.varying.A F.varying.B F.varying.x F.varying.y F.variablePath F.varying.u) (F.atPath p))
    (transport F.Γ F.A F.B F.x F.y p F.u) :=
  (Tm.transportSub F.varying.B_typed F.varying.x_typed F.varying.y_typed F.variablePath_typed F.varying.u_typed hp.section).transitive
    (Equal.transport (.reflexive F.Γ) (A_atPath F hp) (B_atPath F hp) (x_atPath F hp) (y_atPath F hp) (p_atPath F hp) (u_atPath F hp))

/-- Specializing the varying value reconstructs the original two transports. -/
def value_atPath : Equal (Ω := Ω) (F.value p)
    (transport F.Γ F.A F.B F.y F.z F.q (transport F.Γ F.A F.B F.x F.y p F.u)) :=
  (Tm.transportSub F.varying.B_typed F.varying.y_typed F.varying.z_typed F.varying.q_typed
    (Tm.transport F.varying.B_typed F.varying.x_typed F.varying.y_typed F.variablePath_typed F.varying.u_typed) hp.section).transitive
      (Equal.transport (.reflexive F.Γ) (A_atPath F hp) (B_atPath F hp) (y_atPath F hp) (z_atPath F hp)
        (q_atPath F hp) (innerValue_atPath F hp))

private def compositePath_atPath : Equal (Ω := Ω)
    (subTm (concat F.varying.Γ F.varying.A F.varying.x F.varying.y F.varying.z F.variablePath F.varying.q) (F.atPath p))
    (concat F.Γ F.A F.x F.y F.z p F.q) :=
  (F.varying.x_typed.concatSub F.varying.y_typed F.varying.z_typed F.variablePath_typed F.varying.q_typed hp.section).transitive
    (Equal.concat (.reflexive F.Γ) (A_atPath F hp) (x_atPath F hp) (y_atPath F hp) (z_atPath F hp) (p_atPath F hp) (q_atPath F hp))

def compositeValue_atPath : Equal (Ω := Ω) (F.compositeValue p)
    (transport F.Γ F.A F.B F.x F.z (concat F.Γ F.A F.x F.y F.z p F.q) F.u) :=
  (Tm.transportSub F.varying.B_typed F.varying.x_typed F.varying.z_typed
    (F.varying.x_typed.concat F.varying.y_typed F.varying.z_typed F.variablePath_typed F.varying.q_typed)
    F.varying.u_typed hp.section).transitive
      (Equal.transport (.reflexive F.Γ) (A_atPath F hp) (B_atPath F hp) (x_atPath F hp) (z_atPath F hp)
        (compositePath_atPath F hp) (u_atPath F hp))

/-- This compares the selected certificate itself, not only its endpoints. -/
def certificate_atPath : Equal (Ω := Ω) (F.certificate p) (eta F.Γ F.A F.B F.x F.y F.z p F.q F.u) :=
  (Tm.etaSub F.varying.B_typed F.varying.x_typed F.varying.y_typed F.variablePath_typed F.varying.u_typed
    hp.section F.varying.z_typed F.varying.q_typed).transitive
      (Equal.eta (.reflexive F.Γ) (A_atPath F hp) (B_atPath F hp) (x_atPath F hp) (y_atPath F hp) (z_atPath F hp)
        (p_atPath F hp) (q_atPath F hp) (u_atPath F hp))

def fiber_atPath : Equal (Ω := Ω) (F.fiber p) (subTy F.B (sectionSub F.Γ F.A F.z)) :=
  (F.varying.B_typed.sectionLift hp.section F.varying.z_typed).symmetric.transitive
    (Equal.subTy (B_atPath F hp) (Equal.sectionSub (.reflexive F.Γ) (A_atPath F hp) (z_atPath F hp)))

def certificateType_atPath : Equal (Ω := Ω) (F.certificateType p)
    (identity (subTy F.B (sectionSub F.Γ F.A F.z))
      (transport F.Γ F.A F.B F.y F.z F.q (transport F.Γ F.A F.B F.x F.y p F.u))
      (transport F.Γ F.A F.B F.x F.z (concat F.Γ F.A F.x F.y F.z p F.q) F.u)) :=
  (F.certificateType_eq hp).transitive
    (Equal.identity (F.fiber_atPath hp) (F.value_atPath hp) (F.compositeValue_atPath hp))

variable {p' h : Expression V} (hp' : Tm (Ω := Ω) F.Γ F.pathType p')
  (hh : Tm (Ω := Ω) F.Γ (identity F.pathType p p') h)

/-- The first endpoint of dependent action keeps its actual transport in the
varying certificate family; only its selected source value is normalized. -/
def transportedCertificate_atPath : Equal (Ω := Ω) (F.transportedCertificate p p' h)
    (transport F.Γ F.pathType F.certificateFamily p p' h (eta F.Γ F.A F.B F.x F.y F.z p F.q F.u)) :=
  Equal.transport (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _) (.reflexive _)
    (F.certificate_atPath hp)

def dependentAction_normalized : Tm (Ω := Ω) F.Γ
    (identity
      (identity (subTy F.B (sectionSub F.Γ F.A F.z))
        (transport F.Γ F.A F.B F.y F.z F.q (transport F.Γ F.A F.B F.x F.y p' F.u))
        (transport F.Γ F.A F.B F.x F.z (concat F.Γ F.A F.x F.y F.z p' F.q) F.u))
      (transport F.Γ F.pathType F.certificateFamily p p' h (eta F.Γ F.A F.B F.x F.y F.z p F.q F.u))
      (eta F.Γ F.A F.B F.x F.y F.z p' F.q F.u))
    (F.dependentAction p p' h) :=
  (F.dependentAction_typed hp hp' hh).convert
    (Equal.identity (F.certificateType_atPath hp') (F.transportedCertificate_atPath hp) (F.certificate_atPath hp'))

end
end SquareKit.Internal.DependentJudgments.Contextual.Memo.Parameters
