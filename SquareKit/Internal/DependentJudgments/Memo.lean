import SquareKit.Internal.DependentJudgments.DerivedReindexing

/-! The memo's selected certificate is a section in its first path argument.
Its dependent action is generated from that section; its source is transported
in the certificate family. The package remains contextual, without Sigma. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Memo
open GuardedTheory
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}

/-- Schematic source data, with a dependent family over the displayed `A`. -/
structure Parameters (Ω : List (Judgment V)) where
  Γ : Expression V
  A : Expression V
  B : Expression V
  x : Expression V
  y : Expression V
  z : Expression V
  q : Expression V
  u : Expression V
  x_typed : Tm (Ω := Ω) Γ A x
  y_typed : Tm (Ω := Ω) Γ A y
  z_typed : Tm (Ω := Ω) Γ A z
  B_typed : Ty (Ω := Ω) (extend Γ A) B
  q_typed : Tm (Ω := Ω) Γ (identity A y z) q
  u_typed : Tm (Ω := Ω) Γ (subTy B (sectionSub Γ A x)) u

namespace Parameters
variable (F : Parameters Ω)

abbrev pathType := identity F.A F.x F.y
abbrev pathContext := extend F.Γ F.pathType
abbrev pathProjection := weaken F.Γ F.pathType

def pathType_typed : Ty (Ω := Ω) F.Γ F.pathType := F.x_typed.identity F.y_typed

def reindex {Δ σ : Expression V} (hσ : Sub (Ω := Ω) Δ F.Γ σ) : Parameters Ω where
  Γ := Δ
  A := subTy F.A σ
  B := subTy F.B (lift Δ F.A σ)
  x := subTm F.x σ
  y := subTm F.y σ
  z := subTm F.z σ
  q := subTm F.q σ
  u := subTm F.u σ
  x_typed := F.x_typed.substitute hσ
  y_typed := F.y_typed.substitute hσ
  z_typed := F.z_typed.substitute hσ
  B_typed := F.B_typed.substitute (hσ.lift F.x_typed.family)
  q_typed := (F.q_typed.substitute hσ).convert (F.y_typed.identitySub F.z_typed hσ)
  u_typed := (F.u_typed.substitute hσ).convert (F.B_typed.sectionLift hσ F.x_typed).symmetric

/-- Expose a genuinely varying first path, retaining all other parameters. -/
def varying : Parameters Ω := F.reindex F.pathType_typed.weaken
abbrev variablePath : Expression V := generic F.Γ F.pathType

def variablePath_typed : Tm (Ω := Ω) F.pathContext
    (identity F.varying.A F.varying.x F.varying.y) F.variablePath :=
  F.pathType_typed.generic.convert (F.x_typed.identitySub F.y_typed F.pathType_typed.weaken)

abbrev varyingValue : Expression V :=
  transport F.varying.Γ F.varying.A F.varying.B F.varying.y F.varying.z F.varying.q
    (transport F.varying.Γ F.varying.A F.varying.B F.varying.x F.varying.y F.variablePath F.varying.u)
abbrev varyingCompositeValue : Expression V :=
  transport F.varying.Γ F.varying.A F.varying.B F.varying.x F.varying.z
    (concat F.varying.Γ F.varying.A F.varying.x F.varying.y F.varying.z F.variablePath F.varying.q) F.varying.u
abbrev varyingFiber : Expression V := subTy F.varying.B (sectionSub F.varying.Γ F.varying.A F.varying.z)
abbrev certificateFamily : Expression V := identity F.varyingFiber F.varyingValue F.varyingCompositeValue
abbrev certificateSection : Expression V :=
  eta F.varying.Γ F.varying.A F.varying.B F.varying.x F.varying.y F.varying.z F.variablePath F.varying.q F.varying.u

def varyingValue_typed : Tm (Ω := Ω) F.pathContext F.varyingFiber F.varyingValue :=
  Tm.transport F.varying.B_typed F.varying.y_typed F.varying.z_typed F.varying.q_typed
    (Tm.transport F.varying.B_typed F.varying.x_typed F.varying.y_typed F.variablePath_typed F.varying.u_typed)

def varyingCompositeValue_typed : Tm (Ω := Ω) F.pathContext F.varyingFiber F.varyingCompositeValue :=
  Tm.transport F.varying.B_typed F.varying.x_typed F.varying.z_typed
    (F.varying.x_typed.concat F.varying.y_typed F.varying.z_typed F.variablePath_typed F.varying.q_typed) F.varying.u_typed

def certificateSection_typed : Tm (Ω := Ω) F.pathContext F.certificateFamily F.certificateSection :=
  Tm.eta F.varying.B_typed F.varying.x_typed F.varying.y_typed F.variablePath_typed F.varying.u_typed
    F.varying.z_typed F.varying.q_typed

abbrev atPath (p : Expression V) := sectionSub F.Γ F.pathType p
abbrev value (p : Expression V) := subTm F.varyingValue (F.atPath p)
abbrev compositeValue (p : Expression V) := subTm F.varyingCompositeValue (F.atPath p)
abbrev fiber (p : Expression V) := subTy F.varyingFiber (F.atPath p)
abbrev certificateType (p : Expression V) := subTy F.certificateFamily (F.atPath p)
abbrev certificate (p : Expression V) := subTm F.certificateSection (F.atPath p)

def value_typed {p : Expression V} (hp : Tm (Ω := Ω) F.Γ F.pathType p) :
    Tm (Ω := Ω) F.Γ (F.fiber p) (F.value p) := F.varyingValue_typed.substitute hp.section

def certificateType_eq {p : Expression V} (hp : Tm (Ω := Ω) F.Γ F.pathType p) :
    Equal (Ω := Ω) (F.certificateType p) (identity (F.fiber p) (F.value p) (F.compositeValue p)) :=
  F.varyingValue_typed.identitySub F.varyingCompositeValue_typed hp.section

def certificate_typed {p : Expression V} (hp : Tm (Ω := Ω) F.Γ F.pathType p) :
    Tm (Ω := Ω) F.Γ (F.certificateType p) (F.certificate p) := F.certificateSection_typed.substitute hp.section

abbrev transportedCertificate (p p' h : Expression V) : Expression V :=
  transport F.Γ F.pathType F.certificateFamily p p' h (F.certificate p)
abbrev dependentAction (p p' h : Expression V) : Expression V :=
  apd F.Γ F.pathType F.certificateFamily p p' h F.certificateSection

def dependentAction_typed {p p' h : Expression V} (hp : Tm (Ω := Ω) F.Γ F.pathType p)
    (hp' : Tm (Ω := Ω) F.Γ F.pathType p') (hh : Tm (Ω := Ω) F.Γ (identity F.pathType p p') h) :
    Tm (Ω := Ω) F.Γ
      (identity (F.certificateType p') (F.transportedCertificate p p' h) (F.certificate p'))
      (F.dependentAction p p' h) :=
  Tm.apd F.certificateSection_typed hp hp' hh

/-- Contextual dependent data; this adds no object-language pair constructor. -/
structure Package (p : Expression V) where
  selectedValue : Expression V
  selectedCertificate : Expression V
  value_typing : Tm (Ω := Ω) F.Γ (F.fiber p) selectedValue
  certificate_typing : Tm (Ω := Ω) F.Γ
    (identity (F.fiber p) selectedValue (F.compositeValue p)) selectedCertificate

def package {p : Expression V} (hp : Tm (Ω := Ω) F.Γ F.pathType p) : F.Package p where
  selectedValue := F.value p
  selectedCertificate := F.certificate p
  value_typing := F.value_typed hp
  certificate_typing := (F.certificate_typed hp).convert (F.certificateType_eq hp)

def transportedCertificate_typed {p p' h : Expression V} (hp : Tm (Ω := Ω) F.Γ F.pathType p)
    (hp' : Tm (Ω := Ω) F.Γ F.pathType p') (hh : Tm (Ω := Ω) F.Γ (identity F.pathType p p') h) :
    Tm (Ω := Ω) F.Γ (F.certificateType p') (F.transportedCertificate p p' h) :=
  Tm.transport F.certificateSection_typed.family hp hp' hh (F.certificate_typed hp)

/- These equations use object-context arrows. They do not substitute raw
metavariables, nor identify a frozen assignment until its arrows are supplied. -/
section ObjectSubstitution
variable {Δ Θ σ τ p p' h : Expression V}
  (hp : Tm (Ω := Ω) F.Γ F.pathType p) (hp' : Tm (Ω := Ω) F.Γ F.pathType p')
  (hh : Tm (Ω := Ω) F.Γ (identity F.pathType p p') h)
  (hσ : Sub (Ω := Ω) Δ F.Γ σ) (hτ : Sub (Ω := Ω) Θ Δ τ)

def value_subComp : Equal (Ω := Ω) (subTm (subTm (F.value p) σ) τ) (subTm (F.value p) (comp σ τ)) :=
  (F.value_typed hp).subComp hσ hτ

def fiber_subComp : Equal (Ω := Ω) (subTy (subTy (F.fiber p) σ) τ) (subTy (F.fiber p) (comp σ τ)) :=
  (F.value_typed hp).family.subComp hσ hτ

def certificate_subComp : Equal (Ω := Ω) (subTm (subTm (F.certificate p) σ) τ) (subTm (F.certificate p) (comp σ τ)) :=
  (F.certificate_typed hp).subComp hσ hτ

def certificateType_subComp : Equal (Ω := Ω) (subTy (subTy (F.certificateType p) σ) τ)
    (subTy (F.certificateType p) (comp σ τ)) :=
  (F.certificate_typed hp).family.subComp hσ hτ

def dependentAction_subComp : Equal (Ω := Ω) (subTm (subTm (F.dependentAction p p' h) σ) τ)
    (subTm (F.dependentAction p p' h) (comp σ τ)) :=
  (F.dependentAction_typed hp hp' hh).subComp hσ hτ

def transportedCertificate_subComp : Equal (Ω := Ω) (subTm (subTm (F.transportedCertificate p p' h) σ) τ)
    (subTm (F.transportedCertificate p p' h) (comp σ τ)) :=
  (F.transportedCertificate_typed hp hp' hh).subComp hσ hτ

def dependentActionType_subComp : Equal (Ω := Ω)
    (subTy (subTy (identity (F.certificateType p') (F.transportedCertificate p p' h) (F.certificate p')) σ) τ)
    (subTy (identity (F.certificateType p') (F.transportedCertificate p p' h) (F.certificate p')) (comp σ τ)) :=
  (F.dependentAction_typed hp hp' hh).family.subComp hσ hτ

end ObjectSubstitution

end Parameters
end SquareKit.Internal.DependentJudgments.Contextual.Memo
