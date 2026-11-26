import SquareKit.Internal.DependentJudgments.Memo

/-! The frozen memo's contexts and maps, built by context extension and pairing.
Pullback of a displayed tail transports every later dependent binder. No
substitution into the frozen contexts is supplied as an additional premise. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Memo.Frozen
open GuardedTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V : Type} {Ω : List (Judgment V)}

/-- A finite displayed context, retaining a source formation derivation at
 each binder. This is a construction of contexts, not an extra source rule. -/
inductive Display (Ω : List (Judgment V)) : Expression V → Type where
  | nil {Γ} (hΓ : Ctx (Ω := Ω) Γ) : Display Ω Γ
  | cons {Γ A} (hA : Ty (Ω := Ω) Γ A) (tail : Display Ω (extend Γ A)) : Display Ω Γ

namespace Display

def total {Γ} : Display Ω Γ → Expression V
  | .nil _ => Γ
  | .cons _ tail => tail.total

def typing {Γ} : (D : Display Ω Γ) → Ctx (Ω := Ω) D.total
  | .nil hΓ => hΓ
  | .cons _ tail => tail.typing

def projection {Γ} : Display Ω Γ → Expression V
  | .nil _ => identitySub Γ
  | .cons (A := A) _ tail => comp (weaken Γ A) tail.projection

def projectionTyping {Γ} : (D : Display Ω Γ) → Sub (Ω := Ω) D.total Γ D.projection
  | .nil hΓ => hΓ.identity
  | .cons hA tail => hA.weaken.comp tail.projectionTyping

def pullback {Γ} (D : Display Ω Γ) {Δ σ} (hΔ : Ctx (Ω := Ω) Δ)
    (hσ : Sub (Ω := Ω) Δ Γ σ) : Display Ω Δ :=
  match D with
  | .nil _ => .nil hΔ
  | .cons hA tail => .cons (hA.substitute hσ)
      (tail.pullback (hA.substitute hσ).extend (hσ.lift hA))

def square {Γ} (D : Display Ω Γ) {Δ σ} (hσ : Sub (Ω := Ω) Δ Γ σ) : Expression V :=
  match D with
  | .nil _ => σ
  | .cons hA tail => tail.square (hσ.lift hA)

def squareTyping {Γ} (D : Display Ω Γ) {Δ σ} (hΔ : Ctx (Ω := Ω) Δ)
    (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Sub (Ω := Ω) (D.pullback hΔ hσ).total D.total (D.square hσ) :=
  match D with
  | .nil _ => hσ
  | .cons hA tail => tail.squareTyping (hA.substitute hσ).extend (hσ.lift hA)

/-- The square commutes with the projection to its original base. -/
def squareProjection {Γ} (D : Display Ω Γ) {Δ σ} (hΔ : Ctx (Ω := Ω) Δ)
    (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (comp D.projection (D.square hσ))
      (comp σ (D.pullback hΔ hσ).projection) := by
  induction D generalizing Δ σ with
  | nil hΓ => exact hσ.idLeft.transitive hσ.idRight.symmetric
  | @cons Γ A hA tail ih =>
      let hAs := hA.substitute hσ
      let hL := hσ.lift hA
      have hS := tail.squareTyping hAs.extend hL
      have hP := (tail.pullback hAs.extend hL).projectionTyping
      have hW := hA.weakenPair (hσ.comp hAs.weaken)
        (hAs.generic.convert (hA.subComp hσ hAs.weaken))
      simp only [projection, square, pullback]
      exact ((hA.weaken.assoc tail.projectionTyping hS).transitive
        (Equal.comp (.reflexive _) (ih hAs.extend hL))).transitive
        ((hA.weaken.assoc hL hP).symmetric.transitive
          ((Equal.comp hW (.reflexive _)).transitive (hσ.assoc hAs.weaken hP)))

/-- A term pulled along the square agrees with pulling it along the base map.
The family is also reindexed by the same source substitutions. -/
def termSquare {Γ A t} (D : Display Ω Γ) (ht : Tm (Ω := Ω) Γ A t)
    {Δ σ} (hΔ : Ctx (Ω := Ω) Δ) (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm (subTm t D.projection) (D.square hσ))
      (subTm (subTm t σ) (D.pullback hΔ hσ).projection) :=
  (ht.subComp D.projectionTyping (D.squareTyping hΔ hσ)).transitive
    ((Equal.subTm (.reflexive _) (D.squareProjection hΔ hσ)).transitive
      (ht.subComp hσ (D.pullback hΔ hσ).projectionTyping).symmetric)

/-- A displayed variable from the base, weakened through the actual binders. -/
def weakenTerm {Γ} (D : Display Ω Γ) (t : Expression V) : Expression V :=
  match D with
  | .nil _ => t
  | .cons (A := A) _ tail => tail.weakenTerm (subTm t (weaken Γ A))

def weakenTermProjection {Γ A t} (D : Display Ω Γ)
    (ht : Tm (Ω := Ω) Γ A t) :
    Equal (Ω := Ω) (D.weakenTerm t) (subTm t D.projection) := by
  induction D generalizing A t with
  | nil hΓ => exact ht.subId.symmetric
  | cons hB tail ih =>
      exact (ih (ht.substitute hB.weaken)).transitive (ht.subComp hB.weaken tail.projectionTyping)

def weakenTermSquare {Γ A t} (D : Display Ω Γ)
    (ht : Tm (Ω := Ω) Γ A t) {Δ σ} (hΔ : Ctx (Ω := Ω) Δ)
    (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm (D.weakenTerm t) (D.square hσ))
      ((D.pullback hΔ hσ).weakenTerm (subTm t σ)) :=
  (Equal.subTm (D.weakenTermProjection ht) (.reflexive _)).transitive
    ((D.termSquare ht hΔ hσ).transitive
      ((D.pullback hΔ hσ).weakenTermProjection (ht.substitute hσ)).symmetric)

/-- Map into the pullback of a nonempty display after replacing its first
variable. Stating this at an abstract tail avoids unfolding a concrete tail. -/
def replaceHead {Γ A Δ σ Θ τ} (hA : Ty (Ω := Ω) Γ A)
    (tail : Display Ω (extend Γ A)) (hΔ : Ctx (Ω := Ω) Δ)
    (hσ : Sub (Ω := Ω) Δ Γ σ) (hΘ : Ctx (Ω := Ω) Θ)
    (hτ : Sub (Ω := Ω) Θ (extend Δ (subTy A σ)) τ) :
    Sub (Ω := Ω)
      ((tail.pullback (hA.substitute hσ).extend (hσ.lift hA)).pullback hΘ hτ).total
      ((Display.cons hA tail).pullback hΔ hσ).total
      ((tail.pullback (hA.substitute hσ).extend (hσ.lift hA)).square hτ) :=
  (tail.pullback (hA.substitute hσ).extend (hσ.lift hA)).squareTyping hΘ hτ

def weakenEqual {Γ t u} (D : Display Ω Γ) (e : Equal (Ω := Ω) t u) :
    Equal (Ω := Ω) (D.weakenTerm t) (D.weakenTerm u) :=
  match D with
  | .nil _ => e
  | .cons _ tail => tail.weakenEqual (Equal.subTm e (.reflexive _))

/-- Pullback retains the freshly bound variable, including every later
 dependent binder. This applies to paths and to identity witnesses as data. -/
def headSquare {Γ A Δ σ} (hA : Ty (Ω := Ω) Γ A)
    (tail : Display Ω (extend Γ A)) (_hΔ : Ctx (Ω := Ω) Δ)
    (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω)
      (subTm (tail.weakenTerm (generic Γ A)) ((Display.cons hA tail).square hσ))
      ((tail.pullback (hA.substitute hσ).extend (hσ.lift hA)).weakenTerm
        (generic Δ (subTy A σ))) :=
  (tail.weakenTermSquare hA.generic (hA.substitute hσ).extend (hσ.lift hA)).transitive
    ((tail.pullback (hA.substitute hσ).extend (hσ.lift hA)).weakenEqual
      (hA.variablePair (hσ.comp (hA.substitute hσ).weaken)
        ((hA.substitute hσ).generic.convert (hA.subComp hσ (hA.substitute hσ).weaken))))

/-- Replacing a head variable retains every term from its base. -/
def replaceBase {Γ A B t x} (hA : Ty (Ω := Ω) Γ A)
    (tail : Display Ω (extend Γ A)) (hΓ : Ctx (Ω := Ω) Γ)
    (ht : Tm (Ω := Ω) Γ B t) (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω)
      (subTm ((Display.cons hA tail).weakenTerm t) (tail.square hx.section))
      ((tail.pullback hΓ hx.section).weakenTerm t) :=
  (tail.weakenTermSquare (ht.substitute hA.weaken) hΓ hx.section).transitive
    ((tail.pullback hΓ hx.section).weakenEqual (ht.weakenSection hx))

/-- The replaced variable becomes its supplied section, through the full tail. -/
def replaceVariable {Γ A x} (hA : Ty (Ω := Ω) Γ A)
    (tail : Display Ω (extend Γ A)) (hΓ : Ctx (Ω := Ω) Γ)
    (hx : Tm (Ω := Ω) Γ A x) :
    Equal (Ω := Ω)
      (subTm (tail.weakenTerm (generic Γ A)) (tail.square hx.section))
      ((tail.pullback hΓ hx.section).weakenTerm x) :=
  (tail.weakenTermSquare hA.generic hΓ hx.section).transitive
    ((tail.pullback hΓ hx.section).weakenEqual hx.sectionGeneric)

inductive Variable : {Γ : Expression V} → Display Ω Γ → Type where
  | here {Γ A} (hA : Ty (Ω := Ω) Γ A) (tail : Display Ω (extend Γ A)) : Variable (.cons hA tail)
  | there {Γ A} (hA : Ty (Ω := Ω) Γ A) (tail : Display Ω (extend Γ A))
      (i : Variable tail) : Variable (.cons hA tail)

namespace Variable

def term {Γ} {D : Display Ω Γ} : Variable D → Expression V
  | .here (Γ := Γ) (A := A) _ tail => tail.weakenTerm (generic Γ A)
  | .there _ _ i => i.term

def pullback {Γ} {D : Display Ω Γ} (i : Variable D) {Δ σ}
    (hΔ : Ctx (Ω := Ω) Δ) (hσ : Sub (Ω := Ω) Δ Γ σ) : Variable (D.pullback hΔ hσ) :=
  match i with
  | .here hA tail => .here (hA.substitute hσ)
      (tail.pullback (hA.substitute hσ).extend (hσ.lift hA))
  | .there hA tail i => .there (hA.substitute hσ)
      (tail.pullback (hA.substitute hσ).extend (hσ.lift hA))
      (i.pullback (hA.substitute hσ).extend (hσ.lift hA))

/-- Every selected binder is retained, including identity witnesses. -/
def preserved {Γ} {D : Display Ω Γ} (i : Variable D) {Δ σ}
    (hΔ : Ctx (Ω := Ω) Δ) (hσ : Sub (Ω := Ω) Δ Γ σ) :
    Equal (Ω := Ω) (subTm i.term (D.square hσ)) (i.pullback hΔ hσ).term :=
  match i with
  | .here hA tail => Display.headSquare hA tail hΔ hσ
  | .there hA _ i => i.preserved (hA.substitute hσ).extend (hσ.lift hA)

end Variable

end Display
/-- The schematic family and three endpoints at one source context. -/
structure Points (Ω : List (Judgment V)) where
  Γ : Expression V
  A : Expression V
  B : Expression V
  x : Expression V
  y : Expression V
  z : Expression V
  hx : Tm (Ω := Ω) Γ A x
  hy : Tm (Ω := Ω) Γ A y
  hz : Tm (Ω := Ω) Γ A z
  hB : Ty (Ω := Ω) (extend Γ A) B

namespace Points
variable (F : Points Ω)

def reindex {Δ σ} (hσ : Sub (Ω := Ω) Δ F.Γ σ) : Points Ω where
  Γ := Δ
  A := subTy F.A σ
  B := subTy F.B (lift Δ F.A σ)
  x := subTm F.x σ
  y := subTm F.y σ
  z := subTm F.z σ
  hx := F.hx.substitute hσ
  hy := F.hy.substitute hσ
  hz := F.hz.substitute hσ
  hB := F.hB.substitute (hσ.lift F.hx.family)

/-- Fresh endpoint binding; earlier endpoints and the family are reindexed. -/
def addY : Points Ω :=
  { F.reindex F.hx.family.weaken with
    y := generic F.Γ F.A
    hy := F.hx.family.generic }

def addZ : Points Ω :=
  { F.reindex F.hx.family.weaken with
    z := generic F.Γ F.A
    hz := F.hx.family.generic }

abbrev pathType := identity F.A F.x F.y
abbrev hPath : Ty (Ω := Ω) F.Γ F.pathType := F.hx.identity F.hy
end Points

structure OnePath (Ω : List (Judgment V)) extends Points Ω where
  p : Expression V
  hp : Tm (Ω := Ω) Γ (identity A x y) p

namespace OnePath
variable (F : OnePath Ω)
def reindex {Δ σ} (hσ : Sub (Ω := Ω) Δ F.Γ σ) : OnePath Ω where
  toPoints := F.toPoints.reindex hσ
  p := subTm F.p σ
  hp := (F.hp.substitute hσ).convert (F.hx.identitySub F.hy hσ)
end OnePath

def Points.addP (F : Points Ω) : OnePath Ω where
  toPoints := F.reindex F.hPath.weaken
  p := generic F.Γ F.pathType
  hp := F.hPath.generic.convert (F.hx.identitySub F.hy F.hPath.weaken)

structure Parallel (Ω : List (Judgment V)) extends OnePath Ω where
  p' : Expression V
  hp' : Tm (Ω := Ω) Γ (identity A x y) p'

namespace Parallel
variable (F : Parallel Ω)
def reindex {Δ σ} (hσ : Sub (Ω := Ω) Δ F.Γ σ) : Parallel Ω where
  toOnePath := F.toOnePath.reindex hσ
  p' := subTm F.p' σ
  hp' := (F.hp'.substitute hσ).convert (F.hx.identitySub F.hy hσ)
abbrev hIdentity : Ty (Ω := Ω) F.Γ (identity F.toPoints.pathType F.p F.p') := F.hp.identity F.hp'
end Parallel

def OnePath.addParallel (F : OnePath Ω) : Parallel Ω where
  toOnePath := F.reindex F.toPoints.hPath.weaken
  p' := generic F.Γ F.toPoints.pathType
  hp' := F.toPoints.hPath.generic.convert (F.hx.identitySub F.hy F.toPoints.hPath.weaken)

structure Homotopy (Ω : List (Judgment V)) extends Parallel Ω where
  h : Expression V
  hh : Tm (Ω := Ω) Γ (identity (identity A x y) p p') h

namespace Homotopy
variable (F : Homotopy Ω)
def reindex {Δ σ} (hσ : Sub (Ω := Ω) Δ F.Γ σ) : Homotopy Ω where
  toParallel := F.toParallel.reindex hσ
  h := subTm F.h σ
  hh := (F.hh.substitute hσ).convert ((F.hp.identitySub F.hp' hσ).transitive
    (Equal.identity (F.hx.identitySub F.hy hσ) (.reflexive _) (.reflexive _)))
abbrev hQ : Ty (Ω := Ω) F.Γ (identity F.A F.y F.z) := F.hy.identity F.hz
end Homotopy

def Parallel.addH (F : Parallel Ω) : Homotopy Ω where
  toParallel := F.reindex F.hIdentity.weaken
  h := generic F.Γ (identity F.toPoints.pathType F.p F.p')
  hh := F.hIdentity.generic.convert ((F.hp.identitySub F.hp' F.hIdentity.weaken).transitive
    (Equal.identity (F.hx.identitySub F.hy F.hIdentity.weaken) (.reflexive _) (.reflexive _)))

structure WithQ (Ω : List (Judgment V)) extends Homotopy Ω where
  q : Expression V
  hq : Tm (Ω := Ω) Γ (identity A y z) q

namespace WithQ
variable (F : WithQ Ω)
def reindex {Δ σ} (hσ : Sub (Ω := Ω) Δ F.Γ σ) : WithQ Ω where
  toHomotopy := F.toHomotopy.reindex hσ
  q := subTm F.q σ
  hq := (F.hq.substitute hσ).convert (F.hy.identitySub F.hz hσ)
abbrev uType := subTy F.B (sectionSub F.Γ F.A F.x)
abbrev hU : Ty (Ω := Ω) F.Γ F.uType := F.hB.substitute F.hx.section
end WithQ

def Homotopy.addQ (F : Homotopy Ω) : WithQ Ω where
  toHomotopy := F.reindex F.hQ.weaken
  q := generic F.Γ (identity F.A F.y F.z)
  hq := F.hQ.generic.convert (F.hy.identitySub F.hz F.hQ.weaken)

structure Input (Ω : List (Judgment V)) extends WithQ Ω where
  u : Expression V
  hu : Tm (Ω := Ω) Γ (subTy B (sectionSub Γ A x)) u

namespace Input
variable (F : Input Ω)
def reindex {Δ σ} (hσ : Sub (Ω := Ω) Δ F.Γ σ) : Input Ω where
  toWithQ := F.toWithQ.reindex hσ
  u := subTm F.u σ
  hu := (F.hu.substitute hσ).convert (F.hB.sectionLift hσ F.hx).symmetric

def parameters : Parameters Ω where
  Γ := F.Γ
  A := F.A
  B := F.B
  x := F.x
  y := F.y
  z := F.z
  q := F.q
  u := F.u
  xTyping := F.hx
  yTyping := F.hy
  zTyping := F.hz
  familyFormation := F.hB
  qTyping := F.hq
  uTyping := F.hu
end Input

def WithQ.addU (F : WithQ Ω) : Input Ω where
  toWithQ := F.reindex F.hU.weaken
  u := generic F.Γ F.uType
  hu := F.hU.generic.convert (F.hB.sectionLift F.hU.weaken F.hx).symmetric

/-- Signature parameters are schematic over a source context. Taking that
context to be empty gives exactly the memo's signature. -/
structure Signature (Ω : List (Judgment V)) where
  Γ : Expression V
  A : Expression V
  B : Expression V
  hA : Ty (Ω := Ω) Γ A
  hB : Ty (Ω := Ω) (extend Γ A) B

namespace Signature
variable (S : Signature Ω)

def point : Points Ω where
  Γ := extend S.Γ S.A
  A := subTy S.A (weaken S.Γ S.A)
  B := subTy S.B (lift (extend S.Γ S.A) S.A (weaken S.Γ S.A))
  x := generic S.Γ S.A
  y := generic S.Γ S.A
  z := generic S.Γ S.A
  hx := S.hA.generic
  hy := S.hA.generic
  hz := S.hA.generic
  hB := S.hB.substitute (S.hA.weaken.lift S.hA)

def xy : Points Ω := S.point.addY
def xyz : Points Ω := S.xy.addZ
def withP : OnePath Ω := S.xyz.addP
def withParallel : Parallel Ω := S.withP.addParallel
def withH : Homotopy Ω := S.withParallel.addH
def withQ : WithQ Ω := S.withH.addQ
def input : Input Ω := S.withQ.addU

def tailU : Display Ω S.withQ.Γ := .cons S.withQ.hU (.nil S.withQ.hU.extend)
def tailQ : Display Ω S.withH.Γ := .cons S.withH.hQ S.tailU
def tailH : Display Ω S.withParallel.Γ := .cons S.withParallel.hIdentity S.tailQ
def tailParallel : Display Ω S.withP.Γ := .cons S.withP.toPoints.hPath S.tailH
def tailP : Display Ω S.xyz.Γ := .cons S.xyz.hPath S.tailParallel
def tailZ : Display Ω S.xy.Γ := .cons S.xy.hx.family S.tailP

/-- Full context `x,y,z,p,p',h,q,u`. -/
def gamma : Expression V := S.input.Γ

def duplicate : Expression V := sectionSub S.point.Γ S.point.A S.point.x
def duplicateTyping : Sub (Ω := Ω) S.point.Γ S.xy.Γ S.duplicate := S.point.hx.section

/-- Duplicate `x` into the `y` slot, then pull back every subsequent binder. -/
def deltaTail : Display Ω S.point.Γ := S.tailZ.pullback S.point.hx.family.context S.duplicateTyping
def delta : Expression V := S.deltaTail.total
def sigma : Expression V := S.tailZ.square S.duplicateTyping

def sigmaTyping : Sub (Ω := Ω) S.delta S.gamma S.sigma :=
  S.tailZ.squareTyping S.point.hx.family.context S.duplicateTyping

def deltaZType : Expression V := subTy S.xy.A S.duplicate
def deltaZTypeEquality : Equal (Ω := Ω) S.deltaZType S.point.A :=
  S.point.hx.family.weakenSection S.point.hx

def deltaXTypingAsZ : Tm (Ω := Ω) S.point.Γ S.deltaZType S.point.x :=
  S.point.hx.convert S.deltaZTypeEquality.symmetric

def deltaAfterZ : Display Ω (extend S.point.Γ S.deltaZType) :=
  S.tailP.pullback (S.xy.hx.family.substitute S.duplicateTyping).extend
    (S.duplicateTyping.lift S.xy.hx.family)

/-- Duplicate `x` into the remaining `z` slot and retain every later binder. -/
def thetaTail : Display Ω S.point.Γ :=
  S.deltaAfterZ.pullback S.point.hx.family.context S.deltaXTypingAsZ.section
def theta : Expression V := S.thetaTail.total
def tau : Expression V := S.deltaAfterZ.square S.deltaXTypingAsZ.section

def tauTyping : Sub (Ω := Ω) S.theta S.delta S.tau :=
  Display.replaceHead S.xy.hx.family S.tailP S.point.hx.family.context S.duplicateTyping
    S.point.hx.family.context S.deltaXTypingAsZ.section

def deltaInput : Input Ω := S.input.reindex S.sigmaTyping
def thetaInput : Input Ω := S.deltaInput.reindex S.tauTyping

/-- Both old endpoints land at the same retained `x`; the later binders
remain present in the pulled-back display. -/
def sigmaY : Equal (Ω := Ω) (subTm S.input.y S.sigma)
    (S.deltaTail.weakenTerm S.point.x) :=
  (S.tailZ.weakenTermSquare S.xy.hy S.point.hx.family.context S.duplicateTyping).transitive
    (S.deltaTail.weakenEqual S.point.hx.sectionGeneric)

def sigmaX : Equal (Ω := Ω) (subTm S.input.x S.sigma)
    (S.deltaTail.weakenTerm S.point.x) :=
  (S.tailZ.weakenTermSquare S.xy.hx S.point.hx.family.context S.duplicateTyping).transitive
    (S.deltaTail.weakenEqual (S.point.hx.weakenSection S.point.hx))

def deltaYEqX : Equal (Ω := Ω) S.deltaInput.y S.deltaInput.x :=
  S.sigmaY.transitive S.sigmaX.symmetric

/-- The `z` variable is retained as the first binder in Delta. -/
def sigmaZ : Equal (Ω := Ω) (subTm S.input.z S.sigma)
    (S.deltaAfterZ.weakenTerm (generic S.point.Γ S.deltaZType)) :=
  Display.headSquare S.xy.hx.family S.tailP S.point.hx.family.context S.duplicateTyping

/-- The first frozen map turns the two parallel paths into loops without
 replacing the paths by reflexivity. -/
def deltaLoopTyping : Tm (Ω := Ω) S.deltaInput.Γ
    (identity S.deltaInput.A S.deltaInput.x S.deltaInput.x) S.deltaInput.p :=
  S.deltaInput.hp.convert (Equal.identity (.reflexive _) (.reflexive _) S.deltaYEqX)

def deltaParallelLoopTyping : Tm (Ω := Ω) S.deltaInput.Γ
    (identity S.deltaInput.A S.deltaInput.x S.deltaInput.x) S.deltaInput.p' :=
  S.deltaInput.hp'.convert (Equal.identity (.reflexive _) (.reflexive _) S.deltaYEqX)

def tauX : Equal (Ω := Ω) (subTm S.deltaInput.x S.tau)
    (S.thetaTail.weakenTerm S.point.x) :=
  (Equal.subTm S.sigmaX (.reflexive _)).transitive
    (Display.replaceBase (S.xy.hx.family.substitute S.duplicateTyping) S.deltaAfterZ
      S.point.hx.family.context S.point.hx S.deltaXTypingAsZ)

def tauZ : Equal (Ω := Ω) (subTm S.deltaInput.z S.tau)
    (S.thetaTail.weakenTerm S.point.x) :=
  (Equal.subTm S.sigmaZ (.reflexive _)).transitive
    (Display.replaceVariable (S.xy.hx.family.substitute S.duplicateTyping) S.deltaAfterZ
      S.point.hx.family.context S.deltaXTypingAsZ)

def thetaZEqX : Equal (Ω := Ω) S.thetaInput.z S.thetaInput.x :=
  S.tauZ.transitive S.tauX.symmetric

def thetaYEqX : Equal (Ω := Ω) S.thetaInput.y S.thetaInput.x :=
  Equal.subTm S.deltaYEqX (.reflexive _)

/-- The second map turns the retained `q` into the loop `k`, without erasure. -/
def thetaQLoopTyping : Tm (Ω := Ω) S.thetaInput.Γ
    (identity S.thetaInput.A S.thetaInput.x S.thetaInput.x) S.thetaInput.q :=
  S.thetaInput.hq.convert (Equal.identity (.reflexive _) S.thetaYEqX S.thetaZEqX)

/-- Positions of the retained path, witness and value binders. -/
def pSlot : Display.Variable S.tailZ := .there _ _ (.here _ _)
def deltaPSlot : Display.Variable S.deltaAfterZ := .here _ _

def sigmaPRetained : Equal (Ω := Ω) (subTm S.input.p S.sigma)
    (S.pSlot.pullback S.point.hx.family.context S.duplicateTyping).term :=
  S.pSlot.preserved S.point.hx.family.context S.duplicateTyping

def tauPRetained : Equal (Ω := Ω) S.thetaInput.p
    (S.deltaPSlot.pullback S.point.hx.family.context S.deltaXTypingAsZ.section).term :=
  (Equal.subTm S.sigmaPRetained (.reflexive _)).transitive
    (S.deltaPSlot.preserved S.point.hx.family.context S.deltaXTypingAsZ.section)

def parallelSlot : Display.Variable S.tailZ := .there _ _ (.there _ _ (.here _ _))
def deltaParallelSlot : Display.Variable S.deltaAfterZ := .there _ _ (.here _ _)

def sigmaParallelRetained : Equal (Ω := Ω) (subTm S.input.p' S.sigma)
    (S.parallelSlot.pullback S.point.hx.family.context S.duplicateTyping).term :=
  S.parallelSlot.preserved S.point.hx.family.context S.duplicateTyping

def tauParallelRetained : Equal (Ω := Ω) S.thetaInput.p'
    (S.deltaParallelSlot.pullback S.point.hx.family.context S.deltaXTypingAsZ.section).term :=
  (Equal.subTm S.sigmaParallelRetained (.reflexive _)).transitive
    (S.deltaParallelSlot.preserved S.point.hx.family.context S.deltaXTypingAsZ.section)

def homotopySlot : Display.Variable S.tailZ := .there _ _ (.there _ _ (.there _ _ (.here _ _)))
def deltaHomotopySlot : Display.Variable S.deltaAfterZ := .there _ _ (.there _ _ (.here _ _))

def sigmaHomotopyRetained : Equal (Ω := Ω) (subTm S.input.h S.sigma)
    (S.homotopySlot.pullback S.point.hx.family.context S.duplicateTyping).term :=
  S.homotopySlot.preserved S.point.hx.family.context S.duplicateTyping

def tauHomotopyRetained : Equal (Ω := Ω) S.thetaInput.h
    (S.deltaHomotopySlot.pullback S.point.hx.family.context S.deltaXTypingAsZ.section).term :=
  (Equal.subTm S.sigmaHomotopyRetained (.reflexive _)).transitive
    (S.deltaHomotopySlot.preserved S.point.hx.family.context S.deltaXTypingAsZ.section)

def qSlot : Display.Variable S.tailZ := .there _ _ (.there _ _ (.there _ _ (.there _ _ (.here _ _))))
def deltaQSlot : Display.Variable S.deltaAfterZ := .there _ _ (.there _ _ (.there _ _ (.here _ _)))

def sigmaQRetained : Equal (Ω := Ω) (subTm S.input.q S.sigma)
    (S.qSlot.pullback S.point.hx.family.context S.duplicateTyping).term :=
  S.qSlot.preserved S.point.hx.family.context S.duplicateTyping

def tauQRetained : Equal (Ω := Ω) S.thetaInput.q
    (S.deltaQSlot.pullback S.point.hx.family.context S.deltaXTypingAsZ.section).term :=
  (Equal.subTm S.sigmaQRetained (.reflexive _)).transitive
    (S.deltaQSlot.preserved S.point.hx.family.context S.deltaXTypingAsZ.section)

def uSlot : Display.Variable S.tailZ := .there _ _ (.there _ _ (.there _ _ (.there _ _ (.there _ _ (.here _ _)))))
def deltaUSlot : Display.Variable S.deltaAfterZ := .there _ _ (.there _ _ (.there _ _ (.there _ _ (.here _ _))))

def sigmaURetained : Equal (Ω := Ω) (subTm S.input.u S.sigma)
    (S.uSlot.pullback S.point.hx.family.context S.duplicateTyping).term :=
  S.uSlot.preserved S.point.hx.family.context S.duplicateTyping

def tauURetained : Equal (Ω := Ω) S.thetaInput.u
    (S.deltaUSlot.pullback S.point.hx.family.context S.deltaXTypingAsZ.section).term :=
  (Equal.subTm S.sigmaURetained (.reflexive _)).transitive
    (S.deltaUSlot.preserved S.point.hx.family.context S.deltaXTypingAsZ.section)


end Signature

end
end SquareKit.Internal.DependentJudgments.Contextual.Memo.Frozen
