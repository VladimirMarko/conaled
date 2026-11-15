import SquareKit.Internal.DependentJudgments.ReferenceApd

/-! The frozen higher binder constructed in the independent reference calculus.
Only the initial two families are parameters; all context arrows are generated. -/
namespace SquareKit.Internal.DependentJudgments.Contextual.Reference
open GuardedTheory
noncomputable section
variable {V : Type} {Ξ : List (Declaration V)}
namespace FrozenInput

structure Points (Ξ : List (Declaration V)) where
  (Γ A B x y z : Expression V)
  hx : Derives Ξ (.has (.tm Γ A) x)
  hy : Derives Ξ (.has (.tm Γ A) y)
  hz : Derives Ξ (.has (.tm Γ A) z)
  hB : Derives Ξ (.has (.ty (extend Γ A)) B)

namespace Points
variable (F : Points Ξ)
def reindex {Δ σ : Expression V} (hs : Derives Ξ (.has (.sub Δ F.Γ) σ)) : Points Ξ where
  Γ := Δ
  A := subTy F.A σ
  B := subTy F.B (liftSyntax Δ F.A σ)
  x := subTm F.x σ
  y := subTm F.y σ
  z := subTm F.z σ
  hx := .subTm F.hx hs
  hy := .subTm F.hy hs
  hz := .subTm F.hz hs
  hB := .subTy F.hB (Derives.lift F.hx.termFamily hs)

def addY : Points Ξ :=
  { F.reindex (.weaken F.hx.termFamily) with
    y := generic F.Γ F.A
    hy := .generic F.hx.termFamily }
def addZ : Points Ξ :=
  { F.reindex (.weaken F.hx.termFamily) with
    z := generic F.Γ F.A
    hz := .generic F.hx.termFamily }
abbrev pathType := identity F.A F.x F.y
abbrev hPath : Derives Ξ (.has (.ty F.Γ) F.pathType) := .identity F.hx F.hy
end Points

structure OnePath (Ξ : List (Declaration V)) extends Points Ξ where
  p : Expression V
  hp : Derives Ξ (.has (.tm Γ (identity A x y)) p)
namespace OnePath
variable (F : OnePath Ξ)
def reindex {Δ σ : Expression V} (hs : Derives Ξ (.has (.sub Δ F.Γ) σ)) : OnePath Ξ where
  toPoints := F.toPoints.reindex hs
  p := subTm F.p σ
  hp := .convert (.subTm F.hp hs) (.identitySubLaw F.hx F.hy hs)
end OnePath

def Points.addP (F : Points Ξ) : OnePath Ξ where
  toPoints := F.reindex (.weaken F.hPath)
  p := generic F.Γ F.pathType
  hp := .convert (.generic F.hPath) (.identitySubLaw F.hx F.hy (.weaken F.hPath))

structure Parallel (Ξ : List (Declaration V)) extends OnePath Ξ where
  p' : Expression V
  hp' : Derives Ξ (.has (.tm Γ (identity A x y)) p')
namespace Parallel
variable (F : Parallel Ξ)
def reindex {Δ σ : Expression V} (hs : Derives Ξ (.has (.sub Δ F.Γ) σ)) : Parallel Ξ where
  toOnePath := F.toOnePath.reindex hs
  p' := subTm F.p' σ
  hp' := .convert (.subTm F.hp' hs) (.identitySubLaw F.hx F.hy hs)
abbrev hIdentity : Derives Ξ (.has (.ty F.Γ) (identity F.toPoints.pathType F.p F.p')) :=
  .identity F.hp F.hp'
end Parallel

def OnePath.addParallel (F : OnePath Ξ) : Parallel Ξ where
  toOnePath := F.reindex (.weaken F.toPoints.hPath)
  p' := generic F.Γ F.toPoints.pathType
  hp' := .convert (.generic F.toPoints.hPath)
    (.identitySubLaw F.hx F.hy (.weaken F.toPoints.hPath))

/-- Conversion of the inner path type retains the actual outer witness. -/
def reindexIdentity {Γ A x y p p' Δ σ : Expression V}
    (hx : Derives Ξ (.has (.tm Γ A) x)) (hy : Derives Ξ (.has (.tm Γ A) y))
    (hp : Derives Ξ (.has (.tm Γ (identity A x y)) p))
    (hp' : Derives Ξ (.has (.tm Γ (identity A x y)) p'))
    (hs : Derives Ξ (.has (.sub Δ Γ) σ)) :
    Derives Ξ (.eq (.ty Δ) (subTy (identity (identity A x y) p p') σ)
      (identity (identity (subTy A σ) (subTm x σ) (subTm y σ)) (subTm p σ) (subTm p' σ))) := by
  have eA := Derives.identitySubLaw hx hy hs
  have ep := Derives.subTm hp hs
  have ep' := Derives.subTm hp' hs
  have e := Derives.identitySubLaw hp hp' hs
  exact .eqTrans e (.congruence (.inr .identity)
    ![.ty Δ, .tm Δ (subTy (identity A x y) σ), .tm Δ (subTy (identity A x y) σ)]
    e.eqOperands.2 (.identity (.convert ep eA) (.convert ep' eA))
    (Fin.cases eA (Fin.cases (.eqRefl ep) (Fin.cases (.eqRefl ep') (fun i => nomatch i)))))

structure Homotopy (Ξ : List (Declaration V)) extends Parallel Ξ where
  h : Expression V
  hh : Derives Ξ (.has (.tm Γ (identity (identity A x y) p p')) h)
namespace Homotopy
variable (F : Homotopy Ξ)
def reindex {Δ σ : Expression V} (hs : Derives Ξ (.has (.sub Δ F.Γ) σ)) : Homotopy Ξ where
  toParallel := F.toParallel.reindex hs
  h := subTm F.h σ
  hh := .convert (.subTm F.hh hs) (reindexIdentity F.hx F.hy F.hp F.hp' hs)
end Homotopy

def Parallel.addH (F : Parallel Ξ) : Homotopy Ξ where
  toParallel := F.reindex (.weaken F.hIdentity)
  h := generic F.Γ (identity F.toPoints.pathType F.p F.p')
  hh := .convert (.generic F.hIdentity)
    (reindexIdentity F.hx F.hy F.hp F.hp' (.weaken F.hIdentity))

variable {Γ A B : Expression V}
def point (ha : Derives Ξ (.has (.ty Γ) A)) (hb : Derives Ξ (.has (.ty (extend Γ A)) B)) : Points Ξ where
  Γ := extend Γ A
  A := subTy A (weaken Γ A)
  B := subTy B (liftSyntax (extend Γ A) A (weaken Γ A))
  x := generic Γ A
  y := generic Γ A
  z := generic Γ A
  hx := .generic ha
  hy := .generic ha
  hz := .generic ha
  hB := .subTy hb (Derives.lift ha (.weaken ha))

def parallel (ha : Derives Ξ (.has (.ty Γ) A)) (hb : Derives Ξ (.has (.ty (extend Γ A)) B)) :=
  (((point ha hb).addY).addZ).addP.addParallel

def afterH (ha : Derives Ξ (.has (.ty Γ) A)) (hb : Derives Ξ (.has (.ty (extend Γ A)) B)) :=
  (parallel ha hb).addH

def afterQ (ha : Derives Ξ (.has (.ty Γ) A)) (hb : Derives Ξ (.has (.ty (extend Γ A)) B)) :=
  let H := afterH ha hb
  H.reindex (.weaken (.identity H.hy H.hz))

/-- Two further dependent binders follow the selected higher identity. -/
def input (ha : Derives Ξ (.has (.ty Γ) A)) (hb : Derives Ξ (.has (.ty (extend Γ A)) B)) :=
  let Q := afterQ ha hb
  Q.reindex (.weaken (.subTy Q.hB (Derives.sectionMap Q.hx)))

namespace Substitutions
set_option maxHeartbeats 1600000
variable (ha : Derives Ξ (.has (.ty Γ) A)) (hb : Derives Ξ (.has (.ty (extend Γ A)) B))
abbrev xy := (point ha hb).addY
abbrev xyz := (xy ha hb).addZ
abbrev withP := (xyz ha hb).addP
abbrev withParallel := (withP ha hb).addParallel
abbrev withH := (withParallel ha hb).addH
abbrev withQ := afterQ ha hb
abbrev uType := subTy (withQ ha hb).B (sectionSub (withQ ha hb).Γ (withQ ha hb).A (withQ ha hb).x)
abbrev tailP : Tail V := .cons (xyz ha hb).pathType
  (.cons (withP ha hb).toPoints.pathType
  (.cons (identity (withParallel ha hb).toPoints.pathType (withParallel ha hb).p (withParallel ha hb).p')
  (.cons (identity (withH ha hb).A (withH ha hb).y (withH ha hb).z)
  (.cons (uType ha hb) .nil))))
abbrev tailZ : Tail V := .cons (xy ha hb).A (tailP ha hb)

def tailP_typed : Derives Ξ (.tail (xyz ha hb).Γ (tailP ha hb)) :=
  .cons (xyz ha hb).hPath (.cons (withP ha hb).toPoints.hPath
    (.cons (withParallel ha hb).hIdentity (.cons (.identity (withH ha hb).hy (withH ha hb).hz)
      (.cons (.subTy (withQ ha hb).hB (Derives.sectionMap (withQ ha hb).hx))
        (.nil (.extend (.subTy (withQ ha hb).hB (Derives.sectionMap (withQ ha hb).hx))))))))

def tailZ_typed : Derives Ξ (.tail (xy ha hb).Γ (tailZ ha hb)) :=
  .cons (xy ha hb).hx.termFamily (tailP_typed ha hb)

abbrev duplicate := sectionSub (point ha hb).Γ (point ha hb).A (point ha hb).x
abbrev deltaTail := (tailZ ha hb).reindex (point ha hb).Γ (duplicate ha hb)
abbrev delta := (deltaTail ha hb).total (point ha hb).Γ
abbrev sigma := (tailZ ha hb).map (point ha hb).Γ (duplicate ha hb)
def sigma_typed : Derives Ξ (.has (.sub (delta ha hb) (input ha hb).Γ) (sigma ha hb)) :=
  Derives.tailMap (tailZ_typed ha hb) (Derives.sectionMap (point ha hb).hx)

abbrev deltaZType := subTy (xy ha hb).A (duplicate ha hb)
def deltaX : Derives Ξ (.has (.tm (point ha hb).Γ (deltaZType ha hb)) (point ha hb).x) :=
  .convert (point ha hb).hx (.eqSymm (Derives.weakenSectionType (point ha hb).hx.termFamily (point ha hb).hx))
abbrev deltaAfterZ := (tailP ha hb).reindex (extend (point ha hb).Γ (deltaZType ha hb))
  (liftSyntax (point ha hb).Γ (xy ha hb).A (duplicate ha hb))
def deltaAfterZ_typed : Derives Ξ
    (.tail (extend (point ha hb).Γ (deltaZType ha hb)) (deltaAfterZ ha hb)) :=
  Derives.reindexTail (tailP_typed ha hb)
    (Derives.lift (xy ha hb).hx.termFamily (Derives.sectionMap (point ha hb).hx))
abbrev replaceZ := sectionSub (point ha hb).Γ (deltaZType ha hb) (point ha hb).x
abbrev thetaTail := (deltaAfterZ ha hb).reindex (point ha hb).Γ (replaceZ ha hb)
abbrev theta := (thetaTail ha hb).total (point ha hb).Γ
abbrev tau := (deltaAfterZ ha hb).map (point ha hb).Γ (replaceZ ha hb)
def tau_typed : Derives Ξ (.has (.sub (theta ha hb) (delta ha hb)) (tau ha hb)) :=
  Derives.tailMap (deltaAfterZ_typed ha hb) (Derives.sectionMap (deltaX ha hb))
end Substitutions

end FrozenInput
end
end SquareKit.Internal.DependentJudgments.Contextual.Reference
