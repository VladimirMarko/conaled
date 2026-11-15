import SquareKit.Internal.PathTransport.ContextualModel
noncomputable section
namespace Examples.FrozenMemoStages
open SquareKit.Internal.PathTransport.Typed
universe u
variable (M : StructuralModel.{u})
structure Points where
  context : M.Context
  family : M.Family context
  fiber : M.Family (M.extend context family)
  x : M.Section context family
  y : M.Section context family
  z : M.Section context family
namespace Points
variable {M} (R : Points M)
def reindex {Δ : M.Context} (σ : M.Substitution Δ R.context) : Points M where
  context := Δ
  family := M.subTy R.family σ
  fiber := M.subTy R.fiber (M.lift R.family σ)
  x := M.subTm R.x σ
  y := M.subTm R.y σ
  z := M.subTm R.z σ

def initial (A : M.Family M.empty) (B : M.Family (M.extend M.empty A)) : Points M where
  context := M.extend M.empty A
  family := M.subTy A (M.weaken M.empty A)
  fiber := M.subTy B (M.lift A (M.weaken M.empty A))
  x := M.genericVariable M.empty A
  y := M.genericVariable M.empty A
  z := M.genericVariable M.empty A

def addY : Points M :=
  { R.reindex (M.weaken R.context R.family) with
    y := M.genericVariable R.context R.family }
def addZ : Points M :=
  { R.reindex (M.weaken R.context R.family) with
    z := M.genericVariable R.context R.family }
def path := M.identity R.family R.x R.y
end Points

structure OnePath extends Points M where
  p : M.Section context (M.identity family x y)
namespace OnePath
variable {M} (R : OnePath M)
def reindex {Δ : M.Context} (σ : M.Substitution Δ R.context) : OnePath M where
  toPoints := R.toPoints.reindex σ
  p := cast (congrArg (M.Section Δ) (M.identity_sub R.family R.x R.y σ)) (M.subTm R.p σ)
end OnePath

def Points.addP {M} (R : Points M) : OnePath M where
  toPoints := R.reindex (M.weaken R.context R.path)
  p := cast (congrArg (M.Section _) (M.identity_sub R.family R.x R.y (M.weaken R.context R.path)))
    (M.genericVariable R.context R.path)

structure Parallel extends OnePath M where
  p' : M.Section context (M.identity family x y)
namespace Parallel
variable {M} (R : Parallel M)
def identity := M.identity (M.identity R.family R.x R.y) R.p R.p'
end Parallel

def OnePath.addParallel {M} (R : OnePath M) : Parallel M where
  toOnePath := R.reindex (M.weaken R.context R.toPoints.path)
  p' := cast (congrArg (M.Section _) (M.identity_sub R.family R.x R.y (M.weaken R.context R.toPoints.path)))
    (M.genericVariable R.context R.toPoints.path)

variable (A : M.Family M.empty) (B : M.Family (M.extend M.empty A))
def parallel : Parallel M := (((Points.initial A B).addY).addZ).addP.addParallel

def homotopyContext : M.Context := M.extend (parallel M A B).context (parallel M A B).identity
def homotopy := M.genericVariable (parallel M A B).context (parallel M A B).identity

def homotopyPoints : Points M := (parallel M A B).toPoints.reindex
  (M.weaken (parallel M A B).context (parallel M A B).identity)
def qFamily := M.identity (homotopyPoints M A B).family
  (homotopyPoints M A B).y (homotopyPoints M A B).z
def qPoints : Points M := (homotopyPoints M A B).reindex
  (M.weaken (homotopyPoints M A B).context (qFamily M A B))
def uFamily := M.subTy (qPoints M A B).fiber
  (M.sectionSub (qPoints M A B).family (qPoints M A B).x)
def inputContext := M.extend (qPoints M A B).context (uFamily M A B)
def selectedHomotopy := M.subTm
  (M.subTm (homotopy M A B)
    (M.weaken (homotopyPoints M A B).context (qFamily M A B)))
  (M.weaken (qPoints M A B).context (uFamily M A B))
end Examples.FrozenMemoStages
