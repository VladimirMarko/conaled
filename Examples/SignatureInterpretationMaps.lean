import SquareKit.Internal.PathTransport.SignatureInterpretationMaps
import SquareKit.Internal.PathTransport.Authoring
import SquareKit.Internal.DependentJudgments.NativeTypeModel

/-! A fresh J caller with a two-binder dependent tail, preserved through the
existing generated interpreter. The scope case separates structural maps
from maps preserving the primitive signature. -/
namespace Examples.SignatureInterpretationMaps
open SquareKit.Internal.PathTransport Typed Authoring
universe u

namespace DependentTail

def context : CtxDeriv [.base] (extendCode emptyCode (baseCode emptyCode)) :=
  .ext .empty (.base .empty)
def point := BasePoint.variable (CtxDeriv.empty : CtxDeriv [] emptyCode.{u})
def paths := CtxDeriv.path context (.base context) point.deriv
def z := BasePoint.variable paths
def withZ := CtxDeriv.ext paths (.base paths)
def fiber := TyDeriv.fiber z.deriv
def withFiber := CtxDeriv.ext withZ fiber

/-- The later binder has type `fiber z`, so this is a dependent tail. -/
def tail := TelDeriv.cons (.base paths) (.cons fiber (.nil withFiber))
def tailCode := (fun {Γ γ n Δ T} (_ : TelDeriv Γ γ n Δ T) => T) tail
def zAtFiber := z.weaken withZ fiber

def command := PathCommand.make context (.base context) point.deriv tail
  (Motive.reflexivity context (.base context) point.deriv tail
    (.base withFiber) zAtFiber.deriv)

def generic := command.genericTerm
def reflexive := command.reflexiveTerm

def weakening := SubDeriv.weaken context (TyDeriv.fiber point.deriv)
def reindexedBranch := TmDeriv.reindexJBranch context (.base context) point.deriv tail
  command.motive.typing command.motive.branchTyping weakening

def tailMap := SubDeriv.pathTailMap context (.base context) point.deriv tail weakening

variable {M N : Model.{u}} (F : SignatureMap M N)

/-- The entire two-binder telescope is mapped, retaining the second dependency. -/
theorem tail_preserved : F.TelPres tailCode :=
  F.generatedTel tail

/-- Mapping also identifies the full context and its dependent fiber family. -/
theorem context_preserved : F.context (interpretCtx M withFiber) = interpretCtx N withFiber :=
  F.interpretCtx withFiber

theorem fiber_preserved : HEq (F.family (interpretTy M fiber)) (interpretTy N fiber) :=
  F.interpretTy fiber

/-- Endpoint-instantiated J uses the same preservation result as generic J. -/
theorem reflexive_preserved :
    HEq (F.mapTm (interpretTm M reflexive)) (interpretTm N reflexive) :=
  F.interpretTm reflexive

/-- The new caller uses generic J and the existing recursive interpreter. -/
theorem generic_preserved :
    HEq (F.mapTm (interpretTm M generic)) (interpretTm N generic) :=
  F.interpretTm generic

/-- Rebuilding the branch after weakening retains its dependent fiber binder. -/
theorem reindexed_branch_preserved :
    HEq (F.mapTm (interpretTm M reindexedBranch)) (interpretTm N reindexedBranch) :=
  F.interpretTm reindexedBranch

/-- Both endpoint contexts of the reindexed tail substitution are retained. -/
theorem tail_map_preserved :
    HEq (F.substitution (interpretSub M tailMap)) (interpretSub N tailMap) :=
  F.interpretSub tailMap

end DependentTail

namespace Scope
open SquareKit.Internal.DependentJudgments
abbrev inhabited := NativeType.model Unit (fun _ => Unit)
abbrev uninhabited := NativeType.model Empty Empty.elim

/-- The structural operations admit the identity map while the signatures differ. -/
def structural : StructuralMap inhabited.toStructuralModel uninhabited.toStructuralModel where
  context := id
  family := id
  mapTm := id
  substitution := id
  empty := rfl
  extend _ := rfl
  id _ := rfl
  comp _ _ := rfl
  subTy _ _ := rfl
  subTm _ _ := HEq.rfl
  weaken _ := HEq.rfl
  mapVariable _ := HEq.rfl
  identity _ _ _ := rfl
  reflexivity _ _ := HEq.rfl

/-- Structural preservation alone cannot preserve even the generated base type. -/
theorem base_not_preserved :
    structural.family (inhabited.base PUnit) ≠ uninhabited.base (structural.context PUnit) := by
  intro h
  have e : (Unit : Type) = Empty := congrFun h PUnit.unit
  exact Empty.elim (cast e ())

/-- Signature compatibility is satisfiable for the nonempty native model. -/
def nativeIdentity : SignatureMap inhabited inhabited := SignatureMap.identityMap inhabited

/-- The fresh dependent-J derivation specializes to an inhabited concrete model. -/
example : HEq (nativeIdentity.mapTm (interpretTm inhabited DependentTail.generic))
    (interpretTm inhabited DependentTail.generic) :=
  DependentTail.generic_preserved nativeIdentity
end Scope
end Examples.SignatureInterpretationMaps
