import SquareKit.AssemblyCutFold
import Mathlib.CategoryTheory.Endofunctor.Algebra

/-! The finite cut algebra has the endofunctor initiality universal property. -/
universe u
namespace Realizability.Assembly

private noncomputable def ignoreContext {A : Assembly.{u}} (a : Hom (programLift A) A) :
    Hom (prod iterationCuts (programLift A)) A := (snd _ _).comp a

def cutIterValue {A : Assembly.{u}} (a : Hom (programLift A) A) : Nat → A.Carrier
  | 0 => a.toFun none
  | n + 1 => a.toFun (some (cutIterValue a n))

private theorem ignoreContext_value {A : Assembly.{u}} (a : Hom (programLift A) A)
    (γ : iterationCuts.Carrier) (n : Nat) : cutFoldValue (ignoreContext a) γ n = cutIterValue a n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun x => a.toFun (some x)) ih

noncomputable def cutIter {A : Assembly.{u}} (a : Hom (programLift A) A) : Hom iterationCuts A :=
  (pair (Hom.id _) (Hom.id _)).comp (cutFold (ignoreContext a))

theorem cutIter_value {A : Assembly.{u}} (a : Hom (programLift A) A) (n : Nat) :
    (cutIter a).toFun ⟨n⟩ = cutIterValue a n := ignoreContext_value a ⟨n⟩ n

theorem cutIter_square {A : Assembly.{u}} (a : Hom (programLift A) A) :
    cutRoll.comp (cutIter a) = (programLiftMap (cutIter a)).comp a := by
  apply Hom.ext
  intro t
  cases t with
  | none => exact cutIter_value a 0
  | some n =>
    change (cutIter a).toFun ⟨n.down + 1⟩ = a.toFun (some ((cutIter a).toFun n))
    rw [cutIter_value]
    exact congrArg (fun x => a.toFun (some x)) (cutIter_value a n.down).symm

theorem cutIter_unique {A : Assembly.{u}} (a : Hom (programLift A) A)
    (h : Hom iterationCuts A) (hh : cutRoll.comp h = (programLiftMap h).comp a) :
    h = cutIter a := by
  apply Hom.ext
  rintro ⟨n⟩
  rw [cutIter_value]
  induction n with
  | zero => exact congrArg (fun f => f.toFun none) hh
  | succ n ih =>
    have hs := congrArg (fun f => f.toFun (some ⟨n⟩)) hh
    change h.toFun ⟨n + 1⟩ = a.toFun (some (h.toFun ⟨n⟩)) at hs
    exact hs.trans (congrArg (fun x => a.toFun (some x)) ih)

theorem cutInclusion_roll : (programLiftMap cutInclusion).comp finalRoll =
    cutRoll.comp cutInclusion.{u} := by
  apply Hom.ext
  intro t
  cases t <;> rfl

theorem cutInclusion_initial : cutIter finalRoll = cutInclusion.{u} :=
  (cutIter_unique finalRoll cutInclusion cutInclusion_roll.symm).symm

open CategoryTheory
noncomputable def cutAlgebra : Endofunctor.Algebra programLiftFunctor.{u} :=
  ⟨iterationCuts, cutRoll⟩

noncomputable def cutAlgebra_initial : Limits.IsInitial cutAlgebra.{u} :=
  Limits.IsInitial.ofUniqueHom
    (fun X => ⟨cutIter X.str, (cutIter_square X.str).symm⟩)
    (fun X h => Endofunctor.Algebra.Hom.ext (cutIter_unique X.str h.f h.h.symm))

end Realizability.Assembly
