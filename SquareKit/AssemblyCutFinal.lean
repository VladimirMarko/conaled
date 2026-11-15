import SquareKit.AssemblyCutFinalValues
import Mathlib.CategoryTheory.Endofunctor.Algebra

/-! Finality of the finite/full cut coalgebra, including the tracked mediator. -/
universe u
namespace Realizability.Assembly

private theorem finalUnroll_value (n : finalCuts.{u}.Carrier) :
    finalUnroll.toFun n = Option.map ULift.up (cutUnrollValue n.down) := by
  rcases n with ⟨n⟩
  cases n with
  | none => rfl
  | some n => cases n <;> rfl

private theorem finalUnroll_down (n : finalCuts.{u}.Carrier) :
    Option.map ULift.down (finalUnroll.toFun n) = cutUnrollValue n.down := by
  rcases n with ⟨n⟩
  cases n with
  | none => rfl
  | some n => cases n <;> rfl

theorem cutUnfold_square {A : Assembly.{u}} (c : Hom A (programLift A)) :
    (cutUnfold c).comp finalUnroll = c.comp (programLiftMap (cutUnfold c)) := by
  apply Hom.ext
  intro x
  refine (finalUnroll_value ((cutUnfold c).toFun x)).trans ?_
  refine (congrArg (Option.map ULift.up) (unfoldLength_square c.toFun x)).trans ?_
  change Option.map ULift.up (Option.map (unfoldLength c.toFun) (c.toFun x)) =
    Option.map (fun y => ULift.up (unfoldLength c.toFun y)) (c.toFun x)
  cases c.toFun x <;> rfl

theorem cutUnfold_unique {A : Assembly.{u}} (c : Hom A (programLift A))
    (h : Hom A finalCuts) (hh : h.comp finalUnroll = c.comp (programLiftMap h)) :
    h = cutUnfold c := by
  have hp : ∀ x, cutUnrollValue (h.toFun x).down =
      Option.map (fun y => (h.toFun y).down) (c.toFun x) := by
    intro x
    refine (finalUnroll_down (h.toFun x)).symm.trans ?_
    refine (congrArg (fun f => Option.map ULift.down (f.toFun x)) hh).trans ?_
    change Option.map ULift.down (Option.map h.toFun (c.toFun x)) =
      Option.map (fun y => (h.toFun y).down) (c.toFun x)
    cases c.toFun x <;> rfl
  have he := unfoldLength_unique c.toFun (fun x => (h.toFun x).down) hp
  apply Hom.ext
  intro x
  exact ULift.ext (congrFun he x)

open CategoryTheory
noncomputable def cutCoalgebra : Endofunctor.Coalgebra programLiftFunctor.{u} :=
  ⟨finalCuts, finalUnroll⟩

noncomputable def cutCoalgebra_final : Limits.IsTerminal cutCoalgebra.{u} :=
  Limits.IsTerminal.ofUniqueHom
    (fun X => ⟨cutUnfold X.str, (cutUnfold_square X.str).symm⟩)
    (fun X h => Endofunctor.Coalgebra.Hom.ext (cutUnfold_unique X.str h.f h.h.symm))

end Realizability.Assembly
