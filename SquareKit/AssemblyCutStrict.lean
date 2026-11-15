import SquareKit.AssemblyCutInitial
import SquareKit.AssemblyLiftStrength
import Mathlib.CategoryTheory.Monad.Algebra

/-! Strict lifting algebra and its successor universal property. -/
universe u
namespace Realizability.Assembly
open CategoryTheory

/-- The strict algebra is derived from the endofunctor algebra and monad multiplication. -/
noncomputable def cutStrictMap : Hom (programLift iterationCuts.{u}) iterationCuts :=
  ((programLiftMap cutUnroll).comp (programLiftMul _)).comp cutRoll

@[simp] theorem cutStrictMap_none : cutStrictMap.toFun none = (⟨0⟩ : iterationCuts.{u}.Carrier) := rfl

@[simp] theorem cutStrictMap_some (n : iterationCuts.{u}.Carrier) : cutStrictMap.toFun (some n) = n := by
  rcases n with ⟨n⟩
  cases n <;> rfl

noncomputable def cutStrictAlgebra : Monad.Algebra programLiftMonad.{u} where
  A := iterationCuts
  a := cutStrictMap
  unit := Hom.ext cutStrictMap_some
  assoc := by
    apply Hom.ext
    intro t
    cases t with
    | none => rfl
    | some t =>
      change cutStrictMap.toFun t = cutStrictMap.toFun (some (cutStrictMap.toFun t))
      exact (cutStrictMap_some _).symm

theorem strictAlgebra_some (X : Monad.Algebra programLiftMonad.{u}) (x : X.A.Carrier) :
    X.a.toFun (some x) = x := congrArg (fun h => h.toFun x) X.unit

/-- Iteration remains a single tracked arrow over the explicit context. -/
noncomputable def strictIteration {Γ : Assembly.{u}} (X : Monad.Algebra programLiftMonad.{u})
    (g : Hom (prod Γ X.A) X.A) : Hom (prod Γ iterationCuts) X.A :=
  cutFold (((liftStrength Γ X.A).comp (programLiftMap g)).comp X.a)

theorem strictIteration_zero {Γ : Assembly.{u}} (X : Monad.Algebra programLiftMonad.{u})
    (g : Hom (prod Γ X.A) X.A) (γ : Γ.Carrier) :
    (strictIteration X g).toFun (γ, ⟨0⟩) = X.a.toFun none := rfl

theorem strictIteration_succ {Γ : Assembly.{u}} (X : Monad.Algebra programLiftMonad.{u})
    (g : Hom (prod Γ X.A) X.A) (γ : Γ.Carrier) (n : Nat) :
    (strictIteration X g).toFun (γ, ⟨n + 1⟩) =
      g.toFun (γ, (strictIteration X g).toFun (γ, ⟨n⟩)) :=
  strictAlgebra_some X _

noncomputable def strictIter (X : Monad.Algebra programLiftMonad.{u}) (g : Hom X.A X.A) :
    Hom iterationCuts X.A := cutIter ((programLiftMap g).comp X.a)

theorem strictIter_zero (X : Monad.Algebra programLiftMonad.{u}) (g : Hom X.A X.A) :
    (strictIter X g).toFun ⟨0⟩ = X.a.toFun none := cutIter_value _ 0

theorem strictIter_succ (X : Monad.Algebra programLiftMonad.{u}) (g : Hom X.A X.A)
    (n : iterationCuts.Carrier) :
    (strictIter X g).toFun (cutSuccessor.toFun n) = g.toFun ((strictIter X g).toFun n) := by
  have h := congrArg (fun f => f.toFun (some n)) (cutIter_square ((programLiftMap g).comp X.a))
  exact h.trans (strictAlgebra_some X _)

noncomputable def strictIterHom (X : Monad.Algebra programLiftMonad.{u}) (g : Hom X.A X.A) :
    Monad.Algebra.Hom cutStrictAlgebra X where
  f := strictIter X g
  h := by
    apply Hom.ext
    intro t
    cases t with
    | none => exact (strictIter_zero X g).symm
    | some n =>
      change X.a.toFun (some ((strictIter X g).toFun n)) =
        (strictIter X g).toFun (cutStrictMap.toFun (some n))
      exact (strictAlgebra_some X _).trans (congrArg (strictIter X g).toFun (cutStrictMap_some n)).symm

theorem strictIterHom_unique (X : Monad.Algebra programLiftMonad.{u}) (g : Hom X.A X.A)
    (h : Monad.Algebra.Hom cutStrictAlgebra X)
    (hs : cutSuccessor.comp h.f = h.f.comp g) : h = strictIterHom X g := by
  apply Monad.Algebra.Hom.ext
  apply cutIter_unique
  apply Hom.ext
  intro t
  cases t with
  | none => exact (congrArg (fun f => f.toFun none) h.h).symm
  | some n =>
    exact (congrArg (fun f => f.toFun n) hs).trans (strictAlgebra_some X _).symm

/-- Initial among strict algebras equipped with an arbitrary successor. -/
theorem strict_successor_initial (X : Monad.Algebra programLiftMonad.{u}) (g : Hom X.A X.A) :
    ∃! h : Monad.Algebra.Hom cutStrictAlgebra X, cutSuccessor.comp h.f = h.f.comp g := by
  refine ⟨strictIterHom X g, Hom.ext (strictIter_succ X g), ?_⟩
  exact fun h hs => strictIterHom_unique X g h hs

end Realizability.Assembly
