import SquareKit.Internal.PathTransport.ComparisonComprehension

noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- The complete external signature comparison: base functor and primitive
fiber transformation. Neither is required to be invertible. -/
structure Signature where
  base : Context.{u}
  leftFiber : base.left ⥤ Type u
  rightFiber : base.right ⥤ Type u
  fiberMap : leftFiber ⟶ base.map ⋙ rightFiber

namespace Signature
variable (S : Signature.{u})

def baseFamily (Γ : Context.{u}) : Family Γ where
  left := constant S.base.left
  right := constant S.base.right
  map := { app := fun _ => S.base.map, naturality := fun {_ _} _ => rfl }

/-- The section comparison yields the required base-signature square. -/
def baseSubstitution {Γ : Context.{u}} (x : Section (S.baseFamily Γ)) : Substitution Γ S.base where
  left := baseFunctor x.left
  right := baseFunctor x.right
  commutes := by
    have h := congrArg baseFunctor x.commutes
    have hi : baseFunctor (x.left.familyImage (S.baseFamily Γ).map) =
        baseFunctor x.left ⋙ S.base.map := by
      fapply CategoryTheory.Functor.ext
      · intro γ; rfl
      · intro γ δ f
        simp [baseFunctor, GroupoidModel.Section.familyImage, GroupoidModel.Section.lift,
          baseFamily, Grothendieck.map, Grpd.forgetToCat]
    exact hi.symm.trans h

def primitive : Family S.base where
  left := setFamily S.leftFiber
  right := setFamily S.rightFiber
  map := whiskerRight S.fiberMap discrete

/-- Primitive dependent fibers are obtained by the same proved reindexing
operation used by all other families. -/
def fiber {Γ : Context.{u}} (x : Section (S.baseFamily Γ)) : Family Γ :=
  S.primitive.reindex (S.baseSubstitution x)

theorem fiber_left {Γ : Context.{u}} (x : Section (S.baseFamily Γ)) :
    (S.fiber x).left = primitiveFiber S.leftFiber x.left := rfl

theorem fiber_right {Γ : Context.{u}} (x : Section (S.baseFamily Γ)) :
    (S.fiber x).right = primitiveFiber S.rightFiber x.right := rfl

theorem base_sub {Γ Δ : Context.{u}} (σ : Substitution Δ Γ) :
    (S.baseFamily Γ).reindex σ = S.baseFamily Δ := by
  refine @Family.ext _ _ _ rfl rfl ?_
  apply heq_of_eq
  apply NatTrans.ext
  funext γ
  rfl

theorem baseSubstitution_reindex {Γ Δ : Context.{u}}
    (x : Section (S.baseFamily Γ)) (σ : Substitution Δ Γ) :
    S.baseSubstitution (cast (congrArg Section (S.base_sub σ)) (x.reindex σ)) =
      Substitution.comp (S.baseSubstitution x) σ := by
  apply Substitution.ext
  · dsimp [baseSubstitution, Substitution.comp]
    rfl
  · dsimp [baseSubstitution, Substitution.comp]
    rfl

theorem fiber_sub {Γ Δ : Context.{u}} (x : Section (S.baseFamily Γ))
    (σ : Substitution Δ Γ) :
    (S.fiber x).reindex σ =
      S.fiber (cast (congrArg Section (S.base_sub σ)) (x.reindex σ)) := by
  unfold fiber
  rw [S.baseSubstitution_reindex, Family.reindex_comp]

end Signature
end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
