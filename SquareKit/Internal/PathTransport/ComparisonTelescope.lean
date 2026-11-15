import SquareKit.Internal.PathTransport.ComparisonPath

noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory Typed Typed.StructuralModel ContextualElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (S : Signature.{u})
local notation "M" => structuralModel S

theorem model_lift {Γ Δ : Context.{u}} (A : Family Γ) (σ : Substitution Δ Γ) :
    StructuralModel.lift M A σ = A.lift σ := by
  apply Substitution.ext
  · exact congrArg ULift.down (eq_of_heq ((leftProjection S).lift A σ))
  · exact congrArg ULift.down (eq_of_heq ((rightProjection S).lift A σ))

def extendContraction {Γ Δ : Context.{u}} (e : Contraction Δ Γ) (A : Family Γ) :
    Contraction (A.reindex e.forward).extend A.extend :=
  (e.extend A).changeForward (StructuralModel.lift M A e.forward) (by
    rw [model_lift S]
    apply Substitution.ext <;> rfl)

/-- Recurse over every structural dependent declaration. The square is
constructed at each step, not supplied for the completed telescope. -/
def telescopeContraction {Γ Δ : Context.{u}} {n}
    (T : Telescope M Γ n) (e : Contraction Δ Γ) :
    Contraction (Telescope.total M (Telescope.pullback M T e.forward))
      (Telescope.total M T) :=
  match T with
  | .nil => e
  | .cons A tail => telescopeContraction tail (extendContraction S e A)

theorem telescopeContraction_forward {Γ Δ : Context.{u}} {n}
    (T : Telescope M Γ n) (e : Contraction Δ Γ) :
    (telescopeContraction S T e).forward = Telescope.liftSub M T e.forward :=
  match T with
  | .nil => rfl
  | .cons A tail => telescopeContraction_forward tail (extendContraction S e A)

def root {Γ : Context.{u}} (A : Family Γ) (x : Section A) :
    Contraction Γ (StructuralModel.pathContext M A x) :=
  (rootContraction S A x).changeForward (StructuralModel.rootSub M A x)
    (rootContraction_forward S A x)

/-- The full branch inclusion, with its comparison through arbitrary tails. -/
def rootTail {Γ : Context.{u}} {n} (A : Family Γ) (x : Section A)
    (T : Telescope M (StructuralModel.pathContext M A x) n) :
    Contraction (Telescope.total M (Telescope.pullback M T (StructuralModel.rootSub M A x)))
      (Telescope.total M T) :=
  (telescopeContraction S T (root S A x)).changeForward
    (StructuralModel.rootTail M A x T) (telescopeContraction_forward S T (root S A x))

/-- Contextual J has both direct interpretations and a constructed comparison.
Neither a final tail square nor a J compatibility proof is an input. -/
def contextualJ {Γ : Context.{u}} {n} (A : Family Γ) (x : Section A)
    (T : Telescope M (StructuralModel.pathContext M A x) n)
    (D : Family (Telescope.total M T))
    (d : Section (D.reindex (StructuralModel.rootTail M A x T))) : Section D :=
  (rootTail S A x T).eliminate D d

theorem contextualJ_beta {Γ : Context.{u}} {n} (A : Family Γ) (x : Section A)
    (T : Telescope M (StructuralModel.pathContext M A x) n)
    (D : Family (Telescope.total M T))
    (d : Section (D.reindex (StructuralModel.rootTail M A x T))) :
    (contextualJ S A x T D d).reindex (StructuralModel.rootTail M A x T) = d := by
  apply Section.ext
  · exact eliminateSection_beta (rootTail S A x T).left D.left d.left
  · exact eliminateSection_beta (rootTail S A x T).right D.right d.right

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
