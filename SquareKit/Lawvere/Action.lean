import SquareKit.Lawvere.Operations

/-! Carrier-indexed evaluation, with exact transport to bundled algebras. -/
namespace SquareKit.Lawvere.Operations
universe u v w

/-- An operation algebra on a specified carrier. Keeping the carrier as a parameter
lets clients infer scalar instances without unfolding a categorical model. -/
structure Action (O : Operations.{u}) (X : Type w) where
  act : ∀ {n}, O.Op n → (Fin n → X) → X
  var_act : ∀ {n} (i : Fin n) (x : Fin n → X), act (O.var i) x = x i
  subst_act : ∀ {m n} (t : O.Op n) (σ : Fin n → O.Op m) (x : Fin m → X),
    act (O.subst t σ) x = act t (fun i => act (σ i) x)

namespace Action
variable {O : Operations.{u}} {X : Type w}

def algebra (A : Action O X) : O.Algebra where
  Carrier := X
  act := A.act
  var_act := A.var_act
  subst_act := A.subst_act

/-- Restriction leaves the specified carrier unchanged, including at arity zero. -/
def restrict {P : Operations.{v}} (F : O.Map P) (A : Action P X) : Action O X where
  act t x := A.act (F.map t) x
  var_act i x := by rw [F.map_var, A.var_act]
  subst_act t σ x := by rw [F.map_subst, A.subst_act]

@[simp] theorem restrict_act {P : Operations.{v}} (F : O.Map P) (A : Action P X)
    {n} (t : O.Op n) (x : Fin n → X) : (A.restrict F).act t x = A.act (F.map t) x := rfl

/-- Restricting operations and restricting their categorical model agree exactly. -/
theorem restrict_model {P : Operations.{v}} (F : O.Map P) (A : Action P X) :
    (A.restrict F).algebra.model = (Model.restrict F.theoryHom).obj A.algebra.model := rfl
end Action

namespace Algebra
variable {O : Operations.{u}}
def action (A : O.Algebra.{u,w}) : Action O A.Carrier :=
  ⟨A.act, A.var_act, A.subst_act⟩
@[simp] theorem action_algebra (A : O.Algebra.{u,w}) : A.action.algebra = A := rfl
end Algebra

namespace Action
@[simp] theorem algebra_action {O : Operations.{u}} {X : Type w} (A : Action O X) :
    A.algebra.action = A := rfl
end Action

namespace Map
variable {O : Operations.{u}} {P : Operations.{v}} {Q : Operations}
def id (O : Operations.{u}) : O.Map O := ⟨fun t => t, fun _ => rfl, fun _ _ => rfl⟩
def comp (F : O.Map P) (G : P.Map Q) : O.Map Q where
  map t := G.map (F.map t)
  map_var i := by rw [F.map_var, G.map_var]
  map_subst t σ := by rw [F.map_subst, G.map_subst]
end Map

namespace Action
variable {O : Operations.{u}} {P : Operations.{v}} {Q : Operations} {X : Type w}
@[simp] theorem restrict_id (A : Action O X) : A.restrict (Map.id O) = A := rfl
@[simp] theorem restrict_comp (F : O.Map P) (G : P.Map Q) (A : Action Q X) :
    A.restrict (F.comp G) = (A.restrict G).restrict F := rfl
end Action
end SquareKit.Lawvere.Operations
