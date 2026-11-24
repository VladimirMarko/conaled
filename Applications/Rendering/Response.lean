import Mathlib.Algebra.GroupWithZero.Action.Basic
import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Emission/transmission layering, separate from world geometry and sampling. -/
namespace Applications.Rendering

/-- A response emits a value and acts on incoming light by its transmission. -/
@[ext] structure Response (T V : Type*) where
  emission : V
  transmission : T

namespace Response
variable {T V : Type*}

/-- The selected one-way optical model. No positivity is implicit. -/
def eval [Add V] [SMul T V] (r : Response T V) (incoming : V) : V :=
  r.emission + r.transmission • incoming

instance [Zero V] [One T] : One (Response T V) := ⟨⟨0, 1⟩⟩

@[simp] theorem one_emission [Zero V] [One T] : (1 : Response T V).emission = 0 := rfl
@[simp] theorem one_transmission [Zero V] [One T] :
    (1 : Response T V).transmission = 1 := rfl

/-- `front * back` places `front` nearer the observer: `back` acts first. -/
instance [Add V] [SMul T V] [Mul T] : Mul (Response T V) :=
  ⟨fun front back => ⟨front.eval back.emission, front.transmission * back.transmission⟩⟩

@[simp] theorem mul_emission [Add V] [SMul T V] [Mul T]
    (front back : Response T V) :
    (front * back).emission = front.eval back.emission := rfl

@[simp] theorem mul_transmission [Add V] [SMul T V] [Mul T]
    (front back : Response T V) :
    (front * back).transmission = front.transmission * back.transmission := rfl

variable [Monoid T] [AddMonoid V] [DistribMulAction T V]

@[simp] theorem eval_one (incoming : V) : (1 : Response T V).eval incoming = incoming := by
  simp [eval]

/-- Representation composition preserves the entire response, for every incoming value. -/
theorem eval_mul (front back : Response T V) (incoming : V) :
    (front * back).eval incoming = front.eval (back.eval incoming) := by
  simp [eval, smul_add, mul_smul, add_assoc]

instance : Monoid (Response T V) where
  one_mul r := by ext <;> simp [eval]
  mul_one r := by ext <;> simp [eval]
  mul_assoc a b c := by
    ext
    · exact eval_mul a b c.emission
    · exact mul_assoc _ _ _

/-- Standard Mathlib preservation interface, with multiplication in `End` = composition. -/
def meaning : Response T V →* Function.End V where
  toFun := eval
  map_one' := funext eval_one
  map_mul' a b := funext (eval_mul a b)

/-- Front-to-back finite layering evaluates from the back toward the observer. -/
theorem eval_prod (layers : List (Response T V)) (incoming : V) :
    layers.prod.eval incoming = layers.foldr (fun r light => r.eval light) incoming := by
  induction layers with
  | nil => simp
  | cons front rest ih => simp only [List.prod_cons, eval_mul, List.foldr_cons, ih]

/-- A spatial query and its incoming value are separate from the response algebra. -/
def observe {X P : Type*} (scene : X → Response T V) (query : P → X)
    (incoming : P → V) (p : P) : V := (scene (query p)).eval (incoming p)

/-- Pointwise layer composition uses the same response theorem in every query space. -/
theorem observe_mul {X P : Type*} (front back : X → Response T V)
    (query : P → X) (incoming : P → V) (p : P) :
    observe (front * back) query incoming p =
      (front (query p)).eval (observe back query incoming p) :=
  eval_mul _ _ _

/-- Pullback along any query map preserves pointwise response composition. -/
def reindex {X Y : Type*} (f : Y → X) :
    (X → Response T V) →* (Y → Response T V) where
  toFun scene := scene ∘ f
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Scalar/value data unchanged by relabeling; both scene and query are transported. -/
theorem observe_reindex {X Y P : Type*} (e : X ≃ Y) (scene : X → Response T V)
    (query : P → X) (incoming : P → V) :
    observe (reindex e.symm scene) (e ∘ query) incoming = observe scene query incoming := by
  funext p
  simp [observe, reindex]

/-- Independent layer pullbacks agree with observing their original composition. -/
theorem observe_reindex_mul {X Y P : Type*} (e : X ≃ Y)
    (front back : X → Response T V) (query : P → X) (incoming : P → V) :
    observe (reindex e.symm front * reindex e.symm back) (e ∘ query) incoming =
      observe (front * back) query incoming := by
  rw [← (reindex e.symm).map_mul]
  exact observe_reindex e _ _ _

end Response
end Applications.Rendering
