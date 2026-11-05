import Mathlib.Data.Fin.Basic

/-! Finite operation trees with substitution and algebraic evaluation. -/
namespace SquareKit
universe u v w z d

inductive FinitaryTerm (Op : Type u) (arity : Op → Nat) (X : Type v) : Type (max u v)
  | leaf : X → FinitaryTerm Op arity X
  | node (op : Op) : (Fin (arity op) → FinitaryTerm Op arity X) → FinitaryTerm Op arity X

variable {Op : Type u} {X : Type v} {Y : Type w} {Z : Type z}
  {D : Type d} {arity : Op → Nat}

namespace FinitaryTerm

def bind (f : X → FinitaryTerm Op arity Y) : FinitaryTerm Op arity X → FinitaryTerm Op arity Y
  | .leaf x => f x
  | .node op ts => .node op (fun i => bind f (ts i))

def map (f : X → Y) : FinitaryTerm Op arity X → FinitaryTerm Op arity Y := bind (leaf ∘ f)

def fold (alg : (op : Op) → (Fin (arity op) → D) → D) (f : X → D) :
    FinitaryTerm Op arity X → D
  | .leaf x => f x
  | .node op ts => alg op (fun i => fold alg f (ts i))

@[simp] theorem bind_leaf_apply (f : X → FinitaryTerm Op arity Y) (x : X) :
    bind f (.leaf x) = f x := rfl
theorem bind_node_apply (f : X → FinitaryTerm Op arity Y)
    (op : Op) (ts : Fin (arity op) → FinitaryTerm Op arity X) :
    bind f (.node op ts) = .node op (fun i => bind f (ts i)) := rfl
@[simp] theorem fold_leaf_apply (alg : (op : Op) → (Fin (arity op) → D) → D)
    (f : X → D) (x : X) : fold alg f (.leaf x) = f x := rfl
@[simp] theorem fold_node_apply (alg : (op : Op) → (Fin (arity op) → D) → D)
    (f : X → D) (op : Op) (ts : Fin (arity op) → FinitaryTerm Op arity X) :
    fold alg f (.node op ts) = alg op (fun i => fold alg f (ts i)) := rfl

@[simp] theorem bind_leaf (t : FinitaryTerm Op arity X) : bind leaf t = t := by
  induction t with
  | leaf => rfl
  | node op ts ih => simp only [bind]; congr 1; funext i; exact ih i

theorem bind_assoc (t : FinitaryTerm Op arity X) (f : X → FinitaryTerm Op arity Y)
    (g : Y → FinitaryTerm Op arity Z) : bind g (bind f t) = bind (fun x => bind g (f x)) t := by
  induction t with
  | leaf => rfl
  | node op ts ih => simp only [bind]; congr 1; funext i; exact ih i

theorem fold_bind (alg : (op : Op) → (Fin (arity op) → D) → D)
    (f : X → FinitaryTerm Op arity Y) (g : Y → D) (t : FinitaryTerm Op arity X) :
    fold alg g (bind f t) = fold alg (fun x => fold alg g (f x)) t := by
  induction t with
  | leaf => rfl
  | node op ts ih => simp only [bind, fold]; congr 1; funext i; exact ih i
theorem fold_node (f : X → FinitaryTerm Op arity Y) (t : FinitaryTerm Op arity X) :
    fold FinitaryTerm.node f t = bind f t := by
  induction t with
  | leaf => rfl
  | node op ts ih => simp only [fold, bind]; congr 1; funext i; exact ih i

end FinitaryTerm
end SquareKit
