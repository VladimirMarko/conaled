import SquareKit.Internal.CoreSyntax

/-! Declarative typing of the admitted dependent core fragment.
`Context` stores each binder's type in the preceding context. The primitive
rules below state the complete explicit applications and universe arguments.
They use the standard Lean meanings of Eq, And, Exists and their named proof
operations. This is a bounded typing judgment, not a kernel acceptance algorithm. -/
namespace SquareKit.Internal.CoreSyntax
open Lean
abbrev Context := List Expr

inductive Lookup : Context → Nat → Expr → Prop where
  | zero : Lookup (a :: Γ) 0 a.shift
  | succ : Lookup Γ n a → Lookup (b :: Γ) (n + 1) a.shift

def instantiate (b a : Expr) : Expr := b.subst (fun | 0 => a | n + 1 => .bvar n)
def equality (u : Level) (a x y : Expr) := Expr.app3 (.const ``Eq [u]) a x y
def conjunction (p q : Expr) := Expr.app2 (.const ``And []) p q
def existential (u : Level) (a p : Expr) := Expr.app2 (.const ``Exists [u]) a (.lam a p)

inductive HasType : Context → Expr → Expr → Prop where
  | var : Lookup Γ n a → HasType Γ (.bvar n) a
  | sort : HasType Γ (.sort u) (.sort (.succ u))
  | weaken : HasType Γ e a → HasType (b :: Γ) e.shift a.shift
  | pi : HasType Γ a (.sort u) → HasType (a :: Γ) b (.sort v) →
      HasType Γ (.all a b) (.sort (.imax u v))
  | lam : HasType Γ a (.sort u) → HasType (a :: Γ) b t →
      HasType Γ (.lam a b) (.all a t)
  | app : HasType Γ f (.all a b) → HasType Γ x a → HasType Γ (.app f x) (instantiate b x)
  | eqType : HasType Γ a (.sort u) → HasType Γ x a → HasType Γ y a →
      HasType Γ (equality u a x y) (.sort .zero)
  | andType : HasType Γ p (.sort .zero) → HasType Γ q (.sort .zero) →
      HasType Γ (conjunction p q) (.sort .zero)
  | existsType : HasType Γ a (.sort u) → HasType (a :: Γ) p (.sort .zero) →
      HasType Γ (existential u a p) (.sort .zero)
  | andLeft : HasType Γ p (.sort .zero) → HasType Γ q (.sort .zero) →
      HasType Γ h (conjunction p q) →
      HasType Γ (.apps (.const ``And.left []) [p, q, h]) p
  | andRight : HasType Γ p (.sort .zero) → HasType Γ q (.sort .zero) →
      HasType Γ h (conjunction p q) →
      HasType Γ (.apps (.const ``And.right []) [p, q, h]) q
  | andIntro : HasType Γ p (.sort .zero) → HasType Γ q (.sort .zero) →
      HasType Γ h p → HasType Γ k q →
      HasType Γ (.apps (.const ``And.intro []) [p, q, h, k]) (conjunction p q)
  | eqRefl : HasType Γ a (.sort u) → HasType Γ x a →
      HasType Γ (.apps (.const ``Eq.refl [u]) [a, x]) (equality u a x x)
  | eqSymm : HasType Γ a (.sort u) → HasType Γ x a → HasType Γ y a →
      HasType Γ h (equality u a x y) →
      HasType Γ (.apps (.const ``Eq.symm [u]) [a, x, y, h]) (equality u a y x)
  | eqTrans : HasType Γ a (.sort u) → HasType Γ x a → HasType Γ y a → HasType Γ z a →
      HasType Γ h (equality u a x y) → HasType Γ k (equality u a y z) →
      HasType Γ (.apps (.const ``Eq.trans [u]) [a, x, y, z, h, k]) (equality u a x z)
  | congrArg : HasType Γ a (.sort u) → HasType Γ b (.sort v) →
      HasType Γ x a → HasType Γ y a → HasType Γ f (.all a b.shift) →
      HasType Γ h (equality u a x y) →
      HasType Γ (.apps (.const ``congrArg [u, v]) [a, b, x, y, f, h])
        (equality v b (.app f x) (.app f y))
  | existsIntro : HasType Γ a (.sort u) → HasType (a :: Γ) p (.sort .zero) →
      HasType Γ x a → HasType Γ h (instantiate p x) →
      HasType Γ (.apps (.const ``Exists.intro [u]) [a, .lam a p, x, h]) (existential u a p)
  | existsElim : HasType Γ a (.sort u) → HasType (a :: Γ) p (.sort .zero) →
      HasType Γ q (.sort .zero) → HasType Γ h (existential u a p) →
      HasType (p :: a :: Γ) branch q.shift.shift →
      HasType Γ (.apps (.const ``Exists.elim [u]) [a, .lam a p, q, h, .lam a (.lam p branch)]) q

end SquareKit.Internal.CoreSyntax
