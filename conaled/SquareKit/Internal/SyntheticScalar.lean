import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.Ring

/-! Experimental rule-restricted first-order synthetic scalar proofs.
The product argument follows Brasca and Clemente's Apache-2.0 SDG derivation,
revision e4cd622492aba9be421ec0abcf152f58a0ee98df, IsKockLawvere_one/Deriv.lean
(`deriv.leibniz'`, then `deriv_mul`). This is a new source derivation, with no
upstream kernel, choice axiom, or semantic KL class imported.
-/
noncomputable section
namespace SquareKit.Internal.SyntheticScalar

inductive MapExpr (n : ℕ)
  | param (i : Fin n)
  | add (f g : MapExpr n)
  | mul (f g : MapExpr n)
  | derivative (f : MapExpr n)
  deriving DecidableEq

inductive Atom (n : ℕ)
  | base (f : MapExpr n)
  | shifted (f : MapExpr n)
  | epsilon
  deriving DecidableEq

inductive Expr (n : ℕ)
  | atom (a : Atom n)
  | integer (k : ℤ)
  | add (a b : Expr n)
  | mul (a b : Expr n)
  | neg (a : Expr n)
  deriving DecidableEq

namespace Expr
instance {n} : Add (Expr n) := ⟨add⟩
instance {n} : Mul (Expr n) := ⟨mul⟩
instance {n} : Neg (Expr n) := ⟨neg⟩
instance {n} (k : ℕ) : OfNat (Expr n) k := ⟨integer k⟩

def polynomial {n} : Expr n → MvPolynomial (Atom n) ℤ
  | .atom a => MvPolynomial.X a
  | .integer k => MvPolynomial.C k
  | .add a b => polynomial a + polynomial b
  | .mul a b => polynomial a * polynomial b
  | .neg a => -polynomial a

def eval {n} {R : Type*} [CommRing R] (ρ : Atom n → R) : Expr n → R
  | .atom a => ρ a
  | .integer k => k
  | .add a b => eval ρ a + eval ρ b
  | .mul a b => eval ρ a * eval ρ b
  | .neg a => -eval ρ a

theorem eval_polynomial {n} {R : Type*} [CommRing R] (ρ : Atom n → R) (e : Expr n) :
    eval ρ e = MvPolynomial.eval₂ (Int.castRingHom R) ρ (polynomial e) := by
  induction e with
  | atom a => simp [eval, polynomial]
  | integer k => exact (MvPolynomial.eval₂_C (Int.castRingHom R) ρ k).symm
  | add a b ha hb => simp [eval, polynomial, ha, hb]
  | mul a b ha hb => simp [eval, polynomial, ha, hb]
  | neg a ha => simp [eval, polynomial, ha]
end Expr

abbrev base {n} (f : MapExpr n) : Expr n := .atom (.base f)
abbrev shifted {n} (f : MapExpr n) : Expr n := .atom (.shifted f)
abbrev epsilon {n} : Expr n := .atom .epsilon

/-- Complete list of source scalar rules. The ring certificate is equality
in the free integer polynomial ring on syntactic atoms, not semantic equality. -/
inductive Derives {n : ℕ} : Expr n → Expr n → Prop
  | refl (a) : Derives a a
  | symm {a b} : Derives a b → Derives b a
  | trans {a b c} : Derives a b → Derives b c → Derives a c
  | add {a a' b b'} : Derives a a' → Derives b b' → Derives (a+b) (a'+b')
  | mul {a a' b b'} : Derives a a' → Derives b b' → Derives (a*b) (a'*b')
  | neg {a b} : Derives a b → Derives (-a) (-b)
  | ring {a b} : Expr.polynomial a = Expr.polynomial b → Derives a b
  | nilsquare : Derives (epsilon * epsilon) 0
  | taylor (f) : Derives (shifted f) (base f + base (.derivative f) * epsilon)
  | base_add (f g) : Derives (base (.add f g)) (base f + base g)
  | base_mul (f g) : Derives (base (.mul f g)) (base f * base g)
  | shifted_mul (f g) : Derives (shifted (.mul f g)) (shifted f * shifted g)

/-- Separate uniqueness judgment: an expansion certificate determines a slope.
It does not assert cancellation of an individual infinitesimal. -/
inductive Slope {n : ℕ} (f g : MapExpr n) : Prop
  | unique : Derives (shifted f) (base f + base g * epsilon) → Slope f g

abbrev productSlope {n} (f g : MapExpr n) : MapExpr n :=
  .add (.mul (.derivative f) g) (.mul f (.derivative g))

/-- Ring normalization retains the cross term explicitly. -/
theorem product_cross {n} (a b p q : Expr n) :
    Derives ((a+p*epsilon)*(b+q*epsilon))
      ((a*b+(p*b+a*q)*epsilon)+(p*q)*(epsilon*epsilon)) :=
  .ring (by simp only [Expr.polynomial]; ring)

theorem remove_cross {n} (a b p q : Expr n) :
    Derives ((a*b+(p*b+a*q)*epsilon)+(p*q)*(epsilon*epsilon))
      (a*b+(p*b+a*q)*epsilon) := by
  apply Derives.trans (Derives.add (.refl _) (Derives.mul (.refl _) .nilsquare))
  exact .ring (by simp [Expr.polynomial])

/-- The general product expansion is derived from smaller rules. -/
theorem product_expansion {n} (f g : MapExpr n) :
    Derives (shifted (.mul f g))
      (base (.mul f g) + base (productSlope f g) * epsilon) := by
  apply Derives.trans (.shifted_mul f g)
  apply Derives.trans (.mul (.taylor f) (.taylor g))
  apply Derives.trans (product_cross (base f) (base g) (base (.derivative f)) (base (.derivative g)))
  apply Derives.trans (remove_cross (base f) (base g) (base (.derivative f)) (base (.derivative g)))
  apply Derives.symm
  exact .add (.base_mul f g)
    (.mul (.trans (.base_add _ _) (.add (.base_mul _ _) (.base_mul _ _))) (.refl _))

/-- Product rule after the distinct, explicit unique-slope inference. -/
theorem product_rule {n} (f g : MapExpr n) : Slope (.mul f g) (productSlope f g) :=
  .unique (product_expansion f g)

end SquareKit.Internal.SyntheticScalar
