import Squares
import Mathlib.Computability.RegularExpressions

/-!
# Certified symbolic language derivatives

The declarative language semantics and the standard regular-expression syntax
come from Mathlib. We implement smart constructors, an optimized derivative,
normalization, and a recognizer. Their semantic proofs include nullable
concatenation and Kleene star, and hold for every expression and every word.

This is the membership (proposition-valued) specialization of Elliott's
*Symbolic and Automatic Differentiation of Languages* (2021), not a claim that
Boolean recognition retains all parse witnesses. See `Witnesses.lean` for the
proof-relevant semantic layer and ADR 0004 for this boundary.
-/

open scoped Computability

namespace LanguageDerivatives

universe u
variable {α : Type u}

abbrev Regex := RegularExpression

def residual (a : α) (L : Language α) : Language α := {w | a :: w ∈ L}
def residualWord (u : List α) (L : Language α) : Language α := {v | u ++ v ∈ L}

theorem residualWord_append (u v : List α) (L : Language α) :
    residualWord (u ++ v) L = residualWord v (residualWord u L) := by
  apply Language.ext; intro w
  change (u ++ v) ++ w ∈ L ↔ u ++ (v ++ w) ∈ L
  rw [List.append_assoc]

def smartPlus : Regex α → Regex α → Regex α
  | .zero, q => q
  | p, .zero => p
  | p, q => .plus p q

def smartMul : Regex α → Regex α → Regex α
  | .zero, _ => .zero
  | _, .zero => .zero
  | .epsilon, q => q
  | p, .epsilon => p
  | p, q => .comp p q

def smartStar : Regex α → Regex α
  | .zero => .epsilon
  | .epsilon => .epsilon
  | .star p => .star p
  | p => .star p

theorem smartPlus_correct (p q : Regex α) :
    (smartPlus p q).matches' = p.matches' + q.matches' := by
  cases p <;> cases q <;> simp [smartPlus]

theorem smartMul_correct (p q : Regex α) :
    (smartMul p q).matches' = p.matches' * q.matches' := by
  cases p <;> cases q <;> simp [smartMul]

theorem smartStar_correct (p : Regex α) :
    (smartStar p).matches' = p.matches'∗ := by
  cases p <;> simp [smartStar, kstar_idem]

def normalize : Regex α → Regex α
  | .zero => .zero
  | .epsilon => .epsilon
  | .char a => .char a
  | .plus p q => smartPlus (normalize p) (normalize q)
  | .comp p q => smartMul (normalize p) (normalize q)
  | .star p => smartStar (normalize p)

theorem normalize_correct (p : Regex α) : (normalize p).matches' = p.matches' := by
  induction p <;> simp [normalize, smartPlus_correct, smartMul_correct, smartStar_correct, *]

section Decidable
variable [DecidableEq α]

/-- Local simplification prevents the compulsory accumulation of neutral nodes. -/
def derive : Regex α → α → Regex α
  | .zero, _ => .zero
  | .epsilon, _ => .zero
  | .char a, b => if a = b then .epsilon else .zero
  | .plus p q, a => smartPlus (derive p a) (derive q a)
  | .comp p q, a =>
    smartPlus (smartMul (derive p a) q) (if p.matchEpsilon then derive q a else .zero)
  | .star p, a => smartMul (derive p a) (smartStar p)

theorem derive_matches (p : Regex α) (a : α) :
    (derive p a).matches' = (p.deriv a).matches' := by
  induction p with
  | zero => rfl
  | epsilon => rfl
  | char b => rfl
  | plus p q hp hq => simp [derive, RegularExpression.deriv, smartPlus_correct, hp, hq]
  | comp p q hp hq =>
    simp only [derive, smartPlus_correct, smartMul_correct, hp, hq, RegularExpression.deriv]
    cases he : p.matchEpsilon <;> simp [he, hq]
  | star p hp => simp [derive, smartMul_correct, smartStar_correct, hp]

theorem nullable_correct (p : Regex α) : p.matchEpsilon = true ↔ [] ∈ p.matches' :=
  RegularExpression.rmatch_iff_matches' p []

theorem standard_derivative_correct (p : Regex α) (a : α) :
    (p.deriv a).matches' = residual a p.matches' := by
  apply Language.ext; intro w
  change w ∈ (p.deriv a).matches' ↔ a :: w ∈ p.matches'
  rw [← RegularExpression.rmatch_iff_matches', ← RegularExpression.rmatch_iff_matches']
  rfl

/-- The commuting square for one optimized derivative step. -/
theorem derive_correct (p : Regex α) (a : α) :
    (derive p a).matches' = residual a p.matches' := by
  rw [derive_matches, standard_derivative_correct]

def derivatives (p : Regex α) : List α → Regex α
  | [] => p
  | a :: w => derivatives (derive p a) w

theorem derivatives_correct (p : Regex α) (u : List α) :
    (derivatives p u).matches' = residualWord u p.matches' := by
  induction u generalizing p with
  | nil => rfl
  | cons a u ih =>
    rw [derivatives, ih, derive_correct]
    rfl

theorem derivatives_append (p : Regex α) (u v : List α) :
    derivatives p (u ++ v) = derivatives (derivatives p u) v := by
  induction u generalizing p with
  | nil => rfl
  | cons a u ih => simpa [derivatives] using ih (derive p a)

def recognize (p : Regex α) (w : List α) : Bool := (derivatives p w).matchEpsilon

theorem recognize_correct (p : Regex α) (w : List α) :
    recognize p w = true ↔ w ∈ p.matches' := by
  rw [recognize, nullable_correct, derivatives_correct]
  change w ++ [] ∈ p.matches' ↔ w ∈ p.matches'
  simp

/-- A proof-producing decision procedure, not just a tested Boolean function. -/
def decideMembership (p : Regex α) (w : List α) : Decidable (w ∈ p.matches') :=
  decidable_of_iff (recognize p w = true) (recognize_correct p w)

@[reducible] def rep (α : Type u) : Squares.Rep.{u} where
  R := Regex α
  S := Language α
  decode := RegularExpression.matches'

def derivativeSquare (a : α) : Squares.Square (rep α) (rep α) where
  impl := fun p => derive p a
  spec := residual a
  commutes := fun p => derive_correct p a

def derivativesSquare (w : List α) : Squares.Square (rep α) (rep α) where
  impl := fun p => derivatives p w
  spec := residualWord w
  commutes := fun p => derivatives_correct p w

def normalizeSquare : Squares.Square (rep α) (rep α) where
  impl := normalize
  spec := id
  commutes := normalize_correct

def concatSquare : Squares.Square (Squares.product (rep α) (rep α)) (rep α) where
  impl := fun pq => smartMul pq.1 pq.2
  spec := fun LM => LM.1 * LM.2
  commutes := fun pq => smartMul_correct pq.1 pq.2

def starSquare : Squares.Square (rep α) (rep α) where
  impl := smartStar
  spec := fun L => L∗
  commutes := smartStar_correct

/-- Universe lifting keeps observations in the same arrow category as the alphabet. -/
def truthRep : Squares.Rep.{u} where
  R := ULift.{u} Bool
  S := ULift.{u} Prop
  decode := fun b => ⟨b.down = true⟩

def nullableSquare : Squares.Square (rep α) truthRep.{u} where
  impl := fun p => ⟨p.matchEpsilon⟩
  spec := fun L => ⟨[] ∈ L⟩
  commutes := fun p => congrArg ULift.up (propext (nullable_correct p))

/-- Recognition is literally the horizontal pasting of derivative and observation squares. -/
def recognitionSquare (w : List α) : Squares.Square (rep α) truthRep.{u} :=
  Squares.compose nullableSquare (derivativesSquare w)

theorem recognitionSquare_correct (p : Regex α) (w : List α) :
    (recognitionSquare w).impl p = ⟨recognize p w⟩ := rfl

end Decidable

def sample : Regex Char :=
  .comp (.star (.plus (.char 'a') (.char 'b'))) (.comp (.char 'a') (.char 'b'))

example : recognize sample "aabab".toList = true := by decide
example : recognize sample "aabaa".toList = false := by decide
example : recognize (.star (.plus .epsilon (.char 'a'))) "aaa".toList = true := by decide
example : recognize (.comp (.plus .epsilon (.char 'a')) (.char 'b')) "b".toList = true := by decide

end LanguageDerivatives
