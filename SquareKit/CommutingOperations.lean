import Mathlib.Data.List.Basic

/-! A bounded unary interaction comparison: local interchange derives block
reordering for arbitrary finite operation words. Own-theory laws are separate. -/
namespace SquareKit.CommutingOperations
universe u v w

def run {S : Type u} {X : Type v} (op : S → X → X) : List S → X → X
  | [], x => x
  | s :: ss, x => op s (run op ss x)

/-- This is a local requirement per pair of operation symbols. -/
def Interchange {S : Type u} {T : Type w} {X : Type v}
    (left : S → X → X) (right : T → X → X) : Prop :=
  ∀ s t x, left s (right t x) = right t (left s x)

theorem operation_word {S : Type u} {T : Type w} {X : Type v}
    (left : S → X → X) (right : T → X → X) (h : Interchange left right)
    (s : S) (ts : List T) (x : X) :
    left s (run right ts x) = run right ts (left s x) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    change left s (right t (run right ts x)) = right t (run right ts (left s x))
    rw [h s t, ih]

/-- No whole-word compatibility is supplied by the caller. -/
theorem word_word {S : Type u} {T : Type w} {X : Type v}
    (left : S → X → X) (right : T → X → X) (h : Interchange left right)
    (ss : List S) (ts : List T) (x : X) :
    run left ss (run right ts x) = run right ts (run left ss x) := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    change left s (run left ss (run right ts x)) = run right ts (left s (run left ss x))
    rw [ih, operation_word left right h]

/-- The mixed-law contract is necessary as well as sufficient for all words. -/
theorem interchange_iff_words {S : Type u} {T : Type w} {X : Type v}
    (left : S → X → X) (right : T → X → X) :
    Interchange left right ↔ ∀ ss ts x,
      run left ss (run right ts x) = run right ts (run left ss x) := by
  constructor
  · exact word_word left right
  · intro h s t x
    exact h [s] [t] x

def onLeft (_ : Unit) (p : Bool × Bool) : Bool × Bool := (!p.1, p.2)
def onRight (_ : Unit) (p : Bool × Bool) : Bool × Bool := (p.1, false)
/-- A maintenance change preserves idempotence but introduces interaction. -/
def copyLeft (_ : Unit) (p : Bool × Bool) : Bool × Bool := (p.1, p.1)

theorem left_involution (p : Bool × Bool) : onLeft () (onLeft () p) = p := by
  cases p with | mk a b => cases a <;> rfl

theorem right_idempotent (p : Bool × Bool) : onRight () (onRight () p) = onRight () p := rfl

theorem copy_idempotent (p : Bool × Bool) : copyLeft () (copyLeft () p) = copyLeft () p := rfl

theorem independent_interchange : Interchange onLeft onRight := by
  intro s t x
  rfl

theorem independent_words (ss ts : List Unit) (p : Bool × Bool) :
    run onLeft ss (run onRight ts p) = run onRight ts (run onLeft ss p) :=
  word_word onLeft onRight independent_interchange ss ts p

theorem changed_mixed_law_fails : ¬ Interchange onLeft copyLeft := by
  intro h
  have hx := h () () (false, false)
  have hy := congrArg Prod.snd hx
  contradiction

end SquareKit.CommutingOperations
