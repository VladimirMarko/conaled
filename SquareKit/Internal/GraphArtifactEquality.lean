import SquareKit.Internal.CoreSyntax

/-! Structural equality for the bounded artifact boundary. Unlike Lean's fast
BEq operations, these comparisons have kernel-checked reflection theorems.
Metadata expressions are deliberately unsupported. -/
namespace SquareKit.Internal.GraphArtifactEquality
open Lean

deriving instance DecidableEq for LevelMVarId
deriving instance DecidableEq for Level
deriving instance DecidableEq for BinderInfo
deriving instance DecidableEq for Literal
deriving instance DecidableEq for FVarId
deriving instance DecidableEq for MVarId
deriving instance DecidableEq for ReducibilityHints
deriving instance DecidableEq for DefinitionSafety
deriving instance DecidableEq for CoreSyntax.Expr

/-- Binder names are retained here, including in primitive declaration records. -/
def exprEq : Lean.Expr → Lean.Expr → Bool
  | .bvar a, .bvar b => decide (a = b)
  | .fvar a, .fvar b => decide (a = b)
  | .mvar a, .mvar b => decide (a = b)
  | .sort a, .sort b => decide (a = b)
  | .const a us, .const b vs => decide (a = b ∧ us = vs)
  | .app f a, .app g b => exprEq f g && exprEq a b
  | .lam n a b i, .lam m c d j => decide (n = m ∧ i = j) && exprEq a c && exprEq b d
  | .forallE n a b i, .forallE m c d j => decide (n = m ∧ i = j) && exprEq a c && exprEq b d
  | .letE n a b c i, .letE m d e f j =>
      decide (n = m ∧ i = j) && exprEq a d && exprEq b e && exprEq c f
  | .lit a, .lit b => decide (a = b)
  | .proj n i a, .proj m j b => decide (n = m ∧ i = j) && exprEq a b
  | _, _ => false

theorem exprEq_sound {a b : Lean.Expr} (h : exprEq a b = true) : a = b := by
  induction a generalizing b <;> cases b <;>
    simp_all [exprEq, Bool.and_eq_true, decide_eq_true_eq] <;> grind

def valEq (a b : ConstantVal) : Bool :=
  decide (a.name = b.name ∧ a.levelParams = b.levelParams) && exprEq a.type b.type

theorem valEq_sound {a b : ConstantVal} (h : valEq a b = true) : a = b := by
  rcases a with ⟨an, al, aty⟩; rcases b with ⟨bn, bl, bt⟩
  simp only [valEq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨rfl, rfl⟩, h⟩ := h
  cases exprEq_sound h
  rfl

def ruleEq (a b : RecursorRule) : Bool :=
  decide (a.ctor = b.ctor ∧ a.nfields = b.nfields) && exprEq a.rhs b.rhs

theorem ruleEq_sound {a b : RecursorRule} (h : ruleEq a b = true) : a = b := by
  rcases a with ⟨an, af, ar⟩; rcases b with ⟨bn, bf, br⟩
  simp only [ruleEq, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨rfl, rfl⟩, h⟩ := h
  cases exprEq_sound h
  rfl

def listEq (eq : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => eq a b && listEq eq as bs
  | _, _ => false

theorem listEq_sound (eq : α → α → Bool) (sound : ∀ {a b}, eq a b = true → a = b)
    {as bs : List α} (h : listEq eq as bs = true) : as = bs := by
  induction as generalizing bs <;> cases bs <;> simp_all [listEq, Bool.and_eq_true]
  rename_i a as ih b bs
  exact ⟨sound h.1, ih h.2⟩

/-- Rejects opaque, quotient and axiom records; the pinned graph environment
contains none. Every field of each supported declaration kind is compared. -/
def constantEq : ConstantInfo → ConstantInfo → Bool
  | .thmInfo a, .thmInfo b => valEq a.toConstantVal b.toConstantVal && exprEq a.value b.value && decide (a.all = b.all)
  | .defnInfo a, .defnInfo b => valEq a.toConstantVal b.toConstantVal && exprEq a.value b.value &&
      decide (a.hints = b.hints ∧ a.safety = b.safety ∧ a.all = b.all)
  | .inductInfo a, .inductInfo b => valEq a.toConstantVal b.toConstantVal &&
      decide (a.numParams = b.numParams ∧ a.numIndices = b.numIndices ∧ a.all = b.all ∧
        a.ctors = b.ctors ∧ a.numNested = b.numNested ∧ a.isRec = b.isRec ∧
        a.isUnsafe = b.isUnsafe ∧ a.isReflexive = b.isReflexive)
  | .ctorInfo a, .ctorInfo b => valEq a.toConstantVal b.toConstantVal &&
      decide (a.induct = b.induct ∧ a.cidx = b.cidx ∧ a.numParams = b.numParams ∧
        a.numFields = b.numFields ∧ a.isUnsafe = b.isUnsafe)
  | .recInfo a, .recInfo b => valEq a.toConstantVal b.toConstantVal &&
      listEq ruleEq a.rules b.rules &&
      decide (a.all = b.all ∧ a.numParams = b.numParams ∧ a.numIndices = b.numIndices ∧
        a.numMotives = b.numMotives ∧ a.numMinors = b.numMinors ∧ a.k = b.k ∧ a.isUnsafe = b.isUnsafe)
  | _, _ => false

theorem constantEq_sound {a b : ConstantInfo} (h : constantEq a b = true) : a = b := by
  cases a <;> cases b <;> simp only [constantEq, Bool.and_eq_true, decide_eq_true_eq] at h
  all_goals try contradiction
  all_goals rename_i a b
  all_goals cases a; cases b
  all_goals have hv := @valEq_sound
  all_goals have he := @exprEq_sound
  all_goals have hr := @listEq_sound _ ruleEq (@ruleEq_sound)
  all_goals simp only at h
  all_goals grind

end SquareKit.Internal.GraphArtifactEquality
