import SquareKit.RelationalSemanticBoundary
import Mathlib.Tactic

/-! Native one-step configuration semantics, independent of any pattern language. -/
namespace MatchingLogic.Configuration
inductive Cfg where
  | run : Nat → Cfg
  | done : Nat → Cfg
  deriving DecidableEq, Repr
inductive Label where
  | keepA | keepB | bump
  deriving DecidableEq, Repr

def LabeledStep : Cfg → Label → Cfg → Prop
  | .run n, .keepA, d => d = .done n
  | .run n, .keepB, d => d = .done n
  | .run n, .bump, d => d = .done (n+1)
  | .done _, _, _ => False

def outcomes (c : Cfg) : Set Cfg := {d | ∃ l, LabeledStep c l d}
def post (A : Set Cfg) : Set Cfg := {d | ∃ c ∈ A, d ∈ outcomes c}
def Safe (c : Cfg) (B : Set Cfg) : Prop := outcomes c ⊆ B

@[simp] theorem outcomes_run (n : Nat) : outcomes (.run n) = {.done n, .done (n+1)} := by
  ext d
  constructor
  · rintro ⟨l,h⟩
    cases l <;> simp_all [LabeledStep]
  · intro h
    rcases h with h | h
    · exact ⟨.keepA,h⟩
    · exact ⟨.bump,h⟩
@[simp] theorem outcomes_done (n : Nat) : outcomes (.done n) = ∅ := by
  ext d
  simp [outcomes, LabeledStep]
theorem excluded (n : Nat) : Cfg.done (n+2) ∉ outcomes (.run n) := by simp

abbrev Trace (c d : Cfg) := {l : Label // LabeledStep c l d}
theorem Trace.forget {c d : Cfg} (t : Trace c d) : d ∈ outcomes c := ⟨t.val,t.property⟩
def keepA (n : Nat) : Trace (.run n) (.done n) := ⟨.keepA,rfl⟩
def keepB (n : Nat) : Trace (.run n) (.done n) := ⟨.keepB,rfl⟩
theorem keep_distinct (n : Nat) : keepA n ≠ keepB n := by
  intro h
  have := congrArg Subtype.val h
  cases this
theorem forgotten_equal (n : Nat) : (keepA n).forget = (keepB n).forget := Subsingleton.elim _ _
theorem no_recovery (n : Nat) :
    ¬∃ back : (Cfg.done n ∈ outcomes (.run n)) → Trace (.run n) (.done n),
      ∀ t, back t.forget = t := by
  rintro ⟨back,h⟩
  exact keep_distinct n ((h (keepA n)).symm.trans ((congrArg back (forgotten_equal n)).trans (h (keepB n))))

/-- Select a witness explicitly; this does not recover a previously supplied label. -/
def select (c d : Cfg) (h : d ∈ outcomes c) : Trace c d := by
  cases c with
  | done n => simp at h
  | run n =>
    by_cases same : d = .done n
    · exact ⟨.keepA,same⟩
    · have hs : d = .done (n+1) := by simpa [same] using h
      exact ⟨.bump,hs⟩
theorem select_keep (n : Nat) : select (.run n) (.done n) (keepA n).forget = keepA n := by
  simp [select, keepA]
theorem select_bump (n : Nat) (h : Cfg.done (n+1) ∈ outcomes (.run n)) :
    (select (.run n) (.done (n+1)) h).val = .bump := by simp [select]
theorem select_forget {c d : Cfg} (h : d ∈ outcomes c) : (select c d h).forget = h := Subsingleton.elim _ _

def enriched (c : Cfg) : Set (Cfg × Label) := {p | LabeledStep c p.2 p.1}
theorem enriched_forget (c : Cfg) : Prod.fst '' enriched c = outcomes c := by
  ext d
  constructor
  · rintro ⟨⟨d,l⟩,h,rfl⟩; exact ⟨l,h⟩
  · rintro ⟨l,h⟩; exact ⟨(d,l),h,rfl⟩
def boundary : Relational.RelRep where
  R := Cfg
  S := Cfg
  Rel c d := d ∈ outcomes c

theorem boundary_outcomes (c : Cfg) :
    (Relational.SemanticBoundary.possibilities boundary).decode c = outcomes c := rfl
end MatchingLogic.Configuration
