import Applications.Resources.TuringSimulation.StackToTape
import Examples.TuringSimulation

/-!
# Selected stack heights along the actual native TM2 statement path

Uncompiled external draft. EXPECTATIONS.md was frozen before this proof text.
This predicate supplies source-side hypotheses for later primitive geometry.
It does not define a target interval, a visited set, or an occupied-support bound.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.TuringSimulation.StackToTape

open Turing Turing.TM2to1

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq K]

/-- Every executed stack action in this finite source statement body has old
and new selected lengths at most H. Registers, updates, and branch choices are
the actual native source operations. Goto and halt end this body inspection. -/
def InternalHeight : TM2.Stmt Γ Λ σ → σ → (∀ j, List (Γ j)) → ℕ → Prop
  | .push k f q, v, S, H =>
      (S k).length ≤ H ∧ (f v :: S k).length ≤ H ∧
        InternalHeight q v (Function.update S k (f v :: S k)) H
  | .peek k f q, v, S, H =>
      (S k).length ≤ H ∧ (S k).length ≤ H ∧
        InternalHeight q (f v (S k).head?) S H
  | .pop k f q, v, S, H =>
      (S k).length ≤ H ∧ (S k).tail.length ≤ H ∧
        InternalHeight q (f v (S k).head?) (Function.update S k (S k).tail) H
  | .load f q, v, S, H => InternalHeight q (f v) S H
  | .branch p q₁ q₂, v, S, H =>
      cond (p v) (InternalHeight q₁ v S H) (InternalHeight q₂ v S H)
  | .goto _, _, _, _ => True
  | .halt, _, _, _ => True

/-- Group the three native stack actions, retaining their actual register
effect and updated family. Peek's same-stack update reduces to the original family. -/
theorem internalHeight_stRun
    (k : K) (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ)
    (v : σ) (S : ∀ j, List (Γ j)) (H : ℕ) :
    InternalHeight (stRun o q) v S H =
      ((S k).length ≤ H ∧ (stWrite v (S k) o).length ≤ H ∧
        InternalHeight q (stVar v (S k) o)
          (Function.update S k (stWrite v (S k) o)) H) := by
  cases o <;> simp only [stRun, InternalHeight, stWrite, stVar, Function.update_eq_self]

/-- Widening the bound does not change the executed source path or its data. -/
theorem InternalHeight.mono
    (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ j, List (Γ j))
    {H H' : ℕ} (hle : H ≤ H') (h : InternalHeight q v S H) :
    InternalHeight q v S H' := by
  induction q using stmtStRec generalizing v S with
  | run k o q ih =>
    rw [internalHeight_stRun] at h ⊢
    exact ⟨le_trans h.1 hle, le_trans h.2.1 hle,
      ih (stVar v (S k) o) (Function.update S k (stWrite v (S k) o)) h.2.2⟩
  | load f _ ih => exact ih (f v) S h
  | branch p _ _ ih₁ ih₂ =>
    cases hp : p v
    · simp only [InternalHeight, hp, Bool.cond_false] at h ⊢
      exact ih₂ v S h
    · simp only [InternalHeight, hp, Bool.cond_true] at h ⊢
      exact ih₁ v S h
  | goto _ => trivial
  | halt => trivial

/-- The whole-family length-plus-action reserve is sufficient for the actual
path predicate. It is stronger than InternalHeight and is not its definition. -/
theorem internalHeight_of_reserve
    (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ j, List (Γ j)) (H : ℕ)
    (hS : ∀ j, (S j).length + actionBound q ≤ H) :
    InternalHeight q v S H := by
  induction q using stmtStRec generalizing v S with
  | run k o q ih =>
    simp only [actionBound_run] at hS
    rw [internalHeight_stRun]
    have hS' : ∀ j,
        ((Function.update S k (stWrite v (S k) o)) j).length + actionBound q ≤ H := by
      intro j
      by_cases hj : j = k
      · subst j
        rw [Function.update_self]
        have hgrow := stWrite_length_le k o v (S k)
        have hreserve := hS k
        omega
      · rw [Function.update_of_ne hj]
        have hreserve := hS j
        omega
    have hold : (S k).length ≤ H := by
      have hreserve := hS k
      omega
    have hnew : (stWrite v (S k) o).length ≤ H := by
      have hreserve := hS' k
      rw [Function.update_self] at hreserve
      omega
    exact ⟨hold, hnew,
      ih (stVar v (S k) o) (Function.update S k (stWrite v (S k) o)) hS'⟩
  | load f _ ih => exact ih (f v) S hS
  | branch p q₁ q₂ ih₁ ih₂ =>
    have h₁ : ∀ j, (S j).length + actionBound q₁ ≤ H := fun j =>
      le_trans (Nat.add_le_add_left (Nat.le_max_left _ _) _) (hS j)
    have h₂ : ∀ j, (S j).length + actionBound q₂ ≤ H := fun j =>
      le_trans (Nat.add_le_add_left (Nat.le_max_right _ _) _) (hS j)
    cases hp : p v
    · simp only [InternalHeight, hp, Bool.cond_false]
      exact ih₂ v S h₂
    · simp only [InternalHeight, hp, Bool.cond_true]
      exact ih₁ v S h₁
  | goto _ => trivial
  | halt => trivial

/-- A uniform starting length B and supplied syntax bound A give height B+A
for this statement. A program-wide choice of A remains the caller's obligation. -/
theorem internalHeight_of_uniform_bound
    (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ j, List (Γ j)) (B A : ℕ)
    (hS : ∀ j, (S j).length ≤ B) (hA : actionBound q ≤ A) :
    InternalHeight q v S (B + A) :=
  internalHeight_of_reserve q v S (B + A)
    (fun j => Nat.add_le_add (hS j) hA)

end Resources.TuringSimulation.StackToTape

namespace Examples.TuringSimulation.InternalHeightCases

open Turing Turing.TM2to1
open Resources.TuringSimulation.StackToTape

def emptyPeekBody : TM2.Stmt (fun _ : Bool => Bool) Unit Bool :=
  stRun Cases.emptyPeek .halt

def emptyPopBody : TM2.Stmt (fun _ : Bool => Bool) Unit Bool :=
  stRun Cases.emptyPop .halt

/-- An unselected four-cell stack does not exclude the empty peek's H=0 path. -/
theorem empty_peek_height_zero :
    InternalHeight emptyPeekBody false Cases.emptySelectedStacks 0 ∧
      (Cases.emptySelectedStacks true).length = 4 := by
  refine ⟨?_, rfl⟩
  rw [emptyPeekBody, internalHeight_stRun]
  change (0 : ℕ) ≤ 0 ∧ 0 ≤ 0 ∧ True
  decide

/-- Empty pop also permits H=0, with the same unrelated four-cell stack. -/
theorem empty_pop_height_zero :
    InternalHeight emptyPopBody false Cases.emptySelectedStacks 0 ∧
      (Cases.emptySelectedStacks true).length = 4 := by
  refine ⟨?_, rfl⟩
  rw [emptyPopBody, internalHeight_stRun]
  change (0 : ℕ) ≤ 0 ∧ 0 ≤ 0 ∧ True
  decide

/-- The sufficient whole-family reserve is not necessary for the preceding
valid H=0 path; its unrelated true index would require 4+1≤0. -/
theorem empty_peek_not_reserved :
    ¬ (∀ j : Bool,
      (Cases.emptySelectedStacks j).length + actionBound emptyPeekBody ≤ 0) := by
  intro h
  have htrue := h true
  change (5 : ℕ) ≤ 0 at htrue
  exact (by decide : ¬ ((5 : ℕ) ≤ 0)) htrue

/-- The actual internal peak is one even though the complete native source
step starts and ends with empty stacks. Endpoint emptiness cannot replace it. -/
theorem pushPop_height_and_empty_endpoints :
    InternalHeight StatementCases.pushPopBody () StatementCases.emptyFamily 1 ∧
      ¬ InternalHeight StatementCases.pushPopBody () StatementCases.emptyFamily 0 ∧
      TM2.step StatementCases.pushPopProgram
        ⟨some (), (), StatementCases.emptyFamily⟩ =
        some ⟨none, (), StatementCases.emptyFamily⟩ := by
  refine ⟨?_, ?_, StatementCases.pushPop_source_step⟩
  · change (0 : ℕ) ≤ 1 ∧ 1 ≤ 1 ∧ 1 ≤ 1 ∧ 0 ≤ 1 ∧ True
    decide
  · change ¬ ((0 : ℕ) ≤ 0 ∧ 1 ≤ 0 ∧ 1 ≤ 0 ∧ 0 ≤ 0 ∧ True)
    decide

/-- The uniform reserve gives the safe coarser height two, while monotonicity
also transports the independently established precise height one to any H≥1. -/
theorem pushPop_uniform_and_widening :
    InternalHeight StatementCases.pushPopBody () StatementCases.emptyFamily 2 ∧
      ∀ H : ℕ, 1 ≤ H →
        InternalHeight StatementCases.pushPopBody () StatementCases.emptyFamily H := by
  have hzero : ∀ j : Unit, (StatementCases.emptyFamily j).length ≤ 0 := by
    intro j
    exact Nat.le_refl 0
  have hbound : actionBound StatementCases.pushPopBody ≤ 2 := by decide
  refine ⟨internalHeight_of_uniform_bound StatementCases.pushPopBody ()
    StatementCases.emptyFamily 0 2 hzero hbound, ?_⟩
  intro H hH
  exact InternalHeight.mono StatementCases.pushPopBody () StatementCases.emptyFamily
    hH pushPop_height_and_empty_endpoints.1

/-- The supplied false register loads true before branching, so the selected
stack grows from two to three. The unused stack of length four is not constrained. -/
theorem loaded_true_height_three_not_two :
    InternalHeight StatementCases.branchBody false Cases.sourceStacks 3 ∧
      ¬ InternalHeight StatementCases.branchBody false Cases.sourceStacks 2 ∧
      (Cases.sourceStacks true).length = 4 := by
  refine ⟨?_, ?_, rfl⟩
  · change (2 : ℕ) ≤ 3 ∧ 3 ≤ 3 ∧ True
    decide
  · change ¬ ((2 : ℕ) ≤ 2 ∧ 3 ≤ 2 ∧ True)
    decide

/-- Supplied true loads false and chooses halt, so no stack is selected and
H=0 is valid despite the nonempty starting family. This is not a default change. -/
theorem loaded_false_height_zero :
    InternalHeight StatementCases.branchBody true Cases.sourceStacks 0 := by
  change True
  trivial

end Examples.TuringSimulation.InternalHeightCases
