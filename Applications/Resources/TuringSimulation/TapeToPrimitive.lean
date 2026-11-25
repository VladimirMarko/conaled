import Mathlib.Computability.TuringMachine.StackTuringMachine

/-!
# Exact primitive time for the existing native tape translation

The native TM1to0 translator emits one primitive move/write per TM0 step.
Counts follow actual statement branches and tape/register updates. Positivity
is required when transporting equal first steps through folded loads/branches.
The actual TM2to1 simulator has primitive syntax bound at most three.

This statement proof adapts Mathlib TM1to0.tr_respects at
56a005855ea17e0b0958f73ec801ae140b0a1679, copyright(c)2018 Mario Carneiro,
Apache2.0. Full endpoints, live halt and outer none remain distinct.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.TuringSimulation.TapeToPrimitive

open Function Turing

variable {Γ Λ σ : Type*}

/-- Number of actual TM0 transitions emitted for one finite native TM1 body.
Moves and writes each add one; loads/branches are folded by trAux; the terminal
goto or halt emits one write of the current symbol. -/
def primitiveSteps [Inhabited Γ] : TM1.Stmt Γ Λ σ → σ → Tape Γ → ℕ
  | .move d q, v, T => primitiveSteps q v (T.move d) + 1
  | .write f q, v, T => primitiveSteps q v (T.write (f T.head v)) + 1
  | .load f q, v, T => primitiveSteps q (f T.head v) T
  | .branch p q₁ q₂, v, T =>
      cond (p T.head v) (primitiveSteps q₁ v T) (primitiveSteps q₂ v T)
  | .goto _, _, _ => 1
  | .halt, _, _ => 1

/-- The syntax-only maximum emitted primitive count. -/
def primitiveBound : TM1.Stmt Γ Λ σ → ℕ
  | .move _ q => primitiveBound q + 1
  | .write _ q => primitiveBound q + 1
  | .load _ q => primitiveBound q
  | .branch _ q₁ q₂ => max (primitiveBound q₁) (primitiveBound q₂)
  | .goto _ => 1
  | .halt => 1

theorem primitiveSteps_pos [Inhabited Γ]
    (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) : 0 < primitiveSteps q v T := by
  induction q generalizing v T with
  | move _ _ _ => exact Nat.zero_lt_succ _
  | write _ _ _ => exact Nat.zero_lt_succ _
  | load f q IH => exact IH (f T.head v) T
  | branch p q₁ q₂ IH₁ IH₂ =>
    cases hp : p T.head v
    · simpa only [primitiveSteps, hp, Bool.cond_false] using IH₂ v T
    · simpa only [primitiveSteps, hp, Bool.cond_true] using IH₁ v T
  | goto _ => exact Nat.zero_lt_one
  | halt => exact Nat.zero_lt_one

theorem primitiveSteps_le_bound [Inhabited Γ]
    (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) :
    primitiveSteps q v T ≤ primitiveBound q := by
  induction q generalizing v T with
  | move d q IH => exact Nat.add_le_add_right (IH v (T.move d)) 1
  | write f q IH => exact Nat.add_le_add_right (IH v (T.write (f T.head v))) 1
  | load f q IH => exact IH (f T.head v) T
  | branch p q₁ q₂ IH₁ IH₂ =>
    cases hp : p T.head v
    · simp only [primitiveSteps, primitiveBound, hp, Bool.cond_false]
      exact le_trans (IH₂ v T) (Nat.le_max_right _ _)
    · simp only [primitiveSteps, primitiveBound, hp, Bool.cond_true]
      exact le_trans (IH₁ v T) (Nat.le_max_left _ _)
  | goto _ => exact le_rfl
  | halt => exact le_rfl

/-- Equal first steps preserve the exact positive optional-iteration count.
Zero is deliberately excluded: the starting configurations may differ. -/
theorem iterate_some_eq_of_step_eq {α : Type*} (f : α → Option α)
    (a b : α) (n : ℕ) (positive : 0 < n) (same : f a = f b) :
    (flip Bind.bind f)^[n] (some a) = (flip Bind.bind f)^[n] (some b) := by
  cases n with
  | zero => exact False.elim (Nat.not_lt_zero _ positive)
  | succ n =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    change (flip Bind.bind f)^[n] (f a) = (flip Bind.bind f)^[n] (f b)
    rw [same]

section Exact

variable [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
variable (M : Λ → TM1.Stmt Γ Λ σ)

/-- Exact native TM0 execution of one TM1 statement body, retaining the complete
translated configuration and tape. This ends at the translated live TM1 result;
the following outer-none transition is separate. -/
theorem statement_exact (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) :
    (flip Bind.bind (TM0.step (TM1to0.tr M)))^[primitiveSteps q v T]
      (some (⟨(some q, v), T⟩ : TM0.Cfg Γ (TM1to0.Λ' M))) =
      some (TM1to0.trCfg M (TM1.stepAux q v T)) := by
  induction q generalizing v T with
  | move d q IH =>
    rw [primitiveSteps, Function.iterate_succ_apply]
    change (flip Bind.bind (TM0.step (TM1to0.tr M)))^[primitiveSteps q v (T.move d)]
      (some (⟨(some q, v), T.move d⟩ : TM0.Cfg Γ (TM1to0.Λ' M))) = _
    exact IH v (T.move d)
  | write f q IH =>
    rw [primitiveSteps, Function.iterate_succ_apply]
    change (flip Bind.bind (TM0.step (TM1to0.tr M)))^[primitiveSteps q v (T.write (f T.head v))]
      (some (⟨(some q, v), T.write (f T.head v)⟩ : TM0.Cfg Γ (TM1to0.Λ' M))) = _
    exact IH v (T.write (f T.head v))
  | load f q IH =>
    have same : TM0.step (TM1to0.tr M)
        (⟨(some (TM1.Stmt.load f q), v), T⟩ : TM0.Cfg Γ (TM1to0.Λ' M)) =
        TM0.step (TM1to0.tr M) ⟨(some q, f T.head v), T⟩ := rfl
    exact (iterate_some_eq_of_step_eq (TM0.step (TM1to0.tr M)) _ _
      (primitiveSteps q (f T.head v) T) (primitiveSteps_pos q (f T.head v) T) same).trans
        (IH (f T.head v) T)
  | branch p q₁ q₂ IH₁ IH₂ =>
    cases hp : p T.head v
    · have same : TM0.step (TM1to0.tr M)
          (⟨(some (TM1.Stmt.branch p q₁ q₂), v), T⟩ : TM0.Cfg Γ (TM1to0.Λ' M)) =
          TM0.step (TM1to0.tr M) ⟨(some q₂, v), T⟩ := by
        simp only [TM0.step, TM1to0.tr, TM1to0.trAux, hp, Bool.cond_false]
      rw [primitiveSteps, hp, Bool.cond_false, TM1.stepAux, hp, Bool.cond_false]
      exact (iterate_some_eq_of_step_eq (TM0.step (TM1to0.tr M)) _ _
        (primitiveSteps q₂ v T) (primitiveSteps_pos q₂ v T) same).trans (IH₂ v T)
    · have same : TM0.step (TM1to0.tr M)
          (⟨(some (TM1.Stmt.branch p q₁ q₂), v), T⟩ : TM0.Cfg Γ (TM1to0.Λ' M)) =
          TM0.step (TM1to0.tr M) ⟨(some q₁, v), T⟩ := by
        simp only [TM0.step, TM1to0.tr, TM1to0.trAux, hp, Bool.cond_true]
      rw [primitiveSteps, hp, Bool.cond_true, TM1.stepAux, hp, Bool.cond_true]
      exact (iterate_some_eq_of_step_eq (TM0.step (TM1to0.tr M)) _ _
        (primitiveSteps q₁ v T) (primitiveSteps_pos q₁ v T) same).trans (IH₁ v T)
  | goto l =>
    simp only [primitiveSteps, Function.iterate_one, Function.flip_def, Bind.bind,
      Option.bind_some, TM0.step, TM1to0.tr, TM1to0.trAux, TM1.stepAux,
      TM1to0.trCfg, Option.map]
    rw [Tape.write_self]
  | halt =>
    simp only [primitiveSteps, Function.iterate_one, Function.flip_def, Bind.bind,
      Option.bind_some, TM0.step, TM1to0.tr, TM1to0.trAux, TM1.stepAux,
      TM1to0.trCfg, Option.map]
    rw [Tape.write_self]

def statementEvalsTo (q : TM1.Stmt Γ Λ σ) (v : σ) (T : Tape Γ) :
    StateTransition.EvalsTo (TM0.step (TM1to0.tr M))
      (⟨(some q, v), T⟩ : TM0.Cfg Γ (TM1to0.Λ' M))
      (some (TM1to0.trCfg M (TM1.stepAux q v T))) where
  steps := primitiveSteps q v T
  evals_in_steps := statement_exact M q v T

theorem source_step_bounded (P : ℕ) (bounded : ∀ l, primitiveBound (M l) ≤ P)
    (a b : TM1.Cfg Γ Λ σ) (hstep : TM1.step M a = some b) :
    Nonempty (StateTransition.EvalsToInTime (TM0.step (TM1to0.tr M))
      (TM1to0.trCfg M a) (some (TM1to0.trCfg M b)) P) := by
  cases a with
  | mk l v T =>
    cases l with
    | none => cases hstep
    | some l =>
      have hb : TM1.stepAux (M l) v T = b := Option.some.inj hstep
      let run := statementEvalsTo M (M l) v T
      rw [← hb]
      exact ⟨{ toEvalsTo := run
               steps_le_m := le_trans (primitiveSteps_le_bound (M l) v T) (bounded l) }⟩

/-- A whole actual TM1 run with a uniform programme bound lifts to at most T*P
actual TM0 transitions, with the exact translated live endpoint. -/
theorem finite_run_bounded (P : ℕ) (bounded : ∀ l, primitiveBound (M l) ≤ P)
    (a b : TM1.Cfg Γ Λ σ) (T : ℕ)
    (hrun : (flip Bind.bind (TM1.step M))^[T] (some a) = some b) :
    Nonempty (StateTransition.EvalsToInTime (TM0.step (TM1to0.tr M))
      (TM1to0.trCfg M a) (some (TM1to0.trCfg M b)) (T * P)) := by
  induction T generalizing b with
  | zero =>
    simp only [Function.iterate_zero_apply, Option.some.injEq] at hrun
    subst b
    refine ⟨?_⟩
    simpa only [Nat.zero_mul] using
      StateTransition.EvalsToInTime.refl (TM0.step (TM1to0.tr M)) (TM1to0.trCfg M a)
  | succ n IH =>
    have hrun' := hrun
    rw [Function.iterate_succ_apply'] at hrun'
    cases hmid : (flip Bind.bind (TM1.step M))^[n] (some a) with
    | none =>
      rw [hmid] at hrun'
      change (none : Option (TM1.Cfg Γ Λ σ)) = some b at hrun'
      cases hrun'
    | some c =>
      rw [hmid] at hrun'
      have hstep : TM1.step M c = some b := by
        simpa only [Function.flip_def, Bind.bind, Option.bind_some] using hrun'
      obtain ⟨before⟩ := IH c hmid
      obtain ⟨after⟩ := source_step_bounded M P bounded c b hstep
      let run := StateTransition.EvalsTo.trans (TM0.step (TM1to0.tr M))
        (TM1to0.trCfg M a) (TM1to0.trCfg M c) (some (TM1to0.trCfg M b))
        before.toEvalsTo after.toEvalsTo
      refine ⟨{ toEvalsTo := run, steps_le_m := ?_ }⟩
      change after.steps + before.steps ≤ (n + 1) * P
      calc
        _ ≤ P + n * P := Nat.add_le_add after.steps_le_m before.steps_le_m
        _ = (n + 1) * P := by
          rw [Nat.add_mul, Nat.one_mul]
          exact Nat.add_comm _ _

theorem halted_step (v : σ) (T : Tape Γ) :
    TM0.step (TM1to0.tr M) (TM1to0.trCfg M (⟨none, v, T⟩ : TM1.Cfg Γ Λ σ)) = none := rfl

end Exact

section StackSimulator

variable {K : Type*} {Δ : K → Type*} {L R : Type*}

theorem primitiveBound_trNormal (q : TM2.Stmt Δ L R) :
    primitiveBound (TM2to1.trNormal q) = 1 := by
  induction q <;> simp_all only [TM2to1.trNormal, primitiveBound, max_self]

theorem primitiveBound_trStAct_goto [DecidableEq K]
    (k : K) (o : TM2to1.StAct K Δ R k) (q : TM2.Stmt Δ L R) :
    primitiveBound (TM2to1.trStAct (TM1.Stmt.goto (fun _ _ => TM2to1.Λ'.ret q)) o) = 3 := by
  cases o <;> rfl

/-- The actual stack simulator has a global three-primitive bound, even though
its continuation-bearing label type is not globally finite. -/
theorem primitiveBound_stack_tr [DecidableEq K]
    (M : L → TM2.Stmt Δ L R) (l : TM2to1.Λ' K Δ L R) :
    primitiveBound (TM2to1.tr M l) ≤ 3 := by
  cases l with
  | normal l =>
    rw [TM2to1.tr, primitiveBound_trNormal]
    decide
  | go k o q =>
    rw [TM2to1.tr, primitiveBound, primitiveBound_trStAct_goto]
    change max 3 2 ≤ 3
    decide
  | ret q =>
    rw [TM2to1.tr, primitiveBound, primitiveBound_trNormal]
    change max 1 2 ≤ 3
    decide

/-- Lift an already checked native TM1 stack-simulator run to primitive TM0
execution with factor at most three. The exact translated full endpoint remains
inside some; no subsequent outer-none transition is included. -/
theorem stack_run_bounded [DecidableEq K] [Inhabited L] [Inhabited R]
    (M : L → TM2.Stmt Δ L R)
    (a b : TM1.Cfg (TM2to1.Γ' K Δ) (TM2to1.Λ' K Δ L R) R) (W : ℕ)
    (source : StateTransition.EvalsToInTime (TM1.step (TM2to1.tr M)) a (some b) W) :
    Nonempty (StateTransition.EvalsToInTime
      (TM0.step (TM1to0.tr (TM2to1.tr M)))
      (TM1to0.trCfg (TM2to1.tr M) a)
      (some (TM1to0.trCfg (TM2to1.tr M) b)) (3 * W)) := by
  obtain ⟨run⟩ := finite_run_bounded (TM2to1.tr M) 3
    (primitiveBound_stack_tr M) a b source.steps source.evals_in_steps
  refine ⟨{ toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }⟩
  calc
    run.steps ≤ source.steps * 3 := run.steps_le_m
    _ ≤ W * 3 := Nat.mul_le_mul_right 3 source.steps_le_m
    _ = 3 * W := Nat.mul_comm _ _

end StackSimulator

end Resources.TuringSimulation.TapeToPrimitive
