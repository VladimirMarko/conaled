import SquareKit.ReactiveCompiler
import Applications.FRP.Feedback

/-! Two compiled aggregate consumers. Batch summation is an explicit observation;
it is not an order- or occurrence-preserving payload encoding. -/
namespace FRPSpec.Reactive
open FirstOrderCompiler Progress Progress.Feedback

inductive NatPrim : Ty → Ty → Type where
  | literal : Nat → NatPrim .unit .base
  | add : NatPrim (.prod .base .base) .base

def meaning : {a b : Ty} → NatPrim a b → Val Nat a → Val Nat b
  | _, _, .literal n, _ => n
  | _, _, .add, (x,y) => x+y

abbrev K := ListFoldCompiler.functionScalar meaning
abbrev sound := ListFoldCompiler.functionScalarSound meaning

def lit {Γ : Ctx} (n : Nat) : Term NatPrim Γ .base := .prim (.literal n) .unit
def add {Γ : Ctx} (x y : Term NatPrim Γ .base) : Term NatPrim Γ .base :=
  .prim .add (.pair x y)

abbrev pairTy : Ty := .prod .base .base

def jointSeed : Term NatPrim [] pairTy := .pair (lit 0) (lit 0)
def jointNext : Term NatPrim [.base,pairTy] pairTy :=
  .pair (add (.fst (.var (.there .here))) (lit 1))
    (add (.snd (.var (.there .here))) (.var .here))
def jointBody : Term NatPrim [.base,pairTy] (.prod pairTy pairTy) :=
  .letE jointNext (.pair (.var .here) (.var .here))

/-- Compiled data is stored before the runtime step closure is formed. -/
def jointCode := ReactiveCompiler.compile K jointSeed jointBody
def jointMachine : Initialized Nat (Nat × Nat) (Nat × Nat) :=
  ReactiveCompiler.realize K sound.denote jointCode

def jointSpec : Initialized Nat (Nat × Nat) (Nat × Nat) where
  initial := (0,0)
  step := fun (x,k,total) => ((k+1,total+x),(k+1,total+x))

theorem joint_correct : jointMachine = jointSpec := by
  exact ReactiveCompiler.realize_compile K sound jointSeed jointBody

def countBody : Term NatPrim [.base,.base] (.prod .base .base) :=
  .letE (add (.var (.there .here)) (lit 1)) (.pair (.var .here) (.var .here))
def totalBody : Term NatPrim [.base,.base] (.prod .base .base) :=
  .letE (add (.var (.there .here)) (.var .here)) (.pair (.var .here) (.var .here))
def countCode := ReactiveCompiler.compile K (lit 0) countBody
def totalCode := ReactiveCompiler.compile K (lit 0) totalBody
def countMachine : Initialized Nat Nat Nat := ReactiveCompiler.realize K sound.denote countCode
def totalMachine : Initialized Nat Nat Nat := ReactiveCompiler.realize K sound.denote totalCode

def countSpec : Initialized Nat Nat Nat := ⟨fun (_,k) => (k+1,k+1),0⟩
def totalSpec : Initialized Nat Nat Nat := ⟨fun (x,total) => (total+x,total+x),0⟩
theorem count_correct : countMachine = countSpec :=
  ReactiveCompiler.realize_compile K sound (lit 0) countBody
theorem total_correct : totalMachine = totalSpec :=
  ReactiveCompiler.realize_compile K sound (lit 0) totalBody

def duplicate : Term NatPrim [.base] pairTy := .pair (.var .here) (.var .here)
def finish : Term NatPrim [pairTy] pairTy :=
  .pair (.fst (.var .here)) (add (.snd (.var .here)) (.fst (.var .here)))
def duplicateCode := ReactiveCompiler.compileMap K duplicate
def finishCode := ReactiveCompiler.compileMap K finish

def duplicateFn : Nat → Nat × Nat := ReactiveCompiler.realizeMap K sound.denote duplicateCode
def finishFn : Nat × Nat → Nat × Nat := ReactiveCompiler.realizeMap K sound.denote finishCode

theorem duplicate_correct (x : Nat) : duplicateFn x = (x,x) :=
  ReactiveCompiler.map_sound K sound duplicate x
theorem finish_correct (p : Nat × Nat) : finishFn p = (p.1,p.2+p.1) :=
  ReactiveCompiler.map_sound K sound finish p

abbrev WiredState : Type := (PUnit × (Nat × Nat)) × PUnit

def wired : Initialized Nat (Nat × Nat) WiredState :=
  seq (seq (pure duplicateFn) (par countMachine totalMachine)) (pure finishFn)

/-- Independent specification, with no structural Unit states or compiled calls. -/
def wiredSpec : Initialized Nat (Nat × Nat) (Nat × Nat) where
  initial := (0,0)
  step := fun (x,k,total) => ((k+1,total+x+(k+1)),(k+1,total+x))

def StateRel (w : WiredState) (s : Nat × Nat) : Prop := w.1.2 = s

theorem wired_initial : StateRel wired.initial wiredSpec.initial := rfl

theorem wired_step (x y : Nat) (w : WiredState) (s : Nat × Nat)
    (hx : x = y) (hs : StateRel w s) :
    (wired.step (x,w)).1 = (wiredSpec.step (y,s)).1 ∧
      StateRel (wired.step (x,w)).2 (wiredSpec.step (y,s)).2 := by
  subst y
  rcases w with ⟨⟨u,k,total⟩,v⟩
  cases u; cases v
  change (k,total) = s at hs
  subst s
  simp [wired,seq,par,Progress.Feedback.pure,count_correct,total_correct,countSpec,totalSpec,
    duplicate_correct,finish_correct,wiredSpec,StateRel]

theorem wired_stream (a : Stream Nat) :
    (∀ n, StateRel (state wired a n) (state wiredSpec a n)) ∧
      ∀ n, output wired a n = output wiredSpec a n :=
  transport wired wiredSpec Eq StateRel Eq wired_initial wired_step a a (fun _ => rfl)

theorem wired_run (xs : List Nat) (w : WiredState) (s : Nat × Nat) (h : StateRel w s) :
    (run wired.mealy w xs).1 = (run wiredSpec.mealy s xs).1 ∧
      StateRel (run wired.mealy w xs).2 (run wiredSpec.mealy s xs).2 := by
  have hr := run_related wired.mealy wiredSpec.mealy Eq StateRel Eq wired_step
    (List.forall₂_same.mpr (fun _ _ => rfl) : List.Forall₂ Eq xs xs) h
  exact ⟨(by simpa only [List.forall₂_eq_eq_eq] using hr.1),hr.2⟩

/-- Batch adaptation changes the observed input only; each actual batch is a tick. -/
def batches {B S : Type} (f : Initialized Nat B S) : Initialized (List Nat) B S where
  initial := f.initial
  step := fun (batch,s) => f.step (batch.sum,s)

theorem batches_run {B S : Type} (f : Initialized Nat B S) (s : S) (xs : List (List Nat)) :
    run (batches f).mealy s xs = run f.mealy s (xs.map List.sum) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,run]
    rw [ih]
    rfl

theorem consume_joint (xs : List (Option (List Nat))) :
    Feedback.consume (batches jointMachine) jointMachine.initial xs =
      run jointSpec.mealy jointSpec.initial ((Feedback.completed xs).map List.sum) := by
  rw [Feedback.agreement,batches_run,joint_correct]

theorem consume_wired (xs : List (Option (List Nat))) :
    let result := Feedback.consume (batches wired) wired.initial xs
    let expected := run wiredSpec.mealy wiredSpec.initial ((Feedback.completed xs).map List.sum)
    result.1 = expected.1 ∧ StateRel result.2 expected.2 := by
  simp only [Feedback.agreement,batches_run]
  exact wired_run _ _ _ wired_initial

/-- A delayed body emits the old state and only then installs its input. -/
def delayBody : Term NatPrim [.base,.base] (.prod .base .base) :=
  .pair (.var (.there .here)) (.var .here)
def delayCode := ReactiveCompiler.compile K (lit 42) delayBody
def delayed : Initialized Nat Nat Nat := ReactiveCompiler.realize K sound.denote delayCode

theorem delayed_step (x s : Nat) : delayed.step (x,s) = (s,x) :=
  ReactiveCompiler.step_sound K sound (lit 42) delayBody x s

theorem delayed_initial : delayed.initial = 42 :=
  ReactiveCompiler.initial_sound K sound (lit 42) delayBody

end FRPSpec.Reactive
