import Compiler
import Applications.FRP.MigrationPair

/-! A local, acyclic regional language. Raw sum/case code and circuit code remain
separate executable representations. Parallel nodes use a left-then-right tick. -/
namespace FRPSpec.Regional
open Progress Progress.Feedback Applications.Circuits
namespace Rich
open CategoricalCompiler
inductive Prim : Ty → Ty → Type where
  | neg : Prim .base .base
  | conj : Prim (.prod .base .base) .base

def meaning : Prim a b → Val Bool a → Val Bool b
  | .neg, x => !x
  | .conj, x => x.1 && x.2
abbrev inputTy : Ty := .sum .base (.prod .base .base)
abbrev Input := Bool ⊕ (Bool × Bool)

def source : Term Prim [inputTy] .base :=
  .caseE (.var .here) (.var .here)
    (.prim .conj (.pair (.fst (.var .here)) (.prim .neg (.snd (.var .here)))))
def code := compile (rawTarget Prim) source
def execute (x : Input) : Bool := CategoricalCompiler.run meaning code ((),x)

def oracle : Input → Bool
  | .inl b => b
  | .inr (x,y) => x && !y

theorem correct (x : Input) : execute x = oracle x := by
  have h := compile_sound (rawTarget Prim) (rawSound meaning) source ((),x)
  change execute x = eval meaning source ((),x) at h
  rw [h]
  cases x <;> rfl

/-- A closure immediately applied can be removed before selecting a region. -/
def closureCode : Code Prim (.prod .unit inputTy) .base :=
  .comp .apply (.pair (.curry (.comp code .fst)) .terminal)
def loweredCode : Code Prim (.prod .unit inputTy) .base :=
  .comp (.comp code .fst) (.pair .ident .terminal)
theorem lowering_correct (x : Unit × Input) :
    CategoricalCompiler.run meaning closureCode x =
      CategoricalCompiler.run meaning loweredCode x :=
  closed_beta meaning (.comp code .fst) .terminal x

theorem lowered_correct (x : Input) :
    CategoricalCompiler.run meaning loweredCode ((),x) = oracle x := correct x
end Rich

abbrev Input := Rich.Input
abbrev Redundant := {p : Bool × Bool // MigrationPair.valid p}
def encode (b : Bool) : Redundant := ⟨MigrationPair.forward b, MigrationPair.forward_valid b⟩
def decode (p : Redundant) : Bool :=
  (MigrationPair.reverse p.val).getD false

theorem decode_correct (p : Redundant) : decode p = p.val.1 := by
  simp [decode, MigrationPair.reverse_valid p.val p.property]
theorem decode_encode (b : Bool) : decode (encode b) = b := decode_correct _

/-- Raw boundary inputs are checked before admitting the next circuit tick. -/
def checkBoundary (p : Bool × Bool) : Option Bool := MigrationPair.reverse p

def native : Initialized Input Bool Bool := ⟨fun (x,s) => (!s,Rich.oracle x), false⟩
def negateProgram := Indefinite.Program.pure Circuit.not

def fusedProgram := Indefinite.delay.seq negateProgram

/-- Only these leaves are available. There is no function-valued port, effect,
instantaneous cycle or global backend registration mechanism. -/
inductive Plan : Type → Type → Type 1 where
  | rich : Plan Input Bool
  | delay : Plan Bool Bool
  | negate : Plan Bool Bool
  | bareNegate : Plan Bool Bool
  | fused : Plan Bool Bool
  | direct : Plan Input Bool
  | encode : Plan Bool Redundant
  | decode : Plan Redundant Bool
  | side : Plan Bool Bool
  | duplicate : Plan Input (Input × Input)
  | seq : Plan A B → Plan B C → Plan A C
  | par : Plan A B → Plan C D → Plan (A × C) (B × D)

namespace Plan
def State : Plan A B → Type
  | .rich | .negate | .bareNegate | .encode | .decode | .side | .duplicate => PUnit
  | .delay | .direct => Bool
  | .fused => Bool × PUnit
  | .seq p q | .par p q => p.State × q.State

def machine : (p : Plan A B) → Initialized A B p.State
  | .rich => pure Rich.execute
  | .delay => Indefinite.delay.machine
  | .negate => negateProgram.machine
  | .bareNegate => pure Circuit.not.execute
  | .fused => fusedProgram.machine
  | .direct => native
  | .encode => pure Regional.encode
  | .decode => pure Regional.decode
  | .side => pure id
  | .duplicate => pure (fun x => (x,x))
  | .seq p q => Feedback.seq p.machine q.machine
  | .par p q => Feedback.par p.machine q.machine

/-- Independent leaf meanings; composition reuses initialized feedback laws. -/
def meaning : (p : Plan A B) → Initialized A B p.State
  | .rich => pure Rich.oracle
  | .delay => ⟨fun (x,s) => (s,x),false⟩
  | .negate | .bareNegate => pure Bool.not
  | .fused => Feedback.seq ⟨fun (x,s) => (s,x),false⟩ (pure Bool.not)
  | .direct => native
  | .encode => pure Regional.encode
  | .decode => pure (fun p => p.val.1)
  | .side => pure id
  | .duplicate => pure (fun x => (x,x))
  | .seq p q => Feedback.seq p.meaning q.meaning
  | .par p q => Feedback.par p.meaning q.meaning

theorem correct (p : Plan A B) : p.machine = p.meaning := by
  induction p with
  | rich => exact congrArg pure (funext Rich.correct)
  | decode => exact congrArg pure (funext decode_correct)
  | seq p q hp hq => simp only [machine, meaning, hp, hq]; rfl
  | par p q hp hq => simp only [machine, meaning, hp, hq]; rfl
  | _ => rfl

/-- Includes continuation state, not just the output prefix. -/
theorem finite_correct (p : Plan A B) (s : p.State) (xs : List A) :
    run p.machine.mealy s xs = run p.meaning.mealy s xs := by rw [p.correct]

theorem sequential (p : Plan A B) (q : Plan B C) (s : p.State) (t : q.State)
    (xs : List A) :
    run (p.seq q).machine.mealy (s,t) xs =
      let a := run p.machine.mealy s xs
      let b := run q.machine.mealy t a.1
      (b.1,(a.2,b.2)) := run_seq p.machine q.machine s t xs
end Plan

inductive Cut where
  | fused | split | checked
  deriving DecidableEq, Repr

/-- A finite supplied cut catalog, constructed structurally at compile time. -/
def compile : Cut → Plan Input Bool
  | .fused => .seq .rich .fused
  | .split => .seq .rich (.seq .delay .negate)
  | .checked => .seq (.seq (.seq .rich .encode) .decode) (.seq .delay .negate)

def logical : (c : Cut) → (compile c).State → Bool
  | .fused, s => s.2.1
  | .split, s => s.2.1
  | .checked, s => s.2.1

theorem initial_correct (c : Cut) : logical c (compile c).machine.initial = false := by
  cases c <;> rfl

theorem step_correct (c : Cut) (s : (compile c).State) (x : Input) :
    ((compile c).machine.step (x,s)).1 = !logical c s ∧
    logical c ((compile c).machine.step (x,s)).2 = Rich.oracle x := by
  cases c with
  | fused => exact ⟨rfl,Rich.correct x⟩
  | split => exact ⟨rfl,Rich.correct x⟩
  | checked =>
    change (!s.2.1) = (!s.2.1) ∧ decode (encode (Rich.execute x)) = Rich.oracle x
    exact ⟨rfl,(decode_encode _).trans (Rich.correct x)⟩

/-- Every suffix starts from the supplied live joint state. -/
theorem continuation (c : Cut) (s : (compile c).State) (xs : List Input) :
    (run (compile c).machine.mealy s xs).1 = (run native.mealy (logical c s) xs).1 ∧
    logical c (run (compile c).machine.mealy s xs).2 =
      (run native.mealy (logical c s) xs).2 := by
  have h := run_related (compile c).machine.mealy native.mealy Eq
    (fun t b => logical c t = b) Eq
    (by
      intro x y t b hxy htb
      subst y
      subst b
      exact step_correct c t x)
    (List.forall₂_same.mpr (fun _ _ => rfl) : List.Forall₂ Eq xs xs) (s := s) rfl
  exact ⟨by simpa only [List.forall₂_eq_eq_eq] using h.1,h.2⟩

def parallel (c : Cut) : Plan (Input × Bool) (Bool × Bool) := .par (compile c) .side

def fixtures : List Input := [.inl true,.inr (false,true),.inr (true,false),.inl false]

theorem fixture_outputs (c : Cut) :
    (run (compile c).machine.mealy (compile c).machine.initial fixtures).1 =
      [true,false,true,false] := by
  rw [(continuation c _ fixtures).1, initial_correct]
  rfl

theorem fixture_state (c : Cut) :
    logical c (run (compile c).machine.mealy (compile c).machine.initial fixtures).2 = false := by
  rw [(continuation c _ fixtures).2, initial_correct]
  rfl

example : checkBoundary (true,true) = none ∧ checkBoundary (false,false) = none := by decide
example : checkBoundary (true,false) = some true := by decide
example : Rich.oracle (.inr (true,false)) ≠ Rich.oracle (.inr (false,true)) := by decide
example : (run native.mealy false [.inl true,.inl false]).1 = [true,false] := rfl
example : (native.step (.inl true,false)).1 ≠ false := by decide

end FRPSpec.Regional
