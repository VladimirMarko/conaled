import Applications.FRP.IndefiniteIO
import Applications.FRP.MigrationPair

/-! Checked clients of the finite circuit service criterion. -/
namespace Examples.IndefiniteService
open FirstOrderCompiler Applications.Circuits Progress Progress.Feedback FRPSpec.Indefinite

/-- A single delay emits false first, then the previous Boolean. -/
example : run delay.machine.mealy delay.initial [true,false,true,true,false] =
    ([false,true,false,true,true],false) := rfl

/-- Two delays distinguish sequential state retention from pure composition. -/
example : run twice.machine.mealy twice.initial [true,false,true,true,false] =
    ([false,false,true,false,true],(false,true)) := rfl

example (input : Stream Bool) : output twice.machine input =
    output FRPSpec.FiniteDelay.machine (output FRPSpec.FiniteDelay.machine input) :=
  twice_output input

example (input : Stream Bool) (n k : Nat) :
    Program.retained (state delay.machine input n) + (delay.body.allocations.take k).sum ≤ 14 :=
  delay.uniform input n k

/-- Independent resource calculation for the single delay: three node visits,
13 arena cells/frames, and one Boolean retained outside that arena. -/
example : delay.body.work = 3 ∧ delay.body.arena = 13 := ⟨rfl,rfl⟩

example (input : Stream Bool) (n : Nat) :
    Circuit.Executes twice.body (input n,state twice.machine input n)
      (output twice.machine input n,state twice.machine input (n+1)) twice.body.work twice.body.arena :=
  twice.next input n

/-- Branches share no queue and retain two separate delay cells. -/
example (input : Stream (Bool × Bool)) :
    output (delay.par delay).machine input = fun n =>
      (output delay.machine (fun k => (input k).1) n,
       output delay.machine (fun k => (input k).2) n) := by
  rw [Program.par_machine]
  exact par_output _ _ _

/-- Pure bounded operations fit the same criterion without state cells. -/
example (input : Stream Bool) :
    output (Program.pure Circuit.not).machine input = fun n => !(input n) := by
  rw [Program.pure_machine]
  exact pure_output _ _

/-- Source terms enter the same resource criterion through the existing compiler. -/
def seed : Term Gate [] .base := .prim (.constant false) .unit
def body : Term Gate [.base,.base] (.prod .base .base) :=
  .pair (.var (.there .here)) (.var .here)
def compiledDelay := Program.compiled (ReactiveCompiler.compile Circuit.target seed body)

example : compiledDelay.machine = delay.machine := by
  rw [compiledDelay, Program.compiled_source]
  rfl

example (input : Stream Bool) (n k : Nat) :
    Program.retained (state compiledDelay.machine input n) +
      (compiledDelay.body.allocations.take k).sum ≤ 1 + compiledDelay.body.arena :=
  compiledDelay.uniform input n k

/-- Constant finite waits provide an inhabited scheduling premise; arbitrary
finite, non-uniform waits are also admitted by Program.productive. -/
def environment : Program.Environment := ⟨fun _ => 2,fun _ => 3,fun _ => 5⟩
example (input : Stream Bool) (deadline : Nat) :
    ∃ n, deadline < delay.starts environment (n+1) ∧
      Program.Round delay 2 3 5 (delay.starts environment n)
        (input n) (state delay.machine input n) (output delay.machine input n)
        (state delay.machine input (n+1)) (delay.starts environment (n+1)) :=
  delay.productive environment input deadline

/-- Another finite representation retains a redundant complement bit. -/
abbrev redundant := FRPSpec.MigrationPair.redundant
abbrev related := FRPSpec.MigrationPair.related

theorem related_step (x u : Bool) (v : Bool × Bool) (h : related u v) :
    (delay.machine.step (x,u)).1 = (redundant.machine.step (x,v)).1 ∧
      related (delay.machine.step (x,u)).2 (redundant.machine.step (x,v)).2 :=
  FRPSpec.MigrationPair.related_step x u v h

theorem redundant_output (input : Stream Bool) :
    ∀ n, output delay.machine input n = output redundant.machine input n :=
  (delay.transport redundant.machine Eq related Eq rfl
    (by intro x y u v h; subst y; exact related_step x u v)
    input input (fun _ => rfl)).2

/-- The representation-change bound uses #231 covered relational transport.
Operational work/temporary storage are separately provided by redundant.service. -/
example (input : Stream Bool) :
    ∀ n, Program.retained (state redundant.machine input n) ≤ 2 := by
  exact delay.transport_bound redundant.machine related rfl related_step
    Program.retained (fun n => 2*n) (fun _ _ h => Nat.mul_le_mul_left 2 h)
    (fun _ _ _ => Nat.le_refl _) input

/-- Fixed field count does not bound representation size. These counter and
history observations exceed every proposed uniform bound on some prefix. -/
example : ¬ ∃ bound : Nat, ∀ n : Nat, n.size ≤ bound := by
  rintro ⟨bound,h⟩
  have large := h (2^bound)
  rw [Nat.size_pow] at large
  omega

example : ¬ ∃ bound : Nat, ∀ n : Nat, (List.replicate n true).length ≤ bound := by
  simp only [List.length_replicate]
  rintro ⟨bound,h⟩
  have := h (bound+1)
  omega

end Examples.IndefiniteService
