import Applications.Uncomputation.ClientSchedules
import Examples.Uncomputation

/-! The event-composition law recovers native schedule contracts and a client
whose first output is an input to useful work between two uses of a dependency. -/
namespace Uncomputation.Examples
open Schedule

example (retain high : Bool) (k : Nat) (v : Fin 6 → Bool) :
    execute Client.caller (Client.plan retain high k) (Client.input v) =
      some (Client.input (Client.output high k v), Client.caller) :=
  Client.correct retain high k v

/-- Native parallel schedules are another specialization of the same segment law. -/
theorem repeat_parallel (k : Nat) (v : Fin 6 → Bool) :
    execute caller8 ((List.replicate k parallelPlan).flatten) (pairInput v) =
      some (pairInput (pairOutput^[k] v), caller8) :=
  advance_repeat caller8 parallelPlan (fun v => (pairInput v, caller8)) pairOutput
    parallel_ownership k v

/-- Serial reuse has the same caller result under its own scratch embedding. -/
theorem repeat_serial (k : Nat) (v : Fin 6 → Bool) :
    execute caller7 ((List.replicate k serialPlan).flatten) (pairInputSerial v) =
      some (pairInputSerial (pairOutput^[k] v), caller7) :=
  advance_repeat caller7 serialPlan (fun v => (pairInputSerial v, caller7)) pairOutput
    serial_ownership k v

example : Client.costs (Client.plan true false 1) = (5,5,1,0) := Client.low_costs.1
example : Client.costs (Client.plan false false 1) = (7,7,1,0) := Client.low_costs.2
example : Client.costs (Client.plan true true 1) = (7,7,2,0) := Client.high_costs.1
example : Client.costs (Client.plan false true 1) = (9,9,1,0) := Client.high_costs.2

example (k : Nat) : work ((Client.plan false true k).flatMap Event.gates) = 6 + k * 3 :=
  (Client.work_depth false true k).1

/-- The specification depends on the first updated output, rather than a dummy
allocation in the gap. Both logical controls and the unused caller wire survive. -/
example : Client.output true 1 ![true,true,false,false,false,true] =
    ![true,true,true,true,true,true] := by decide

example : Client.costs (Client.plan true true 0) = (4,4,1,0) ∧
    Client.costs (Client.plan false true 0) = (6,6,1,0) := by decide

example : advance Client.caller (Client.gap true 6)
    (Client.boundary true (fun _ => false)) = none := Client.retained_wire_not_available

example {R : Type} [Fintype R] [DecidableEq R]
    (v : (Fin 6 → Bool) × R → ℂ) :
    coherent (Equiv.prodCongr (Client.perm false true 1) (Equiv.refl R))
      (embedState (fun p => (Client.input p.1,p.2)) v) =
    embedState (fun p => (Client.input p.1,p.2))
      (coherent (Equiv.prodCongr (Client.outputPerm true 1) (Equiv.refl R)) v) :=
  Client.coherent_reference false true 1 v

end Uncomputation.Examples
