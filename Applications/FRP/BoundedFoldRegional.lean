import Applications.FRP.BoundedFoldResources

/-! A local fold-to-circuit composition. The boundary owns a Boolean slot, a
synchronization frame and a retained adapter bit. It never enqueues ticks. -/
namespace FRPSpec.BoundedFold
open Applications.Circuits Progress Progress.Feedback

namespace Regional

def consumer : Circuit .base .base := .gate (.not 0)

def machine (capacity : Nat) : Initialized (Batch capacity) Bool (Bool × Bool) where
  initial := (false,false)
  step p :=
    let next := execute p.2.1 p.1.val
    let copied := p.2.1
    (consumer.execute copied,(next,copied))

/-- Adapter state remembers the most recently transferred bit. -/
theorem step_correct (xs : Batch capacity) (s adapter : Bool) :
    (machine capacity).step (xs,(s,adapter)) = (!s,(parity s xs.val,s)) := by
  simp [machine, execute_correct,consumer,Circuit.execute,Gate.meaning]

/-- Independent composition meaning, including retained adapter observation. -/
def native (capacity : Nat) : Initialized (Batch capacity) Bool (Bool × Bool) :=
  ⟨fun (xs,s,_) => (!s,(parity s xs.val,s)),(false,false)⟩

theorem machine_correct (capacity : Nat) : machine capacity = native capacity := by
  unfold machine native
  congr 1

theorem run_correct (xs : List (Batch capacity)) (s : Bool × Bool) :
    run (machine capacity).mealy s xs = run (native capacity).mealy s xs := by
  rw [machine_correct]

def storage (capacity : Nat) := max (BoundedFold.storage capacity + 3) (consumer.arena + 5)

def consumerTrace : List Nat :=
  (List.range (consumer.allocations.length+1)).map
    (fun k => 4 + (consumer.allocations.take k).sum) ++ [consumer.arena + 5, 2]

/-- Three reserved boundary cells stay live while the fold executes. Once the
fold releases its batch, next state and those cells remain through the consumer.
The output copy coexists with its arena before acceptance/reclamation. -/
inductive Executes : List Bool → Bool × Bool → Bool × (Bool × Bool) → List Nat → Prop where
  | compose {xs s adapter next trace y}
      (left : BoundedFold.Executes xs.length xs s next (work xs.length) trace)
      (right : Circuit.Executes consumer s y consumer.work consumer.arena) :
      Executes xs (s,adapter) (y,(next,s)) (trace.map (· + 3) ++ consumerTrace)

theorem executes (xs : Batch capacity) (s : Bool × Bool) :
    Executes xs.val s ((machine capacity).step (xs,s))
      ((liveTrace xs.val.length s.1 xs.val).map (· + 3) ++ consumerTrace) :=
  .compose (BoundedFold.executes _ _ _ (Nat.le_refl _)) (consumer.executes _)

theorem trace_bound (xs : Batch capacity) (s : Bool × Bool) (v : Nat)
    (hv : v ∈ (liveTrace xs.val.length s.1 xs.val).map (· + 3) ++ consumerTrace) :
    v ≤ storage capacity := by
  simp only [List.mem_append,List.mem_map] at hv
  rcases hv with ⟨k,hk,rfl⟩ | hc
  · exact (Nat.add_le_add_right (BoundedFold.trace_bound xs.property _ _ k hk) 3).trans
      (Nat.le_max_left _ _)
  · simp only [consumerTrace,List.mem_append,List.mem_map,List.mem_cons,List.not_mem_nil, or_false] at hc
    have hm : consumer.arena + 5 ≤ storage capacity := Nat.le_max_right _ _
    rcases hc with ⟨k,_,rfl⟩ | rfl | rfl
    · have hp := consumer.arena_prefix k; omega
    · exact hm
    · omega

/-- The boundary adds four logical operations (reserve/synchronize, transfer,
adapter update and acceptance) as well as the consumer dispatches. -/
def duration (env : Environment) (input : Stream (Batch capacity)) (n : Nat) :=
  env.inputWait n + env.schedulerWait n + work (input n).val.length +
    consumer.work + 4 + env.sinkWait n + 1

def starts (env : Environment) (input : Stream (Batch capacity)) : Nat → Nat
  | 0 => 0
  | n+1 => starts env input n + duration env input n

inductive Round (env : Environment) (n : Nat) (xs : Batch capacity) :
    Nat → Bool × Bool → Bool × (Bool × Bool) → Nat → Prop where
  | service {s result trace start} (evaluation : Executes xs.val s result trace) :
      Round env n xs start s result
        (start + (env.inputWait n + env.schedulerWait n + work xs.val.length +
          consumer.work + 4 + env.sinkWait n + 1))

theorem scheduled (env : Environment) (input : Stream (Batch capacity)) (n : Nat) :
    Round env n (input n) (starts env input n) (state (machine capacity) input n)
      (output (machine capacity) input n,state (machine capacity) input (n+1))
      (starts env input (n+1)) := .service (executes _ _)

/-- Local finite evaluation plus finite environmental waits supplies service
for the composed executor, including its boundary. -/
theorem productive (env : Environment) (input : Stream (Batch capacity)) (deadline : Nat) :
    ∃ n, deadline < starts env input (n+1) ∧
      Round env n (input n) (starts env input n) (state (machine capacity) input n)
        (output (machine capacity) input n,state (machine capacity) input (n+1))
        (starts env input (n+1)) := by
  have lower : ∀ n, n ≤ starts env input n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih => simp only [starts,duration]; omega
  exact ⟨deadline,by have := lower (deadline+1); omega,scheduled env input deadline⟩

/-- Regional bounds alone miss the live boundary. This concrete execution
actually visits a checkpoint exceeding the fold's independent bound. -/
theorem boundary_separator :
    consumer.arena ≤ BoundedFold.storage 1 ∧
    ∃ v ∈ (liveTrace 1 false [true]).map (· + 3) ++ consumerTrace,
      BoundedFold.storage 1 < v := by decide

end Regional
end FRPSpec.BoundedFold
