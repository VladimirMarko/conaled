import Applications.FRP.RegionalPendingPlan

/-! Native service executions and copied-value lifetimes. These are logical
allocations of the actual finite client, not host heap measurements. -/
namespace FRPSpec.Regional.Pending
open Applications.Circuits

/-- Two optional residual records, including presence tags. -/
def retainedCells : Cut → Nat | .checked => 24 | _ => 22

def internalArena : Cut → Nat
  | .fused => jointBody.arena
  | .split => Indefinite.delay.body.arena + Circuit.not.arena + Circuit.xor.arena
  | .checked => 4 + Indefinite.delay.body.arena + Circuit.not.arena + Circuit.xor.arena

/-- Old/new encoded stores coexist with decoded and updated 22-cell stores.
Eight cells retain primitive results and changed request fields; sixteen cells
retain wrapper control and observations, four retain the internal deliveries. -/
def serviceCapacity (cut : Cut) : Nat :=
  192 + 16 + 4 + 2 * retainedCells cut + 44 + max (Rich.arena Rich.code) (internalArena cut) + 8

/-- Concrete native calls made by this client. No closure or graph language. -/
inductive ServiceCall where
  | quiet
  | producer (input : Bool)
  | delay (input old : Bool)
  | negate (input : Bool)
  | join (d n : Bool)
  | whole (input old : Bool)
  | protocol (command : PendingMigration.Command)

inductive ServiceValue where
  | quiet
  | scalar (value : Bool)
  | pair (value : Bool × Bool)
  | protocol (out : PendingMigration.Outcome)

def serviceValue (s : Active) : ServiceCall → ServiceValue
  | .quiet => .quiet
  | .producer x => .scalar (produce x)
  | .delay x b => .pair (Indefinite.delay.machine.step (x,b))
  | .negate x => .scalar (Circuit.not.execute x)
  | .join d n => .scalar (Circuit.xor.execute (d,n))
  | .whole x b => .pair (wholeResult s.cut x b)
  | .protocol c => .protocol (PendingMigration.step s.protocol c)

def serviceAllocations (s : Active) : ServiceCall → List Nat
  | .quiet => []
  | .producer x => Rich.allocations Rich.code ((),Sum.inl x)
  | .delay _ _ => Indefinite.delay.body.allocations
  | .negate _ => Circuit.not.allocations
  | .join _ _ => Circuit.xor.allocations
  | .whole _ _ => match s.cut with
    | .fused => jointBody.allocations
    | .split => Indefinite.delay.body.allocations ++ Circuit.not.allocations ++ Circuit.xor.allocations
    | .checked => 4 :: (Indefinite.delay.body.allocations ++ Circuit.not.allocations ++ Circuit.xor.allocations)
  | .protocol c => [PendingMigration.temporarySlots s.protocol c]

/-- Every evaluator constructor carries the actual code, arguments, result and
allocation derivation. Whole split execution retains all three arenas until
return; checked execution additionally retains its encode/decode copies. -/
inductive NativeServiceRuns (s : Active) : ServiceCall → ServiceValue → List Nat → Prop where
  | quiet : NativeServiceRuns s .quiet .quiet []
  | producer (x y : Bool) (trace : List Nat)
      (run : Rich.Allocates Rich.code ((),Sum.inl x) y trace) :
      NativeServiceRuns s (.producer x) (.scalar y) trace
  | delay (x b : Bool) (y : Bool × Bool)
      (run : Circuit.Executes Indefinite.delay.body (x,b) y Indefinite.delay.body.work Indefinite.delay.body.arena) :
      NativeServiceRuns s (.delay x b) (.pair y) Indefinite.delay.body.allocations
  | negate (x y : Bool)
      (run : Circuit.Executes Circuit.not x y Circuit.not.work Circuit.not.arena) :
      NativeServiceRuns s (.negate x) (.scalar y) Circuit.not.allocations
  | join (d n y : Bool)
      (run : Circuit.Executes Circuit.xor (d,n) y Circuit.xor.work Circuit.xor.arena) :
      NativeServiceRuns s (.join d n) (.scalar y) Circuit.xor.allocations
  | fused (x b : Bool) (y : Bool × Bool) (cut : s.cut = .fused)
      (run : Circuit.Executes jointBody (x,b) y jointBody.work jointBody.arena) :
      NativeServiceRuns s (.whole x b) (.pair y) jointBody.allocations
  | split (x b : Bool) (d : Bool × Bool) (n y : Bool) (cut : s.cut = .split)
      (dr : Circuit.Executes Indefinite.delay.body (x,b) d Indefinite.delay.body.work Indefinite.delay.body.arena)
      (nr : Circuit.Executes Circuit.not x n Circuit.not.work Circuit.not.arena)
      (jr : Circuit.Executes Circuit.xor (d.1,n) y Circuit.xor.work Circuit.xor.arena) :
      NativeServiceRuns s (.whole x b) (.pair (y,d.2))
        (Indefinite.delay.body.allocations ++ Circuit.not.allocations ++ Circuit.xor.allocations)
  | checked (x b : Bool) (d : Bool × Bool) (n y : Bool) (cut : s.cut = .checked)
      (dr : Circuit.Executes Indefinite.delay.body (decode (encode x),b) d Indefinite.delay.body.work Indefinite.delay.body.arena)
      (nr : Circuit.Executes Circuit.not (decode (encode x)) n Circuit.not.work Circuit.not.arena)
      (jr : Circuit.Executes Circuit.xor (d.1,n) y Circuit.xor.work Circuit.xor.arena) :
      NativeServiceRuns s (.whole x b) (.pair (y,d.2))
        (4 :: (Indefinite.delay.body.allocations ++ Circuit.not.allocations ++ Circuit.xor.allocations))
  | protocol (c : PendingMigration.Command) :
      NativeServiceRuns s (.protocol c) (.protocol (PendingMigration.step s.protocol c))
        [PendingMigration.temporarySlots s.protocol c]

theorem native_service_runs (s : Active) (c : ServiceCall) :
    NativeServiceRuns s c (serviceValue s c) (serviceAllocations s c) := by
  cases c with
  | quiet => exact .quiet
  | producer x => exact .producer x _ _ (Rich.allocates Rich.code Rich.code_analyzable _)
  | delay x b => exact .delay x b _ (Circuit.executes _ _)
  | negate x => exact .negate x _ (Circuit.executes _ _)
  | join d n => exact .join d n _ (Circuit.executes _ _)
  | protocol c => exact .protocol c
  | whole x b =>
    cases h : s.cut with
    | fused => simpa [serviceValue,serviceAllocations,wholeResult,h,Indefinite.Program.machine] using
        NativeServiceRuns.fused (s := s) x b _ h (Circuit.executes _ _)
    | split => simpa [serviceValue,serviceAllocations,wholeResult,h,Indefinite.Program.machine] using
        NativeServiceRuns.split (s := s) x b _ _ _ h (Circuit.executes _ _) (Circuit.executes _ _) (Circuit.executes _ _)
    | checked => simpa [serviceValue,serviceAllocations,wholeResult,h,Indefinite.Program.machine] using
        NativeServiceRuns.checked (s := s) x b _ _ _ h (Circuit.executes _ _) (Circuit.executes _ _) (Circuit.executes _ _)

/-- Arena occupancy at every entered allocation prefix, not just endpoints. -/
def serviceTrace (s : Active) (allocations : List Nat) : List Nat :=
  let old := PendingMigration.stateSlots s.protocol + 16 + 4 + retainedCells s.cut
  [old,old+22] ++
    (occupancies allocations).map (fun arena => old + 22 + arena + 8) ++
    [old+22+22+retainedCells s.cut+allocations.sum+8]

/-- The inherited queue/request peak may coexist with all wrapper copies. -/
def ServiceCertified (cut : Cut) (capacity : Nat) : Prop :=
  ∀ (s : Active), s.cut = cut → PendingMigration.Bounded s.protocol →
    ∀ c live, live ∈ serviceTrace s (serviceAllocations s c) → live ≤ capacity

theorem service_allocations_bound (s : Active) (c : ServiceCall)
    (hs : PendingMigration.Bounded s.protocol) :
    (serviceAllocations s c).sum ≤ 54 + max (Rich.arena Rich.code) (internalArena s.cut) := by
  have left := Nat.le_max_left (Rich.arena Rich.code) (internalArena s.cut)
  have right := Nat.le_max_right (Rich.arena Rich.code) (internalArena s.cut)
  cases c with
  | quiet => simp [serviceAllocations]
  | producer x =>
    have bound := Rich.allocations_le Rich.code ((),Sum.inl x)
    change (Rich.allocations Rich.code ((),Sum.inl x)).sum ≤ _
    omega
  | delay x b =>
    have bound : Indefinite.delay.body.arena ≤ internalArena s.cut := by cases s.cut <;> decide
    simp only [serviceAllocations,Circuit.allocations_sum]
    omega
  | negate x =>
    have bound : Circuit.not.arena ≤ internalArena s.cut := by cases s.cut <;> decide
    simp only [serviceAllocations,Circuit.allocations_sum]
    omega
  | join d n =>
    have bound : Circuit.xor.arena ≤ internalArena s.cut := by cases s.cut <;> decide
    simp only [serviceAllocations,Circuit.allocations_sum]
    omega
  | whole x b =>
    have exactSum : (serviceAllocations s (.whole x b)).sum = internalArena s.cut := by
      cases h : s.cut <;> simp [serviceAllocations,internalArena,h,Circuit.allocations_sum,Nat.add_assoc]
    rw [exactSum]
    omega
  | protocol c =>
    have bound := PendingMigration.temporary_slots_bound s.protocol c hs
    simp only [serviceAllocations,List.sum_cons,List.sum_nil,Nat.add_zero]
    omega

theorem service_trace_bound (s : Active) (c : ServiceCall)
    (hs : PendingMigration.Bounded s.protocol) :
    ∀ live ∈ serviceTrace s (serviceAllocations s c), live ≤ serviceCapacity s.cut := by
  have retained := PendingMigration.state_slots_bound s.protocol hs
  have bound := service_allocations_bound s c hs
  intro live mem
  simp only [serviceTrace,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with ((rfl | rfl) | mem) | rfl
  · unfold serviceCapacity; omega
  · unfold serviceCapacity; omega
  · obtain ⟨arena,ha,rfl⟩ := List.mem_map.mp mem
    obtain ⟨n,_,rfl⟩ := List.mem_map.mp ha
    have prefixBound := take_sum_le (serviceAllocations s c) n
    unfold serviceCapacity
    omega
  · unfold serviceCapacity; omega

theorem service_certified (cut : Cut) (capacity : Nat) (bound : serviceCapacity cut ≤ capacity) :
    ServiceCertified cut capacity := by
  intro s hc hs c live mem
  have h := service_trace_bound s c hs live mem
  rw [hc] at h
  exact h.trans bound

end FRPSpec.Regional.Pending
