import Applications.Suspensions.CacheAccounting
import Examples.SuspensionPending

/-!
# Counting the actual first force and later cache hits

The existing literal suspension first emits body0, returns 7, writes cache0,
then delivers its successful match. There are five actual events and exactly
one cache write, independently of a larger absorbing observation budget.

The raw bound is applied with freshness proved from the actual states of this
run, rather than assumed for the example. Its cached result then supplies a
settled later force whose cache-write count is zero for every budget. No pure
source theorem or unrestricted single-write conclusion is used here.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionCacheAccounting
open Suspensions.Core Suspensions.Core.Machine Suspensions.Core.Observation
open Examples.SuspensionPending

private def cachedMemory : Memory Unit :=
  Suspensions.memoize memory 0 (.atom (.integer 7))

private def answer : Answer Unit := ⟨cachedMemory, .matched []⟩

/-- Independent expected event order: the successful write precedes the
wildcard match, and the final transition delivers its result. -/
theorem first_force_trace :
    observe parameters 5 firstForce =
      (.inl answer, FreeAddMonoid.ofList [.body 0, .core, .cacheWrite 0, .core, .core]) := rfl

theorem first_force_evaluates :
    Progress.Evaluates (step parameters) firstForce answer 5 :=
  completed_sound first_force_trace

private theorem first_bounded : ConfigBounded firstForce :=
  startPattern_bounded (Suspensions.delay_bounded Suspensions.bounded_empty body [])
    [] (.suspended .wildcard) (.address 0)

/-- The only body entry is the first step, whose pending stack is empty.
All budgets after actual completion are answers, so contribute no live case. -/
theorem first_force_fresh : FreshEntries parameters firstForce := by
  intro budget next observed address event
  by_cases before : budget < 5
  · have positions : budget = 0 ∨ budget = 1 ∨ budget = 2 ∨ budget = 3 ∨ budget = 4 := by omega
    rcases positions with rfl | rfl | rfl | rfl | rfl
    · cases observed
      exact List.not_mem_nil
    · cases observed
      cases event
    · cases observed
      cases event
    · cases observed
      cases event
    · cases observed
      cases event
  · have after : 5 ≤ budget := by omega
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le after
    have finished : Prefix.observe parameters 5 firstForce = .inl answer :=
      (observe_erases parameters 5 firstForce).symm.trans (congrArg Prod.fst first_force_trace)
    rw [Prefix.stays_finished parameters 5 extra firstForce answer finished] at observed
    cases observed

/-- Every address and every budget use the public conditional count theorem,
with all its raw hypotheses established for this actual force. -/
theorem first_force_at_most_one (address budget : Nat) :
    cacheWrites address (observe parameters budget firstForce).2 ≤ 1 :=
  cacheWrites_observe_le_one first_bounded List.nodup_nil first_force_fresh address budget

/-- The public stack-preservation result supplies distinctness at any actual
unfinished prefix; no direct enumeration of its later stack is needed here. -/
theorem first_force_pending_distinct (budget : Nat) (next : Config Unit)
    (observed : Prefix.observe parameters budget firstForce = .inr next) :
    (pendingAddresses next.stack).Nodup :=
  first_force_fresh.observe_pending_nodup List.nodup_nil observed

theorem completed_count_and_other_address :
    cacheWrites 0 (observe parameters 5 firstForce).2 = 1 ∧
    cacheWrites 1 (observe parameters 5 firstForce).2 = 0 := by
  rw [first_force_trace]
  exact ⟨rfl, rfl⟩

/-- The actual completion, rather than a presumed transition at every budget,
justifies retaining exactly one write after an arbitrary finished suffix. -/
theorem extra_budget_keeps_one (extra : Nat) :
    cacheWrites 0 (observe parameters (5 + extra) firstForce).2 = 1 := by
  have finished : Prefix.observe parameters 5 firstForce = .inl answer :=
    (observe_erases parameters 5 firstForce).symm.trans (congrArg Prod.fst first_force_trace)
  rw [cacheWrites_observe_after_finished finished extra 0]
  exact completed_count_and_other_address.1

/-- The count is a standard resource reweighting of the same ordered trace. -/
theorem first_force_reweighted :
    Resources.reweight (cacheWrites 0) (observe parameters 5 firstForce) = (.inl answer, 1) := by
  rw [first_force_trace]
  rfl

private def laterForce : Config Unit :=
  startPattern cachedMemory [] (.suspended .wildcard) (.address 0)

/-- The cached state is obtained from the actual first run. Its later force
hits, and settled-address preservation gives zero writes for every budget. -/
theorem later_hit_writes_zero (budget : Nat) :
    (transition parameters laterForce).2 = .hit 0 ∧
    cacheWrites 0 (observe parameters budget laterForce).2 = 0 := by
  have bounded : Suspensions.Bounded cachedMemory :=
    evaluates_bounded first_bounded first_force_evaluates
  have valid : ConfigBounded laterForce :=
    startPattern_bounded bounded [] (.suspended .wildcard) (.address 0)
  have settled : Settled 0 laterForce := ⟨⟨.atom (.integer 7), rfl⟩, List.not_mem_nil⟩
  exact ⟨rfl, cacheWrites_observe_settled valid settled budget⟩

end Examples.SuspensionCacheAccounting
