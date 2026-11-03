import Applications.Suspensions.BodyAccounting
import Applications.Resources.Persistent.Realization
import Mathlib.Data.List.Nodup

/-!
# Body-entry observations and shared debit identities

The existing ordered event trace determines both the ordered body addresses
and their finite support. The unchanged debit interpreter, with one shared
identity per body address and zero unshared charge, counts that support. It
counts body-entry occurrences exactly when the projected list has no repeats.

The conditional body-entry theorem establishes this nonrepetition for actual
observations. This selects body-entry events only; it neither prices all machine
transitions nor bounds work inside a body.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.Observation
open Machine
open Resources.Persistent

/-- Retain the physical address of a body-entry event, and no other event. -/
def bodyAddress : Event → Option Nat
  | .body address => some address
  | _ => none

/-- Body addresses in their actual occurrence order, retaining repetitions. -/
def bodyAddresses (events : FreeAddMonoid Event) : List Nat :=
  (FreeAddMonoid.toList events).filterMap bodyAddress

theorem bodyAddresses_add (first second : FreeAddMonoid Event) :
    bodyAddresses (first + second) = bodyAddresses first ++ bodyAddresses second := by
  simp only [bodyAddresses, FreeAddMonoid.toList_add, List.filterMap_append]

private theorem count_filterMap_bodyAddress (address : Nat) (events : List Event) :
    (events.filterMap bodyAddress).count address = events.count (.body address) := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      cases event <;> simp [bodyAddress, List.count_cons, ih, beq_iff_eq]

/-- Projecting to addresses preserves the existing actual count at each address. -/
theorem bodyAddresses_count (address : Nat) (events : FreeAddMonoid Event) :
    (bodyAddresses events).count address = bodyEntries address events :=
  count_filterMap_bodyAddress address (FreeAddMonoid.toList events)

/-- Nonrepetition is the ordinary list consequence of the per-address bounds. -/
theorem bodyAddresses_nodup_iff (events : FreeAddMonoid Event) :
    (bodyAddresses events).Nodup ↔ ∀ address, bodyEntries address events ≤ 1 := by
  simp only [List.nodup_iff_count_le_one, bodyAddresses_count]

/-- Occurrences and finite support agree only under the stated nonrepetition. -/
theorem bodyAddresses_length_eq_card {events : FreeAddMonoid Event}
    (unique : (bodyAddresses events).Nodup) :
    (bodyAddresses events).length = (bodyAddresses events).toFinset.card :=
  (List.toFinset_card_of_nodup unique).symm

/-- Count all body-entry occurrences, including repeated entries at one address. -/
def totalBodyEntries : FreeAddMonoid Event →+ Nat where
  toFun events := (bodyAddresses events).length
  map_zero' := rfl
  map_add' first second := by
    rw [bodyAddresses_add, List.length_append]

theorem totalBodyEntries_eq_length (events : FreeAddMonoid Event) :
    totalBodyEntries events = (bodyAddresses events).length := rfl

/-- This additive observation gives each body event weight one and every other
event weight zero. It is an event indicator, not a body-work cost model. -/
theorem totalBodyEntries_eq_lift :
    totalBodyEntries = FreeAddMonoid.lift
      (fun event => (bodyAddress event).toList.length) := by
  apply FreeAddMonoid.hom_eq
  intro event
  cases event <;> rfl

/-- A body event exposes precisely its physical address to the existing shared
debit interpreter. Equal code at different addresses is not identified. -/
def bodyDebits : Event → Finset Nat
  | .body address => {address}
  | _ => ∅

/-- The ordinary support interpreter forgets repetitions but no body identity. -/
theorem realizationSupport_bodyDebits (events : List Event) :
    realizationSupport bodyDebits events = (events.filterMap bodyAddress).toFinset := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      cases event <;> simp [realizationSupport, bodyDebits, bodyAddress, ih]

/-- For any event word, the existing debit interpreter charges the number of
distinct body addresses. No nonrepetition or source-execution premise is needed. -/
theorem body_realization_cost (events : FreeAddMonoid Event) :
    (Resources.run (realizeStep (fun _ => 0) bodyDebits)
      (FreeAddMonoid.toList events) ∅).2 = (bodyAddresses events).toFinset.card := by
  rw [realize_run_cost, realizationSupport_bodyDebits]
  simp [bodyAddresses]

/-- With nonrepetition, the interpreter charge is the actual entry observation. -/
theorem body_realization_cost_of_nodup {events : FreeAddMonoid Event}
    (unique : (bodyAddresses events).Nodup) :
    (Resources.run (realizeStep (fun _ => 0) bodyDebits)
      (FreeAddMonoid.toList events) ∅).2 = totalBodyEntries events := by
  rw [body_realization_cost, totalBodyEntries_eq_length]
  exact List.toFinset_card_of_nodup unique

/-- The per-address body bounds, rather than successful-write uniqueness,
justify replacing distinct support by actual occurrences. -/
theorem body_realization_cost_of_counts {events : FreeAddMonoid Event}
    (bounded : ∀ address, bodyEntries address events ≤ 1) :
    (Resources.run (realizeStep (fun _ => 0) bodyDebits)
      (FreeAddMonoid.toList events) ∅).2 = totalBodyEntries events :=
  body_realization_cost_of_nodup ((bodyAddresses_nodup_iff events).mpr bounded)

variable {Primitive : Type}

/-- The total body-entry count reweights the same measured machine workload. -/
theorem totalBodyEntries_workload_reweight (parameters : Parameters Primitive) (budget : Nat)
    (state : Answer Primitive ⊕ Config Primitive) :
    Resources.reweight totalBodyEntries (workload parameters budget state) =
      Resources.run (fun instruction state => Resources.reweight totalBodyEntries
        (measuredAdvance parameters instruction state)) (List.replicate budget ()) state := by
  rw [totalBodyEntries_eq_lift]
  exact workload_reweight parameters budget state _

/-- The raw body theorem applies to every observation budget, including an
unfinished prefix or unused budget after an answer. Initial Nodup is not assumed. -/
theorem bodyAddresses_observe_nodup {parameters : Parameters Primitive}
    {config : Config Primitive} (valid : ConfigBounded config)
    (fresh : FreshEntries parameters config)
    (noUnwind : ∀ address, NoMemoizeUnwind parameters config address) (budget : Nat) :
    (bodyAddresses (observe parameters budget config).2).Nodup := by
  apply (bodyAddresses_nodup_iff _).mpr
  intro address
  exact bodyEntries_observe_le_one valid fresh (noUnwind address) budget

/-- The unchanged debit interpreter agrees with the actual body-entry metric
under the raw structural and prefix conditions that ensure nonrepetition. -/
theorem body_realization_observe_cost {parameters : Parameters Primitive}
    {config : Config Primitive} (valid : ConfigBounded config)
    (fresh : FreshEntries parameters config)
    (noUnwind : ∀ address, NoMemoizeUnwind parameters config address) (budget : Nat) :
    (Resources.run (realizeStep (fun _ => 0) bodyDebits)
      (FreeAddMonoid.toList (observe parameters budget config).2) ∅).2 =
        totalBodyEntries (observe parameters budget config).2 :=
  body_realization_cost_of_nodup (bodyAddresses_observe_nodup valid fresh noUnwind budget)

end Suspensions.Core.Observation
