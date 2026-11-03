import Applications.Resources.Persistent.Debits

/-!
# Persistent debit laws on parallel, forked and cyclic operation histories

These labels are independent finite calculations exercising the public source
laws and aggregate theorem. They interpret abstract debit work; they do not
identify arbitrary suspension-machine body work with a deduplicated support.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.PersistentDebits
open Resources.Persistent
universe u

private theorem fresh_at {N : Type u} [DecidableEq N] (origin : N) (debits : Set Nat) :
    Fresh (fun v => if v = origin then debits else ∅) := by
  intro u v different
  apply Set.disjoint_left.mpr
  intro d hu hv
  by_cases atOrigin : u = origin
  · have away : v ≠ origin := fun h => different (atOrigin.trans h.symm)
    simp only [ite_eq_right away, Set.mem_empty_iff_false] at hv
  · simp only [ite_eq_right atOrigin, Set.mem_empty_iff_false] at hu

namespace Parallel

inductive Node where
  | source
  | joined
  deriving DecidableEq

inductive Arrow : Node → Node → Type where
  | first : Arrow .source .joined
  | second : Arrow .source .joined

instance : Quiver Node where Hom := Arrow

def allocations (v : Node) : Set Nat := if v = .source then {7, 8} else ∅
def finiteAllocations (v : Node) : Finset Nat := if v = .source then {7, 8} else ∅

def discharges : Node → Multiset Nat
  | .source => 0
  | .joined => 7 ::ₘ 7 ::ₘ 0

def realizations : Node → Multiset Nat
  | .source => 0
  | .joined => 7 ::ₘ 7 ::ₘ 0

def scope : Finset Node := {.source, .joined}

theorem arrows_are_distinct : (Arrow.first : Node.source ⟶ Node.joined) ≠ Arrow.second := by
  intro equal
  cases equal

theorem closed : HistoryClosed scope := by
  intro _ _ u _
  cases u <;> simp [scope]

theorem fresh : Fresh allocations := fresh_at Node.source {7, 8}

theorem allocated : Allocated allocations discharges := by
  intro v d member
  cases v with
  | source => simp [discharges] at member
  | joined =>
      have equal : d = 7 := by simpa [discharges] using member
      subst d
      exact ⟨.source, history_of_edge Arrow.first, by simp [allocations]⟩

theorem paid : Paid discharges realizations := by
  intro v d member
  exact ⟨v, history_refl v, member⟩

theorem law : Discipline allocations discharges realizations := ⟨fresh, allocated, paid⟩

/-- Both argument occurrences remain present, while the realized debit is shared. -/
theorem multiplicity_and_support :
    (discharges .joined).card = 2 ∧ (realizations .joined).card = 2 ∧
      supportUnion scope realizations = {7} ∧ dischargeCost scope discharges = 2 := by
  decide

theorem bound : (supportUnion scope realizations).card ≤ dischargeCost scope discharges :=
  realized_card_le closed law.paid

theorem unique_origin : ∃! v, v ∈ history Node.joined ∧ 7 ∈ allocations v :=
  realized_origin_unique law.fresh law.allocated law.paid (by simp [realizations])

theorem finite_allocations_coe (v : Node) : (finiteAllocations v : Set Nat) = allocations v := by
  cases v <;> ext d <;> simp [finiteAllocations, allocations]

/-- Debit8 remains unrealized allocated work; it is not part of the actual support. -/
theorem allocated_partition :
    (supportUnion scope realizations).card + (unrealizedDebits scope finiteAllocations realizations).card = 2 := by
  have freshFinite : Fresh fun v => (finiteAllocations v : Set Nat) := by
    simpa only [finite_allocations_coe] using law.fresh
  have allocatedFinite : Allocated (fun v => (finiteAllocations v : Set Nat)) discharges := by
    simpa only [finite_allocations_coe] using law.allocated
  calc
    (supportUnion scope realizations).card + (unrealizedDebits scope finiteAllocations realizations).card =
        scope.sum (fun v => (finiteAllocations v).card) :=
      shared_partition closed freshFinite allocatedFinite law.paid
    _ = 2 := by decide

theorem unrealized_is_allocated : unrealizedDebits scope finiteAllocations realizations = {8} := by
  decide

/-- Injective debit renaming transports the source laws and both observations. -/
theorem renamed {E : Type u} [DecidableEq E] (embedding : Nat ↪ E) :
    Discipline (fun v => embedding '' allocations v)
      (fun v => (discharges v).map embedding) (fun v => (realizations v).map embedding) ∧
    (supportUnion scope (fun v => (realizations v).map embedding)).card = 1 ∧
    dischargeCost scope (fun v => (discharges v).map embedding) = 2 ∧
    (unrealizedDebits scope (fun v => (finiteAllocations v).map embedding)
      (fun v => (realizations v).map embedding)).card = 1 := by
  refine ⟨law.map embedding, ?_, ?_, ?_⟩
  · calc
      (supportUnion scope (fun v => (realizations v).map embedding)).card =
          (supportUnion scope realizations).card := supportUnion_map_card embedding scope realizations
      _ = 1 := by decide
  · calc
      dischargeCost scope (fun v => (discharges v).map embedding) =
          dischargeCost scope discharges := dischargeCost_map embedding scope discharges
      _ = 2 := by decide
  · calc
      (unrealizedDebits scope (fun v => (finiteAllocations v).map embedding)
          (fun v => (realizations v).map embedding)).card =
          (unrealizedDebits scope finiteAllocations realizations).card :=
        unrealizedDebits_map_card embedding scope finiteAllocations realizations
      _ = 1 := by decide

/-- Paid realization by itself does not supply an allocation origin. -/
theorem invented_debit :
    Paid discharges realizations ∧ ¬ Allocated (fun _ : Node => (∅ : Set Nat)) discharges := by
  refine ⟨paid, ?_⟩
  intro provenance
  obtain ⟨_, _, impossible⟩ := provenance .joined 7 (by simp [discharges])
  exact impossible

/-- Identifying independently allocated work violates the separate freshness law. -/
theorem duplicate_allocation : ¬ Fresh (fun _ : Node => ({7} : Set Nat)) := by
  intro fresh
  have equal : Node.source = Node.joined :=
    allocation_origin_unique (d := 7) fresh (by simp) (by simp)
  cases equal

end Parallel

namespace Fork

inductive Node where
  | origin
  | left
  | right
  deriving DecidableEq

inductive Arrow : Node → Node → Type where
  | toLeft : Arrow .origin .left
  | toRight : Arrow .origin .right

instance : Quiver Node where Hom := Arrow

def allocations (v : Node) : Set Nat := if v = .origin then {7} else ∅

def discharges : Node → Multiset Nat
  | .origin => 7 ::ₘ 0
  | .left | .right => 0

def realizations : Node → Multiset Nat
  | .origin => 0
  | .left | .right => 7 ::ₘ 0

def scope : Finset Node := {.origin, .left, .right}
def operations : List Node := [.origin, .left, .right]

theorem operations_nodup : operations.Nodup := by decide
theorem operations_toFinset : operations.toFinset = scope := by decide

theorem closed : HistoryClosed scope := by
  intro _ _ u _
  cases u <;> simp [scope]

theorem fresh : Fresh allocations := fresh_at Node.origin {7}

theorem allocated : Allocated allocations discharges := by
  intro v d member
  cases v with
  | origin =>
      have equal : d = 7 := by simpa [discharges] using member
      subst d
      exact ⟨.origin, history_refl Node.origin, by simp [allocations]⟩
  | left => simp [discharges] at member
  | right => simp [discharges] at member

theorem paid : Paid discharges realizations := by
  intro v d member
  cases v with
  | origin => simp [realizations] at member
  | left =>
      have equal : d = 7 := by simpa [realizations] using member
      subst d
      exact ⟨.origin, history_of_edge Arrow.toLeft, by simp [discharges]⟩
  | right =>
      have equal : d = 7 := by simpa [realizations] using member
      subst d
      exact ⟨.origin, history_of_edge Arrow.toRight, by simp [discharges]⟩

theorem law : Discipline allocations discharges realizations := ⟨fresh, allocated, paid⟩

/-- One prior payment supports both logical futures under the source law. -/
theorem bound : (supportUnion scope realizations).card ≤ dischargeCost scope discharges :=
  realized_card_le closed law.paid

theorem exact_costs :
    supportUnion scope realizations = {7} ∧
      dischargeCost scope discharges = 1 ∧ dischargeCost scope realizations = 2 := by
  decide

/-- Counting repeated realization work as call-by-name exceeds the available charge. -/
theorem repeated_realization_exceeds : dischargeCost scope discharges < dischargeCost scope realizations := by
  decide

theorem right_not_in_left_history : Node.right ∉ history Node.left := by
  intro reached
  have equal : Node.right = Node.left :=
    history_eq_of_no_outgoing (fun _ edge => by cases edge) reached
  cases equal

def partialAllocations (v : Node) : Set Nat := if v = .origin then {7, 8} else ∅

def partialDischarges : Node → Multiset Nat
  | .origin => 0
  | .left => 7 ::ₘ 0
  | .right => 8 ::ₘ 0

def partialRealizations : Node → Multiset Nat
  | .left => 7 ::ₘ 8 ::ₘ 0
  | .origin | .right => 0

theorem partial_fresh : Fresh partialAllocations := fresh_at Node.origin {7, 8}

theorem partial_allocated : Allocated partialAllocations partialDischarges := by
  intro v d member
  cases v with
  | origin => simp [partialDischarges] at member
  | left =>
      have equal : d = 7 := by simpa [partialDischarges] using member
      subst d
      exact ⟨.origin, history_of_edge Arrow.toLeft, by simp [partialAllocations]⟩
  | right =>
      have equal : d = 8 := by simpa [partialDischarges] using member
      subst d
      exact ⟨.origin, history_of_edge Arrow.toRight, by simp [partialAllocations]⟩

/-- All debits are paid somewhere globally, but a different branch cannot cooperate. -/
theorem partial_global_coverage :
    supportUnion scope partialRealizations ⊆ supportUnion scope partialDischarges := by
  decide

theorem partial_global_bound :
    (supportUnion scope partialRealizations).card ≤ dischargeCost scope partialDischarges :=
  (Finset.card_le_card partial_global_coverage).trans (supportUnion_card_le scope partialDischarges)

theorem partial_not_paid : ¬ Paid partialDischarges partialRealizations := by
  intro paid
  obtain ⟨v, reached, discharged⟩ := paid .left 8 (by simp [partialRealizations])
  cases v with
  | origin => simp [partialDischarges] at discharged
  | left => simp [partialDischarges] at discharged
  | right => exact right_not_in_left_history reached

end Fork

namespace Cycle

inductive Node where
  | first
  | second
  deriving DecidableEq

inductive Arrow : Node → Node → Type where
  | forward : Arrow .first .second
  | backward : Arrow .second .first

instance : Quiver Node where Hom := Arrow

def allocations (v : Node) : Set Nat := if v = .first then {7} else ∅

def discharges : Node → Multiset Nat
  | .first => 0
  | .second => 7 ::ₘ 0

def realizations : Node → Multiset Nat
  | .first => 7 ::ₘ 0
  | .second => 0

def scope : Finset Node := {.first, .second}
def openScope : Finset Node := {.first}
def boundary : Finset Nat := {7}

theorem closed : HistoryClosed scope := by
  intro _ _ u _
  cases u <;> simp [scope]

theorem fresh : Fresh allocations := fresh_at Node.first {7}

theorem allocated : Allocated allocations discharges := by
  intro v d member
  cases v with
  | first => simp [discharges] at member
  | second =>
      have equal : d = 7 := by simpa [discharges] using member
      subst d
      exact ⟨.first, history_of_edge Arrow.forward, by simp [allocations]⟩

theorem paid : Paid discharges realizations := by
  intro v d member
  cases v with
  | first =>
      have equal : d = 7 := by simpa [realizations] using member
      subst d
      exact ⟨.second, history_of_edge Arrow.backward, by simp [discharges]⟩
  | second => simp [realizations] at member

theorem law : Discipline allocations discharges realizations := ⟨fresh, allocated, paid⟩

theorem bound : (supportUnion scope realizations).card ≤ dischargeCost scope discharges :=
  realized_card_le closed law.paid

theorem exact_costs :
    (supportUnion scope realizations).card = 1 ∧ dischargeCost scope discharges = 1 ∧
      (supportUnion openScope realizations).card = 1 ∧ dischargeCost openScope discharges = 0 := by
  decide

theorem open_not_closed : ¬ HistoryClosed openScope := by
  intro closed
  have member : Node.second ∈ openScope :=
    closed (v := .first) (by simp [openScope]) (history_of_edge Arrow.backward)
  simp [openScope] at member

/-- The same complete source-valid labels do not establish an open-scope bound. -/
theorem open_scope_exceeds :
    dischargeCost openScope discharges < (supportUnion openScope realizations).card := by
  decide

theorem paid_with_boundary : PaidWithBoundary openScope boundary discharges realizations := by
  intro v member d realized
  cases v with
  | first =>
      have equal : d = 7 := by simpa [realizations] using realized
      subst d
      exact ⟨.second, history_of_edge Arrow.backward, by simp [discharges],
        Or.inr (by simp [boundary])⟩
  | second => simp [openScope] at member

/-- The external discharge witness supplies the missing boundary term. -/
theorem boundary_bound :
    (supportUnion openScope realizations).card ≤ boundary.card + dischargeCost openScope discharges :=
  realized_card_le_boundary paid_with_boundary

end Cycle
end Examples.PersistentDebits
