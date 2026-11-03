import Applications.Resources.Persistent.History
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Set.Image
import Mathlib.Tactic.Common

/-!
# Debit allocation, discharge and realization on persistent histories

The three source laws remain distinct. Allocation labels are sets; discharge
and realization labels are multisets whose membership forgets multiplicity.
The finite aggregate theorem derives its support inclusion from actual local
discharge witnesses and a history-closed scope. Its cost is abstract debit
accounting, not a theorem about arbitrary suspension-machine body work.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.Persistent
universe u q v w
variable {V : Type u} {D : Type v} {E : Type w}

/-- I: different operation occurrences allocate disjoint debit identities. -/
def Fresh (s : V → Set D) : Prop :=
  ∀ ⦃u v : V⦄, u ≠ v → Disjoint (s u) (s v)

/-- II: discharge refers to an allocation in the operation's logical history. -/
def Allocated [Quiver.{q} V] (s : V → Set D) (a : V → Multiset D) : Prop :=
  ∀ v d, d ∈ a v → ∃ u, u ∈ history v ∧ d ∈ s u

/-- III: realization refers to a discharge in the operation's logical history.
This is support membership, not an inequality of multiset multiplicities. -/
def Paid [Quiver.{q} V] (a r : V → Multiset D) : Prop :=
  ∀ v d, d ∈ r v → ∃ u, u ∈ history v ∧ d ∈ a u

/-- A convenient proposition bundle; the individual laws can be used separately. -/
structure Discipline [Quiver.{q} V] (s : V → Set D) (a r : V → Multiset D) : Prop where
  fresh : Fresh s
  allocated : Allocated s a
  paid : Paid a r

variable {s : V → Set D} {a r : V → Multiset D}

/-- Discharge provenance and paid realization compose along logical history. -/
theorem realized_origin [Quiver.{q} V] (allocated : Allocated s a) (paid : Paid a r)
    {v : V} {d : D} (realized : d ∈ r v) :
    ∃ u, u ∈ history v ∧ d ∈ s u := by
  obtain ⟨w, hw, hd⟩ := paid v d realized
  obtain ⟨u, hu, allocatedDebit⟩ := allocated w d hd
  exact ⟨u, history_trans hu hw, allocatedDebit⟩

/-- Freshness identifies the origin of an allocated debit without a finite scope. -/
theorem allocation_origin_unique (fresh : Fresh s) {u v : V} {d : D}
    (hu : d ∈ s u) (hv : d ∈ s v) : u = v := by
  by_contra different
  exact Set.disjoint_left.mp (fresh different) hu hv

theorem realized_origin_unique [Quiver.{q} V] (fresh : Fresh s) (allocated : Allocated s a)
    (paid : Paid a r) {v : V} {d : D} (realized : d ∈ r v) :
    ∃! u, u ∈ history v ∧ d ∈ s u := by
  obtain ⟨u, hu, hd⟩ := realized_origin allocated paid realized
  refine ⟨u, ⟨hu, hd⟩, ?_⟩
  intro w hw
  exact allocation_origin_unique fresh hw.2 hd

/-- A local witness condition for an explicitly accounted finite scope. -/
def PaidWithin (scope : Finset V) (a r : V → Multiset D) : Prop :=
  ∀ v ∈ scope, ∀ d ∈ r v, ∃ u ∈ scope, d ∈ a u

theorem paidWithin_of_closed [Quiver.{q} V] {scope : Finset V} (closed : HistoryClosed scope)
    (paid : Paid a r) : PaidWithin scope a r := by
  intro v hv d hd
  obtain ⟨u, hu, discharged⟩ := paid v d hd
  exact ⟨u, closed hv hu, discharged⟩

/-- For an open scope, the supporting discharge is still in the realizing
operation's history. A witness outside the scope must name a boundary debit.
The boundary records discharge credit, not a set of already cached work. -/
def PaidWithBoundary [Quiver.{q} V] (scope : Finset V) (boundary : Finset D)
    (a r : V → Multiset D) : Prop :=
  ∀ v ∈ scope, ∀ d ∈ r v,
    ∃ u, u ∈ history v ∧ d ∈ a u ∧ (u ∈ scope ∨ d ∈ boundary)

theorem paidWithBoundary_of_closed [Quiver.{q} V] {scope : Finset V} (boundary : Finset D)
    (closed : HistoryClosed scope) (paid : Paid a r) :
    PaidWithBoundary scope boundary a r := by
  intro v hv d hd
  obtain ⟨u, hu, discharged⟩ := paid v d hd
  exact ⟨u, hu, discharged, Or.inl (closed hv hu)⟩

/-- Union of supports, intentionally discarding repeated debit occurrences. -/
def supportUnion [DecidableEq D] (scope : Finset V)
    (labels : V → Multiset D) : Finset D :=
  scope.biUnion fun v => (labels v).toFinset

/-- Discharge cost intentionally retains every multiset occurrence. -/
def dischargeCost (scope : Finset V) (labels : V → Multiset D) : Nat :=
  scope.sum fun v => (labels v).card

section FiniteSupport
variable [DecidableEq D] {scope : Finset V}

@[simp] theorem mem_supportUnion {labels : V → Multiset D} {d : D} :
    d ∈ supportUnion scope labels ↔ ∃ v ∈ scope, d ∈ labels v := by
  simp only [supportUnion, Finset.mem_biUnion, Multiset.mem_toFinset]

theorem supportUnion_mono {left right : Finset V} (included : left ⊆ right)
    (labels : V → Multiset D) : supportUnion left labels ⊆ supportUnion right labels := by
  intro d hd
  obtain ⟨v, hv, member⟩ := mem_supportUnion.mp hd
  exact mem_supportUnion.mpr ⟨v, included hv, member⟩

theorem supportUnion_card_le (scope : Finset V) (labels : V → Multiset D) :
    (supportUnion scope labels).card ≤ dischargeCost scope labels := by
  calc
    (supportUnion scope labels).card ≤ scope.sum (fun v => (labels v).toFinset.card) :=
      Finset.card_biUnion_le
    _ ≤ dischargeCost scope labels :=
      Finset.sum_le_sum fun v _ => (labels v).toFinset_card_le

theorem realized_support_subset_of_within (paid : PaidWithin scope a r) :
    supportUnion scope r ⊆ supportUnion scope a := by
  intro d hd
  obtain ⟨v, hv, realized⟩ := mem_supportUnion.mp hd
  obtain ⟨u, hu, discharged⟩ := paid v hv d realized
  exact mem_supportUnion.mpr ⟨u, hu, discharged⟩

/-- The source-local law supplies the global inclusion on a closed scope. -/
theorem realized_support_subset [Quiver.{q} V] (closed : HistoryClosed scope) (paid : Paid a r) :
    supportUnion scope r ⊆ supportUnion scope a :=
  realized_support_subset_of_within (paidWithin_of_closed closed paid)

theorem realized_card_le_of_within (paid : PaidWithin scope a r) :
    (supportUnion scope r).card ≤ dischargeCost scope a :=
  (Finset.card_le_card (realized_support_subset_of_within paid)).trans
    (supportUnion_card_le scope a)

/-- Repeated realizations count once, whereas repeated discharges may all pay.
No freshness or allocation law is needed for this numerical consequence. -/
theorem realized_card_le [Quiver.{q} V] (closed : HistoryClosed scope) (paid : Paid a r) :
    (supportUnion scope r).card ≤ dischargeCost scope a :=
  realized_card_le_of_within (paidWithin_of_closed closed paid)

theorem realized_support_subset_boundary [Quiver.{q} V] {boundary : Finset D}
    (paid : PaidWithBoundary scope boundary a r) :
    supportUnion scope r ⊆ boundary ∪ supportUnion scope a := by
  intro d hd
  obtain ⟨v, hv, realized⟩ := mem_supportUnion.mp hd
  obtain ⟨u, _, discharged, accounted⟩ := paid v hv d realized
  rcases accounted with inside | boundaryMember
  · exact Finset.mem_union.mpr (Or.inr (mem_supportUnion.mpr ⟨u, inside, discharged⟩))
  · exact Finset.mem_union.mpr (Or.inl boundaryMember)

theorem realized_card_le_boundary [Quiver.{q} V] {boundary : Finset D}
    (paid : PaidWithBoundary scope boundary a r) :
    (supportUnion scope r).card ≤ boundary.card + dischargeCost scope a := by
  calc
    (supportUnion scope r).card ≤ (boundary ∪ supportUnion scope a).card :=
      Finset.card_le_card (realized_support_subset_boundary paid)
    _ ≤ boundary.card + (supportUnion scope a).card := Finset.card_union_le _ _
    _ ≤ boundary.card + dischargeCost scope a :=
      Nat.add_le_add_left (supportUnion_card_le scope a) boundary.card

/-- Finite allocation labels specialize the unrestricted allocation sets. -/
def allocationUnion (scope : Finset V) (allocated : V → Finset D) : Finset D :=
  scope.biUnion allocated

@[simp] theorem mem_allocationUnion {allocated : V → Finset D} {d : D} :
    d ∈ allocationUnion scope allocated ↔ ∃ v ∈ scope, d ∈ allocated v := by
  exact Finset.mem_biUnion

theorem allocationUnion_card {allocated : V → Finset D}
    (fresh : Fresh fun v => (allocated v : Set D)) :
    (allocationUnion scope allocated).card = scope.sum (fun v => (allocated v).card) := by
  apply Finset.card_biUnion
  intro u _ v _ different
  exact Finset.disjoint_left.mpr fun _ hu hv => Set.disjoint_left.mp (fresh different) hu hv

theorem realized_support_subset_allocation [Quiver.{q} V] {allocated : V → Finset D}
    (closed : HistoryClosed scope)
    (provenance : Allocated (fun v => (allocated v : Set D)) a) (paid : Paid a r) :
    supportUnion scope r ⊆ allocationUnion scope allocated := by
  intro d hd
  obtain ⟨v, hv, realized⟩ := mem_supportUnion.mp hd
  obtain ⟨u, hu, created⟩ := realized_origin provenance paid realized
  exact mem_allocationUnion.mpr ⟨u, closed hv hu, created⟩

/-- Only allocated but unrealized work belongs to this complement. -/
def unrealizedDebits (scope : Finset V) (allocated : V → Finset D)
    (realized : V → Multiset D) : Finset D :=
  allocationUnion scope allocated \ supportUnion scope realized

theorem realized_disjoint_unrealized (scope : Finset V) (allocated : V → Finset D)
    (realized : V → Multiset D) :
    Disjoint (supportUnion scope realized) (unrealizedDebits scope allocated realized) := by
  exact Finset.disjoint_left.mpr fun _ hr hu => (Finset.mem_sdiff.mp hu).2 hr

theorem allocated_partition_union [Quiver.{q} V] {allocated : V → Finset D}
    (closed : HistoryClosed scope)
    (provenance : Allocated (fun v => (allocated v : Set D)) a) (paid : Paid a r) :
    supportUnion scope r ∪ unrealizedDebits scope allocated r = allocationUnion scope allocated :=
  Finset.union_sdiff_of_subset (realized_support_subset_allocation closed provenance paid)

theorem allocated_partition_card [Quiver.{q} V] {allocated : V → Finset D}
    (closed : HistoryClosed scope)
    (provenance : Allocated (fun v => (allocated v : Set D)) a) (paid : Paid a r) :
    (supportUnion scope r).card + (unrealizedDebits scope allocated r).card =
      (allocationUnion scope allocated).card := by
  calc
    (supportUnion scope r).card + (unrealizedDebits scope allocated r).card =
        (unrealizedDebits scope allocated r).card + (supportUnion scope r).card := Nat.add_comm _ _
    _ = (allocationUnion scope allocated).card :=
      Finset.card_sdiff_add_card_eq_card (realized_support_subset_allocation closed provenance paid)

theorem shared_partition [Quiver.{q} V] {allocated : V → Finset D}
    (closed : HistoryClosed scope) (fresh : Fresh fun v => (allocated v : Set D))
    (provenance : Allocated (fun v => (allocated v : Set D)) a) (paid : Paid a r) :
    (supportUnion scope r).card + (unrealizedDebits scope allocated r).card =
      scope.sum (fun v => (allocated v).card) :=
  (allocated_partition_card closed provenance paid).trans (allocationUnion_card fresh)

end FiniteSupport

/-! Debit renaming uses ordinary images and maps; no graph data changes. -/

theorem fresh_map (embedding : D ↪ E) (fresh : Fresh s) :
    Fresh fun v => embedding '' s v := by
  intro u v different
  exact Set.disjoint_image_of_injective embedding.injective (fresh different)

/-- Provenance transport itself does not need injectivity. -/
theorem allocated_map [Quiver.{q} V] (f : D → E) (allocated : Allocated s a) :
    Allocated (fun v => f '' s v) (fun v => (a v).map f) := by
  intro v e member
  obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp member
  obtain ⟨u, hu, created⟩ := allocated v d hd
  exact ⟨u, hu, d, created, rfl⟩

theorem paid_map [Quiver.{q} V] (f : D → E) (paid : Paid a r) :
    Paid (fun v => (a v).map f) (fun v => (r v).map f) := by
  intro v e member
  obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp member
  obtain ⟨u, hu, discharged⟩ := paid v d hd
  exact ⟨u, hu, Multiset.mem_map.mpr ⟨d, discharged, rfl⟩⟩

theorem Discipline.map [Quiver.{q} V] (law : Discipline s a r) (embedding : D ↪ E) :
    Discipline (fun v => embedding '' s v)
      (fun v => (a v).map embedding) (fun v => (r v).map embedding) :=
  ⟨fresh_map embedding law.fresh, allocated_map embedding law.allocated,
    paid_map embedding law.paid⟩

theorem paidWithBoundary_map [Quiver.{q} V] {scope : Finset V} {boundary : Finset D}
    (embedding : D ↪ E) (paid : PaidWithBoundary scope boundary a r) :
    PaidWithBoundary scope (boundary.map embedding)
      (fun v => (a v).map embedding) (fun v => (r v).map embedding) := by
  intro v hv e member
  obtain ⟨d, hd, rfl⟩ := Multiset.mem_map.mp member
  obtain ⟨u, hu, discharged, accounted⟩ := paid v hv d hd
  refine ⟨u, hu, Multiset.mem_map.mpr ⟨d, discharged, rfl⟩, ?_⟩
  rcases accounted with inside | boundaryMember
  · exact Or.inl inside
  · exact Or.inr (Finset.mem_map.mpr ⟨d, boundaryMember, rfl⟩)

theorem dischargeCost_map (f : D → E) (scope : Finset V) (labels : V → Multiset D) :
    dischargeCost scope (fun v => (labels v).map f) = dischargeCost scope labels := by
  simp only [dischargeCost, Multiset.card_map]

section RenamedSupport
variable [DecidableEq D] [DecidableEq E]

theorem supportUnion_map (embedding : D ↪ E) (scope : Finset V)
    (labels : V → Multiset D) :
    supportUnion scope (fun v => (labels v).map embedding) = (supportUnion scope labels).map embedding := by
  ext e
  constructor
  · intro member
    obtain ⟨v, hv, mappedMember⟩ := mem_supportUnion.mp member
    obtain ⟨d, originalMember, imageEq⟩ := Multiset.mem_map.mp mappedMember
    exact Finset.mem_map.mpr ⟨d, mem_supportUnion.mpr ⟨v, hv, originalMember⟩, imageEq⟩
  · intro member
    obtain ⟨d, supportMember, imageEq⟩ := Finset.mem_map.mp member
    obtain ⟨v, hv, originalMember⟩ := mem_supportUnion.mp supportMember
    exact mem_supportUnion.mpr ⟨v, hv, Multiset.mem_map.mpr ⟨d, originalMember, imageEq⟩⟩

theorem supportUnion_map_card (embedding : D ↪ E) (scope : Finset V)
    (labels : V → Multiset D) :
    (supportUnion scope (fun v => (labels v).map embedding)).card = (supportUnion scope labels).card := by
  rw [supportUnion_map, Finset.card_map]

theorem allocationUnion_map (embedding : D ↪ E) (scope : Finset V)
    (allocated : V → Finset D) :
    allocationUnion scope (fun v => (allocated v).map embedding) =
      (allocationUnion scope allocated).map embedding := by
  ext e
  constructor
  · intro member
    obtain ⟨v, hv, mappedMember⟩ := mem_allocationUnion.mp member
    obtain ⟨d, originalMember, imageEq⟩ := Finset.mem_map.mp mappedMember
    exact Finset.mem_map.mpr ⟨d, mem_allocationUnion.mpr ⟨v, hv, originalMember⟩, imageEq⟩
  · intro member
    obtain ⟨d, supportMember, imageEq⟩ := Finset.mem_map.mp member
    obtain ⟨v, hv, originalMember⟩ := mem_allocationUnion.mp supportMember
    exact mem_allocationUnion.mpr ⟨v, hv, Finset.mem_map.mpr ⟨d, originalMember, imageEq⟩⟩

theorem allocationUnion_map_card (embedding : D ↪ E) (scope : Finset V)
    (allocated : V → Finset D) :
    (allocationUnion scope (fun v => (allocated v).map embedding)).card =
      (allocationUnion scope allocated).card := by
  rw [allocationUnion_map, Finset.card_map]

theorem unrealizedDebits_map (embedding : D ↪ E) (scope : Finset V)
    (allocated : V → Finset D) (realized : V → Multiset D) :
    unrealizedDebits scope (fun v => (allocated v).map embedding)
      (fun v => (realized v).map embedding) = (unrealizedDebits scope allocated realized).map embedding := by
  simp only [unrealizedDebits, allocationUnion_map, supportUnion_map, Finset.map_sdiff]

theorem unrealizedDebits_map_card (embedding : D ↪ E) (scope : Finset V)
    (allocated : V → Finset D) (realized : V → Multiset D) :
    (unrealizedDebits scope (fun v => (allocated v).map embedding)
      (fun v => (realized v).map embedding)).card = (unrealizedDebits scope allocated realized).card := by
  rw [unrealizedDebits_map, Finset.card_map]

end RenamedSupport
end Resources.Persistent
