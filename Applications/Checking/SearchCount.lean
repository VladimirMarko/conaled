import SquareKit.FiniteSearch

/-!
# Checked finite-search counts

A frontier certificate proposes one count for each ordered frontier occurrence.
Its declarative validity uses the lengths of residual answer lists; the checker
uses `FiniteSearch.count`. Every proposal is checked. The consumer returns an
answer only after acceptance and makes no assumption about its producer.

Verification still computes all residual counts. The refinement proofs do not
assert a speedup, a bound on kernel evaluation, or distinct-state cardinality.
-/

set_option autoImplicit false
set_option warningAsError true

namespace SearchCount

open FiniteSearch
universe u
variable {State : Type u}

def checkCount (next : State → List State) (depth : Nat) (state : State)
    (claimed : Nat) : Bool := count next depth state == claimed

theorem checkCount_iff (next : State → List State) (depth : Nat) (state : State)
    (claimed : Nat) :
    checkCount next depth state claimed = true ↔
      (enumerate next depth state).length = claimed := by
  simp only [checkCount, beq_iff_eq, count_eq_length]

structure Certificate where
  depth : Nat
  counts : List Nat
  deriving DecidableEq

def Certificate.value (certificate : Certificate) : Nat := certificate.counts.sum

/-- Intended meaning of all the proposed residual counts, with frontier order. -/
def Valid (next : State → List State) (total : Nat) (state : State)
    (certificate : Certificate) : Prop :=
  certificate.depth ≤ total ∧
    certificate.counts = (enumerate next certificate.depth state).map
      (fun child => (enumerate next (total - certificate.depth) child).length)

def verify (next : State → List State) (total : Nat) (state : State)
    (certificate : Certificate) : Bool :=
  decide (certificate.depth ≤ total) &&
    (certificate.counts ==
      (enumerate next certificate.depth state).map (count next (total - certificate.depth)))

/-- Acceptance checks validity rather than trusting a claimed sum. -/
theorem verify_iff (next : State → List State) (total : Nat) (state : State)
    (certificate : Certificate) :
    verify next total state certificate = true ↔ Valid next total state certificate := by
  simp only [verify, Valid, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  rw [show count next (total - certificate.depth) =
      (fun child => (enumerate next (total - certificate.depth) child).length) from
    funext (count_eq_length next (total - certificate.depth))]

theorem verify_sound (next : State → List State) (total : Nat) (state : State)
    (certificate : Certificate) (accepted : verify next total state certificate = true) :
    (enumerate next total state).length = certificate.value := by
  simp only [verify, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at accepted
  have split : certificate.depth + (total - certificate.depth) = total := by omega
  rw [← count_eq_length, ← split, count_partition, ← accepted.2]
  rfl

/-- A simple producer; soundness also applies to proposals from other producers. -/
def certificate (next : State → List State) (total depth : Nat) (state : State) : Certificate :=
  ⟨depth, (enumerate next depth state).map (count next (total - depth))⟩

theorem verify_certificate (next : State → List State) (total depth : Nat) (state : State)
    (bounded : depth ≤ total) :
    verify next total state (certificate next total depth state) = true := by
  simp [verify, certificate, bounded]

/-- Checked consumption preserves failure rather than releasing an unchecked sum. -/
def release (next : State → List State) (total : Nat) (state : State)
    (certificate : Certificate) : Option Nat :=
  if verify next total state certificate then some certificate.value else none

theorem release_eq_some_iff (next : State → List State) (total : Nat) (state : State)
    (certificate : Certificate) (value : Nat) :
    release next total state certificate = some value ↔
      Valid next total state certificate ∧ certificate.value = value := by
  unfold release
  cases checked : verify next total state certificate <;>
    simp [checked, ← verify_iff]

theorem release_sound (next : State → List State) (total : Nat) (state : State)
    (certificate : Certificate) (value : Nat)
    (accepted : release next total state certificate = some value) :
    (enumerate next total state).length = value := by
  obtain ⟨valid, rfl⟩ := (release_eq_some_iff next total state certificate value).mp accepted
  exact verify_sound next total state certificate ((verify_iff next total state certificate).mpr valid)

/-- Any producer can supply a residual backend: rejected proposals decline the query. -/
def checkedTail (next : State → List State) (produce : Nat → State → Certificate) : Tail State :=
  fun depth state => release next depth state (produce depth state)

/-- The backend contract is proved from checking; it assumes nothing about the producer. -/
theorem checkedTail_exact (next : State → List State) (produce : Nat → State → Certificate) :
    Exact next (checkedTail next produce) := by
  intro depth state value accepted
  have sound := release_sound next depth state (produce depth state) value accepted
  exact sound.symm.trans (count_eq_length next depth state).symm

end SearchCount
