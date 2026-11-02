import Applications.Durability.Storage
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Filter

/-!
# Mutable memory for captured suspensions

The memory component of Okasaki's thesis Appendix A (pp. 133–135) stores
ordinary values and expression/environment thunks in one address space.
`Bounded` gives finite memory separately from the raw operations. It constrains
occupied addresses, not addresses occurring inside values or environments;
recursive environments may therefore contain cycles.

Only fresh allocation preserves every occupied cell. Replacement and SRec have
their own footprint laws and do not claim immutable `Durability.Extends`.
This module supplies memory operations, not an evaluator or a once-only cache
policy. In particular, successive successful forcing frames may overwrite the
same address with different values.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions

inductive Cell (Code Env Value : Type) where
  | value (result : Value)
  | thunk (code : Code) (capturedEnv : Env)

structure State (Code Env Value : Type) where
  memory : Durability.Heap (Cell Code Env Value)
  next : Nat
  exceptionNames : Finset Nat

variable {Code Env Value : Type}

/-- A finite frontier, with no restriction on references inside a stored cell. -/
def Bounded (s : State Code Env Value) : Prop :=
  ∀ address, s.next ≤ address → s.memory address = none

def empty : State Code Env Value := ⟨fun _ => none, 0, ∅⟩

theorem bounded_empty : Bounded (empty : State Code Env Value) := fun _ _ => rfl

theorem Bounded.fresh {s : State Code Env Value} (h : Bounded s) :
    s.memory s.next = none := h _ (Nat.le_refl _)

theorem Bounded.occupied_lt {s : State Code Env Value} (h : Bounded s)
    {address : Nat} {cell : Cell Code Env Value} (lookup : s.memory address = some cell) :
    address < s.next := by
  by_contra outside
  have absent := h address (Nat.le_of_not_lt outside)
  rw [lookup] at absent
  cases absent

/-- The represented finite domain; under `Bounded` it includes every occupied
address, as `mem_domain` proves. No equality on code, environments or values is
needed to test whether a cell is occupied. -/
def domain (s : State Code Env Value) : Finset Nat :=
  (Finset.range s.next).filter fun address => (s.memory address).isSome

theorem mem_domain {s : State Code Env Value} (h : Bounded s) (address : Nat) :
    address ∈ domain s ↔ ∃ cell, s.memory address = some cell := by
  cases lookup : s.memory address with
  | none => simp [domain, lookup]
  | some cell => simp [domain, lookup, h.occupied_lt lookup]

/-- A total point update. Source writes to existing cells supply the separate
occupied-address premise when preserving validity and memory domain. -/
def replace (s : State Code Env Value) (address : Nat) (cell : Cell Code Env Value) :
    State Code Env Value :=
  { s with memory := Durability.put s.memory address cell }

@[simp] theorem replace_lookup (s : State Code Env Value) (address : Nat)
    (cell : Cell Code Env Value) :
    (replace s address cell).memory address = some cell := by
  simp [replace, Durability.put]

theorem replace_other (s : State Code Env Value) (address : Nat)
    (cell : Cell Code Env Value) {other : Nat} (different : other ≠ address) :
    (replace s address cell).memory other = s.memory other := by
  simp [replace, Durability.put, different]

@[simp] theorem replace_next (s : State Code Env Value) (address : Nat)
    (cell : Cell Code Env Value) : (replace s address cell).next = s.next := rfl

@[simp] theorem replace_exceptionNames (s : State Code Env Value) (address : Nat)
    (cell : Cell Code Env Value) :
    (replace s address cell).exceptionNames = s.exceptionNames := rfl

theorem replace_bounded {s : State Code Env Value} (h : Bounded s) {address : Nat}
    (inside : address < s.next) (cell : Cell Code Env Value) :
    Bounded (replace s address cell) := by
  intro other outside
  have different : other ≠ address := by
    change s.next ≤ other at outside
    omega
  exact (replace_other s address cell different).trans (h other outside)

theorem replace_bounded_of_occupied {s : State Code Env Value} (h : Bounded s)
    {address : Nat} {old : Cell Code Env Value} (lookup : s.memory address = some old)
    (cell : Cell Code Env Value) : Bounded (replace s address cell) :=
  replace_bounded h (h.occupied_lt lookup) cell

theorem replace_domain {s : State Code Env Value} (h : Bounded s) {address : Nat}
    {old : Cell Code Env Value} (lookup : s.memory address = some old)
    (cell : Cell Code Env Value) : domain (replace s address cell) = domain s := by
  apply Finset.ext
  intro other
  rw [mem_domain (replace_bounded_of_occupied h lookup cell), mem_domain h]
  by_cases same : other = address
  · subst other
    simp [lookup]
  · rw [replace_other s address cell same]

theorem replace_overwrite (s : State Code Env Value) (address : Nat)
    (earlier later : Cell Code Env Value) :
    replace (replace s address earlier) address later = replace s address later := by
  have memoryEq : Durability.put (Durability.put s.memory address earlier) address later =
      Durability.put s.memory address later := by
    funext other
    by_cases same : other = address <;> simp [Durability.put, same]
  exact congrArg (fun memory => (⟨memory, s.next, s.exceptionNames⟩ : State Code Env Value)) memoryEq

def memoize (s : State Code Env Value) (address : Nat) (value : Value) :
    State Code Env Value := replace s address (.value value)

@[simp] theorem memoize_lookup (s : State Code Env Value) (address : Nat) (value : Value) :
    (memoize s address value).memory address = some (.value value) :=
  replace_lookup s address (.value value)

theorem memoize_other (s : State Code Env Value) (address : Nat) (value : Value)
    {other : Nat} (different : other ≠ address) :
    (memoize s address value).memory other = s.memory other :=
  replace_other s address (.value value) different

@[simp] theorem memoize_next (s : State Code Env Value) (address : Nat) (value : Value) :
    (memoize s address value).next = s.next := rfl

@[simp] theorem memoize_exceptionNames (s : State Code Env Value) (address : Nat)
    (value : Value) : (memoize s address value).exceptionNames = s.exceptionNames := rfl

theorem memoize_bounded {s : State Code Env Value} (h : Bounded s) {address : Nat}
    {old : Cell Code Env Value} (lookup : s.memory address = some old) (value : Value) :
    Bounded (memoize s address value) := replace_bounded_of_occupied h lookup (.value value)

theorem memoize_domain {s : State Code Env Value} (h : Bounded s) {address : Nat}
    {old : Cell Code Env Value} (lookup : s.memory address = some old) (value : Value) :
    domain (memoize s address value) = domain s := replace_domain h lookup (.value value)

/-- A later successful write wins, including after a reentrant successful
write. This is an update law, not a claim that arbitrary source bodies finish. -/
theorem memoize_overwrite (s : State Code Env Value) (address : Nat) (earlier later : Value) :
    memoize (memoize s address earlier) address later = memoize s address later :=
  replace_overwrite s address (.value earlier) (.value later)

/-- Fresh-choice allocation, specified without a state frontier or a chosen
allocation algorithm. It is the memory component of the source creation rule. -/
structure FreshAllocation (before : Durability.Heap (Cell Code Env Value))
    (cell : Cell Code Env Value) (address : Nat)
    (after : Durability.Heap (Cell Code Env Value)) : Prop where
  fresh : before address = none
  installed : after address = some cell
  others : ∀ other, other ≠ address → after other = before other

theorem FreshAllocation.put {memory : Durability.Heap (Cell Code Env Value)}
    {address : Nat} (fresh : memory address = none) (cell : Cell Code Env Value) :
    FreshAllocation memory cell address (Durability.put memory address cell) where
  fresh := fresh
  installed := by simp [Durability.put]
  others other different := by simp [Durability.put, different]

/-- The deterministic realization chooses the current frontier. -/
def allocate (s : State Code Env Value) (cell : Cell Code Env Value) :
    State Code Env Value × Nat :=
  ({ memory := Durability.put s.memory s.next cell,
     next := s.next + 1, exceptionNames := s.exceptionNames }, s.next)

@[simp] theorem allocate_address (s : State Code Env Value) (cell : Cell Code Env Value) :
    (allocate s cell).2 = s.next := rfl

@[simp] theorem allocate_next (s : State Code Env Value) (cell : Cell Code Env Value) :
    (allocate s cell).1.next = s.next + 1 := rfl

@[simp] theorem allocate_exceptionNames (s : State Code Env Value)
    (cell : Cell Code Env Value) :
    (allocate s cell).1.exceptionNames = s.exceptionNames := rfl

@[simp] theorem allocate_lookup (s : State Code Env Value) (cell : Cell Code Env Value) :
    (allocate s cell).1.memory (allocate s cell).2 = some cell := by
  simp [allocate, Durability.put]

theorem allocate_other (s : State Code Env Value) (cell : Cell Code Env Value)
    {other : Nat} (different : other ≠ s.next) :
    (allocate s cell).1.memory other = s.memory other := by
  simp [allocate, Durability.put, different]

theorem allocate_bounded {s : State Code Env Value} (h : Bounded s)
    (cell : Cell Code Env Value) : Bounded (allocate s cell).1 := by
  intro address outside
  change s.next + 1 ≤ address at outside
  exact (allocate_other s cell (by omega)).trans (h address (by omega))

theorem allocate_realizes {s : State Code Env Value} (h : Bounded s)
    (cell : Cell Code Env Value) :
    FreshAllocation s.memory cell (allocate s cell).2 (allocate s cell).1.memory :=
  FreshAllocation.put h.fresh cell

/-- Immutable extension is appropriate for this fresh step only. -/
theorem allocate_extends {s : State Code Env Value} (h : Bounded s)
    (cell : Cell Code Env Value) : Durability.Extends s.memory (allocate s cell).1.memory :=
  Durability.extends_put s.memory s.next cell h.fresh

theorem allocate_retains {s : State Code Env Value} (h : Bounded s)
    {address : Nat} {old : Cell Code Env Value} (lookup : s.memory address = some old)
    (cell : Cell Code Env Value) : (allocate s cell).1.memory address = some old :=
  allocate_extends h cell address old lookup

theorem allocate_distinct (s : State Code Env Value) (first second : Cell Code Env Value) :
    (allocate (allocate s first).1 second).2 ≠ (allocate s first).2 := by
  simp

/-- Creation stores code and its creation environment; it has no body evaluator. -/
def delay (s : State Code Env Value) (code : Code) (capturedEnv : Env) :
    State Code Env Value × Nat := allocate s (.thunk code capturedEnv)

@[simp] theorem delay_address (s : State Code Env Value) (code : Code) (capturedEnv : Env) :
    (delay s code capturedEnv).2 = s.next := rfl

@[simp] theorem delay_next (s : State Code Env Value) (code : Code) (capturedEnv : Env) :
    (delay s code capturedEnv).1.next = s.next + 1 := rfl

@[simp] theorem delay_exceptionNames (s : State Code Env Value) (code : Code)
    (capturedEnv : Env) : (delay s code capturedEnv).1.exceptionNames = s.exceptionNames := rfl

theorem delay_captures (s : State Code Env Value) (code : Code) (capturedEnv : Env) :
    (delay s code capturedEnv).1.memory (delay s code capturedEnv).2 =
      some (.thunk code capturedEnv) := allocate_lookup s (.thunk code capturedEnv)

theorem delay_bounded {s : State Code Env Value} (h : Bounded s)
    (code : Code) (capturedEnv : Env) : Bounded (delay s code capturedEnv).1 :=
  allocate_bounded h (.thunk code capturedEnv)

theorem delay_realizes {s : State Code Env Value} (h : Bounded s)
    (code : Code) (capturedEnv : Env) :
    FreshAllocation s.memory (.thunk code capturedEnv)
      (delay s code capturedEnv).2 (delay s code capturedEnv).1.memory :=
  allocate_realizes h (.thunk code capturedEnv)

def Cell.extendEnv (extend : Env → Env) : Cell Code Env Value → Cell Code Env Value
  | .value result => .value result
  | .thunk code capturedEnv => .thunk code (extend capturedEnv)

/-- SRec's total memory action. Only target thunks have their environments
extended. Ordinary values, including values at target addresses, remain intact. -/
def srec (s : State Code Env Value) (targets : Finset Nat) (extend : Env → Env) :
    State Code Env Value :=
  { s with memory := fun address =>
      if address ∈ targets then (s.memory address).map (Cell.extendEnv extend)
      else s.memory address }

@[simp] theorem srec_next (s : State Code Env Value) (targets : Finset Nat)
    (extend : Env → Env) : (srec s targets extend).next = s.next := rfl

@[simp] theorem srec_exceptionNames (s : State Code Env Value) (targets : Finset Nat)
    (extend : Env → Env) : (srec s targets extend).exceptionNames = s.exceptionNames := rfl

theorem srec_other (s : State Code Env Value) (targets : Finset Nat) (extend : Env → Env)
    {address : Nat} (outside : address ∉ targets) :
    (srec s targets extend).memory address = s.memory address := by
  simp [srec, outside]

theorem srec_thunk {s : State Code Env Value} {targets : Finset Nat} (extend : Env → Env)
    {address : Nat} (inside : address ∈ targets) {code : Code} {capturedEnv : Env}
    (lookup : s.memory address = some (.thunk code capturedEnv)) :
    (srec s targets extend).memory address = some (.thunk code (extend capturedEnv)) := by
  simp [srec, inside, lookup, Cell.extendEnv]

theorem srec_value {s : State Code Env Value} (targets : Finset Nat) (extend : Env → Env)
    {address : Nat} {value : Value} (lookup : s.memory address = some (.value value)) :
    (srec s targets extend).memory address = some (.value value) := by
  by_cases inside : address ∈ targets <;> simp [srec, inside, lookup, Cell.extendEnv]

theorem srec_absent {s : State Code Env Value} (targets : Finset Nat) (extend : Env → Env)
    {address : Nat} (absent : s.memory address = none) :
    (srec s targets extend).memory address = none := by
  by_cases inside : address ∈ targets <;> simp [srec, inside, absent]

theorem srec_isSome (s : State Code Env Value) (targets : Finset Nat) (extend : Env → Env)
    (address : Nat) : ((srec s targets extend).memory address).isSome =
      (s.memory address).isSome := by
  by_cases inside : address ∈ targets
  · cases lookup : s.memory address <;> simp [srec, inside, lookup]
  · simp [srec, inside]

theorem srec_domain (s : State Code Env Value) (targets : Finset Nat) (extend : Env → Env) :
    domain (srec s targets extend) = domain s := by
  apply Finset.ext
  intro address
  simp only [domain, Finset.mem_filter, srec_next, srec_isSome]

theorem srec_bounded {s : State Code Env Value} (h : Bounded s) (targets : Finset Nat)
    (extend : Env → Env) : Bounded (srec s targets extend) := by
  intro address outside
  exact srec_absent targets extend (h address outside)

/-- The source recursive-binding situation supplies unforced thunks at its
address targets. This is separate from the total SRec operation's definition. -/
def RecursiveTargets (s : State Code Env Value) (targets : Finset Nat) : Prop :=
  ∀ address ∈ targets, ∃ code capturedEnv,
    s.memory address = some (.thunk code capturedEnv)

theorem RecursiveTargets.updated {s : State Code Env Value} {targets : Finset Nat}
    (h : RecursiveTargets s targets) (extend : Env → Env) {address : Nat}
    (inside : address ∈ targets) :
    ∃ code capturedEnv, s.memory address = some (.thunk code capturedEnv) ∧
      (srec s targets extend).memory address = some (.thunk code (extend capturedEnv)) := by
  obtain ⟨code, capturedEnv, lookup⟩ := h address inside
  exact ⟨code, capturedEnv, lookup, srec_thunk extend inside lookup⟩

theorem RecursiveTargets.srec {s : State Code Env Value} {targets : Finset Nat}
    (h : RecursiveTargets s targets) (extend : Env → Env) :
    RecursiveTargets (srec s targets extend) targets := by
  intro address inside
  obtain ⟨code, capturedEnv, _, updated⟩ := h.updated extend inside
  exact ⟨code, extend capturedEnv, updated⟩

end Suspensions
