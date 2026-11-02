import Applications.Suspensions.Relocation

/-!
# A reference effect survives private allocation

The direct body updates the old reference at zero to seven and returns a new
reference containing nine. Its new address is one. With a private delayed cell
at one, the transported execution returns address two instead; both observable
reference contents agree through the general execution relation.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionRelocation
open Suspensions Suspensions.Core Suspensions.Core.Machine
open Suspensions.Core.Renaming Suspensions.Core.Relocation

def parameters : Parameters Unit := ⟨fun _ _ => .stuck .primitive, 0, 1⟩

theorem primitives_equivariant (frontier : Nat) :
    Equivariant parameters (shift frontier) := fun _ _ => rfl

def integer (n : Int) : Value Unit := .atom (.integer n)

def initial : Memory Unit := (Suspensions.allocate Suspensions.empty (.value (integer 5))).1

def bindings : Env Unit := [(0, .address 0)]

def body : Expr Unit :=
  .bind .wildcard (.assign (.variable 0) (.atom (.integer 7)))
    (.reference (.atom (.integer 9)))

def withPrivate : Memory Unit := (Suspensions.delay initial body bindings).1

def directFinal : Memory Unit :=
  (Suspensions.allocate (Suspensions.memoize initial 0 (integer 7)) (.value (integer 9))).1

theorem direct_execution :
    Progress.Evaluates (step parameters) (start initial bindings body)
      ⟨directFinal, .value (.address 1)⟩ 13 :=
  Progress.search_sound (fuel := 32) (by rfl)

theorem related_initial :
    ConfigsRelated 1 (start initial bindings body) (start withPrivate bindings body) := by
  refine ⟨⟨⟨rfl, rfl, ?_⟩, by decide⟩, rfl, rfl⟩
  intro address
  by_cases old : address = 0
  · subst address
    rfl
  · have newer : 1 ≤ address := by omega
    rw [shift_new newer]
    have nonzero : address + 1 ≠ 0 := by omega
    have notPrivate : address + 1 ≠ 1 := by omega
    simp [withPrivate, initial, Suspensions.delay, Suspensions.allocate,
      Suspensions.empty, Durability.put, old, nonzero, notPrivate]

/-- The new execution is obtained from the public transport theorem. Its
result and both reference effects are then read from the resulting relation. -/
theorem relocated_execution :
    ∃ memory, Progress.Evaluates (step parameters) (start withPrivate bindings body)
      ⟨memory, .value (.address 2)⟩ 13 ∧
      memory.memory 0 = some (.value (integer 7)) ∧
      memory.memory 2 = some (.value (integer 9)) ∧ memory.next = 3 := by
  obtain ⟨answer, execution, related⟩ :=
    evaluates_forward (primitives_equivariant 1) direct_execution related_initial
  rcases answer with ⟨memory, outcome⟩
  have returned : outcome = .value (.address 2) := related.2
  subst outcome
  refine ⟨memory, execution, ?_, ?_, ?_⟩
  · have lookup := related.1.1.lookup 0
    exact lookup
  · have lookup := related.1.1.lookup 1
    exact lookup
  · exact related.1.1.frontier

theorem reflected_execution {answer : Answer Unit} {count : Nat}
    (execution : Progress.Evaluates (step parameters) (start withPrivate bindings body)
      answer count) : count = 13 := by
  obtain ⟨output, direct, _⟩ :=
    evaluates_backward (primitives_equivariant 1) execution related_initial
  exact (direct.unique direct_execution).2

end Examples.SuspensionRelocation
