import Applications.Suspensions.Decomposition

/-!
# Body faults and caller faults are distinct

The first body allocates a reference and then faults; an appended source
handler cannot undo the allocation or catch the fault. The second body returns
an integer normally, but its caller attempts to read that integer as an address.
The all-outcome decomposition recovers the normal body despite the final fault.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionDecomposition
open Suspensions Suspensions.Core Suspensions.Core.Machine

def parameters : Parameters Unit where
  primitive := fun _ _ => .stuck .primitive
  matchException := 0
  bindException := 1

def allocatingFault : Expr Unit :=
  .bind .wildcard (.reference (.atom (.integer 5))) (.read (.atom (.integer 0)))

def afterAllocation : Memory Unit :=
  (Suspensions.allocate Suspensions.empty (.value (.atom (.integer 5)))).1

def handler : List (Frame Unit) :=
  [.handler [] [(.wildcard, .atom (.integer 7))]]

theorem body_fault :
    Progress.Evaluates (step parameters) (start Suspensions.empty [] allocatingFault)
      ⟨afterAllocation, .stuck .expectedAddress⟩ 10 :=
  Progress.search_sound (fuel := 16) (by rfl)

theorem handler_retains_fault_and_allocation :
    Progress.Evaluates (step parameters)
      (appendFrames (start Suspensions.empty [] allocatingFault) handler)
      ⟨afterAllocation, .stuck .expectedAddress⟩ 10 ∧
      afterAllocation.memory 0 = some (.value (.atom (.integer 5))) :=
  ⟨evaluates_stuck_append body_fault rfl handler, rfl⟩

def literal : Expr Unit := .atom (.integer 7)

theorem literal_returns :
    Progress.Evaluates (step parameters) (start Suspensions.empty [] literal)
      ⟨Suspensions.empty, .value (.atom (.integer 7))⟩ 2 :=
  .next rfl (.done rfl)

theorem caller_fault :
    Progress.Evaluates (step parameters)
      (appendFrames (start Suspensions.empty [] literal) [.read])
      ⟨Suspensions.empty, .stuck .expectedAddress⟩ 2 :=
  .next rfl (.done rfl)

/-- A final fault need not be an isolated-body fault. Decomposition recovers
the actual two-step normal body and the one-step failing caller. -/
theorem caller_fault_recovers_normal_body :
    ∃ n m,
      Progress.Evaluates (step parameters) (start Suspensions.empty [] literal)
        ⟨Suspensions.empty, .value (.atom (.integer 7))⟩ n ∧
      Progress.Evaluates (step parameters)
        ⟨Suspensions.empty, .value (.atom (.integer 7)), [.read]⟩
        ⟨Suspensions.empty, .stuck .expectedAddress⟩ m ∧
      n = 2 ∧ m = 1 := by
  rcases evaluates_split_all caller_fault with ⟨body, _⟩ |
    ⟨answer, control, n, m, body, boundary, residual, count⟩
  · have impossible := congrArg Answer.result (body.unique literal_returns).1
    cases impossible
  · have same := body.unique literal_returns
    have answerEq : answer = ⟨Suspensions.empty, .value (.atom (.integer 7))⟩ := same.1
    have countEq : n = 2 := same.2
    subst answer
    have controlEq : control = .value (.atom (.integer 7)) := Option.some.inj boundary.symm
    subst control
    refine ⟨n, m, body, residual, countEq, ?_⟩
    omega

end Examples.SuspensionDecomposition
