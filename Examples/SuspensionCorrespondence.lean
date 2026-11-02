import Applications.Suspensions.Correspondence

/-!
# A concrete execution also satisfies the independent source rules

The counter starts at zero. The thunk captures one, while the later caller
binds the same variable to ninety-nine. Forcing against literal zero increments
the counter, caches the captured one and fails. Forcing against literal one
then succeeds without another counter update. The source derivations below
come from the proved execution correspondence, not from assumed body effects.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionCorrespondence
open Suspensions Suspensions.Core Suspensions.Core.Machine
open Suspensions.Core.Correspondence

def parameters : Parameters Unit := ⟨fun _ _ => .stuck .primitive, 0, 1⟩

def intValue (n : Int) : Value Unit := .atom (.integer n)

def body : Expr Unit :=
  .bind .wildcard (.assign (.variable 2) (.atom (.integer 1))) (.variable 0)

def captured : Env Unit := [(0, intValue 1), (2, .address 0)]

def caller : Env Unit := [(0, intValue 99), (2, .address 0)]

def initial : Memory Unit :=
  (Suspensions.delay (Suspensions.allocate Suspensions.empty (.value (intValue 0))).1
    body captured).1

def finalMemory : Memory Unit :=
  Suspensions.memoize (Suspensions.memoize initial 0 (intValue 1)) 1 (intValue 1)

theorem failed_execution :
    matching parameters initial caller (.suspended (.atom (.integer 0)))
      (.address 1) (.ok none) finalMemory := by
  exact ⟨_, Progress.search_sound (fuel := 40) (by rfl)⟩

theorem failed_source_rule :
    Source.SuspensionMatch (evaluation parameters) (matching parameters)
      initial caller 1 (.atom (.integer 0)) (.ok none) finalMemory :=
  suspension_match_complete failed_execution

theorem cached_execution :
    matching parameters finalMemory caller (.suspended (.atom (.integer 1)))
      (.address 1) (.ok (some [])) finalMemory := by
  exact ⟨_, Progress.search_sound (fuel := 8) (by rfl)⟩

theorem cached_source_rule :
    Source.SuspensionMatch (evaluation parameters) (matching parameters)
      finalMemory caller 1 (.atom (.integer 1)) (.ok (some [])) finalMemory :=
  suspension_match_complete cached_execution

theorem retained_counter_and_cache :
    finalMemory.memory 0 = some (.value (intValue 1)) ∧
      finalMemory.memory 1 = some (.value (intValue 1)) ∧ finalMemory.next = 2 := by
  exact ⟨rfl, rfl, rfl⟩

/-- The first source derivation cannot quietly discard either the failed
match or its changed memory; determinism includes both observations. -/
theorem failed_source_unique {answer : Except (Value Unit) (Option (Env Unit))}
    {memory : Memory Unit}
    (source : Source.SuspensionMatch (evaluation parameters) (matching parameters)
      initial caller 1 (.atom (.integer 0)) answer memory) :
    answer = .ok none ∧ memory = finalMemory :=
  matching_deterministic (suspension_match_sound source) failed_execution

end Examples.SuspensionCorrespondence
