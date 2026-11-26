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

theorem cached_trace_has_no_body_or_write :
    Progress.Evaluates (tracedStep parameters)
      (startPattern finalMemory caller (.suspended (.atom (.integer 1))) (.address 1), [])
      (⟨finalMemory, .matched []⟩, [.hit 1, .core, .core]) 3 :=
  .next rfl (.next rfl (.done rfl))

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

def pair : Value Unit := .record [(0, .address 0), (1, .address 1)]

def pairPattern (counter : Int) (inner : Pattern) : Pattern :=
  .record [(0, .reference (.atom (.integer counter))), (1, inner)]

def ordered : List (Pattern × Expr Unit) :=
  [(pairPattern 1 .wildcard, .atom (.integer 10)),
   (pairPattern 0 (.suspended (.atom (.integer 0))), .atom (.integer 20)),
   (pairPattern 0 .wildcard, .atom (.integer 30)),
   (pairPattern 1 .wildcard, .atom (.integer 40))]

/-- The second pattern changes the counter before failing, so the third
pattern now fails too. Standalone ordered matching returns bare mismatch. -/
theorem first_three_execution :
    Clauses parameters initial caller pair (ordered.take 3) (.ok none) finalMemory :=
  ⟨_, Progress.search_sound (fuel := 100) (by rfl)⟩

theorem first_three_source_rules :
    Source.Alternatives
      (Source.ClauseMatch (evaluation parameters) (matching parameters) Env.extend)
      initial caller pair (ordered.take 3) (.ok none) finalMemory :=
  alternatives_complete first_three_execution

/-- The fourth pattern observes the changed counter and becomes selectable. -/
theorem fourth_execution :
    Clauses parameters initial caller pair ordered (.ok (some (intValue 40))) finalMemory :=
  ⟨_, Progress.search_sound (fuel := 120) (by rfl)⟩

theorem fourth_source_rules :
    Source.Alternatives
      (Source.ClauseMatch (evaluation parameters) (matching parameters) Env.extend)
      initial caller pair ordered (.ok (some (intValue 40))) finalMemory :=
  alternatives_complete fourth_execution

end Examples.SuspensionCorrespondence
