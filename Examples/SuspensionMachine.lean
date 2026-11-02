import Applications.Suspensions.Machine

/-!
# Actual suspension evaluations

The expected values and effects are worked out in the local statement record
before these executions are checked. Each case turns a closed finite search
equation into `Progress.Evaluates` through `Progress.search_sound`. Resource
events are observations of the same explicit transitions.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.SuspensionMachine
open Suspensions Suspensions.Core Suspensions.Core.Machine

inductive Primitive where
  | increment
  deriving DecidableEq, Repr

def primitives : Primitive → Value Primitive → PrimitiveResult Primitive
  | .increment, .atom (.integer n) => .value (.atom (.integer (n + 1)))
  | _, _ => .stuck .primitive

def parameters : Parameters Primitive := ⟨primitives, 0, 1⟩

def initial : Memory Primitive := { Suspensions.empty with exceptionNames := {0, 1} }

def integer (n : Int) : Expr Primitive := .atom (.integer n)

def boolean (b : Bool) : Expr Primitive := .atom (.boolean b)

/-- This single source term is also the subject of the independent static audit.
It uses no primitive operation and is polymorphic in the primitive vocabulary. -/
def cachedReference {Operation : Type} : Expr Operation :=
  .bind (.variable 1)
    (.delay (.reference (.function [(.variable 2, .variable 2)])))
    (.bind .wildcard
      (.assign (force (.variable 1)) (.function [(.wildcard, .atom (.integer 0))]))
      (.apply (.read (force (.variable 1))) (.atom (.boolean true))))

/-- The delayed variable uses its creation binding, not the later shadowing. -/
def lexical : Expr Primitive :=
  .bind (.variable 1) (integer 1)
    (.bind (.variable 2) (.delay (.variable 1))
      (.bind (.variable 1) (integer 2) (force (.variable 2))))

theorem lexical_capture :
    ∃ answer events steps,
      Progress.Evaluates (tracedStep parameters) (start initial [] lexical, [])
        (answer, events) steps ∧
      answer.result = .value (.atom (.integer 1)) ∧
      answer.memory.memory 0 = some (.value (.atom (.integer 1))) ∧
      events.count (.body 0) = 1 ∧ events.count (.cacheWrite 0) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Progress.search_sound (fuel := 80) (by rfl)
  · exact ⟨rfl, rfl, rfl, rfl⟩

/-- The same suspension is forced twice; the second occurrence uses its cache. -/
def aliased : Expr Primitive :=
  .bind (.variable 1) (.delay (integer 7))
    (.bind .wildcard (force (.variable 1)) (force (.variable 1)))

theorem alias_cache_reuse :
    ∃ answer events steps,
      Progress.Evaluates (tracedStep parameters) (start initial [] aliased, [])
        (answer, events) steps ∧
      answer.result = .value (.atom (.integer 7)) ∧ answer.memory.next = 1 ∧
      events.count (.body 0) = 1 ∧ events.count (.cacheWrite 0) = 1 ∧
      events.count (.hit 0) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Progress.search_sound (fuel := 100) (by rfl)
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The trace instrumentation is connected to the public uninstrumented machine. -/
theorem lexical_capture_uninstrumented :
    ∃ answer steps, Progress.Evaluates (step parameters) (start initial [] lexical) answer steps ∧
      answer.result = .value (.atom (.integer 1)) := by
  obtain ⟨answer, events, steps, evaluated, value, _⟩ := lexical_capture
  exact ⟨answer, steps, traced_evaluates_erases evaluated, value⟩

def pairPattern (b : Bool) (tail : Pattern) : Pattern :=
  .record [(1, .reference (.atom (.boolean b))), (2, tail)]

/-- Appendix A's first three clauses, with their printed answers0,1,2. -/
def clauses3 : List (Pattern × Expr Primitive) :=
  [(pairPattern true .wildcard, integer 0),
   (pairPattern false (.suspended (.atom (.integer 0))), integer 1),
   (pairPattern false .wildcard, integer 2)]

def clauses4 : List (Pattern × Expr Primitive) :=
  clauses3 ++ [(pairPattern true .wildcard, integer 3)]

def effectfulClauses (clauses : List (Pattern × Expr Primitive)) : Expr Primitive :=
  .bind (.variable 1) (.reference (boolean false))
    (.apply (.function clauses)
      (.record [(1, .variable 1),
        (2, .delay (.bind .wildcard (.assign (.variable 1) (boolean true)) (integer 1)))]))

/-- The three source clauses exhaust after the second clause changes memory. -/
theorem three_clauses_exhaust :
    ∃ answer events steps,
      Progress.Evaluates (tracedStep parameters)
        (start initial [] (effectfulClauses clauses3), []) (answer, events) steps ∧
      answer.result = .raised (.exception 0 none) ∧
      answer.memory.memory 0 = some (.value (.atom (.boolean true))) ∧
      answer.memory.memory 1 = some (.value (.atom (.integer 1))) ∧
      events.count (.body 1) = 1 ∧ events.count (.cacheWrite 1) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Progress.search_sound (fuel := 200) (by rfl)
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The appended source clause sees the new reference value and returns3. -/
theorem fourth_clause_reachable :
    ∃ answer events steps,
      Progress.Evaluates (tracedStep parameters)
        (start initial [] (effectfulClauses clauses4), []) (answer, events) steps ∧
      answer.result = .value (.atom (.integer 3)) ∧
      answer.memory.memory 0 = some (.value (.atom (.boolean true))) ∧
      answer.memory.memory 1 = some (.value (.atom (.integer 1))) ∧
      events.count (.body 1) = 1 ∧ events.count (.cacheWrite 1) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Progress.search_sound (fuel := 220) (by rfl)
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def assignmentUnit : Expr Primitive :=
  .bind (.variable 1) (.reference (boolean false))
    (.bind (.record []) (.assign (.variable 1) (boolean true)) (.read (.variable 1)))

/-- Assignment's source unit is accepted by the empty-record unit pattern. -/
theorem assignment_unit_matches :
    ∃ answer events steps,
      Progress.Evaluates (tracedStep parameters) (start initial [] assignmentUnit, [])
        (answer, events) steps ∧
      answer.result = .value (.atom (.boolean true)) ∧
      answer.memory.memory 0 = some (.value (.atom (.boolean true))) ∧
      events.count (.referenceWrite 0) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Progress.search_sound (fuel := 100) (by rfl)
  · exact ⟨rfl, rfl, rfl⟩

/-- The cached reference contains the integer-valued replacement when reread. -/
theorem cached_reference_integer :
    ∃ answer events steps,
      Progress.Evaluates (tracedStep parameters) (start initial [] cachedReference, [])
        (answer, events) steps ∧
      answer.result = .value (.atom (.integer 0)) ∧ answer.memory.next = 2 ∧
      answer.memory.memory 0 = some (.value (.address 1)) ∧
      events.count (.body 0) = 1 ∧ events.count (.cacheWrite 0) = 1 ∧
      events.count (.hit 0) = 1 ∧ events.count (.referenceWrite 1) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Progress.search_sound (fuel := 200) (by rfl)
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Examples.SuspensionMachine
