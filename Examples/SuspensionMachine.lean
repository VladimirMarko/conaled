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
  refine ⟨_, _, _, Progress.search_sound (step := tracedStep parameters)
    (fuel := 80) (by rfl), ?_⟩
  exact ⟨rfl, rfl, rfl, rfl⟩

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
  refine ⟨_, _, _, Progress.search_sound (step := tracedStep parameters)
    (fuel := 100) (by rfl), ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

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
  refine ⟨_, _, _, Progress.search_sound (step := tracedStep parameters)
    (fuel := 200) (by rfl), ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The appended source clause sees the new reference value and returns3. -/
theorem fourth_clause_reachable :
    ∃ answer events steps,
      Progress.Evaluates (tracedStep parameters)
        (start initial [] (effectfulClauses clauses4), []) (answer, events) steps ∧
      answer.result = .value (.atom (.integer 3)) ∧
      answer.memory.memory 0 = some (.value (.atom (.boolean true))) ∧
      answer.memory.memory 1 = some (.value (.atom (.integer 1))) ∧
      events.count (.body 1) = 1 ∧ events.count (.cacheWrite 1) = 1 := by
  refine ⟨_, _, _, Progress.search_sound (step := tracedStep parameters)
    (fuel := 220) (by rfl), ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

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
  refine ⟨_, _, _, Progress.search_sound (step := tracedStep parameters)
    (fuel := 100) (by rfl), ?_⟩
  exact ⟨rfl, rfl, rfl⟩

/-- The cached reference contains the integer-valued replacement when reread. -/
theorem cached_reference_integer :
    ∃ answer events steps,
      Progress.Evaluates (tracedStep parameters) (start initial [] cachedReference, [])
        (answer, events) steps ∧
      answer.result = .value (.atom (.integer 0)) ∧ answer.memory.next = 2 ∧
      answer.memory.memory 0 = some (.value (.address 1)) ∧
      events.count (.body 0) = 1 ∧ events.count (.cacheWrite 0) = 1 ∧
      events.count (.hit 0) = 1 ∧ events.count (.referenceWrite 1) = 1 := by
  refine ⟨_, _, _, Progress.search_sound (step := tracedStep parameters)
    (fuel := 200) (by rfl), ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def guarded (body continuation : Expr Primitive) : Expr Primitive :=
  .bind (.variable 1) (.reference (boolean false))
    (.recursive [(2, .delay body)] continuation)

def reentrantOverwrite : Expr Primitive :=
  guarded
    (.branch (.read (.variable 1)) (integer 7)
      (.bind .wildcard (.assign (.variable 1) (boolean true))
        (.apply (.primitive .increment) (force (.variable 2)))))
    (.bind .wildcard (force (.variable 2)) (force (.variable 2)))

/-- An inner successful force is followed by the outer successful overwrite. -/
theorem reentrant_overwrite :
    ∃ answer events steps,
      Progress.Evaluates (tracedStep parameters) (start initial [] reentrantOverwrite, [])
        (answer, events) steps ∧
      answer.result = .value (.atom (.integer 8)) ∧
      answer.memory.memory 1 = some (.value (.atom (.integer 8))) ∧
      answer.memory.memory 0 = some (.value (.atom (.boolean true))) ∧
      events.count (.body 1) = 2 ∧ events.count (.cacheWrite 1) = 2 ∧
      events.count (.hit 1) = 1 := by
  refine ⟨_, _, _, Progress.search_sound (step := tracedStep parameters)
    (fuel := 300) (by rfl), ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def reentrantRaises (continuation : Expr Primitive) : Expr Primitive :=
  .newException 3
    (guarded
      (.branch (.read (.variable 1)) (integer 7)
        (.bind .wildcard (.assign (.variable 1) (boolean true))
          (.bind .wildcard (force (.variable 2)) (.raise (.variable 3)))))
      continuation)

/-- The outer exceptional return leaves the inner successful cache in memory. -/
theorem outer_exception_preserves_inner :
    ∃ answer events steps,
      Progress.Evaluates (tracedStep parameters)
        (start initial [] (reentrantRaises (force (.variable 2))), []) (answer, events) steps ∧
      answer.result = .raised (.exception 2 none) ∧
      answer.memory.memory 1 = some (.value (.atom (.integer 7))) ∧
      events.count (.body 1) = 2 ∧ events.count (.cacheWrite 1) = 1 := by
  refine ⟨_, _, _, Progress.search_sound (step := tracedStep parameters)
    (fuel := 300) (by rfl), ?_⟩
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- After handling that outer exception, another force uses the inner cache. -/
theorem outer_exception_then_hit :
    ∃ answer events steps,
      Progress.Evaluates (tracedStep parameters)
        (start initial [] (reentrantRaises
          (.handle (force (.variable 2)) [(.exception 3 none, force (.variable 2))])), [])
        (answer, events) steps ∧
      answer.result = .value (.atom (.integer 7)) ∧
      answer.memory.memory 1 = some (.value (.atom (.integer 7))) ∧
      events.count (.body 1) = 2 ∧ events.count (.cacheWrite 1) = 1 ∧
      events.count (.hit 1) = 1 := by
  refine ⟨_, _, _, Progress.search_sound (step := tracedStep parameters)
    (fuel := 350) (by rfl), ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def repeatedCreation : Expr Primitive :=
  .bind .wildcard (force (.delay (integer 7))) (force (.delay (integer 7)))

/-- Repeating delay creation differs from aliasing one existing address. -/
theorem repeated_creation_runs_twice :
    ∃ answer events steps,
      Progress.Evaluates (tracedStep parameters) (start initial [] repeatedCreation, [])
        (answer, events) steps ∧
      answer.result = .value (.atom (.integer 7)) ∧ answer.memory.next = 2 ∧
      events.count (.body 0) = 1 ∧ events.count (.body 1) = 1 ∧
      events.count (.hit 0) = 0 ∧ events.count (.hit 1) = 0 := by
  refine ⟨_, _, _, Progress.search_sound (step := tracedStep parameters)
    (fuel := 150) (by rfl), ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def exceptionalInner : Expr Primitive :=
  .newException 3
    (.bind (.variable 1) (.delay (.delay (.raise (.variable 3))))
      (.handle
        (.bind (.suspended (.suspended .wildcard)) (.variable 1) (force (.variable 1)))
        [(.exception 3 none, force (.variable 1))]))

/-- The inner pattern raises after the successful outer result is cached. -/
theorem exceptional_inner_retains_outer_cache :
    ∃ answer events steps,
      Progress.Evaluates (tracedStep parameters) (start initial [] exceptionalInner, [])
        (answer, events) steps ∧
      answer.result = .value (.address 1) ∧
      answer.memory.memory 0 = some (.value (.address 1)) ∧
      events.count (.body 0) = 1 ∧ events.count (.body 1) = 1 ∧
      events.count (.cacheWrite 0) = 1 ∧ events.count (.cacheWrite 1) = 0 ∧
      events.count (.hit 0) = 1 := by
  refine ⟨_, _, _, Progress.search_sound (step := tracedStep parameters)
    (fuel := 250) (by rfl), ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def repeatedExceptions : Expr Primitive :=
  .newException 3
    (.bind (.variable 1) (.delay (.raise (.variable 3)))
      (.bind .wildcard
        (.handle (force (.variable 1)) [(.exception 3 none, .record [])])
        (.handle (force (.variable 1)) [(.exception 3 none, integer 5)])))

/-- A body exception is not cached: handling and retrying enters the body again. -/
theorem repeated_body_exceptions :
    ∃ answer events steps,
      Progress.Evaluates (tracedStep parameters) (start initial [] repeatedExceptions, [])
        (answer, events) steps ∧
      answer.result = .value (.atom (.integer 5)) ∧ answer.memory.next = 1 ∧
      events.count (.body 0) = 2 ∧ events.count (.cacheWrite 0) = 0 ∧
      events.count (.hit 0) = 0 := by
  refine ⟨_, _, _, Progress.search_sound (step := tracedStep parameters)
    (fuel := 250) (by rfl), ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def shallowConstructor : Expr Primitive :=
  .newException 3
    (force (.delay (.constructor 10 (some (.delay (.raise (.variable 3)))))))

/-- Returning a constructor containing a suspension does not force that field. -/
theorem shallow_constructor_observation :
    ∃ answer events steps,
      Progress.Evaluates (tracedStep parameters) (start initial [] shallowConstructor, [])
        (answer, events) steps ∧
      answer.result = .value (.constructor 10 (some (.address 1))) ∧ answer.memory.next = 2 ∧
      events.count (.body 0) = 1 ∧ events.count (.body 1) = 0 ∧
      events.count (.cacheWrite 0) = 1 ∧ events.count (.cacheWrite 1) = 0 := by
  refine ⟨_, _, _, Progress.search_sound (step := tracedStep parameters)
    (fuel := 150) (by rfl), ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def lazyClauses : List (Pattern × Expr Primitive) :=
  [(.reference (.atom (.boolean false)), .delay (integer 1)),
   (.reference (.atom (.boolean true)), .delay (integer 2))]

def lazySelection : Expr Primitive :=
  .bind (.variable 1) (.reference (boolean false))
    (.bind (.variable 2) (.apply (lazyFunction 9 lazyClauses) (.variable 1))
      (.bind .wildcard (.assign (.variable 1) (boolean true)) (force (.variable 2))))

/-- Identifier9 is fresh here; the clauses run only after the reference changes. -/
theorem lazy_function_delays_matching :
    ∃ answer events steps,
      Progress.Evaluates (tracedStep parameters) (start initial [] lazySelection, [])
        (answer, events) steps ∧
      answer.result = .value (.atom (.integer 2)) ∧ answer.memory.next = 3 ∧
      answer.memory.memory 0 = some (.value (.atom (.boolean true))) ∧
      events.count (.body 1) = 1 ∧ events.count (.body 2) = 1 ∧
      events.count (.referenceWrite 0) = 1 := by
  refine ⟨_, _, _, Progress.search_sound (step := tracedStep parameters)
    (fuel := 300) (by rfl), ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def currentExceptionPattern : Expr Primitive :=
  .newException 3
    (.bind (.variable 1) (.delay (.variable 3))
      (.newException 3 (.bind (.suspended (.exception 3 none)) (.variable 1) (integer 9))))

/-- Body and inner pattern use different environments when a name is shadowed. -/
theorem exception_pattern_uses_current_environment :
    ∃ answer events steps,
      Progress.Evaluates (tracedStep parameters) (start initial [] currentExceptionPattern, [])
        (answer, events) steps ∧
      answer.result = .raised (.exception 1 none) ∧
      answer.memory.memory 0 = some (.value (.exception 2 none)) ∧
      events.count (.freshException 2) = 1 ∧ events.count (.freshException 3) = 1 ∧
      events.count (.body 0) = 1 ∧ events.count (.cacheWrite 0) = 1 := by
  refine ⟨_, _, _, Progress.search_sound (step := tracedStep parameters)
    (fuel := 150) (by rfl), ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def referenceInner : Expr Primitive :=
  .bind (.variable 1) (.reference (boolean false))
    (.bind (.variable 2)
      (.delay (.bind .wildcard (.assign (.variable 1) (boolean true)) (integer 1)))
      (.bind (.variable 3) (.reference (.variable 2))
        (.apply (.function
          [(.reference (.suspended (.atom (.integer 0))), boolean false),
           (.wildcard, .read (.variable 1))]) (.variable 3))))

/-- Reference matching preserves the effects of its failed suspended subpattern. -/
theorem reference_inner_effects_retained :
    ∃ answer events steps,
      Progress.Evaluates (tracedStep parameters) (start initial [] referenceInner, [])
        (answer, events) steps ∧
      answer.result = .value (.atom (.boolean true)) ∧
      answer.memory.memory 0 = some (.value (.atom (.boolean true))) ∧
      answer.memory.memory 1 = some (.value (.atom (.integer 1))) ∧
      events.count (.referenceRead 2) = 1 ∧ events.count (.body 1) = 1 ∧
      events.count (.cacheWrite 1) = 1 := by
  refine ⟨_, _, _, Progress.search_sound (step := tracedStep parameters)
    (fuel := 220) (by rfl), ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩


/-- The function calls the suspension, whose captured recursive environment calls
that same function. The outer thunk and reference are outside the recursive group. -/
def mutualCreation : Expr Primitive :=
  .bind (.variable 3) (.delay (integer 99))
    (.bind (.variable 4) (.reference (integer 5))
      (.recursive
        [(1, .function [(.variable 5,
          .branch (.variable 5) (integer 7) (force (.variable 2)))]),
         (2, .delay (.apply (.variable 1) (boolean true)))]
        (.apply (.variable 1) (boolean false))))

/-- Rec and SRec connect both directions of the mutual dependency. SRec preserves
an unrelated outer thunk's exact captured environment, and the reference value. -/
theorem mutual_function_suspension :
    ∃ answer events steps,
      Progress.Evaluates (tracedStep parameters) (start initial [] mutualCreation, [])
        (answer, events) steps ∧
      answer.result = .value (.atom (.integer 7)) ∧ answer.memory.next = 3 ∧
      answer.memory.memory 0 = some (.thunk (integer 99) []) ∧
      answer.memory.memory 1 = some (.value (.atom (.integer 5))) ∧
      answer.memory.memory 2 = some (.value (.atom (.integer 7))) ∧
      events.count (.body 2) = 1 ∧ events.count (.cacheWrite 2) = 1 ∧
      events.count (.body 0) = 0 := by
  refine ⟨_, _, _, Progress.search_sound (step := tracedStep parameters)
    (fuel := 300) (by rfl), ?_⟩
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def rawStuck : Expr Primitive :=
  .bind .wildcard (.reference (integer 7)) (.read (integer 0))

/-- A raw type error remains distinct from a source exception and retains effects. -/
theorem raw_stuck_retains_state :
    ∃ answer events steps,
      Progress.Evaluates (tracedStep parameters) (start initial [] rawStuck, [])
        (answer, events) steps ∧
      answer.result = .stuck .expectedAddress ∧ answer.memory.next = 1 ∧
      answer.memory.memory 0 = some (.value (.atom (.integer 7))) ∧
      events.count (.allocate 0) = 1 := by
  refine ⟨_, _, _, Progress.search_sound (step := tracedStep parameters)
    (fuel := 80) (by rfl), ?_⟩
  exact ⟨rfl, rfl, rfl, rfl⟩

end Examples.SuspensionMachine
