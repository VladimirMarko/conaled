import Applications.Suspensions.Observation

/-!
# Agreement of the existing event instruments

The list-traced machine appends each transition event to a supplied prior
log. The resource observer records only the events of the observed run, in
the same order. A finite traced evaluation therefore determines both the
observer's complete answer and its exact newly recorded event list.

The proof follows the actual evaluation derivation. It introduces no event
generator, evaluator, completion bound or assumption about event counts.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.Observation
open Machine

variable {Primitive : Type}

/-- The resource observation at the actual finite run length reaches the
same full answer. Its new events extend the supplied prior list exactly. -/
theorem traced_evaluates_observe {parameters : Parameters Primitive}
    {input : Config Primitive × List Event} {output : Answer Primitive × List Event}
    {steps : Nat}
    (run : Progress.Evaluates (tracedStep parameters) input output steps) :
    (observe parameters steps input.1).1 = .inl output.1 ∧
      input.2 ++ FreeAddMonoid.toList (observe parameters steps input.1).2 = output.2 := by
  induction run with
  | @done input output finished =>
      rcases input with ⟨config, prior⟩
      rcases output with ⟨answer, events⟩
      rcases actual : transition parameters config with ⟨choice, event⟩
      cases choice with
      | inl result =>
          have same : (result, prior ++ [event]) = (answer, events) :=
            Sum.inl.inj (by
              simpa only [tracedStep, measuredStep, Resources.reweight, actual] using finished)
          have sameAnswer : result = answer := congrArg Prod.fst same
          have sameEvents : prior ++ [event] = events := congrArg Prod.snd same
          have observed : observe parameters 1 config = (.inl result, FreeAddMonoid.of event) := by
            change workload parameters (0 + 1) (.inr config) = _
            rw [workload_succ, measuredAdvance_running, actual]
            simp only [Resources.bind, workload_finished, add_zero]
          constructor
          · rw [observed]
            exact congrArg Sum.inl sameAnswer
          · simpa only [observed, FreeAddMonoid.toList_of] using sameEvents
      | inr next =>
          simp [tracedStep, measuredStep, Resources.reweight, actual] at finished
  | @next input next output steps moved _ ih =>
      rcases input with ⟨config, prior⟩
      rcases next with ⟨following, logged⟩
      rcases output with ⟨answer, events⟩
      rcases actual : transition parameters config with ⟨choice, event⟩
      cases choice with
      | inl result =>
          simp [tracedStep, measuredStep, Resources.reweight, actual] at moved
      | inr continued =>
          have same : (continued, prior ++ [event]) = (following, logged) :=
            Sum.inr.inj (by
              simpa only [tracedStep, measuredStep, Resources.reweight, actual] using moved)
          have sameConfig : continued = following := congrArg Prod.fst same
          have sameLog : prior ++ [event] = logged := congrArg Prod.snd same
          have afterAnswer : (observe parameters steps continued).1 = .inl answer := by
            rw [sameConfig]
            exact ih.1
          have afterEvents : (prior ++ [event]) ++
              FreeAddMonoid.toList (observe parameters steps continued).2 = events := by
            rw [sameConfig, sameLog]
            exact ih.2
          have observed : observe parameters (steps + 1) config =
              ((observe parameters steps continued).1,
                FreeAddMonoid.of event + (observe parameters steps continued).2) := by
            rw [observe, workload_succ, measuredAdvance_running, actual]
            rfl
          constructor
          · simpa only [observed] using afterAnswer
          · simpa only [observed, FreeAddMonoid.toList_add, FreeAddMonoid.toList_of,
              List.append_assoc] using afterEvents

/-- With no prior events, the actual finite traced result is exactly the
resource observer's new event list, with the same full answer. -/
theorem traced_evaluates_observe_nil {parameters : Parameters Primitive}
    {config : Config Primitive} {answer : Answer Primitive} {events : List Event} {steps : Nat}
    (run : Progress.Evaluates (tracedStep parameters) (config, []) (answer, events) steps) :
    (observe parameters steps config).1 = .inl answer ∧
      FreeAddMonoid.toList (observe parameters steps config).2 = events :=
  traced_evaluates_observe run

end Suspensions.Core.Observation
