import Applications.Suspensions.Pure.Ordinary
import Applications.Suspensions.Pure.Forcing
import Applications.Suspensions.Pure.RecursiveStep

/-!
# Finite raw executions have pure interpretations

The proof composes actual finite prefixes of the two existing machines.
Ordinary transitions and force/cache operations consume one raw step;
recursive creation consumes its positive, explicitly counted prefix. Cache
reuse expands an already stored pure-body certificate. Thus induction is on
the remaining raw evaluation count, without assuming that open bodies finish
or that active addresses are distinct.

The private block certificate only collects these proved local laws. Its
prefix and evaluation fields use the existing observation and evaluation
interfaces; it is not a replacement execution semantics. The correspondence
preserves values, exceptions, matching outcomes and admitted runtime faults.
The two transition counts need not agree.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure.Simulation
open Representation Memory History Recurrence Domain DomainState WorldDomain Compatibility

variable {Primitive : Type}

private inductive ExecutionBlock (rawParameters : Core.Machine.Parameters Primitive)
    (parameters : Machine.Parameters Primitive) (operations : Primitive → Prop)
    (world : World Primitive) (raw : Core.Machine.Config Primitive)
    (view : Machine.Config Primitive) : Prop
  | done {answer : Core.Machine.Answer Primitive} {result : Machine.Result Primitive}
      (rawStep : Core.Machine.step rawParameters raw = .inl answer)
      (pureStep : Machine.step parameters view = .inl result)
      (state : StateRep parameters world answer.memory)
      (resultRep : ResultRep world answer.result result)
      (events : ∀ address, (Core.Machine.transition rawParameters raw).2 ≠ .body address)
  | next {afterWorld : World Primitive} {rawAfter : Core.Machine.Config Primitive}
      {pureAfter : Machine.Config Primitive} {rawSteps pureSteps : Nat}
      (positive : 0 < rawSteps) (extension : Durability.Extends world afterWorld)
      (allowed : WorldAllowed operations afterWorld)
      (rawPrefix : Core.Prefix.observe rawParameters rawSteps raw = .inr rawAfter)
      (purePrefix : Reaches parameters pureSteps view pureAfter)
      (represented : ConfigRep parameters afterWorld rawAfter pureAfter)
      (events : rawSteps = 1 ∨
        ∀ index config, index < rawSteps →
          Core.Prefix.observe rawParameters index raw = .inr config →
          ∀ address, (Core.Machine.transition rawParameters config).2 ≠ .body address)

variable {rawParameters : Core.Machine.Parameters Primitive}
  {parameters : Machine.Parameters Primitive} {operations : Primitive → Prop}
  {world : World Primitive} {raw : Core.Machine.Config Primitive} {view : Machine.Config Primitive}

private theorem ordinary_block (represented : ConfigRep parameters world raw view)
    (allowed : ConfigAllowed operations view) (worldAllowed : WorldAllowed operations world)
    (compatible : ParametersCompatible operations rawParameters parameters) (ordinary : IsOrdinary raw) :
    ExecutionBlock rawParameters parameters operations world raw view := by
  have compared := ordinary_step represented allowed compatible ordinary
  generalize rawEquation : Core.Machine.step rawParameters raw = rawResult at compared
  generalize pureEquation : Machine.step parameters view = pureResult at compared
  cases compared with
  | next unchanged after =>
      exact .next (by decide) (Durability.Extends.refl world) worldAllowed
        (rawSteps := 1) rawEquation (Reaches.one pureEquation) after (Or.inl rfl)
  | done unchanged result =>
      refine .done rawEquation pureEquation ?_ result (ordinary_event_ne_body rawParameters ordinary)
      simpa only [unchanged] using represented.memory

private theorem execution_block (represented : ConfigRep parameters world raw view)
    (allowed : ConfigAllowed operations view) (worldAllowed : WorldAllowed operations world)
    (compatible : ParametersCompatible operations rawParameters parameters) :
    ExecutionBlock rawParameters parameters operations world raw view := by
  by_cases ordinary : IsOrdinary raw
  · exact ordinary_block represented allowed worldAllowed compatible ordinary
  have shapes := (not_ordinary_iff raw).mp ordinary
  rcases raw with ⟨memory, rawControl, rawStack⟩
  rcases view with ⟨control, pureStack⟩
  rcases represented with ⟨state, controls, frames, histories⟩
  rcases shapes with delayed | recursive | forced | returned | raised
  · obtain ⟨environment, body, equal⟩ := delayed
    change rawControl = .eval environment (.delay body) at equal
    subst rawControl
    cases controls with
    | eval expression captured =>
        obtain ⟨extension, rawStep, pureStep, after⟩ :=
          delay_entry rawParameters body state captured frames histories
        refine .next (rawSteps := 1) (by decide) extension ?_
          (congrArg Prod.fst rawStep) pureStep after (Or.inl rfl)
        exact worldAllowed.put _ _
          (.suspension ((CodeAllowed.delay_iff body).mp allowed.1.2) allowed.1.1 .none)
  · obtain ⟨environment, bindings, body, equal⟩ := recursive
    change rawControl = .eval environment (.recursive bindings body) at equal
    subst rawControl
    cases controls with
    | eval expression captured =>
        obtain ⟨afterWorld, rawAfter, pureAfter, extension, afterAllowed,
            rawPrefix, purePrefix, after, events⟩ :=
          recursive_entry rawParameters state worldAllowed captured allowed.1.1 allowed.1.2
            frames histories
        exact .next (by omega) extension afterAllowed rawPrefix purePrefix after (Or.inr events)
  · obtain ⟨environment, inner, address, equal⟩ := forced
    change rawControl = .pattern environment (.suspended inner) (.address address) at equal
    subst rawControl
    cases controls with
    | pattern pattern captured value =>
        cases value with
        | address found =>
            obtain ⟨cell, occupied, cellRep⟩ := state.meanings address _ found
            cases cellRep with
            | thunk bodyCapture =>
                obtain ⟨rawStep, pureStep, after⟩ :=
                  enter_thunk rawParameters state found occupied captured frames histories
                exact .next (rawSteps := 1) (by decide) (Durability.Extends.refl world)
                  worldAllowed (congrArg Prod.fst rawStep) pureStep after (Or.inl rfl)
            | cached value evaluation =>
                obtain ⟨result, steps, evaluated, rawStep, pureStep, after⟩ :=
                  reuse_cached rawParameters state found occupied captured frames histories
                exact .next (rawSteps := 1) (by decide) (Durability.Extends.refl world)
                  worldAllowed (congrArg Prod.fst rawStep) pureStep after (Or.inl rfl)
  · obtain ⟨value, address, environment, inner, tail, equal, stack⟩ := returned
    change rawControl = .value value at equal
    change rawStack = .memoize address environment inner :: tail at stack
    subst rawControl
    subst rawStack
    cases controls with
    | value valueRep =>
        cases frames with
        | cons head rest =>
            cases head with
            | memoize pattern found captured =>
                obtain ⟨rawStep, pureStep, after⟩ :=
                  return_memoize rawParameters state found captured valueRep rest histories
                exact .next (rawSteps := 1) (by decide) (Durability.Extends.refl world)
                  worldAllowed (congrArg Prod.fst rawStep) pureStep after (Or.inl rfl)
  · obtain ⟨packet, address, environment, inner, tail, equal, stack⟩ := raised
    change rawControl = .raised packet at equal
    change rawStack = .memoize address environment inner :: tail at stack
    subst rawControl
    subst rawStack
    cases controls with
    | raised valueRep =>
        cases frames with
        | cons head rest =>
            cases head with
            | memoize pattern found captured =>
                obtain ⟨rawStep, pureStep, after⟩ :=
                  raise_memoize rawParameters state valueRep rest histories
                exact .next (rawSteps := 1) (by decide) (Durability.Extends.refl world)
                  worldAllowed (congrArg Prod.fst rawStep) pureStep after (Or.inl rfl)

/-- Every actual finite raw evaluation from a related, admitted configuration
has a finite pure evaluation and represented reached memory/result. Nothing in
the premises requires finite evaluation of a newly allocated or active body. -/
theorem finite_correspondence {answer : Core.Machine.Answer Primitive} {total : Nat}
    (compatible : ParametersCompatible operations rawParameters parameters)
    (preserve : ParametersPreserve operations parameters)
    (worldAllowed : WorldAllowed operations world)
    (represented : ConfigRep parameters world raw view) (allowed : ConfigAllowed operations view)
    (evaluation : Progress.Evaluates (Core.Machine.step rawParameters) raw answer total) :
    ∃ afterWorld result steps,
      Durability.Extends world afterWorld ∧ WorldAllowed operations afterWorld ∧
      StateRep parameters afterWorld answer.memory ∧ ResultRep afterWorld answer.result result ∧
      Progress.Evaluates (Machine.step parameters) view result steps := by
  induction total using Nat.strong_induction_on generalizing world raw view with
  | h total ih =>
      cases execution_block represented allowed worldAllowed compatible with
      | done rawStep pureStep state result events =>
          have same := (evaluation.unique (.done rawStep)).1
          subst answer
          exact ⟨world, _, 1, Durability.Extends.refl world, worldAllowed, state, result,
            .done pureStep⟩
      | next positive extension afterAllowed rawPrefix purePrefix after events =>
          obtain ⟨remaining, residual, count⟩ := Core.Recursive.evaluates_strip_prefix rawPrefix evaluation
          have afterCode := reaches_preserves preserve allowed purePrefix
          obtain ⟨lastWorld, result, steps, finalExtension, finalAllowed, state, resultRep, pureRun⟩ :=
            ih remaining (by omega) afterAllowed after afterCode residual
          exact ⟨lastWorld, result, _, extension.trans finalExtension, finalAllowed, state, resultRep,
            purePrefix.evaluates pureRun⟩

/-- Every actual body-entry event in a finite observed prefix has a related
pure configuration, with its own actual pure prefix. The surrounding raw run
need not terminate. Recursive creation's intermediate states are handled by
its proved absence of body-entry events, rather than assigned a false stable
configuration relation. -/
theorem body_entry_correspondence {index address : Nat} {config : Core.Machine.Config Primitive}
    (compatible : ParametersCompatible operations rawParameters parameters)
    (preserve : ParametersPreserve operations parameters)
    (worldAllowed : WorldAllowed operations world)
    (represented : ConfigRep parameters world raw view) (allowed : ConfigAllowed operations view)
    (reached : Core.Prefix.observe rawParameters index raw = .inr config)
    (event : (Core.Machine.transition rawParameters config).2 = .body address) :
    ∃ afterWorld pureConfig steps,
      Durability.Extends world afterWorld ∧ WorldAllowed operations afterWorld ∧
      ConfigRep parameters afterWorld config pureConfig ∧ ConfigAllowed operations pureConfig ∧
      Reaches parameters steps view pureConfig := by
  induction index using Nat.strong_induction_on generalizing world raw view with
  | h index ih =>
      by_cases zero : index = 0
      · subst index
        have same : raw = config := Sum.inr.inj reached
        subst config
        exact ⟨world, view, 0, Durability.Extends.refl world, worldAllowed,
          represented, allowed, rfl⟩
      · cases execution_block represented allowed worldAllowed compatible with
        | done rawStep pureStep state result events =>
            cases index with
            | zero => exact False.elim (zero rfl)
            | succ previous =>
                rw [Core.Prefix.observe_succ, rawStep, Core.Prefix.iterate_answer] at reached
                cases reached
        | @next afterWorld rawAfter pureAfter rawSteps pureSteps positive extension
            afterAllowed rawPrefix purePrefix after events =>
            by_cases inside : index < rawSteps
            · rcases events with one | absent
              · exact False.elim (zero (by omega))
              · exact False.elim (absent index config inside reached address event)
            · have beyond : rawSteps ≤ index := by omega
              have composed : Core.Prefix.observe rawParameters ((index - rawSteps) + rawSteps) raw =
                  Core.Prefix.observe rawParameters (index - rawSteps) rawAfter := by
                unfold Core.Prefix.observe at rawPrefix ⊢
                rw [Function.iterate_add_apply, rawPrefix]
              have residualObserved :
                  Core.Prefix.observe rawParameters (index - rawSteps) rawAfter = .inr config :=
                composed.symm.trans (by simpa only [Nat.sub_add_cancel beyond] using reached)
              have afterCode := reaches_preserves preserve allowed purePrefix
              obtain ⟨lastWorld, pureConfig, steps, finalExtension, finalAllowed,
                  finalRep, finalCode, pureRest⟩ :=
                ih (index - rawSteps) (by omega) afterAllowed after afterCode residualObserved
              exact ⟨lastWorld, pureConfig, pureSteps + steps, extension.trans finalExtension,
                finalAllowed, finalRep, finalCode, purePrefix.trans pureRest⟩

end Suspensions.Pure.Simulation
