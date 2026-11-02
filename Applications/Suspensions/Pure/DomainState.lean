import Applications.Suspensions.Pure.Domain
import Applications.Suspensions.Pure.Recurrence

/-!
# Hereditary domains throughout pure evaluation

The source and value domain is retained by the actual pure machine, including
code stored in caller frames. Recursive descriptor entry uses the proved
member construction law; it does not expand descriptors in the predicates.
Selected primitive operations supply their independent output-domain law.

Every diagnostic fault is admitted. These results preserve hereditary code
restrictions, not types, successful matching or termination. In particular,
the admitted source domain still contains applications that fault.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure.DomainState
open Domain Machine
variable {Primitive : Type}

def ControlAllowed (operations : Primitive → Prop) : Control Primitive → Prop
  | .eval environment expression =>
      EnvAllowed operations environment ∧ CodeAllowed operations expression
  | .value value | .raised value => ValueAllowed operations value
  | .pattern environment pattern value =>
      EnvAllowed operations environment ∧ PatternAllowed pattern ∧ ValueAllowed operations value
  | .matched bindings => EnvAllowed operations bindings
  | .mismatch => True
  | .clauses environment clauses value =>
      EnvAllowed operations environment ∧ ClausesCodeAllowed operations clauses ∧
        ValueAllowed operations value
  | .rows environment patterns fields bindings =>
      EnvAllowed operations environment ∧ PatternFieldsAllowed patterns ∧
        EnvAllowed operations fields ∧ EnvAllowed operations bindings

def FrameAllowed (operations : Primitive → Prop) : Frame Primitive → Prop
  | .constructor _ | .raise | .applicationResult => True
  | .record environment _ remaining done =>
      EnvAllowed operations environment ∧ NamedCodeAllowed operations remaining ∧
        EnvAllowed operations done
  | .function environment argument =>
      EnvAllowed operations environment ∧ CodeAllowed operations argument
  | .argument function => ValueAllowed operations function
  | .bindValue environment pattern body =>
      EnvAllowed operations environment ∧ PatternAllowed pattern ∧ CodeAllowed operations body
  | .bindMatch environment body =>
      EnvAllowed operations environment ∧ CodeAllowed operations body
  | .branch environment yes no =>
      EnvAllowed operations environment ∧ CodeAllowed operations yes ∧ CodeAllowed operations no
  | .handler environment clauses =>
      EnvAllowed operations environment ∧ ClausesCodeAllowed operations clauses
  | .handlerResult original | .layered _ original => ValueAllowed operations original
  | .clause environment body remaining value =>
      EnvAllowed operations environment ∧ CodeAllowed operations body ∧
        ClausesCodeAllowed operations remaining ∧ ValueAllowed operations value
  | .force environment inner => EnvAllowed operations environment ∧ PatternAllowed inner
  | .row environment remaining fields earlier =>
      EnvAllowed operations environment ∧ PatternFieldsAllowed remaining ∧
        EnvAllowed operations fields ∧ EnvAllowed operations earlier

def ConfigAllowed (operations : Primitive → Prop) (config : Config Primitive) : Prop :=
  ControlAllowed operations config.control ∧ List.Forall (FrameAllowed operations) config.stack

def ResultAllowed (operations : Primitive → Prop) : Result Primitive → Prop
  | .value value | .raised value => ValueAllowed operations value
  | .matched bindings => EnvAllowed operations bindings
  | .mismatch | .stuck _ => True

def OutcomeAllowed (operations : Primitive → Prop) : Result Primitive ⊕ Config Primitive → Prop
  | .inl answer => ResultAllowed operations answer
  | .inr config => ConfigAllowed operations config

variable {operations : Primitive → Prop} {parameters : Parameters Primitive}

private theorem frames_cons {frame : Frame Primitive} {stack : List (Frame Primitive)}
    (head : FrameAllowed operations frame) (tail : List.Forall (FrameAllowed operations) stack) :
    List.Forall (FrameAllowed operations) (frame :: stack) :=
  (List.forall_cons _ _ _).mpr ⟨head, tail⟩

private theorem optional_some {value : Value Primitive}
    (allowed : OptionalValueAllowed operations (some value)) : ValueAllowed operations value := by
  cases allowed with
  | some value => exact value

theorem start_allowed {environment : Env Primitive} {expression : Core.Expr Primitive}
    (capture : EnvAllowed operations environment) (code : CodeAllowed operations expression) :
    ConfigAllowed operations (start environment expression) := ⟨⟨capture, code⟩, trivial⟩

theorem startPattern_allowed {environment : Env Primitive} {pattern : Core.Pattern}
    {value : Value Primitive} (capture : EnvAllowed operations environment)
    (matching : PatternAllowed pattern) (argument : ValueAllowed operations value) :
    ConfigAllowed operations (startPattern environment pattern value) :=
  ⟨⟨capture, matching, argument⟩, trivial⟩

private theorem eval_preserves (parameters : Parameters Primitive) {environment : Env Primitive}
    {expression : Core.Expr Primitive} {stack : List (Frame Primitive)}
    (capture : EnvAllowed operations environment) (code : CodeAllowed operations expression)
    (frames : List.Forall (FrameAllowed operations) stack) :
    OutcomeAllowed operations (step parameters ⟨.eval environment expression, stack⟩) := by
  cases expression with
  | atom atom => exact ⟨.atom atom, frames⟩
  | variable name =>
      cases found : Env.lookup environment name with
      | none => simp only [step, transition, found, finish, OutcomeAllowed, ResultAllowed]
      | some value =>
          simpa only [step, transition, found, proceed, OutcomeAllowed, ConfigAllowed,
            ControlAllowed] using And.intro (capture.lookup found) frames
  | primitive operation =>
      exact ⟨.primitive ((CodeAllowed.primitive_iff operation).mp code), frames⟩
  | constructor tag argument =>
      cases argument with
      | none => exact ⟨.constructor .none, frames⟩
      | some body =>
          exact ⟨⟨capture, (CodeAllowed.constructorArgument_iff tag body).mp code⟩,
            frames_cons trivial frames⟩
  | record fields =>
      have allowed := (CodeAllowed.record_iff fields).mp code
      cases fields with
      | nil => exact ⟨.record .nil, frames⟩
      | cons field remaining =>
          rcases field with ⟨label, body⟩
          obtain ⟨head, tail⟩ := (NamedCodeAllowed.cons_iff label body remaining).mp allowed
          exact ⟨⟨capture, head⟩, frames_cons ⟨capture, tail, .nil⟩ frames⟩
  | function clauses =>
      exact ⟨.closure ((CodeAllowed.function_iff clauses).mp code) capture .none, frames⟩
  | apply function argument =>
      obtain ⟨operator, operand⟩ := (CodeAllowed.apply_iff function argument).mp code
      exact ⟨⟨capture, operator⟩, frames_cons ⟨capture, operand⟩ frames⟩
  | bind pattern value body =>
      obtain ⟨matching, right, continuation⟩ := (CodeAllowed.bind_iff pattern value body).mp code
      exact ⟨⟨capture, right⟩, frames_cons ⟨capture, matching, continuation⟩ frames⟩
  | recursive bindings body =>
      obtain ⟨definitions, continuation, _, distinct⟩ := (CodeAllowed.recursive_iff bindings body).mp code
      cases decoded : Rhs.ofBindings bindings with
      | error name => simp only [step, transition, decoded, finish, OutcomeAllowed, ResultAllowed]
      | ok definitions' =>
          have group := GroupAllowed.of_decoded definitions distinct decoded capture
          simpa only [step, transition, decoded, proceed, OutcomeAllowed, ConfigAllowed,
            ControlAllowed] using And.intro
              (And.intro (bodyEnvironment_allowed capture (.some group)) continuation) frames
  | branch condition yes no =>
      obtain ⟨test, positive, negative⟩ := (CodeAllowed.branch_iff condition yes no).mp code
      exact ⟨⟨capture, test⟩, frames_cons ⟨capture, positive, negative⟩ frames⟩
  | reference _ | read _ | assign _ _ | newException _ _ => trivial
  | delay body => exact ⟨.suspension ((CodeAllowed.delay_iff body).mp code) capture .none, frames⟩
  | raise packet =>
      exact ⟨⟨capture, (CodeAllowed.raise_iff packet).mp code⟩, frames_cons trivial frames⟩
  | handle body clauses =>
      obtain ⟨right, handlers⟩ := (CodeAllowed.handle_iff body clauses).mp code
      exact ⟨⟨capture, right⟩, frames_cons ⟨capture, handlers⟩ frames⟩

private theorem argument_preserves
    (preserve : ParametersPreserve operations parameters) {function value : Value Primitive}
    {stack : List (Frame Primitive)} (operator : ValueAllowed operations function)
    (operand : ValueAllowed operations value) (frames : List.Forall (FrameAllowed operations) stack) :
    OutcomeAllowed operations (step parameters ⟨.value value, .argument function :: stack⟩) := by
  cases function with
  | closure clauses captured recursive =>
      obtain ⟨code, capture, group⟩ := (ValueAllowed.closure_iff clauses captured recursive).mp operator
      exact ⟨⟨bodyEnvironment_allowed capture group, code, operand⟩, frames_cons trivial frames⟩
  | primitive operation =>
      have output := preserve operation ((ValueAllowed.primitive_iff operation).mp operator) value operand
      cases returned : parameters.primitive operation value with
      | value result =>
          rw [returned] at output
          simpa only [step, transition, returned, proceed, OutcomeAllowed, ConfigAllowed,
            ControlAllowed] using And.intro ((PrimitiveResultAllowed.value_iff result).mp output) frames
      | raised packet =>
          rw [returned] at output
          simpa only [step, transition, returned, proceed, OutcomeAllowed, ConfigAllowed,
            ControlAllowed] using And.intro ((PrimitiveResultAllowed.raised_iff packet).mp output) frames
      | stuck fault => simp only [step, transition, returned, finish, OutcomeAllowed, ResultAllowed]
  | constructor tag argument =>
      cases argument with
      | none => exact ⟨.constructor (.some operand), frames⟩
      | some _ => trivial
  | exception tag argument =>
      cases argument with
      | none => exact ⟨.exception (.some operand), frames⟩
      | some _ => trivial
  | atom _ | record _ | suspension _ _ _ => trivial

private theorem value_preserves
    (preserve : ParametersPreserve operations parameters) {value : Value Primitive}
    {stack : List (Frame Primitive)} (allowed : ValueAllowed operations value)
    (frames : List.Forall (FrameAllowed operations) stack) :
    OutcomeAllowed operations (step parameters ⟨.value value, stack⟩) := by
  cases stack with
  | nil => exact allowed
  | cons frame rest =>
      obtain ⟨head, tail⟩ := (List.forall_cons _ _ _).mp frames
      cases frame with
      | constructor tag => exact ⟨.constructor (.some allowed), tail⟩
      | record environment label remaining done =>
          obtain ⟨capture, code, earlier⟩ := head
          have fields : EnvAllowed operations (done ++ [(label, value)]) :=
            earlier.append (.cons allowed .nil)
          cases remaining with
          | nil => exact ⟨.record fields, tail⟩
          | cons field remaining =>
              rcases field with ⟨nextLabel, body⟩
              obtain ⟨next, remainingCode⟩ := (NamedCodeAllowed.cons_iff nextLabel body remaining).mp code
              exact ⟨⟨capture, next⟩, frames_cons ⟨capture, remainingCode, fields⟩ tail⟩
      | function environment argument =>
          exact ⟨head, frames_cons allowed tail⟩
      | argument function => exact argument_preserves preserve head allowed tail
      | bindValue environment pattern body =>
          exact ⟨⟨head.1, head.2.1, allowed⟩, frames_cons ⟨head.1, head.2.2⟩ tail⟩
      | branch environment yes no =>
          cases value with
          | atom atom =>
              cases atom with
              | boolean selected =>
                  cases selected with
                  | false => exact ⟨⟨head.1, head.2.2⟩, tail⟩
                  | true => exact ⟨⟨head.1, head.2.1⟩, tail⟩
              | integer _ => trivial
          | constructor _ _ | record _ | closure _ _ _ | suspension _ _ _ | primitive _
          | exception _ _ => trivial
      | raise =>
          cases value with
          | exception _ _ => exact ⟨allowed, tail⟩
          | atom _ | constructor _ _ | record _ | closure _ _ _ | suspension _ _ _ | primitive _ => trivial
      | handler _ _ | handlerResult _ | applicationResult => exact ⟨allowed, tail⟩
      | force environment inner => exact ⟨⟨head.1, head.2, allowed⟩, tail⟩
      | bindMatch _ _ | clause _ _ _ _ | row _ _ _ _ | layered _ _ => trivial

private theorem raised_preserves (parameters : Parameters Primitive) {packet : Value Primitive}
    {stack : List (Frame Primitive)} (allowed : ValueAllowed operations packet)
    (frames : List.Forall (FrameAllowed operations) stack) :
    OutcomeAllowed operations (step parameters ⟨.raised packet, stack⟩) := by
  cases stack with
  | nil => exact allowed
  | cons frame rest =>
      obtain ⟨head, tail⟩ := (List.forall_cons _ _ _).mp frames
      cases frame <;> try exact ⟨allowed, tail⟩
      case handler environment clauses =>
        exact ⟨⟨head.1, head.2, allowed⟩, frames_cons allowed tail⟩

private theorem pattern_preserves (parameters : Parameters Primitive) {environment : Env Primitive}
    {pattern : Core.Pattern} {value : Value Primitive} {stack : List (Frame Primitive)}
    (capture : EnvAllowed operations environment) (matching : PatternAllowed pattern)
    (allowed : ValueAllowed operations value) (frames : List.Forall (FrameAllowed operations) stack) :
    OutcomeAllowed operations (step parameters ⟨.pattern environment pattern value, stack⟩) := by
  cases matching with
  | wildcard => exact ⟨.nil, frames⟩
  | variable name => exact ⟨.cons allowed .nil, frames⟩
  | atom atom =>
      cases value <;> try exact ⟨trivial, frames⟩
      case atom actual =>
        by_cases same : atom = actual
        · simpa only [step, transition, same, if_true, proceed, OutcomeAllowed,
            ConfigAllowed, ControlAllowed] using And.intro (EnvAllowed.nil (operations := operations)) frames
        · simpa only [step, transition, same, if_false, proceed, OutcomeAllowed,
            ConfigAllowed, ControlAllowed] using And.intro True.intro frames
  | constructor tag =>
      cases value <;> try exact ⟨trivial, frames⟩
      case constructor actual argument =>
        cases argument with
        | some _ => exact ⟨trivial, frames⟩
        | none =>
            by_cases same : tag = actual
            · simpa only [step, transition, same, if_true, proceed, OutcomeAllowed,
                ConfigAllowed, ControlAllowed] using And.intro (EnvAllowed.nil (operations := operations)) frames
            · simpa only [step, transition, same, if_false, proceed, OutcomeAllowed,
                ConfigAllowed, ControlAllowed] using And.intro True.intro frames
  | @constructorArgument tag innerPattern inner =>
      cases value <;> try exact ⟨trivial, frames⟩
      case constructor actual argument =>
        cases argument with
        | none => exact ⟨trivial, frames⟩
        | some argument =>
            have argumentAllowed := optional_some ((ValueAllowed.constructor_iff actual _).mp allowed)
            by_cases same : tag = actual
            · simpa only [step, transition, same, if_true, proceed, OutcomeAllowed,
                ConfigAllowed, ControlAllowed] using And.intro (And.intro capture (And.intro inner argumentAllowed)) frames
            · simpa only [step, transition, same, if_false, proceed, OutcomeAllowed,
                ConfigAllowed, ControlAllowed] using And.intro True.intro frames
  | exception name =>
      cases found : Env.lookup environment name with
      | none => simp only [step, transition, found, finish, OutcomeAllowed, ResultAllowed]
      | some binding =>
          cases binding <;>
            try simp only [step, transition, found, finish, OutcomeAllowed, ResultAllowed]
          case exception tag argument =>
            cases argument with
            | some _ => simp only [step, transition, found, finish, OutcomeAllowed, ResultAllowed]
            | none =>
                cases value <;>
                  try simpa only [step, transition, found, proceed, OutcomeAllowed, ConfigAllowed,
                    ControlAllowed] using And.intro True.intro frames
                case exception actual argument =>
                  cases argument with
                  | some _ =>
                      simpa only [step, transition, found, proceed, OutcomeAllowed, ConfigAllowed,
                        ControlAllowed] using And.intro True.intro frames
                  | none =>
                      by_cases same : tag = actual
                      · simpa only [step, transition, found, same, if_true, proceed, OutcomeAllowed,
                          ConfigAllowed, ControlAllowed] using
                            And.intro (EnvAllowed.nil (operations := operations)) frames
                      · simpa only [step, transition, found, same, if_false, proceed, OutcomeAllowed,
                          ConfigAllowed, ControlAllowed] using And.intro True.intro frames
  | @exceptionArgument name innerPattern inner =>
      cases found : Env.lookup environment name with
      | none => simp only [step, transition, found, finish, OutcomeAllowed, ResultAllowed]
      | some binding =>
          cases binding <;>
            try simp only [step, transition, found, finish, OutcomeAllowed, ResultAllowed]
          case exception tag argument =>
            cases argument with
            | some _ => simp only [step, transition, found, finish, OutcomeAllowed, ResultAllowed]
            | none =>
                cases value <;>
                  try simpa only [step, transition, found, proceed, OutcomeAllowed, ConfigAllowed,
                    ControlAllowed] using And.intro True.intro frames
                case exception actual argument =>
                  cases argument with
                  | none =>
                      simpa only [step, transition, found, proceed, OutcomeAllowed, ConfigAllowed,
                        ControlAllowed] using And.intro True.intro frames
                  | some argument =>
                      have argumentAllowed := optional_some ((ValueAllowed.exception_iff actual _).mp allowed)
                      by_cases same : tag = actual
                      · simpa only [step, transition, found, same, if_true, proceed, OutcomeAllowed,
                          ConfigAllowed, ControlAllowed] using
                            And.intro (And.intro capture (And.intro inner argumentAllowed)) frames
                      · simpa only [step, transition, found, same, if_false, proceed, OutcomeAllowed,
                          ConfigAllowed, ControlAllowed] using And.intro True.intro frames
  | record patternsAllowed =>
      cases value <;> try trivial
      case record fields =>
        have fieldsAllowed := (ValueAllowed.record_iff fields).mp allowed
        cases patternsAllowed with
        | nil =>
            cases fields with
            | nil => exact ⟨.nil, frames⟩
            | cons _ _ => trivial
        | cons pattern remaining =>
            exact ⟨⟨capture, .cons pattern remaining, fieldsAllowed, .nil⟩, frames⟩
  | suspended inner =>
      cases value <;> try trivial
      case suspension body captured recursive =>
        obtain ⟨code, environmentAllowed, group⟩ := (ValueAllowed.suspension_iff body captured recursive).mp allowed
        exact ⟨⟨bodyEnvironment_allowed environmentAllowed group, code⟩,
          frames_cons ⟨capture, inner⟩ frames⟩
  | layered inner =>
      exact ⟨⟨capture, inner, allowed⟩, frames_cons allowed frames⟩

private theorem matched_preserves (parameters : Parameters Primitive) {bindings : Env Primitive}
    {stack : List (Frame Primitive)} (allowed : EnvAllowed operations bindings)
    (frames : List.Forall (FrameAllowed operations) stack) :
    OutcomeAllowed operations (step parameters ⟨.matched bindings, stack⟩) := by
  cases stack with
  | nil => exact allowed
  | cons frame rest =>
      obtain ⟨head, tail⟩ := (List.forall_cons _ _ _).mp frames
      cases frame <;> try trivial
      case bindMatch environment body => exact ⟨⟨head.1.extend allowed, head.2⟩, tail⟩
      case clause environment body remaining value => exact ⟨⟨head.1.extend allowed, head.2.1⟩, tail⟩
      case row environment remaining fields earlier =>
        exact ⟨⟨head.1, head.2.1, head.2.2.1, head.2.2.2.extend allowed⟩, tail⟩
      case layered name value => exact ⟨(EnvAllowed.cons head .nil).extend allowed, tail⟩

private theorem mismatch_preserves (parameters : Parameters Primitive) {stack : List (Frame Primitive)}
    (frames : List.Forall (FrameAllowed operations) stack) :
    OutcomeAllowed operations (step parameters ⟨.mismatch, stack⟩) := by
  cases stack with
  | nil => trivial
  | cons frame rest =>
      obtain ⟨head, tail⟩ := (List.forall_cons _ _ _).mp frames
      cases frame <;> try trivial
      case clause environment body remaining value => exact ⟨⟨head.1, head.2.2.1, head.2.2.2⟩, tail⟩
      case bindMatch environment body => exact ⟨.exception .none, tail⟩
      case applicationResult => exact ⟨.exception .none, tail⟩
      case handlerResult original => exact ⟨head, tail⟩
      case row environment remaining fields earlier => exact ⟨trivial, tail⟩
      case layered name value => exact ⟨trivial, tail⟩

private theorem clauses_preserves (parameters : Parameters Primitive) {environment : Env Primitive}
    {clauses : List (Core.Pattern × Core.Expr Primitive)} {value : Value Primitive}
    {stack : List (Frame Primitive)} (capture : EnvAllowed operations environment)
    (code : ClausesCodeAllowed operations clauses) (allowed : ValueAllowed operations value)
    (frames : List.Forall (FrameAllowed operations) stack) :
    OutcomeAllowed operations (step parameters ⟨.clauses environment clauses value, stack⟩) := by
  cases clauses with
  | nil => exact ⟨trivial, frames⟩
  | cons clause remaining =>
      rcases clause with ⟨pattern, body⟩
      obtain ⟨matching, right, tail⟩ := (ClausesCodeAllowed.cons_iff pattern body remaining).mp code
      exact ⟨⟨capture, matching, allowed⟩, frames_cons ⟨capture, right, tail, allowed⟩ frames⟩

private theorem rows_preserves (parameters : Parameters Primitive) {environment : Env Primitive}
    {patterns : List (Nat × Core.Pattern)} {fields bindings : Env Primitive}
    {stack : List (Frame Primitive)} (capture : EnvAllowed operations environment)
    (matching : PatternFieldsAllowed patterns) (values : EnvAllowed operations fields)
    (earlier : EnvAllowed operations bindings) (frames : List.Forall (FrameAllowed operations) stack) :
    OutcomeAllowed operations (step parameters ⟨.rows environment patterns fields bindings, stack⟩) := by
  cases matching with
  | nil => exact ⟨earlier, frames⟩
  | @cons label pattern remaining head tail =>
      cases found : Env.lookup fields label with
      | none => simp only [step, transition, found, finish, OutcomeAllowed, ResultAllowed]
      | some value =>
          simpa only [step, transition, found, proceed, OutcomeAllowed, ConfigAllowed, ControlAllowed] using
            And.intro (And.intro capture (And.intro head (values.lookup found)))
              (frames_cons (frame := .row environment remaining fields bindings)
                ⟨capture, tail, values, earlier⟩ frames)

/-- One actual machine step retains the domain, with primitive output
preservation supplied independently of representation compatibility. -/
theorem step_preserves (preserve : ParametersPreserve operations parameters)
    {input : Config Primitive} (initial : ConfigAllowed operations input) :
    OutcomeAllowed operations (step parameters input) := by
  rcases input with ⟨control, stack⟩
  obtain ⟨allowed, frames⟩ := initial
  cases control with
  | eval environment expression => exact eval_preserves parameters allowed.1 allowed.2 frames
  | value value => exact value_preserves preserve allowed frames
  | raised packet => exact raised_preserves parameters allowed frames
  | pattern environment pattern value =>
      exact pattern_preserves parameters allowed.1 allowed.2.1 allowed.2.2 frames
  | matched bindings => exact matched_preserves parameters allowed frames
  | mismatch => exact mismatch_preserves parameters frames
  | clauses environment clauses value =>
      exact clauses_preserves parameters allowed.1 allowed.2.1 allowed.2.2 frames
  | rows environment patterns fields bindings =>
      exact rows_preserves parameters allowed.1 allowed.2.1 allowed.2.2.1 allowed.2.2.2 frames

/-- Finite execution supplies the result premise; no termination property is
part of the domain or of this preservation theorem. -/
theorem evaluates_preserves (preserve : ParametersPreserve operations parameters)
    {input : Config Primitive} {output : Result Primitive} {steps : Nat}
    (initial : ConfigAllowed operations input)
    (evaluation : Progress.Evaluates (step parameters) input output steps) :
    ResultAllowed operations output := by
  revert initial
  induction evaluation with
  | done finished =>
      intro initial
      have allowed := step_preserves preserve initial
      rw [finished] at allowed
      exact allowed
  | next moved _ ih =>
      intro initial
      have allowed := step_preserves preserve initial
      rw [moved] at allowed
      exact ih allowed

/-- Unfinished prefixes retain admissible control and caller frames. The
existing `Reaches` observer records actual steps, without an absorbing tail. -/
theorem reaches_preserves (preserve : ParametersPreserve operations parameters)
    {input next : Config Primitive} {steps : Nat} (initial : ConfigAllowed operations input)
    (reached : Recurrence.Reaches parameters steps input next) : ConfigAllowed operations next := by
  induction steps generalizing input with
  | zero =>
      have same := (Recurrence.reaches_zero_iff parameters input next).mp reached
      subst input
      exact initial
  | succ steps ih =>
      obtain ⟨middle, moved, remaining⟩ :=
        (Recurrence.reaches_succ_iff parameters steps input next).mp reached
      have allowed := step_preserves preserve initial
      rw [moved] at allowed
      exact ih allowed remaining

end Suspensions.Pure.DomainState
