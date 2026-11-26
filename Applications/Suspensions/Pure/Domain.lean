import Applications.Suspensions.Pure.Compatibility
import Applications.Suspensions.Recursive

/-!
# Hereditary code restrictions for the pure interpretation

The existing effect predicates remain the effect boundary. `RecursiveForm`
adds only permitted recursive right-hand sides and distinct recursive binder
names, at every nested declaration. This is not the complete source typing or
well-formedness judgment: empty matches, repeated record labels, unbound names
and ill-typed applications remain possible.

The value predicates inspect finite stored code, earlier captures and group
descriptors. They never expand `Group.members` in their definitions. Their
preservation under member construction is a theorem, so cyclic source groups
need neither cyclic Lean values nor terminating-body premises.

This domain is independent of heap representation and finite evaluation.
Primitive output preservation is a separate operation law from relational
compatibility, and the existing scalar basis discharges it through its
output-origin theorem.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure.Domain

mutual
  def RecursiveForm {Primitive : Type} : Core.Expr Primitive → Prop
    | .atom _ | .variable _ | .primitive _ => True
    | .constructor _ argument => OptionalRecursiveForm argument
    | .record fields => NamedRecursiveForms fields
    | .function clauses => ClauseRecursiveForms clauses
    | .apply function argument | .assign function argument =>
        RecursiveForm function ∧ RecursiveForm argument
    | .bind _ value body => RecursiveForm value ∧ RecursiveForm body
    | .recursive bindings body =>
        Core.Recursive.Permitted bindings ∧ (bindings.map Prod.fst).Nodup ∧
          NamedRecursiveForms bindings ∧ RecursiveForm body
    | .branch condition yes no =>
        RecursiveForm condition ∧ RecursiveForm yes ∧ RecursiveForm no
    | .reference body | .read body | .delay body | .raise body => RecursiveForm body
    | .handle body clauses => RecursiveForm body ∧ ClauseRecursiveForms clauses
    | .newException _ body => RecursiveForm body
  termination_by expression => sizeOf expression
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def OptionalRecursiveForm {Primitive : Type} : Option (Core.Expr Primitive) → Prop
    | none => True
    | some body => RecursiveForm body
  termination_by argument => sizeOf argument
  decreasing_by simp_wf

  def NamedRecursiveForms {Primitive : Type} : List (Nat × Core.Expr Primitive) → Prop
    | [] => True
    | (_, body) :: rest => RecursiveForm body ∧ NamedRecursiveForms rest
  termination_by fields => sizeOf fields
  decreasing_by
    all_goals simp_wf
    all_goals omega

  def ClauseRecursiveForms {Primitive : Type} : List (Core.Pattern × Core.Expr Primitive) → Prop
    | [] => True
    | (_, body) :: rest => RecursiveForm body ∧ ClauseRecursiveForms rest
  termination_by clauses => sizeOf clauses
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

def CodeAllowed {Primitive : Type} (operations : Primitive → Prop)
    (expression : Core.Expr Primitive) : Prop :=
  ExpressionAllowed operations expression ∧ RecursiveForm expression

def NamedCodeAllowed {Primitive : Type} (operations : Primitive → Prop)
    (fields : List (Nat × Core.Expr Primitive)) : Prop :=
  NamedExpressionsAllowed operations fields ∧ NamedRecursiveForms fields

def ClausesCodeAllowed {Primitive : Type} (operations : Primitive → Prop)
    (clauses : List (Core.Pattern × Core.Expr Primitive)) : Prop :=
  ClausesAllowed operations clauses ∧ ClauseRecursiveForms clauses

def RhsAllowed {Primitive : Type} (operations : Primitive → Prop) (rhs : Rhs Primitive) : Prop :=
  CodeAllowed operations rhs.toExpr

variable {Primitive : Type} {operations : Primitive → Prop}

theorem CodeAllowed.effects {expression : Core.Expr Primitive}
    (allowed : CodeAllowed operations expression) : ExpressionAllowed operations expression :=
  allowed.1

theorem CodeAllowed.form {expression : Core.Expr Primitive}
    (allowed : CodeAllowed operations expression) : RecursiveForm expression := allowed.2

theorem CodeAllowed.atom (atom : Core.Atom) : CodeAllowed operations (.atom atom) :=
  ⟨.atom atom, by simp [RecursiveForm]⟩

theorem CodeAllowed.variable (name : Nat) : CodeAllowed operations (.variable name) :=
  ⟨.variable name, by simp [RecursiveForm]⟩

theorem CodeAllowed.primitive_iff (operation : Primitive) :
    CodeAllowed operations (.primitive operation) ↔ operations operation := by
  constructor
  · intro allowed
    cases allowed.effects with
    | primitive selected => exact selected
  · intro selected
    exact ⟨.primitive selected, by simp [RecursiveForm]⟩

theorem CodeAllowed.constructor (tag : Nat) : CodeAllowed operations (.constructor tag none) :=
  ⟨.constructor tag, by simp [RecursiveForm, OptionalRecursiveForm]⟩

theorem CodeAllowed.constructor_argument_iff (tag : Nat) (body : Core.Expr Primitive) :
    CodeAllowed operations (.constructor tag (some body)) ↔ CodeAllowed operations body := by
  simp only [CodeAllowed, RecursiveForm, OptionalRecursiveForm]
  constructor
  · rintro ⟨effects, form⟩
    cases effects with
    | constructor_argument inner => exact ⟨inner, form⟩
  · rintro ⟨effects, form⟩
    exact ⟨.constructor_argument effects, form⟩

theorem NamedCodeAllowed.nil : NamedCodeAllowed operations [] :=
  ⟨.nil, by simp [NamedRecursiveForms]⟩

theorem NamedCodeAllowed.cons_iff (name : Nat) (body : Core.Expr Primitive)
    (rest : List (Nat × Core.Expr Primitive)) :
    NamedCodeAllowed operations ((name, body) :: rest) ↔
      CodeAllowed operations body ∧ NamedCodeAllowed operations rest := by
  simp only [NamedCodeAllowed, NamedRecursiveForms, CodeAllowed]
  constructor
  · rintro ⟨effects, headForm, tailForm⟩
    cases effects with
    | cons head tail => exact ⟨⟨head, headForm⟩, tail, tailForm⟩
  · rintro ⟨⟨head, headForm⟩, tail, tailForm⟩
    exact ⟨.cons head tail, headForm, tailForm⟩

theorem ClausesCodeAllowed.nil : ClausesCodeAllowed operations [] :=
  ⟨.nil, by simp [ClauseRecursiveForms]⟩

theorem ClausesCodeAllowed.cons_iff (pattern : Core.Pattern) (body : Core.Expr Primitive)
    (rest : List (Core.Pattern × Core.Expr Primitive)) :
    ClausesCodeAllowed operations ((pattern, body) :: rest) ↔
      PatternAllowed pattern ∧ CodeAllowed operations body ∧ ClausesCodeAllowed operations rest := by
  simp only [ClausesCodeAllowed, ClauseRecursiveForms, CodeAllowed]
  constructor
  · rintro ⟨effects, headForm, tailForm⟩
    cases effects with
    | cons matching head tail => exact ⟨matching, ⟨head, headForm⟩, tail, tailForm⟩
  · rintro ⟨matching, ⟨head, headForm⟩, tail, tailForm⟩
    exact ⟨.cons matching head tail, headForm, tailForm⟩

theorem CodeAllowed.record_iff (fields : List (Nat × Core.Expr Primitive)) :
    CodeAllowed operations (.record fields) ↔ NamedCodeAllowed operations fields := by
  simp only [CodeAllowed, RecursiveForm, NamedCodeAllowed]
  constructor
  · rintro ⟨effects, form⟩
    cases effects with
    | record fields => exact ⟨fields, form⟩
  · rintro ⟨effects, form⟩
    exact ⟨.record effects, form⟩

theorem CodeAllowed.function_iff (clauses : List (Core.Pattern × Core.Expr Primitive)) :
    CodeAllowed operations (.function clauses) ↔ ClausesCodeAllowed operations clauses := by
  simp only [CodeAllowed, RecursiveForm, ClausesCodeAllowed]
  constructor
  · rintro ⟨effects, form⟩
    cases effects with
    | function clauses => exact ⟨clauses, form⟩
  · rintro ⟨effects, form⟩
    exact ⟨.function effects, form⟩

theorem CodeAllowed.apply_iff (function argument : Core.Expr Primitive) :
    CodeAllowed operations (.apply function argument) ↔
      CodeAllowed operations function ∧ CodeAllowed operations argument := by
  simp only [CodeAllowed, RecursiveForm]
  constructor
  · rintro ⟨effects, functionForm, argumentForm⟩
    cases effects with
    | apply operator operand => exact ⟨⟨operator, functionForm⟩, operand, argumentForm⟩
  · rintro ⟨⟨operator, functionForm⟩, operand, argumentForm⟩
    exact ⟨.apply operator operand, functionForm, argumentForm⟩

theorem CodeAllowed.bind_iff (pattern : Core.Pattern) (value body : Core.Expr Primitive) :
    CodeAllowed operations (.bind pattern value body) ↔
      PatternAllowed pattern ∧ CodeAllowed operations value ∧ CodeAllowed operations body := by
  simp only [CodeAllowed, RecursiveForm]
  constructor
  · rintro ⟨effects, valueForm, bodyForm⟩
    cases effects with
    | bind matching right continuation =>
        exact ⟨matching, ⟨right, valueForm⟩, continuation, bodyForm⟩
  · rintro ⟨matching, ⟨right, valueForm⟩, continuation, bodyForm⟩
    exact ⟨.bind matching right continuation, valueForm, bodyForm⟩

theorem CodeAllowed.recursive_iff (bindings : List (Nat × Core.Expr Primitive))
    (body : Core.Expr Primitive) :
    CodeAllowed operations (.recursive bindings body) ↔
      NamedCodeAllowed operations bindings ∧ CodeAllowed operations body ∧
        Core.Recursive.Permitted bindings ∧ (bindings.map Prod.fst).Nodup := by
  simp only [CodeAllowed, RecursiveForm, NamedCodeAllowed]
  constructor
  · rintro ⟨effects, permitted, distinct, definitionsForm, bodyForm⟩
    cases effects with
    | recursive definitions continuation =>
        exact ⟨⟨definitions, definitionsForm⟩, ⟨continuation, bodyForm⟩, permitted, distinct⟩
  · rintro ⟨⟨definitions, definitionsForm⟩, ⟨continuation, bodyForm⟩, permitted, distinct⟩
    exact ⟨.recursive definitions continuation, permitted, distinct, definitionsForm, bodyForm⟩

theorem CodeAllowed.branch_iff (condition yes no : Core.Expr Primitive) :
    CodeAllowed operations (.branch condition yes no) ↔
      CodeAllowed operations condition ∧ CodeAllowed operations yes ∧ CodeAllowed operations no := by
  simp only [CodeAllowed, RecursiveForm]
  constructor
  · rintro ⟨effects, conditionForm, yesForm, noForm⟩
    cases effects with
    | branch test positive negative =>
        exact ⟨⟨test, conditionForm⟩, ⟨positive, yesForm⟩, negative, noForm⟩
  · rintro ⟨⟨test, conditionForm⟩, ⟨positive, yesForm⟩, negative, noForm⟩
    exact ⟨.branch test positive negative, conditionForm, yesForm, noForm⟩

theorem CodeAllowed.delay_iff (body : Core.Expr Primitive) :
    CodeAllowed operations (.delay body) ↔ CodeAllowed operations body := by
  simp only [CodeAllowed, RecursiveForm]
  constructor
  · rintro ⟨effects, form⟩
    cases effects with
    | delay body => exact ⟨body, form⟩
  · rintro ⟨effects, form⟩
    exact ⟨.delay effects, form⟩

theorem CodeAllowed.raise_iff (packet : Core.Expr Primitive) :
    CodeAllowed operations (.raise packet) ↔ CodeAllowed operations packet := by
  simp only [CodeAllowed, RecursiveForm]
  constructor
  · rintro ⟨effects, form⟩
    cases effects with
    | raise packet => exact ⟨packet, form⟩
  · rintro ⟨effects, form⟩
    exact ⟨.raise effects, form⟩

theorem CodeAllowed.handle_iff (body : Core.Expr Primitive)
    (clauses : List (Core.Pattern × Core.Expr Primitive)) :
    CodeAllowed operations (.handle body clauses) ↔
      CodeAllowed operations body ∧ ClausesCodeAllowed operations clauses := by
  simp only [CodeAllowed, RecursiveForm, ClausesCodeAllowed]
  constructor
  · rintro ⟨effects, bodyForm, clausesForm⟩
    cases effects with
    | handle right handlers => exact ⟨⟨right, bodyForm⟩, handlers, clausesForm⟩
  · rintro ⟨⟨right, bodyForm⟩, handlers, clausesForm⟩
    exact ⟨.handle right handlers, bodyForm, clausesForm⟩

theorem CodeAllowed.force {body : Core.Expr Primitive} (allowed : CodeAllowed operations body) :
    CodeAllowed operations (Core.force body) := by
  apply (CodeAllowed.apply_iff _ _).mpr
  refine ⟨?_, allowed⟩
  apply (CodeAllowed.function_iff _).mpr
  apply (ClausesCodeAllowed.cons_iff _ _ []).mpr
  exact ⟨.suspended (.variable 0), CodeAllowed.variable 0, ClausesCodeAllowed.nil⟩

theorem RhsAllowed.function_iff (clauses : List (Core.Pattern × Core.Expr Primitive)) :
    RhsAllowed operations (.function clauses) ↔ ClausesCodeAllowed operations clauses :=
  CodeAllowed.function_iff clauses

theorem RhsAllowed.delay_iff (body : Core.Expr Primitive) :
    RhsAllowed operations (.delay body) ↔ CodeAllowed operations body :=
  CodeAllowed.delay_iff body

/-- The source's permitted RHS shapes suffice to recover a finite descriptor
with exactly the original ordered bindings. No execution premise is needed. -/
theorem decode_permitted {bindings : List (Nat × Core.Expr Primitive)}
    (permitted : Core.Recursive.Permitted bindings) :
    ∃ decoded, Rhs.ofBindings bindings = .ok decoded ∧ Rhs.toBindings decoded = bindings := by
  obtain ⟨decoded, found⟩ : ∃ decoded, Rhs.ofBindings bindings = .ok decoded := by
    revert permitted
    induction bindings with
    | nil => intro _; exact ⟨[], rfl⟩
    | cons binding rest ih =>
        rcases binding with ⟨name, expression⟩
        intro permitted
        obtain ⟨head, tail⟩ := (Core.Recursive.permitted_cons name expression rest).mp permitted
        obtain ⟨rhs, first⟩ := (Rhs.ofExpr_success_iff expression).mpr head
        obtain ⟨following, last⟩ := ih tail
        refine ⟨(name, rhs) :: following, ?_⟩
        rw [Rhs.ofBindings, first, last]
        rfl
  exact ⟨decoded, found, Rhs.toBindings_ofBindings found⟩

theorem NamedCodeAllowed.member {fields : List (Nat × Core.Expr Primitive)}
    {name : Nat} {body : Core.Expr Primitive} (allowed : NamedCodeAllowed operations fields)
    (member : (name, body) ∈ fields) : CodeAllowed operations body := by
  revert allowed member
  induction fields with
  | nil => intro _ impossible; cases impossible
  | cons binding rest ih =>
      rcases binding with ⟨key, expression⟩
      intro allowed member
      obtain ⟨head, tail⟩ := (NamedCodeAllowed.cons_iff key expression rest).mp allowed
      rcases List.mem_cons.mp member with same | later
      · cases same
        exact head
      · exact ih tail later

theorem NamedCodeAllowed.rhs {bindings : List (Nat × Rhs Primitive)} {name : Nat}
    {rhs : Rhs Primitive} (allowed : NamedCodeAllowed operations (Rhs.toBindings bindings))
    (member : (name, rhs) ∈ bindings) : RhsAllowed operations rhs := by
  exact allowed.member (List.mem_map.mpr ⟨(name, rhs), member, rfl⟩)

theorem NamedCodeAllowed.of_rhs {bindings : List (Nat × Rhs Primitive)}
    (allowed : ∀ binding ∈ bindings, RhsAllowed operations binding.2) :
    NamedCodeAllowed operations (Rhs.toBindings bindings) := by
  revert allowed
  induction bindings with
  | nil => intro _; exact .nil
  | cons binding rest ih =>
      rcases binding with ⟨name, rhs⟩
      intro allowed
      apply (NamedCodeAllowed.cons_iff name rhs.toExpr (Rhs.toBindings rest)).mpr
      exact ⟨allowed _ List.mem_cons_self,
        ih (fun entry member => allowed entry (List.mem_cons_of_mem _ member))⟩

mutual
  inductive ValueAllowed {Primitive : Type} (operations : Primitive → Prop) : Value Primitive → Prop
    | atom (atom : Core.Atom) : ValueAllowed operations (.atom atom)
    | constructor {tag : Nat} {argument : Option (Value Primitive)}
        (allowed : OptionalValueAllowed operations argument) :
        ValueAllowed operations (.constructor tag argument)
    | record {fields : Env Primitive} (allowed : EnvAllowed operations fields) :
        ValueAllowed operations (.record fields)
    | closure {clauses : List (Core.Pattern × Core.Expr Primitive)} {captured : Env Primitive}
        {recursive : Option (Suspensions.Pure.Group Primitive)}
        (code : ClausesCodeAllowed operations clauses) (environment : EnvAllowed operations captured)
        (group : OptionalGroupAllowed operations recursive) :
        ValueAllowed operations (.closure clauses captured recursive)
    | suspension {body : Core.Expr Primitive} {captured : Env Primitive}
        {recursive : Option (Suspensions.Pure.Group Primitive)}
        (code : CodeAllowed operations body) (environment : EnvAllowed operations captured)
        (group : OptionalGroupAllowed operations recursive) :
        ValueAllowed operations (.suspension body captured recursive)
    | primitive {operation : Primitive} (selected : operations operation) :
        ValueAllowed operations (.primitive operation)
    | exception {name : Nat} {argument : Option (Value Primitive)}
        (allowed : OptionalValueAllowed operations argument) :
        ValueAllowed operations (.exception name argument)

  inductive EnvAllowed {Primitive : Type} (operations : Primitive → Prop) : Env Primitive → Prop
    | nil : EnvAllowed operations []
    | cons {name : Nat} {value : Value Primitive} {rest : Env Primitive}
        (head : ValueAllowed operations value) (tail : EnvAllowed operations rest) :
        EnvAllowed operations ((name, value) :: rest)

  inductive OptionalValueAllowed {Primitive : Type} (operations : Primitive → Prop) :
      Option (Value Primitive) → Prop
    | none : OptionalValueAllowed operations none
    | some {value : Value Primitive} (allowed : ValueAllowed operations value) :
        OptionalValueAllowed operations (some value)

  inductive GroupAllowed {Primitive : Type} (operations : Primitive → Prop) :
      Suspensions.Pure.Group Primitive → Prop
    | mk {bindings : List (Nat × Rhs Primitive)} {outer : Env Primitive}
        (definitions : ∀ binding ∈ bindings, RhsAllowed operations binding.2)
        (distinct : (bindings.map Prod.fst).Nodup) (environment : EnvAllowed operations outer) :
        GroupAllowed operations (.mk bindings outer)

  inductive OptionalGroupAllowed {Primitive : Type} (operations : Primitive → Prop) :
      Option (Suspensions.Pure.Group Primitive) → Prop
    | none : OptionalGroupAllowed operations none
    | some {group : Suspensions.Pure.Group Primitive} (allowed : GroupAllowed operations group) :
        OptionalGroupAllowed operations (some group)
end

theorem ValueAllowed.constructor_iff (tag : Nat) (argument : Option (Value Primitive)) :
    ValueAllowed operations (.constructor tag argument) ↔ OptionalValueAllowed operations argument := by
  constructor
  · intro allowed
    cases allowed with
    | constructor argument => exact argument
  · exact .constructor

theorem ValueAllowed.record_iff (fields : Env Primitive) :
    ValueAllowed operations (.record fields) ↔ EnvAllowed operations fields := by
  constructor
  · intro allowed
    cases allowed with
    | record fields => exact fields
  · exact .record

theorem ValueAllowed.closure_iff (clauses : List (Core.Pattern × Core.Expr Primitive))
    (captured : Env Primitive) (recursive : Option (Suspensions.Pure.Group Primitive)) :
    ValueAllowed operations (.closure clauses captured recursive) ↔
      ClausesCodeAllowed operations clauses ∧ EnvAllowed operations captured ∧
        OptionalGroupAllowed operations recursive := by
  constructor
  · intro allowed
    cases allowed with
    | closure code environment group => exact ⟨code, environment, group⟩
  · rintro ⟨code, environment, group⟩
    exact .closure code environment group

theorem ValueAllowed.suspension_iff (body : Core.Expr Primitive) (captured : Env Primitive)
    (recursive : Option (Suspensions.Pure.Group Primitive)) :
    ValueAllowed operations (.suspension body captured recursive) ↔
      CodeAllowed operations body ∧ EnvAllowed operations captured ∧
        OptionalGroupAllowed operations recursive := by
  constructor
  · intro allowed
    cases allowed with
    | suspension code environment group => exact ⟨code, environment, group⟩
  · rintro ⟨code, environment, group⟩
    exact .suspension code environment group

theorem ValueAllowed.primitive_iff (operation : Primitive) :
    ValueAllowed operations (.primitive operation) ↔ operations operation := by
  constructor
  · intro allowed
    cases allowed with
    | primitive selected => exact selected
  · exact .primitive

theorem ValueAllowed.exception_iff (name : Nat) (argument : Option (Value Primitive)) :
    ValueAllowed operations (.exception name argument) ↔ OptionalValueAllowed operations argument := by
  constructor
  · intro allowed
    cases allowed with
    | exception argument => exact argument
  · exact .exception

theorem EnvAllowed.of_members {environment : Env Primitive}
    (members : ∀ binding ∈ environment, ValueAllowed operations binding.2) :
    EnvAllowed operations environment := by
  revert members
  induction environment with
  | nil => intro _; exact .nil
  | cons binding rest ih =>
      rcases binding with ⟨name, value⟩
      intro members
      exact .cons (members _ (List.mem_cons_self))
        (ih (fun entry member => members entry (List.mem_cons_of_mem _ member)))

theorem EnvAllowed.append {first second : Env Primitive}
    (earlier : EnvAllowed operations first) (later : EnvAllowed operations second) :
    EnvAllowed operations (first ++ second) := by
  revert earlier
  induction first with
  | nil => intro _; exact later
  | cons binding rest ih =>
      intro allowed
      cases allowed with
      | cons head tail => exact .cons head (ih tail)

theorem EnvAllowed.extend {base additions : Env Primitive}
    (original : EnvAllowed operations base) (added : EnvAllowed operations additions) :
    EnvAllowed operations (Env.extend base additions) := added.append original

theorem EnvAllowed.lookup {environment : Env Primitive} {name : Nat} {value : Value Primitive}
    (allowed : EnvAllowed operations environment) (found : Env.lookup environment name = some value) :
    ValueAllowed operations value := by
  revert allowed found
  induction environment with
  | nil => intro _ impossible; cases impossible
  | cons binding rest ih =>
      rcases binding with ⟨key, entry⟩
      intro allowed found
      cases allowed with
      | cons head tail =>
          by_cases same : name = key
          · subst name
            rw [Env.lookup_cons_eq] at found
            cases Option.some.inj found
            exact head
          · rw [Env.lookup_cons_ne name key entry rest same] at found
            exact ih tail found

theorem GroupAllowed.outer {group : Suspensions.Pure.Group Primitive}
    (allowed : GroupAllowed operations group) : EnvAllowed operations group.outer := by
  cases allowed with
  | mk _ _ environment => exact environment

theorem GroupAllowed.distinct {group : Suspensions.Pure.Group Primitive}
    (allowed : GroupAllowed operations group) : (group.bindings.map Prod.fst).Nodup := by
  cases allowed with
  | mk _ distinct _ => exact distinct

theorem GroupAllowed.rhs {group : Suspensions.Pure.Group Primitive} {name : Nat} {rhs : Rhs Primitive}
    (allowed : GroupAllowed operations group) (member : (name, rhs) ∈ group.bindings) :
    RhsAllowed operations rhs := by
  cases allowed with
  | mk definitions _ _ => exact definitions _ member

theorem GroupAllowed.definitions {group : Suspensions.Pure.Group Primitive}
    (allowed : GroupAllowed operations group) :
    NamedCodeAllowed operations (Rhs.toBindings group.bindings) := by
  apply NamedCodeAllowed.of_rhs
  rintro ⟨name, rhs⟩ member
  exact allowed.rhs member

/-- Decoding keeps exactly the original code and binder names; no evaluation
or closing operation is assumed by this source-to-descriptor connection. -/
theorem GroupAllowed.of_decoded {bindings : List (Nat × Core.Expr Primitive)}
    {decoded : List (Nat × Rhs Primitive)} {outer : Env Primitive}
    (code : NamedCodeAllowed operations bindings) (distinct : (bindings.map Prod.fst).Nodup)
    (decodedFrom : Rhs.ofBindings bindings = .ok decoded) (environment : EnvAllowed operations outer) :
    GroupAllowed operations (.mk decoded outer) := by
  have source := Rhs.toBindings_ofBindings decodedFrom
  rw [← source] at code distinct
  refine .mk ?_ ?_ environment
  · rintro ⟨name, rhs⟩ member
    exact code.rhs member
  · simpa only [Rhs.toBindings_names] using distinct

theorem RhsAllowed.instantiate {group : Suspensions.Pure.Group Primitive} {rhs : Rhs Primitive}
    (allowed : RhsAllowed operations rhs) (groupAllowed : GroupAllowed operations group) :
    ValueAllowed operations (rhs.instantiate group) := by
  cases rhs with
  | function clauses =>
      exact .closure ((RhsAllowed.function_iff clauses).mp allowed) groupAllowed.outer
        (.some groupAllowed)
  | delay body =>
      exact .suspension ((RhsAllowed.delay_iff body).mp allowed) groupAllowed.outer
        (.some groupAllowed)

theorem GroupAllowed.members {group : Suspensions.Pure.Group Primitive}
    (allowed : GroupAllowed operations group) : EnvAllowed operations group.members := by
  apply EnvAllowed.of_members
  intro entry member
  obtain ⟨binding, present, equal⟩ := List.mem_map.mp member
  rcases binding with ⟨name, rhs⟩
  subst entry
  exact (allowed.rhs (List.mem_reverse.mp present)).instantiate allowed

theorem bodyEnvironment_allowed {captured : Env Primitive}
    {recursive : Option (Suspensions.Pure.Group Primitive)}
    (environment : EnvAllowed operations captured) (group : OptionalGroupAllowed operations recursive) :
    EnvAllowed operations (bodyEnvironment captured recursive) := by
  cases group with
  | none => exact environment
  | some allowed => exact environment.extend allowed.members

inductive PrimitiveResultAllowed {Primitive : Type} (operations : Primitive → Prop) :
    Machine.PrimitiveResult Primitive → Prop
  | value {value : Value Primitive} (allowed : ValueAllowed operations value) :
      PrimitiveResultAllowed operations (.value value)
  | raised {packet : Value Primitive} (allowed : ValueAllowed operations packet) :
      PrimitiveResultAllowed operations (.raised packet)
  | stuck (fault : Machine.Fault) : PrimitiveResultAllowed operations (.stuck fault)

def OperationPreserves (operations : Primitive → Prop)
    (operation : Value Primitive → Machine.PrimitiveResult Primitive) : Prop :=
  ∀ input, ValueAllowed operations input → PrimitiveResultAllowed operations (operation input)

def ParametersPreserve (operations : Primitive → Prop) (parameters : Machine.Parameters Primitive) :
    Prop := ∀ operation, operations operation → OperationPreserves operations (parameters.primitive operation)

theorem PrimitiveResultAllowed.value_iff (value : Value Primitive) :
    PrimitiveResultAllowed operations (.value value) ↔ ValueAllowed operations value := by
  constructor
  · intro allowed
    cases allowed with
    | value represented => exact represented
  · exact .value

theorem PrimitiveResultAllowed.raised_iff (packet : Value Primitive) :
    PrimitiveResultAllowed operations (.raised packet) ↔ ValueAllowed operations packet := by
  constructor
  · intro allowed
    cases allowed with
    | raised represented => exact represented
  · exact .raised

/-- This holds for every selection of the basis tokens. Identity keeps the
allowed input, while the scalar operations introduce only atoms or a fault. -/
theorem basic_operation_preserves (selected : Compatibility.BasicOperation → Prop)
    (operation : Compatibility.BasicOperation) :
    OperationPreserves selected (Compatibility.basicPure operation) := by
  intro input allowed
  rcases Compatibility.basicPure_output_origin operation input with
    identity | ⟨atom, scalar⟩ | fault
  · rw [identity]
    exact .value allowed
  · rw [scalar]
    exact .value (.atom atom)
  · rw [fault]
    exact .stuck .primitive

theorem basic_parameters_preserve (selected : Compatibility.BasicOperation → Prop)
    (matchTag bindTag : Nat) :
    ParametersPreserve selected (Compatibility.basicPureParameters matchTag bindTag) :=
  fun operation _ => basic_operation_preserves selected operation

end Suspensions.Pure.Domain
