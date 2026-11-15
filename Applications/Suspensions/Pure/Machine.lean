import Applications.Suspensions.Pure.Value
import Applications.Progress.Evaluation
import Applications.Resources.Measured

/-!
# Explicit evaluation without a suspension cache

This auxiliary interpretation uses the same source expressions and patterns as
the heap machine. A suspension is finite code, capture and a recursive group
descriptor. Every suspended pattern enters that body; normal return resumes
the inner pattern under its caller environment, without writing a cache.

Reference operations, reference patterns and fresh exception declarations are
explicitly outside this interpretation. Fixed exception packets and handlers
remain. Primitive operations are parameters; their eventual relationship to
heap-machine primitives is a separate obligation.

Every transition contributes one positive unit to `Progress.Evaluates`. Group
validation and member construction are local mathematical operations, so that
count is neither the heap-machine count nor a host-runtime bound. The body-entry
event retains its complete finite meaning. No adequacy, termination or absence
of recursive forcing is asserted here.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure.Machine

inductive ExcludedEffect where
  | reference
  | read
  | assign
  | referencePattern
  | newException
  deriving DecidableEq, Repr

inductive Fault where
  | unboundVariable (name : Nat)
  | expectedFunction
  | expectedBoolean
  | expectedSuspension
  | expectedException
  | expectedRecord
  | expectedEmptyRecord
  | missingField (label : Nat)
  | invalidExceptionBinding (name : Nat)
  | invalidRecursiveRhs (name : Nat)
  | invalidContinuation
  | excludedEffect (effect : ExcludedEffect)
  | primitive
  deriving DecidableEq, Repr

inductive PrimitiveResult (Primitive : Type) where
  | value (result : Value Primitive)
  | raised (packet : Value Primitive)
  | stuck (fault : Fault)

/-- Operations only. Effect and interpretation laws are supplied separately. -/
structure Parameters (Primitive : Type) where
  primitive : Primitive → Value Primitive → PrimitiveResult Primitive
  matchException : Nat
  bindException : Nat

inductive Result (Primitive : Type) where
  | value (result : Value Primitive)
  | raised (packet : Value Primitive)
  | matched (bindings : Env Primitive)
  | mismatch
  | stuck (fault : Fault)

inductive Control (Primitive : Type) where
  | eval (environment : Env Primitive) (expression : Core.Expr Primitive)
  | value (result : Value Primitive)
  | raised (packet : Value Primitive)
  | pattern (environment : Env Primitive) (pattern : Core.Pattern) (value : Value Primitive)
  | matched (bindings : Env Primitive)
  | mismatch
  | clauses (environment : Env Primitive)
      (clauses : List (Core.Pattern × Core.Expr Primitive)) (value : Value Primitive)
  | rows (environment : Env Primitive) (patterns : List (Nat × Core.Pattern))
      (fields : List (Nat × Value Primitive)) (bindings : Env Primitive)

inductive Frame (Primitive : Type) where
  | constructor (tag : Nat)
  | record (environment : Env Primitive) (label : Nat)
      (remaining : List (Nat × Core.Expr Primitive)) (done : List (Nat × Value Primitive))
  | function (environment : Env Primitive) (argument : Core.Expr Primitive)
  | argument (function : Value Primitive)
  | bindValue (environment : Env Primitive) (pattern : Core.Pattern) (body : Core.Expr Primitive)
  | bindMatch (environment : Env Primitive) (body : Core.Expr Primitive)
  | branch (environment : Env Primitive) (yes no : Core.Expr Primitive)
  | raise
  | handler (environment : Env Primitive) (clauses : List (Core.Pattern × Core.Expr Primitive))
  | handlerResult (original : Value Primitive)
  | applicationResult
  | clause (environment : Env Primitive) (body : Core.Expr Primitive)
      (remaining : List (Core.Pattern × Core.Expr Primitive)) (value : Value Primitive)
  | force (environment : Env Primitive) (inner : Core.Pattern)
  | row (environment : Env Primitive) (remaining : List (Nat × Core.Pattern))
      (fields : List (Nat × Value Primitive)) (earlier : Env Primitive)
  | layered (name : Nat) (value : Value Primitive)

structure Config (Primitive : Type) where
  control : Control Primitive
  stack : List (Frame Primitive)

/-- The body identity includes the descriptor, not an allocation identifier. -/
inductive Event (Primitive : Type) where
  | core
  | body (expression : Core.Expr Primitive) (captured : Env Primitive)
      (recursive : Option (Group Primitive))

variable {Primitive : Type}

def start (environment : Env Primitive) (expression : Core.Expr Primitive) : Config Primitive :=
  ⟨.eval environment expression, []⟩

def startPattern (environment : Env Primitive) (pattern : Core.Pattern)
    (value : Value Primitive) : Config Primitive := ⟨.pattern environment pattern value, []⟩

def proceed (control : Control Primitive) (stack : List (Frame Primitive))
    (event : Event Primitive := .core) :
    (Result Primitive ⊕ Config Primitive) × Event Primitive := (.inr ⟨control, stack⟩, event)

def finish (result : Result Primitive) :
    (Result Primitive ⊕ Config Primitive) × Event Primitive := (.inl result, .core)

/-- One explicit transition; evaluating a suspension body is never hidden here. -/
def transition (parameters : Parameters Primitive) (config : Config Primitive) :
    (Result Primitive ⊕ Config Primitive) × Event Primitive :=
  let k := config.stack
  match config.control with
  | .eval env expression => match expression with
    | .atom a => proceed (.value (.atom a)) k
    | .variable name => match Env.lookup env name with
      | some v => proceed (.value v) k
      | none => finish (.stuck (.unboundVariable name))
    | .primitive op => proceed (.value (.primitive op)) k
    | .constructor tag none => proceed (.value (.constructor tag none)) k
    | .constructor tag (some e) => proceed (.eval env e) (.constructor tag :: k)
    | .record [] => proceed (.value (.record [])) k
    | .record ((label, e) :: rest) => proceed (.eval env e) (.record env label rest [] :: k)
    | .function clauses => proceed (.value (.closure clauses env none)) k
    | .apply f a => proceed (.eval env f) (.function env a :: k)
    | .bind p e body => proceed (.eval env e) (.bindValue env p body :: k)
    | .recursive bindings body => match Rhs.ofBindings bindings with
      | .error name => finish (.stuck (.invalidRecursiveRhs name))
      | .ok definitions =>
          let group := Group.mk definitions env
          proceed (.eval (bodyEnvironment env (some group)) body) k
    | .branch condition yes no => proceed (.eval env condition) (.branch env yes no :: k)
    | .reference _ => finish (.stuck (.excludedEffect .reference))
    | .read _ => finish (.stuck (.excludedEffect .read))
    | .assign _ _ => finish (.stuck (.excludedEffect .assign))
    | .delay body => proceed (.value (.suspension body env none)) k
    | .raise e => proceed (.eval env e) (.raise :: k)
    | .handle e clauses => proceed (.eval env e) (.handler env clauses :: k)
    | .newException _ _ => finish (.stuck (.excludedEffect .newException))
  | .value v => match k with
    | [] => finish (.value v)
    | frame :: rest => match frame with
      | .constructor tag => proceed (.value (.constructor tag (some v))) rest
      | .record env label remaining done =>
          let fields := done ++ [(label, v)]
          match remaining with
          | [] => proceed (.value (.record fields)) rest
          | (nextLabel, e) :: remaining =>
              proceed (.eval env e) (.record env nextLabel remaining fields :: rest)
      | .function env argument => proceed (.eval env argument) (.argument v :: rest)
      | .argument f => match f with
        | .closure clauses captured recursive =>
            proceed (.clauses (bodyEnvironment captured recursive) clauses v)
              (.applicationResult :: rest)
        | .primitive op => match parameters.primitive op v with
          | .value value => proceed (.value value) rest
          | .raised packet => proceed (.raised packet) rest
          | .stuck fault => finish (.stuck fault)
        | .constructor tag none => proceed (.value (.constructor tag (some v))) rest
        | .exception tag none => proceed (.value (.exception tag (some v))) rest
        | _ => finish (.stuck .expectedFunction)
      | .bindValue env p body => proceed (.pattern env p v) (.bindMatch env body :: rest)
      | .branch env yes no => match v with
        | .atom (.boolean b) => proceed (.eval env (if b then yes else no)) rest
        | _ => finish (.stuck .expectedBoolean)
      | .raise => match v with
        | .exception _ _ => proceed (.raised v) rest
        | _ => finish (.stuck .expectedException)
      | .handler _ _ | .handlerResult _ | .applicationResult => proceed (.value v) rest
      | .force env inner => proceed (.pattern env inner v) rest
      | _ => finish (.stuck .invalidContinuation)
  | .raised packet => match k with
    | [] => finish (.raised packet)
    | .handler env clauses :: rest =>
        proceed (.clauses env clauses packet) (.handlerResult packet :: rest)
    | _ :: rest => proceed (.raised packet) rest
  | .pattern env p v => match p with
    | .wildcard => proceed (.matched []) k
    | .variable name => proceed (.matched [(name, v)]) k
    | .atom a => match v with
      | .atom b => proceed (if a = b then .matched [] else .mismatch) k
      | _ => proceed .mismatch k
    | .constructor tag argument => match v, argument with
      | .constructor actual none, none =>
          proceed (if tag = actual then .matched [] else .mismatch) k
      | .constructor actual (some value), some inner =>
          proceed (if tag = actual then .pattern env inner value else .mismatch) k
      | _, _ => proceed .mismatch k
    | .exception name argument => match Env.lookup env name with
      | some (.exception tag none) => match v, argument with
        | .exception actual none, none =>
            proceed (if tag = actual then .matched [] else .mismatch) k
        | .exception actual (some value), some inner =>
            proceed (if tag = actual then .pattern env inner value else .mismatch) k
        | _, _ => proceed .mismatch k
      | _ => finish (.stuck (.invalidExceptionBinding name))
    | .record patterns => match v, patterns with
      | .record [], [] => proceed (.matched []) k
      | .record (_ :: _), [] => finish (.stuck .expectedEmptyRecord)
      | .record fields, _ :: _ => proceed (.rows env patterns fields []) k
      | _, _ => finish (.stuck .expectedRecord)
    | .reference _ => finish (.stuck (.excludedEffect .referencePattern))
    | .suspended inner => match v with
      | .suspension body captured recursive =>
          proceed (.eval (bodyEnvironment captured recursive) body) (.force env inner :: k)
            (.body body captured recursive)
      | _ => finish (.stuck .expectedSuspension)
    | .layered name inner => proceed (.pattern env inner v) (.layered name v :: k)
  | .matched bindings => match k with
    | [] => finish (.matched bindings)
    | .bindMatch env body :: rest => proceed (.eval (Env.extend env bindings) body) rest
    | .clause env body _ _ :: rest => proceed (.eval (Env.extend env bindings) body) rest
    | .row env remaining fields earlier :: rest =>
        proceed (.rows env remaining fields (Env.extend earlier bindings)) rest
    | .layered name v :: rest => proceed (.matched (Env.extend [(name, v)] bindings)) rest
    | _ => finish (.stuck .invalidContinuation)
  | .mismatch => match k with
    | [] => finish .mismatch
    | .clause env _ remaining v :: rest => proceed (.clauses env remaining v) rest
    | .bindMatch _ _ :: rest => proceed (.raised (.exception parameters.bindException none)) rest
    | .applicationResult :: rest => proceed (.raised (.exception parameters.matchException none)) rest
    | .handlerResult original :: rest => proceed (.raised original) rest
    | .row _ _ _ _ :: rest | .layered _ _ :: rest => proceed .mismatch rest
    | _ => finish (.stuck .invalidContinuation)
  | .clauses env clauses v => match clauses with
    | [] => proceed .mismatch k
    | (p, body) :: remaining => proceed (.pattern env p v) (.clause env body remaining v :: k)
  | .rows env patterns fields bindings => match patterns with
    | [] => proceed (.matched bindings) k
    | (label, p) :: remaining => match Env.lookup fields label with
      | some v => proceed (.pattern env p v) (.row env remaining fields bindings :: k)
      | none => finish (.stuck (.missingField label))

def step (parameters : Parameters Primitive) : Progress.Machine (Config Primitive) (Result Primitive) :=
  fun config => (transition parameters config).1

def measuredStep (parameters : Parameters Primitive) (config : Config Primitive) :
    Resources.Measured (Result Primitive ⊕ Config Primitive) (List (Event Primitive)) :=
  Resources.reweight (fun event => [event]) (transition parameters config)

theorem measuredStep_value (parameters : Parameters Primitive) (config : Config Primitive) :
    (measuredStep parameters config).1 = step parameters config := rfl

def tracedStep (parameters : Parameters Primitive) :
    Progress.Machine (Config Primitive × List (Event Primitive))
      (Result Primitive × List (Event Primitive)) :=
  fun (config, before) =>
    let result := measuredStep parameters config
    match result.1 with
    | .inl answer => .inl (answer, before ++ result.2)
    | .inr next => .inr (next, before ++ result.2)

/-- Extract exact body meanings without an equality decision on source code. -/
def bodyEntries (events : List (Event Primitive)) :
    List (Core.Expr Primitive × Env Primitive × Option (Group Primitive)) :=
  events.filterMap fun
    | .core => none
    | .body expression captured recursive => some (expression, captured, recursive)

theorem tracedStep_erases (parameters : Parameters Primitive)
    (input : Config Primitive × List (Event Primitive)) :
    Sum.map Prod.fst Prod.fst (tracedStep parameters input) = step parameters input.1 := by
  rcases input with ⟨config, before⟩
  rcases out : transition parameters config with ⟨next, event⟩
  cases next <;> simp [tracedStep, measuredStep, Resources.reweight, step, out]

theorem traced_evaluates_erases {parameters : Parameters Primitive}
    {input : Config Primitive × List (Event Primitive)}
    {output : Result Primitive × List (Event Primitive)} {steps : Nat}
    (evaluation : Progress.Evaluates (tracedStep parameters) input output steps) :
    Progress.Evaluates (step parameters) input.1 output.1 steps := by
  induction evaluation with
  | @done input output finished =>
      apply Progress.Evaluates.done
      exact (tracedStep_erases parameters input).symm.trans
        (congrArg (Sum.map Prod.fst Prod.fst) finished)
  | @next input next output steps moved _ ih =>
      apply Progress.Evaluates.next
      · exact (tracedStep_erases parameters input).symm.trans
          (congrArg (Sum.map Prod.fst Prod.fst) moved)
      · exact ih

theorem tracedStep_length (parameters : Parameters Primitive)
    (input : Config Primitive × List (Event Primitive)) :
    (match tracedStep parameters input with
      | .inl answer => answer.2.length
      | .inr next => next.2.length) = input.2.length + 1 := by
  rcases input with ⟨config, before⟩
  rcases out : transition parameters config with ⟨next, event⟩
  cases next <;> simp [tracedStep, measuredStep, Resources.reweight, out]

/-- All transitions are counted, including ordinary continuation returns. -/
theorem traced_evaluates_length {parameters : Parameters Primitive}
    {input : Config Primitive × List (Event Primitive)}
    {output : Result Primitive × List (Event Primitive)} {steps : Nat}
    (evaluation : Progress.Evaluates (tracedStep parameters) input output steps) :
    output.2.length = input.2.length + steps := by
  induction evaluation with
  | @done input output finished =>
      simpa only [finished] using tracedStep_length parameters input
  | @next input next output steps moved _ ih =>
      have length : next.2.length = input.2.length + 1 := by
        simpa only [moved] using tracedStep_length parameters input
      omega

theorem evaluates_positive {parameters : Parameters Primitive} {input : Config Primitive}
    {output : Result Primitive} {steps : Nat}
    (evaluation : Progress.Evaluates (step parameters) input output steps) : 0 < steps := by
  cases evaluation <;> omega

theorem delay_transition (parameters : Parameters Primitive) (env : Env Primitive)
    (body : Core.Expr Primitive) (stack : List (Frame Primitive)) :
    transition parameters ⟨.eval env (.delay body), stack⟩ =
      proceed (.value (.suspension body env none)) stack := rfl

theorem body_transition (parameters : Parameters Primitive) (env captured : Env Primitive)
    (recursive : Option (Group Primitive)) (inner : Core.Pattern) (body : Core.Expr Primitive)
    (stack : List (Frame Primitive)) :
    transition parameters ⟨.pattern env (.suspended inner) (.suspension body captured recursive), stack⟩ =
      proceed (.eval (bodyEnvironment captured recursive) body) (.force env inner :: stack)
        (.body body captured recursive) := rfl

theorem body_return (parameters : Parameters Primitive) (env : Env Primitive)
    (inner : Core.Pattern) (value : Value Primitive) (stack : List (Frame Primitive)) :
    transition parameters ⟨.value value, .force env inner :: stack⟩ =
      proceed (.pattern env inner value) stack := rfl

theorem body_exception (parameters : Parameters Primitive) (env : Env Primitive)
    (inner : Core.Pattern) (packet : Value Primitive) (stack : List (Frame Primitive)) :
    transition parameters ⟨.raised packet, .force env inner :: stack⟩ =
      proceed (.raised packet) stack := rfl

theorem recursive_transition (parameters : Parameters Primitive) (env : Env Primitive)
    (definitions : List (Nat × Rhs Primitive)) (body : Core.Expr Primitive)
    (stack : List (Frame Primitive)) :
    transition parameters ⟨.eval env (.recursive (Rhs.toBindings definitions) body), stack⟩ =
      proceed (.eval (bodyEnvironment env (some (.mk definitions env))) body) stack := by
  simp [transition]

end Suspensions.Pure.Machine
