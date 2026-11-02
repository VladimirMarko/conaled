import Applications.Suspensions.Syntax
import Applications.Suspensions.Store
import Applications.Progress.Evaluation
import Applications.Resources.Measured

/-!
# Local transitions for the suspension core

Forcing evaluates a stored body through ordinary machine transitions. A
successful return writes the cache before the caller's inner pattern runs.
Failure and exception continuations retain the state reached so far; there is
no blackhole marker, rollback, exception cache, or implicit total evaluation.
The independent source-rule correspondence is a separate layer.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.Machine

abbrev Memory (Primitive : Type) := State (Expr Primitive) (Env Primitive) (Value Primitive)

inductive Fault where
  | unboundVariable (name : Nat)
  | missingAddress (address : Nat)
  | expectedFunction
  | expectedBoolean
  | expectedAddress
  | expectedReferenceValue
  | expectedException
  | expectedRecord
  | expectedEmptyRecord
  | missingField (label : Nat)
  | invalidExceptionBinding (name : Nat)
  | invalidRecursiveRhs (name : Nat)
  | invalidContinuation
  | primitive
  deriving DecidableEq, Repr

inductive PrimitiveResult (Primitive : Type) where
  | value (result : Value Primitive)
  | raised (packet : Value Primitive)
  | stuck (fault : Fault)

/-- Operations alone: basis validity and source primitive laws remain separate. -/
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

structure Answer (Primitive : Type) where
  memory : Memory Primitive
  result : Result Primitive

inductive Control (Primitive : Type) where
  | eval (environment : Env Primitive) (expression : Expr Primitive)
  | value (result : Value Primitive)
  | raised (packet : Value Primitive)
  | pattern (environment : Env Primitive) (pattern : Pattern) (value : Value Primitive)
  | matched (bindings : Env Primitive)
  | mismatch
  | clauses (environment : Env Primitive)
      (clauses : List (Pattern × Expr Primitive)) (value : Value Primitive)
  | rows (environment : Env Primitive) (patterns : List (Nat × Pattern))
      (fields : List (Nat × Value Primitive)) (bindings : Env Primitive)
  | recursive (environment : Env Primitive) (bindings : List (Nat × Expr Primitive))
      (created : Env Primitive) (body : Expr Primitive)

inductive Frame (Primitive : Type) where
  | constructor (tag : Nat)
  | record (environment : Env Primitive) (label : Nat)
      (remaining : List (Nat × Expr Primitive)) (done : List (Nat × Value Primitive))
  | function (environment : Env Primitive) (argument : Expr Primitive)
  | argument (function : Value Primitive)
  | bindValue (environment : Env Primitive) (pattern : Pattern) (body : Expr Primitive)
  | bindMatch (environment : Env Primitive) (body : Expr Primitive)
  | branch (environment : Env Primitive) (yes no : Expr Primitive)
  | reference
  | read
  | assignReference (environment : Env Primitive) (value : Expr Primitive)
  | assignValue (reference : Value Primitive)
  | raise
  | handler (environment : Env Primitive) (clauses : List (Pattern × Expr Primitive))
  | handlerResult (original : Value Primitive)
  | applicationResult
  | clause (environment : Env Primitive) (body : Expr Primitive)
      (remaining : List (Pattern × Expr Primitive)) (value : Value Primitive)
  | memoize (address : Nat) (environment : Env Primitive) (inner : Pattern)
  | row (environment : Env Primitive) (remaining : List (Nat × Pattern))
      (fields : List (Nat × Value Primitive)) (earlier : Env Primitive)
  | layered (name : Nat) (value : Value Primitive)
  | recursive (environment : Env Primitive) (name : Nat)
      (remaining : List (Nat × Expr Primitive)) (created : Env Primitive)
      (body : Expr Primitive)

structure Config (Primitive : Type) where
  memory : Memory Primitive
  control : Control Primitive
  stack : List (Frame Primitive)

/-- Events record the transition taken, not a constant-time implementation claim. -/
inductive Event where
  | core
  | allocate (address : Nat)
  | body (address : Nat)
  | hit (address : Nat)
  | cacheWrite (address : Nat)
  | referenceRead (address : Nat)
  | referenceWrite (address : Nat)
  | freshException (name : Nat)
  deriving DecidableEq, Repr

variable {Primitive : Type}

def start (memory : Memory Primitive) (environment : Env Primitive)
    (expression : Expr Primitive) : Config Primitive := ⟨memory, .eval environment expression, []⟩

def startPattern (memory : Memory Primitive) (environment : Env Primitive)
    (pattern : Pattern) (value : Value Primitive) : Config Primitive :=
  ⟨memory, .pattern environment pattern value, []⟩

def addressRange (bindings : Env Primitive) : Finset Nat :=
  (bindings.filterMap fun (name, _) => match bindings.lookup name with
    | some (.address address) => some address
    | _ => none).toFinset

def freshExceptionName (memory : Memory Primitive) : Nat := memory.exceptionNames.sup id + 1

theorem freshExceptionName_fresh (memory : Memory Primitive) :
    freshExceptionName memory ∉ memory.exceptionNames := by
  intro present
  have bound : freshExceptionName memory ≤ memory.exceptionNames.sup id := Finset.le_sup (f := id) present
  unfold freshExceptionName at bound
  omega

def proceed (memory : Memory Primitive) (control : Control Primitive)
    (stack : List (Frame Primitive)) (event : Event := .core) :
    (Answer Primitive ⊕ Config Primitive) × Event :=
  (.inr ⟨memory, control, stack⟩, event)

def finish (memory : Memory Primitive) (result : Result Primitive) :
    (Answer Primitive ⊕ Config Primitive) × Event := (.inl ⟨memory, result⟩, .core)

/-- One explicit source-core transition, including continuation return/unwind. -/
def transition (parameters : Parameters Primitive) (config : Config Primitive) :
    (Answer Primitive ⊕ Config Primitive) × Event :=
  let s := config.memory
  let k := config.stack
  match config.control with
  | .eval env expression => match expression with
    | .atom a => proceed s (.value (.atom a)) k
    | .variable name => match env.lookup name with
      | some v => proceed s (.value v) k
      | none => finish s (.stuck (.unboundVariable name))
    | .primitive op => proceed s (.value (.primitive op)) k
    | .constructor tag none => proceed s (.value (.constructor tag none)) k
    | .constructor tag (some e) => proceed s (.eval env e) (.constructor tag :: k)
    | .record [] => proceed s (.value (.record [])) k
    | .record ((label, e) :: rest) =>
        proceed s (.eval env e) (.record env label rest [] :: k)
    | .function clauses => proceed s (.value (.closure clauses env [])) k
    | .apply f a => proceed s (.eval env f) (.function env a :: k)
    | .bind p e body => proceed s (.eval env e) (.bindValue env p body :: k)
    | .recursive bindings body => proceed s (.recursive env bindings [] body) k
    | .branch condition yes no => proceed s (.eval env condition) (.branch env yes no :: k)
    | .reference e => proceed s (.eval env e) (.reference :: k)
    | .read e => proceed s (.eval env e) (.read :: k)
    | .assign r e => proceed s (.eval env r) (.assignReference env e :: k)
    | .delay body =>
        let allocated := Suspensions.delay s body env
        proceed allocated.1 (.value (.address allocated.2)) k (.allocate allocated.2)
    | .raise e => proceed s (.eval env e) (.raise :: k)
    | .handle e clauses => proceed s (.eval env e) (.handler env clauses :: k)
    | .newException name body =>
        let tag := freshExceptionName s
        let next := {s with exceptionNames := insert tag s.exceptionNames}
        proceed next (.eval (Env.extend env [(name, .exception tag none)]) body) k
          (.freshException tag)
  | .value v => match k with
    | [] => finish s (.value v)
    | frame :: rest => match frame with
      | .constructor tag => proceed s (.value (.constructor tag (some v))) rest
      | .record env label remaining done =>
          let fields := done ++ [(label, v)]
          match remaining with
          | [] => proceed s (.value (.record fields)) rest
          | (nextLabel, e) :: remaining =>
              proceed s (.eval env e) (.record env nextLabel remaining fields :: rest)
      | .function env argument => proceed s (.eval env argument) (.argument v :: rest)
      | .argument f => match f with
        | .closure clauses env recursive =>
            proceed s (.clauses (Env.extend env (Env.rec recursive)) clauses v)
              (.applicationResult :: rest)
        | .primitive op => match parameters.primitive op v with
          | .value value => proceed s (.value value) rest
          | .raised packet => proceed s (.raised packet) rest
          | .stuck fault => finish s (.stuck fault)
        | .constructor tag none => proceed s (.value (.constructor tag (some v))) rest
        | .exception tag none => proceed s (.value (.exception tag (some v))) rest
        | _ => finish s (.stuck .expectedFunction)
      | .bindValue env p body => proceed s (.pattern env p v) (.bindMatch env body :: rest)
      | .branch env yes no => match v with
        | .atom (.boolean b) => proceed s (.eval env (if b then yes else no)) rest
        | _ => finish s (.stuck .expectedBoolean)
      | .reference =>
          let allocated := Suspensions.allocate s (.value v)
          proceed allocated.1 (.value (.address allocated.2)) rest (.allocate allocated.2)
      | .read => match v with
        | .address a => match s.memory a with
          | some (.value value) => proceed s (.value value) rest (.referenceRead a)
          | some (.thunk _ _) => finish s (.stuck .expectedReferenceValue)
          | none => finish s (.stuck (.missingAddress a))
        | _ => finish s (.stuck .expectedAddress)
      | .assignReference env e => proceed s (.eval env e) (.assignValue v :: rest)
      | .assignValue reference => match reference with
        | .address a => match s.memory a with
          | some (.value _) =>
              proceed (Suspensions.memoize s a v) (.value (.record [])) rest (.referenceWrite a)
          | some (.thunk _ _) => finish s (.stuck .expectedReferenceValue)
          | none => finish s (.stuck (.missingAddress a))
        | _ => finish s (.stuck .expectedAddress)
      | .raise => match v with
        | .exception _ _ => proceed s (.raised v) rest
        | _ => finish s (.stuck .expectedException)
      | .handler _ _ | .handlerResult _ | .applicationResult => proceed s (.value v) rest
      | .memoize a env inner =>
          proceed (Suspensions.memoize s a v) (.pattern env inner v) rest (.cacheWrite a)
      | .recursive env name remaining created body =>
          proceed s (.recursive env remaining (Env.extend created [(name, v)]) body) rest
      | _ => finish s (.stuck .invalidContinuation)
  | .raised packet => match k with
    | [] => finish s (.raised packet)
    | .handler env clauses :: rest =>
        proceed s (.clauses env clauses packet) (.handlerResult packet :: rest)
    | _ :: rest => proceed s (.raised packet) rest
  | .pattern env p v => match p with
    | .wildcard => proceed s (.matched []) k
    | .variable name => proceed s (.matched [(name, v)]) k
    | .atom a => match v with
      | .atom b => proceed s (if a = b then .matched [] else .mismatch) k
      | _ => proceed s .mismatch k
    | .constructor tag argument => match v, argument with
      | .constructor actual none, none =>
          proceed s (if tag = actual then .matched [] else .mismatch) k
      | .constructor actual (some value), some inner =>
          proceed s (if tag = actual then .pattern env inner value else .mismatch) k
      | _, _ => proceed s .mismatch k
    | .exception name argument => match env.lookup name with
      | some (.exception tag none) => match v, argument with
        | .exception actual none, none =>
            proceed s (if tag = actual then .matched [] else .mismatch) k
        | .exception actual (some value), some inner =>
            proceed s (if tag = actual then .pattern env inner value else .mismatch) k
        | _, _ => proceed s .mismatch k
      | _ => finish s (.stuck (.invalidExceptionBinding name))
    | .record patterns => match v, patterns with
      | .record [], [] => proceed s (.matched []) k
      | .record (_ :: _), [] => finish s (.stuck .expectedEmptyRecord)
      | .record fields, _ :: _ => proceed s (.rows env patterns fields []) k
      | _, _ => finish s (.stuck .expectedRecord)
    | .reference inner => match v with
      | .address a => match s.memory a with
        | some (.value value) => proceed s (.pattern env inner value) k (.referenceRead a)
        | some (.thunk _ _) => finish s (.stuck .expectedReferenceValue)
        | none => finish s (.stuck (.missingAddress a))
      | _ => finish s (.stuck .expectedAddress)
    | .suspended inner => match v with
      | .address a => match s.memory a with
        | some (.value value) => proceed s (.pattern env inner value) k (.hit a)
        | some (.thunk body captured) =>
            proceed s (.eval captured body) (.memoize a env inner :: k) (.body a)
        | none => finish s (.stuck (.missingAddress a))
      | _ => finish s (.stuck .expectedAddress)
    | .layered name inner => proceed s (.pattern env inner v) (.layered name v :: k)
  | .matched bindings => match k with
    | [] => finish s (.matched bindings)
    | .bindMatch env body :: rest => proceed s (.eval (Env.extend env bindings) body) rest
    | .clause env body _ _ :: rest => proceed s (.eval (Env.extend env bindings) body) rest
    | .row env remaining fields earlier :: rest =>
        proceed s (.rows env remaining fields (Env.extend earlier bindings)) rest
    | .layered name v :: rest => proceed s (.matched (Env.extend [(name, v)] bindings)) rest
    | _ => finish s (.stuck .invalidContinuation)
  | .mismatch => match k with
    | [] => finish s .mismatch
    | .clause env _ remaining v :: rest => proceed s (.clauses env remaining v) rest
    | .bindMatch _ _ :: rest => proceed s (.raised (.exception parameters.bindException none)) rest
    | .applicationResult :: rest =>
        proceed s (.raised (.exception parameters.matchException none)) rest
    | .handlerResult original :: rest => proceed s (.raised original) rest
    | .row _ _ _ _ :: rest | .layered _ _ :: rest => proceed s .mismatch rest
    | _ => finish s (.stuck .invalidContinuation)
  | .clauses env clauses v => match clauses with
    | [] => proceed s .mismatch k
    | (p, body) :: remaining =>
        proceed s (.pattern env p v) (.clause env body remaining v :: k)
  | .rows env patterns fields bindings => match patterns with
    | [] => proceed s (.matched bindings) k
    | (label, p) :: remaining => match Env.lookup fields label with
      | some v => proceed s (.pattern env p v) (.row env remaining fields bindings :: k)
      | none => finish s (.stuck (.missingField label))
  | .recursive env bindings created body => match bindings with
    | [] =>
        let recursive := Env.rec created
        let state := Suspensions.srec s (addressRange recursive) (fun captured => Env.extend captured recursive)
        proceed state (.eval (Env.extend env recursive) body) k
    | (name, e) :: remaining =>
        if recursiveRhs e then
          proceed s (.eval env e) (.recursive env name remaining created body :: k)
        else finish s (.stuck (.invalidRecursiveRhs name))

def step (parameters : Parameters Primitive) : Progress.Machine (Config Primitive) (Answer Primitive) :=
  fun config => (transition parameters config).1

/-- Singleton event lists compose through the existing ordered resource monoid. -/
def measuredStep (parameters : Parameters Primitive) (config : Config Primitive) :
    Resources.Measured (Answer Primitive ⊕ Config Primitive) (List Event) :=
  Resources.reweight (fun event => [event]) (transition parameters config)

theorem measuredStep_value (parameters : Parameters Primitive) (config : Config Primitive) :
    (measuredStep parameters config).1 = step parameters config := rfl

def tracedStep (parameters : Parameters Primitive) :
    Progress.Machine (Config Primitive × List Event) (Answer Primitive × List Event) :=
  fun (config, before) =>
    let result := measuredStep parameters config
    match result.1 with
    | .inl answer => .inl (answer, before ++ result.2)
    | .inr next => .inr (next, before ++ result.2)

theorem tracedStep_erases (parameters : Parameters Primitive)
    (input : Config Primitive × List Event) :
    Sum.map Prod.fst Prod.fst (tracedStep parameters input) = step parameters input.1 := by
  rcases input with ⟨config, before⟩
  rcases out : transition parameters config with ⟨next, event⟩
  cases next <;> simp [tracedStep, measuredStep, Resources.reweight, step, out]

/-- Event collection preserves the existing finite evaluation and transition count. -/
theorem traced_evaluates_erases {parameters : Parameters Primitive}
    {input : Config Primitive × List Event} {output : Answer Primitive × List Event} {steps : Nat}
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

theorem delay_transition (parameters : Parameters Primitive) (s : Memory Primitive)
    (env : Env Primitive) (body : Expr Primitive) (stack : List (Frame Primitive)) :
    transition parameters ⟨s, .eval env (.delay body), stack⟩ =
      let out := Suspensions.delay s body env
      proceed out.1 (.value (.address out.2)) stack (.allocate out.2) := rfl

theorem hit_transition (parameters : Parameters Primitive) (s : Memory Primitive)
    (env : Env Primitive) (inner : Pattern) (a : Nat) (v : Value Primitive)
    (stack : List (Frame Primitive)) (found : s.memory a = some (.value v)) :
    transition parameters ⟨s, .pattern env (.suspended inner) (.address a), stack⟩ =
      proceed s (.pattern env inner v) stack (.hit a) := by simp [transition, found]

theorem body_transition (parameters : Parameters Primitive) (s : Memory Primitive)
    (env captured : Env Primitive) (inner : Pattern) (a : Nat) (body : Expr Primitive)
    (stack : List (Frame Primitive)) (found : s.memory a = some (.thunk body captured)) :
    transition parameters ⟨s, .pattern env (.suspended inner) (.address a), stack⟩ =
      proceed s (.eval captured body) (.memoize a env inner :: stack) (.body a) := by
  simp [transition, found]

theorem memoize_before_match (parameters : Parameters Primitive) (s : Memory Primitive)
    (env : Env Primitive) (inner : Pattern) (a : Nat) (v : Value Primitive)
    (stack : List (Frame Primitive)) :
    transition parameters ⟨s, .value v, .memoize a env inner :: stack⟩ =
      proceed (Suspensions.memoize s a v) (.pattern env inner v) stack (.cacheWrite a) := rfl

theorem raised_skips_memoize (parameters : Parameters Primitive) (s : Memory Primitive)
    (env : Env Primitive) (inner : Pattern) (a : Nat) (packet : Value Primitive)
    (stack : List (Frame Primitive)) :
    transition parameters ⟨s, .raised packet, .memoize a env inner :: stack⟩ =
      proceed s (.raised packet) stack := rfl

theorem failed_clause_retains_state (parameters : Parameters Primitive) (s : Memory Primitive)
    (env : Env Primitive) (body : Expr Primitive) (remaining : List (Pattern × Expr Primitive))
    (v : Value Primitive) (stack : List (Frame Primitive)) :
    transition parameters ⟨s, .mismatch, .clause env body remaining v :: stack⟩ =
      proceed s (.clauses env remaining v) stack := rfl

end Suspensions.Core.Machine
