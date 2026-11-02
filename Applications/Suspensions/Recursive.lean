import Applications.Suspensions.AddressRange
import Applications.Suspensions.Prefix

/-!
# Actual creation and closing of recursive function/suspension bindings

Only the existing `RecursiveRhs` forms are permitted: function closures and
delayed expressions. This creation phase never evaluates a function body or a
delayed body. Its fold follows the machine's actual three transitions per
permitted binding. A rejected raw right side retains the reached memory and
the machine fault; it does not roll earlier allocations back.

The invariant on effective address bindings derives the unforced-thunk premise
needed by the source SRec rule. Closing then satisfies a componentwise source
relation and occurs in the actual machine execution. Captured environments
may contain cycles; there is no fixed-point axiom or address-order restriction
on values inside those environments.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Core.Recursive
open Machine
variable {Primitive : Type}

def Permitted (bindings : List (Nat × Expr Primitive)) : Prop :=
  List.Forall (fun binding => RecursiveRhs binding.2) bindings

theorem permitted_cons (name : Nat) (rhs : Expr Primitive)
    (rest : List (Nat × Expr Primitive)) :
    Permitted ((name, rhs) :: rest) ↔ RecursiveRhs rhs ∧ Permitted rest :=
  List.forall_cons _ _ _

/-- The original environment is used for every simultaneous right side.
Collected bindings are made recursively visible only by the later close. -/
def create (memory : Memory Primitive) (environment : Env Primitive)
    (bindings : List (Nat × Expr Primitive)) (created : Env Primitive := []) :
    Except (Answer Primitive) (Memory Primitive × Env Primitive) :=
  match bindings with
  | [] => .ok (memory, created)
  | (name, rhs) :: rest => match rhs with
    | .function clauses =>
        create memory environment rest
          (Env.extend created [(name, .closure clauses environment [])])
    | .delay code =>
        let allocated := Suspensions.delay memory code environment
        create allocated.1 environment rest
          (Env.extend created [(name, .address allocated.2)])
    | _ => .error ⟨memory, .stuck (.invalidRecursiveRhs name)⟩

theorem create_nil (memory : Memory Primitive) (environment created : Env Primitive) :
    create memory environment [] created = .ok (memory, created) := rfl

theorem create_function (memory : Memory Primitive) (environment : Env Primitive)
    (name : Nat) (clauses : List (Pattern × Expr Primitive))
    (rest : List (Nat × Expr Primitive)) (created : Env Primitive) :
    create memory environment ((name, .function clauses) :: rest) created =
      create memory environment rest
        (Env.extend created [(name, .closure clauses environment [])]) := rfl

theorem create_delay (memory : Memory Primitive) (environment : Env Primitive)
    (name : Nat) (code : Expr Primitive) (rest : List (Nat × Expr Primitive))
    (created : Env Primitive) :
    create memory environment ((name, .delay code) :: rest) created =
      create (Suspensions.delay memory code environment).1 environment rest
        (Env.extend created [(name, .address (Suspensions.delay memory code environment).2)]) := rfl

/-- Address-valued effective bindings point to unforced thunks. Shadowed list
entries do not determine the environment lookup or the SRec target set. -/
def CreatedThunks (memory : Memory Primitive) (created : Env Primitive) : Prop :=
  ∀ name address, Env.lookup created name = some (.address address) →
    ∃ code captured, memory.memory address = some (.thunk code captured)

theorem CreatedThunks.nil (memory : Memory Primitive) : CreatedThunks memory [] := by
  intro name address found
  cases found

theorem CreatedThunks.mono {before after : Memory Primitive} {created : Env Primitive}
    (old : CreatedThunks before created)
    (retained : Durability.Extends before.memory after.memory) : CreatedThunks after created := by
  intro name address found
  obtain ⟨code, captured, lookup⟩ := old name address found
  exact ⟨code, captured, retained _ _ lookup⟩

theorem CreatedThunks.cons {memory : Memory Primitive} {created : Env Primitive}
    (old : CreatedThunks memory created) (name : Nat) (value : Value Primitive)
    (installed : ∀ address, value = .address address →
      ∃ code captured, memory.memory address = some (.thunk code captured)) :
    CreatedThunks memory (Env.extend created [(name, value)]) := by
  intro key address found
  change Env.lookup ((name, value) :: created) key = some (.address address) at found
  by_cases same : key = name
  · subst key
    rw [Env.lookup_cons_eq] at found
    exact installed address (Option.some.inj found)
  · rw [Env.lookup_cons_ne key name value created same] at found
    exact old key address found

theorem CreatedThunks.targets {memory : Memory Primitive} {created : Env Primitive}
    (held : CreatedThunks memory created) :
    Suspensions.RecursiveTargets memory (addressRange (Env.rec created)) := by
  intro address inside
  rw [addressRange_rec] at inside
  obtain ⟨name, found⟩ := (mem_addressRange created address).mp inside
  exact held name address found

/-- Permitted creation always finishes, independently of what its unexecuted
bodies would do. This is a finite syntax/creation fact, not body termination. -/
theorem create_exists (memory : Memory Primitive) (environment : Env Primitive)
    (bindings : List (Nat × Expr Primitive)) (created : Env Primitive)
    (permitted : Permitted bindings) :
    ∃ result, create memory environment bindings created = .ok result := by
  revert permitted
  induction bindings generalizing memory created with
  | nil => intro _; exact ⟨(memory, created), rfl⟩
  | cons binding rest ih =>
      rcases binding with ⟨name, rhs⟩
      intro permitted
      obtain ⟨allowed, remaining⟩ := (permitted_cons name rhs rest).mp permitted
      cases allowed with
      | function clauses =>
          simpa only [create_function] using
            ih (memory := memory)
              (created := Env.extend created [(name, .closure clauses environment [])]) remaining
      | delay code =>
          simpa only [create_delay] using
            ih (memory := (Suspensions.delay memory code environment).1)
              (created := Env.extend created
                [(name, .address (Suspensions.delay memory code environment).2)]) remaining

/-- Extension is valid for this creation phase alone: it performs only fresh
allocation. SRec's later environment replacements have their own relation. -/
theorem create_preserves {memory : Memory Primitive} {environment : Env Primitive}
    {bindings : List (Nat × Expr Primitive)} {created : Env Primitive}
    {result : Memory Primitive × Env Primitive} (permitted : Permitted bindings)
    (bounded : Suspensions.Bounded memory) (held : CreatedThunks memory created)
    (made : create memory environment bindings created = .ok result) :
    Suspensions.Bounded result.1 ∧ CreatedThunks result.1 result.2 ∧
      Durability.Extends memory.memory result.1.memory := by
  revert permitted bounded held made
  induction bindings generalizing memory created result with
  | nil =>
      intro _ bounded held made
      rw [create_nil] at made
      have equal : (memory, created) = result := Except.ok.inj made
      subst result
      exact ⟨bounded, held, Durability.Extends.refl _⟩
  | cons binding rest ih =>
      rcases binding with ⟨name, rhs⟩
      intro permitted bounded held made
      obtain ⟨allowed, remaining⟩ := (permitted_cons name rhs rest).mp permitted
      cases allowed with
      | function clauses =>
          have extended : CreatedThunks memory
              (Env.extend created [(name, .closure clauses environment [])]) :=
            held.cons name (.closure clauses environment []) (by
              intro address impossible
              cases impossible)
          rw [create_function] at made
          exact ih remaining bounded extended made
      | delay code =>
          let allocated := Suspensions.delay memory code environment
          have valid : Suspensions.Bounded allocated.1 :=
            Suspensions.delay_bounded bounded code environment
          have extension : Durability.Extends memory.memory allocated.1.memory :=
            Suspensions.allocate_extends bounded (.thunk code environment)
          have retained : CreatedThunks allocated.1 created := held.mono extension
          have extended : CreatedThunks allocated.1
              (Env.extend created [(name, .address allocated.2)]) :=
            retained.cons name (.address allocated.2) (by
              intro address equal
              have same : allocated.2 = address := Value.address.inj equal
              subst address
              exact ⟨code, environment, Suspensions.delay_captures memory code environment⟩)
          rw [create_delay] at made
          obtain ⟨finalBounded, finalThunks, tailExtension⟩ :=
            ih remaining valid extended made
          exact ⟨finalBounded, finalThunks, extension.trans tailExtension⟩

def closeMemory (memory : Memory Primitive) (created : Env Primitive) : Memory Primitive :=
  Suspensions.srec memory (addressRange (Env.rec created))
    (fun captured => Env.extend captured (Env.rec created))

def closeEnvironment (environment created : Env Primitive) : Env Primitive :=
  Env.extend environment (Env.rec created)

/-- The source SRec conditions, stated without the implementation operation.
The unforced-thunk premise is part of applicability and must be established. -/
structure Closes (before : Memory Primitive) (created : Env Primitive)
    (after : Memory Primitive) : Prop where
  ready : Suspensions.RecursiveTargets before (addressRange (Env.rec created))
  exceptionNames : after.exceptionNames = before.exceptionNames
  domain : ∀ address, (after.memory address).isSome = (before.memory address).isSome
  outside : ∀ address, address ∉ addressRange (Env.rec created) →
    after.memory address = before.memory address
  thunks : ∀ address code captured, address ∈ addressRange (Env.rec created) →
    before.memory address = some (.thunk code captured) →
    after.memory address = some (.thunk code (Env.extend captured (Env.rec created)))

theorem close_correct {memory : Memory Primitive} {created : Env Primitive}
    (ready : Suspensions.RecursiveTargets memory (addressRange (Env.rec created))) :
    Closes memory created (closeMemory memory created) where
  ready := ready
  exceptionNames := Suspensions.srec_exceptionNames _ _ _
  domain address := Suspensions.srec_isSome _ _ _ address
  outside _ outside := Suspensions.srec_other _ _ _ outside
  thunks _ _ _ inside found := Suspensions.srec_thunk _ inside found

theorem close_bounded {memory : Memory Primitive} (bounded : Suspensions.Bounded memory)
    (created : Env Primitive) : Suspensions.Bounded (closeMemory memory created) :=
  Suspensions.srec_bounded bounded _ _

theorem close_next (memory : Memory Primitive) (created : Env Primitive) :
    (closeMemory memory created).next = memory.next := rfl

private theorem observe_after_prefix {parameters : Parameters Primitive}
    {config next : Config Primitive} {budget : Nat}
    (first : Prefix.observe parameters budget config = .inr next) (extra : Nat) :
    Prefix.observe parameters (budget + extra) config = Prefix.observe parameters extra next := by
  unfold Prefix.observe at first ⊢
  rw [Nat.add_comm budget extra, Function.iterate_add_apply, first]

private theorem function_creation_prefix (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (name : Nat) (clauses : List (Pattern × Expr Primitive))
    (rest : List (Nat × Expr Primitive)) (created : Env Primitive) (body : Expr Primitive)
    (stack : List (Frame Primitive)) :
    Prefix.observe parameters 3
        ⟨memory, .recursive environment ((name, .function clauses) :: rest) created body, stack⟩ =
      .inr ⟨memory, .recursive environment rest
        (Env.extend created [(name, .closure clauses environment [])]) body, stack⟩ := rfl

private theorem delay_creation_prefix (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (name : Nat) (code : Expr Primitive)
    (rest : List (Nat × Expr Primitive)) (created : Env Primitive) (body : Expr Primitive)
    (stack : List (Frame Primitive)) :
    Prefix.observe parameters 3
        ⟨memory, .recursive environment ((name, .delay code) :: rest) created body, stack⟩ =
      let allocated := Suspensions.delay memory code environment
      .inr ⟨allocated.1, .recursive environment rest
        (Env.extend created [(name, .address allocated.2)]) body, stack⟩ := rfl

/-- The creation fold is the actual machine prefix, with no body evaluator
hidden inside it. The residual control has not yet performed SRec. -/
theorem create_prefix {parameters : Parameters Primitive} {memory : Memory Primitive}
    {environment : Env Primitive} {bindings : List (Nat × Expr Primitive)}
    {created : Env Primitive} {result : Memory Primitive × Env Primitive}
    (permitted : Permitted bindings)
    (made : create memory environment bindings created = .ok result)
    (body : Expr Primitive) (stack : List (Frame Primitive)) :
    Prefix.observe parameters (3 * bindings.length)
        ⟨memory, .recursive environment bindings created body, stack⟩ =
      .inr ⟨result.1, .recursive environment [] result.2 body, stack⟩ := by
  revert permitted made
  induction bindings generalizing memory created result with
  | nil =>
      intro _ made
      rw [create_nil] at made
      have equal : (memory, created) = result := Except.ok.inj made
      subst result
      rfl
  | cons binding rest ih =>
      rcases binding with ⟨name, rhs⟩
      intro permitted made
      obtain ⟨allowed, remaining⟩ := (permitted_cons name rhs rest).mp permitted
      have count : 3 * ((name, rhs) :: rest).length = 3 + 3 * rest.length := by
        simp only [List.length_cons]
        omega
      cases allowed with
      | function clauses =>
          rw [create_function] at made
          have first := function_creation_prefix parameters memory environment name clauses rest created body stack
          rw [count, observe_after_prefix first (3 * rest.length)]
          exact ih remaining made
      | delay code =>
          rw [create_delay] at made
          have first := delay_creation_prefix parameters memory environment name code rest created body stack
          rw [count, observe_after_prefix first (3 * rest.length)]
          exact ih remaining made

/-- Closing is the final creation transition of the concrete recursive rule. -/
theorem enter_body_prefix {parameters : Parameters Primitive} {memory : Memory Primitive}
    {environment : Env Primitive} {bindings : List (Nat × Expr Primitive)}
    {result : Memory Primitive × Env Primitive} (permitted : Permitted bindings)
    (made : create memory environment bindings [] = .ok result) (body : Expr Primitive) :
    Prefix.observe parameters (3 * bindings.length + 2)
        (start memory environment (.recursive bindings body)) =
      .inr (start (closeMemory result.1 result.2) (closeEnvironment environment result.2) body) := by
  have first : Prefix.observe parameters 1 (start memory environment (.recursive bindings body)) =
      .inr ⟨memory, .recursive environment bindings [] body, []⟩ := rfl
  have middle := create_prefix (parameters := parameters) permitted made body []
  have selected := (observe_after_prefix first (3 * bindings.length)).trans middle
  have last : Prefix.observe parameters 1 ⟨result.1, .recursive environment [] result.2 body, []⟩ =
      .inr (start (closeMemory result.1 result.2) (closeEnvironment environment result.2) body) := rfl
  have entered := (observe_after_prefix selected 1).trans last
  have count : (1 + 3 * bindings.length) + 1 = 3 * bindings.length + 2 := by omega
  simpa only [count] using entered

private theorem evaluates_after_prefix {parameters : Parameters Primitive}
    {config next : Config Primitive} {budget : Nat} {answer : Answer Primitive} {steps : Nat}
    (prefix : Prefix.observe parameters budget config = .inr next)
    (tail : Progress.Evaluates (step parameters) next answer steps) :
    Progress.Evaluates (step parameters) config answer (budget + steps) := by
  induction budget generalizing config with
  | zero =>
      have equal : config = next := Sum.inr.inj prefix
      subst config
      simpa only [Nat.zero_add] using tail
  | succ budget ih =>
      cases moved : step parameters config with
      | inl stopped =>
          rw [Prefix.observe_succ, moved, Prefix.iterate_answer] at prefix
          cases prefix
      | inr following =>
          have rest : Prefix.observe parameters budget following = .inr next := by
            simpa only [Prefix.observe_succ, moved] using prefix
          have continued := Progress.Evaluates.next moved (ih rest)
          have count : (budget + steps) + 1 = (budget + 1) + steps := by omega
          simpa only [count] using continued

/-- If the recursive body has a finite evaluation, the actual expression has
that same reached answer after its explicit creation/closing prefix. -/
theorem evaluates_from_body {parameters : Parameters Primitive} {memory : Memory Primitive}
    {environment : Env Primitive} {bindings : List (Nat × Expr Primitive)}
    {result : Memory Primitive × Env Primitive} {body : Expr Primitive}
    {answer : Answer Primitive} {steps : Nat} (permitted : Permitted bindings)
    (made : create memory environment bindings [] = .ok result)
    (evaluation : Progress.Evaluates (step parameters)
      (start (closeMemory result.1 result.2) (closeEnvironment environment result.2) body) answer steps) :
    Progress.Evaluates (step parameters) (start memory environment (.recursive bindings body))
      answer (3 * bindings.length + 2 + steps) :=
  evaluates_after_prefix (enter_body_prefix permitted made body) evaluation

/-- The source applicability premise follows from actual allowed creation.
Both the SRec relation and the reached machine state are conclusions. -/
theorem realizes_recursive_binding (parameters : Parameters Primitive) (memory : Memory Primitive)
    (environment : Env Primitive) (bindings : List (Nat × Expr Primitive)) (body : Expr Primitive)
    (permitted : Permitted bindings) (bounded : Suspensions.Bounded memory) :
    ∃ result,
      create memory environment bindings [] = .ok result ∧
      Suspensions.Bounded result.1 ∧
      Closes result.1 result.2 (closeMemory result.1 result.2) ∧
      Prefix.observe parameters (3 * bindings.length + 2)
          (start memory environment (.recursive bindings body)) =
        .inr (start (closeMemory result.1 result.2) (closeEnvironment environment result.2) body) := by
  obtain ⟨result, made⟩ := create_exists memory environment bindings [] permitted
  obtain ⟨valid, thunks, _retained⟩ :=
    create_preserves permitted bounded (CreatedThunks.nil memory) made
  exact ⟨result, made, valid, close_correct thunks.targets, enter_body_prefix permitted made body⟩

end Suspensions.Core.Recursive
