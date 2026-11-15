import SquareKit.StaticFunctionCost
import Applications.FRP.RegionalSpace

/-! Compile the finite static-function fragment once, then execute its residual
circuit. State is the preceding mapped pair, with arbitrary restart values. -/
namespace FRPSpec.StaticFunctionReactive
open FirstOrderCompiler Applications.Circuits Progress.Feedback StaticFunction

abbrev pairTy : Ty := .prod .base .base
abbrev Pair := Bool × Bool

def literal (b : Bool) : Term Gate Γ .base := .prim (.constant b) .unit
def identityBody : Term Gate (.base :: Γ) .base := .var .here
def negationBody : Term Gate (.base :: Γ) .base := .prim (.not 0) (.var .here)
def maskBody (mask : Bool) : Term Gate (.base :: Γ) .base :=
  .prim (.xor 0 0) (.pair (.var .here) (literal mask))

/-- A finite sequence of static function parameters. Captures in these closed
unary bodies are explicit literals; runtime inputs are supplied separately. -/
abbrev StaticBody := Term Gate [.base] .base

def liftBody (body : StaticBody) : Term Gate (.base :: Γ) .base :=
  Term.rename (fun v => by cases v with | here => exact .here | there v => nomatch v) body

theorem liftBody_correct (body : StaticBody) (ρ : Val Bool (context Γ)) (x : Bool) :
    eval Gate.meaning (liftBody body) (ρ,x) = eval Gate.meaning body ((),x) := by
  apply Term.eval_rename
  intro a v
  cases v with
  | here => rfl
  | there v => nomatch v

def stages (bodies : List StaticBody) (input : Expr Gate Γ pairTy) : Expr Gate Γ pairTy :=
  match bodies with
  | [] => input
  | body :: rest => stages rest (.mapPair (liftBody body) input)

/-- Ordinary functional source, independent of syntax substitution and circuits. -/
def nativeMap (bodies : List StaticBody) (x : Pair) : Pair :=
  match bodies with
  | [] => x
  | body :: rest => nativeMap rest
      (eval Gate.meaning body ((),x.1),eval Gate.meaning body ((),x.2))

theorem stages_correct (bodies : List StaticBody) (input : Expr Gate Γ pairTy)
    (ρ : Val Bool (context Γ)) :
    (stages bodies input).meaning Gate.meaning ρ = nativeMap bodies (input.meaning Gate.meaning ρ) := by
  induction bodies generalizing input with
  | nil => rfl
  | cons body rest ih => simp only [stages, ih, Expr.meaning, liftBody_correct (Γ := Γ), nativeMap]

def seed (s : Pair) : Term Gate [] pairTy := .pair (literal s.1) (literal s.2)
def stagedBody (bodies : List StaticBody) : Expr Gate [pairTy,pairTy] (.prod pairTy pairTy) :=
  .pair (.value (.var (.there .here))) (stages bodies (.value (.var .here)))

def program (bodies : List StaticBody) (initial : Pair) : Indefinite.Program pairTy pairTy pairTy :=
  Indefinite.Program.compiled (ReactiveCompiler.compile Circuit.target (seed initial) (measured (stagedBody bodies)).1)

def native (bodies : List StaticBody) (initial : Pair) : Initialized Pair Pair Pair :=
  ⟨fun (x,s) => (s,nativeMap bodies x),initial⟩

theorem machine_correct (bodies : List StaticBody) (initial : Pair) :
    (program bodies initial).machine = native bodies initial := by
  unfold program
  rw [measured_correct]
  rw [Indefinite.Program.compiled_source]
  unfold ReactiveCompiler.source native
  congr 1
  funext xs
  rcases xs with ⟨x,s⟩
  change eval Gate.meaning (stagedBody bodies).residual (((),s),x) = _
  rw [Expr.residual_correct]
  simp only [stagedBody, Expr.meaning, eval, lookup, stages_correct]

/-- Every suffix and every current continuation, not only the seeded run. -/
theorem run_correct (bodies : List StaticBody) (initial current : Pair) (xs : List Pair) :
    run (program bodies initial).machine.mealy current xs = run (native bodies initial).mealy current xs := by
  rw [machine_correct]

/-- This applies to any producer with a proved value boundary, whether or not
that producer internally supports functions or sums. -/
theorem boundary_correct {A : Type} (producer oracle : A → Pair)
    (h : ∀ x, producer x = oracle x) (bodies : List StaticBody) (initial current : Pair) (x : A) :
    (program bodies initial).machine.step (producer x,current) =
      (current,nativeMap bodies (oracle x)) := by
  rw [machine_correct, h]; rfl

/-- Actual circuit adapter, included in every resource claim below. -/
def duplicate : Circuit .base pairTy := .pair .identity .identity

def regionalMachine (bodies : List StaticBody) (initial : Pair) : Initialized Regional.Input Pair Pair :=
  let compiled := program bodies initial
  ⟨fun (x,s) => compiled.body.execute (duplicate.execute (Regional.Rich.execute x),s),initial⟩

def regionalStep (bodies : List StaticBody) (initial : Pair) (x : Regional.Input) (s : Pair) : Pair × Pair :=
  (regionalMachine bodies initial).step (x,s)

theorem regional_correct (bodies : List StaticBody) (initial s : Pair) (x : Regional.Input) :
    regionalStep bodies initial x s = (s,nativeMap bodies (Regional.Rich.oracle x,Regional.Rich.oracle x)) := by
  exact boundary_correct (fun x => duplicate.execute (Regional.Rich.execute x))
    (fun x => (Regional.Rich.oracle x,Regional.Rich.oracle x))
    (fun x => by simp only [duplicate, Circuit.execute, Regional.Rich.correct]) bodies initial s x

inductive Request where
  | static (bodies : List StaticBody) (initial : Pair)
  | dynamicFunction (value : Bool → Bool)
  | escapingEnvironment (capture : Bool) (closure : Bool → Bool → Bool)
  | opaqueNative

inductive Status where
  | accepted | rejectedCapacity | unsupported
  deriving DecidableEq, Repr

/-- Selected requirements are consumed here: only statically supplied bodies
with finite first-order state are sent to the circuit backend. -/
inductive Admission (capacity : Nat) where
  | accepted (executable : Indefinite.Program pairTy pairTy pairTy)
      (fits : cells pairTy + executable.body.arena ≤ capacity)
  | rejectedCapacity (required : Nat) (exceeds : capacity < required)
  | unsupported

def assess (request : Request) (capacity : Nat) : Admission capacity :=
  match request with
  | .static bodies initial =>
      if h : cells pairTy + (program bodies initial).body.arena ≤ capacity then
        .accepted (program bodies initial) h
      else .rejectedCapacity _ (Nat.lt_of_not_ge h)
  | _ => .unsupported

def Admission.status : Admission capacity → Status
  | .accepted _ _ => .accepted
  | .rejectedCapacity _ _ => .rejectedCapacity
  | .unsupported => .unsupported

/-- Execution consumes the stored admitted circuit and its seed. `some current`
resumes a continuation; `none` starts at the stored seed. Negative outcomes
contain no executor and return no execution result. -/
def Admission.execute (selection : Admission capacity) (current : Option Pair)
    (inputs : List Pair) : Option (List Pair × Pair) :=
  match selection with
  | .accepted executable _ => some (run executable.machine.mealy
      (current.getD executable.initial) inputs)
  | .rejectedCapacity _ _ | .unsupported => none

/-- The bound belongs to the same stored executor used by `execute`. -/
theorem stored_uniform (executable : Indefinite.Program pairTy pairTy pairTy)
    (fits : cells pairTy + executable.body.arena ≤ capacity)
    (input : Progress.Stream Pair) (n k : Nat) :
    Indefinite.Program.retained (Progress.Feedback.state executable.machine input n) +
      (executable.body.allocations.take k).sum ≤ capacity :=
  (executable.uniform input n k).trans fits

theorem selected_execution (bodies : List StaticBody) (initial : Pair) (capacity : Nat)
    (fits : cells pairTy + (program bodies initial).body.arena ≤ capacity)
    (current : Option Pair) (inputs : List Pair) :
    (assess (.static bodies initial) capacity).execute current inputs =
      some (run (native bodies initial).mealy (current.getD initial) inputs) := by
  simp only [assess, fits, ↓reduceDIte, Admission.execute]
  have hm := machine_correct bodies initial
  have hi : (program bodies initial).initial = initial := congrArg Initialized.initial hm
  rw [hi, hm]

theorem negative_nonexecution (selection : Admission capacity)
    (negative : selection.status ≠ .accepted) (current : Option Pair) (inputs : List Pair) :
    selection.execute current inputs = none := by
  cases selection <;> simp_all [Admission.status, Admission.execute]

theorem admitted_iff (bodies : List StaticBody) (initial : Pair) (capacity : Nat) :
    (assess (.static bodies initial) capacity).status = .accepted ↔
      cells pairTy + (program bodies initial).body.arena ≤ capacity := by
  simp only [assess]; split <;> simp_all [Admission.status]

/-- Bounded service follows from the actual compiled executor and accepted
capacity, rather than from the source's semantic theorem alone. -/
theorem admitted_uniform (bodies : List StaticBody) (initial : Pair) (capacity : Nat)
    (accepted : (assess (.static bodies initial) capacity).status = .accepted)
    (input : Progress.Stream Pair) (n k : Nat) :
    Indefinite.Program.retained (Progress.Feedback.state (program bodies initial).machine input n) +
      ((program bodies initial).body.allocations.take k).sum ≤ capacity :=
  ((program bodies initial).uniform input n k).trans ((admitted_iff bodies initial capacity).mp accepted)

theorem dynamic_unsupported (capacity : Nat) (f : Bool → Bool)
    (capture : Bool) (closure : Bool → Bool → Bool) :
    (assess (.dynamicFunction f) capacity).status = .unsupported ∧
    (assess (.escapingEnvironment capture closure) capacity).status = .unsupported := ⟨rfl,rfl⟩

/-- The composed executor retains both region arenas until tick completion.
Boundary copies allocate one Boolean and one pair, even though the host may
share them. This conservative trace makes no inter-region reclamation claim. -/
inductive RegionalExecutes (bodies : List StaticBody) (initial : Pair) (x : Regional.Input) (s : Pair) :
    Pair × Pair → Nat → List Nat → Prop where
  | tick {b : Bool} {pair : Pair} {result : Pair × Pair} {w : Nat} {trace : List Nat}
      (richWork : Regional.Rich.Executes Regional.Rich.code ((),x) b w)
      (richSpace : Regional.Rich.Allocates Regional.Rich.code ((),x) b trace)
      (adapter : Circuit.Executes duplicate b pair duplicate.work duplicate.arena)
      (consumer : Circuit.Executes (program bodies initial).body (pair,s) result
        (program bodies initial).body.work (program bodies initial).body.arena) :
      RegionalExecutes bodies initial x s result
        (w + 1 + duplicate.work + 2 + (program bodies initial).body.work)
        (trace ++ [1] ++ duplicate.allocations ++ [2] ++ (program bodies initial).body.allocations)

def regionalAllocations (bodies : List StaticBody) (initial : Pair) (x : Regional.Input) : List Nat :=
  Regional.Rich.allocations Regional.Rich.code ((),x) ++ [1] ++ duplicate.allocations ++ [2] ++
    (program bodies initial).body.allocations

theorem regional_executes (bodies : List StaticBody) (initial s : Pair) (x : Regional.Input) :
    RegionalExecutes bodies initial x s (regionalStep bodies initial x s)
      (Regional.Rich.dispatches Regional.Rich.code ((),x) + 1 + duplicate.work + 2 +
        (program bodies initial).body.work) (regionalAllocations bodies initial x) :=
  .tick (Regional.Rich.executes _ Regional.Rich.code_analyzable _)
    (Regional.Rich.allocates _ Regional.Rich.code_analyzable _) (duplicate.executes _)
    ((program bodies initial).body.executes _)

def regionalStorage (bodies : List StaticBody) (initial : Pair) : Nat :=
  2 + 3 + Regional.Rich.arena Regional.Rich.code + 1 + duplicate.arena + 2 +
    (program bodies initial).body.arena

theorem regional_uniform (bodies : List StaticBody) (initial : Pair) (x : Regional.Input) (k : Nat) :
    2 + 3 + ((regionalAllocations bodies initial x).take k).sum ≤ regionalStorage bodies initial := by
  have hp := Regional.take_sum_le (regionalAllocations bodies initial x) k
  have hr := Regional.Rich.allocations_le Regional.Rich.code ((),x)
  simp only [regionalAllocations, List.sum_append, List.sum_cons, List.sum_nil,
    Circuit.allocations_sum] at hp
  unfold regionalStorage regionalAllocations
  omega

end FRPSpec.StaticFunctionReactive
