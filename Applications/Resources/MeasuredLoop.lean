import Applications.Resources.FoldCompiler
import SquareKit.Iteration

/-! Experimental finite loops with an explicit measured native baseline and a
small typed comparison layer over the existing scalar compiler. Costs count
supplied primitive charges, comparisons and one control visit per guard.
They do not describe host time, allocation or ordered primitive traces. -/
namespace Resources.MeasuredLoop
open FirstOrderCompiler Iteration

/-- Finite relational transport needs agreement only on related states. Validity
can be included in `R`; neither a decoder nor a global target rank is required. -/
theorem transport {α β : Type*} {p : α → Bool} {q : β → Bool}
    {f : α → α} {g : β → β} (R : α → β → Prop)
    (guard : ∀ x y, R x y → q y = p x)
    (step : ∀ x y, R x y → p x = false → R (f x) (g y))
    {x z : α} (h : UntilSpec p f x z) {y : β} (related : R x y) :
    ∃ w, UntilSpec q g y w ∧ R z w := by
  induction h generalizing y with
  | stop hp => exact ⟨y, .stop ((guard _ _ related).trans hp), related⟩
  | step hp _ ih =>
    obtain ⟨w, hw, hr⟩ := ih (step _ _ related hp)
    exact ⟨w, .step ((guard _ _ related).trans hp) hw, hr⟩

/-- Graph relations recover the existing functional finite-execution law. -/
theorem transport_map {α β : Type*} {p : α → Bool} {q : β → Bool}
    {f : α → α} {g : β → β} (e : α → β)
    (guard : ∀ x, q (e x) = p x)
    (step : ∀ x, p x = false → e (f x) = g (e x))
    {x z : α} (h : UntilSpec p f x z) : UntilSpec q g (e x) (e z) := by
  obtain ⟨w, hw, he⟩ := transport (fun a b => e a = b)
    (by intro a b hab; subst b; exact guard a)
    (by intro a b hab hp; subst b; exact step a hp) h rfl
  simpa [← he] using hw

/-- Erasure supplies a target rank only when it preserves continuing steps. -/
theorem rank_pullback {α β : Type*} (p : α → Bool) (q : β → Bool)
    (f : α → α) (g : β → β) (erase : β → α) (rank : α → Nat)
    (guard : ∀ y, p (erase y) = q y)
    (step : ∀ y, q y = false → erase (g y) = f (erase y))
    (decreases : ∀ x, p x = false → rank (f x) < rank x) :
    ∀ y, q y = false → rank (erase (g y)) < rank (erase y) := by
  intro y hy
  rw [step y hy]
  exact decreases _ ((guard y).trans hy)

/-- Counts actual continuing transitions, without using rank as a cost bound. -/
inductive Steps {α : Type*} (p : α → Bool) (f : α → α) : Nat → α → α → Prop
  | stop {x} : p x = true → Steps p f 0 x x
  | step {n x y} : p x = false → Steps p f n (f x) y → Steps p f (n+1) x y

theorem Steps.until {α : Type*} {p : α → Bool} {f : α → α} {n x y}
    (h : Steps p f n x y) : UntilSpec p f x y := by
  induction h with
  | stop hp => exact .stop hp
  | step hp _ ih => exact .step hp ih

def run {α : Type*} (guard : α → Measured Bool Nat) (body : α → Measured α Nat)
    (rank : α → Nat)
    (decreases : ∀ x, (guard x).1 = false → rank (body x).1 < rank x)
    (x : α) : Measured α Nat :=
  let test := guard x
  if h : test.1 = true then (x, test.2 + 1)
  else
    let next := body x
    let rest := run guard body rank decreases next.1
    (rest.1, test.2 + 1 + next.2 + rest.2)
termination_by rank x
decreasing_by
  apply decreases
  simpa only [Bool.not_eq_true] using h

/-- Exact bill includes the final successful test, even for zero iterations.
The extra unit per test is the declared control-dispatch tariff. -/
theorem run_of_steps {α : Type*} (guard : α → Measured Bool Nat)
    (body : α → Measured α Nat) (rank : α → Nat)
    (decreases : ∀ x, (guard x).1 = false → rank (body x).1 < rank x)
    (gc bc : Nat) (hg : ∀ x, (guard x).2 = gc) (hb : ∀ x, (body x).2 = bc)
    {n x y} (h : Steps (fun s => (guard s).1) (fun s => (body s).1) n x y) :
    run guard body rank decreases x = (y, (n+1)*(gc+1)+n*bc) := by
  induction h with
  | stop hp => rw [run]; simp [hp, hg]
  | step hp _ ih =>
    rw [run]
    simp only [hp, Bool.false_eq_true, ↓reduceDIte, ih, hg, hb]
    congr 1
    simp only [Nat.add_mul, Nat.one_mul]
    omega

/-- The native adapter returns the same state as the existing ranked executor. -/
theorem run_value {α : Type*} (guard : α → Measured Bool Nat)
    (body : α → Measured α Nat) (rank : α → Nat)
    (decreases : ∀ x, (guard x).1 = false → rank (body x).1 < rank x) (x : α) :
    (run guard body rank decreases x).1 =
      runUntil (fun s => (guard s).1) (fun s => (body s).1) rank decreases x := by
  have spec := runUntil_spec (fun s => (guard s).1) (fun s => (body s).1) rank decreases x
  generalize hout : runUntil (fun s => (guard s).1) (fun s => (body s).1) rank decreases x = y at spec ⊢
  clear hout
  induction spec with
  | stop hp => rw [run]; simp [hp]
  | step hp _ ih => rw [run]; simpa [hp] using ih

/-- Booleans remain in this comparison layer, not in the scalar type grammar. -/
structure Test (Prim : Ty → Ty → Type) (Γ : Ctx) where
  left : Term Prim Γ .base
  right : Term Prim Γ .base

namespace Test
variable {Prim : Ty → Ty → Type}
variable (meaning : {a b : Ty} → Prim a b → Val Nat a → Val Nat b)
variable (charge : {a b : Ty} → Prim a b → Nat)

def eval (t : Test Prim Γ) (ρ : Val Nat (context Γ)) : Bool :=
  decide (FirstOrderCompiler.eval meaning t.left ρ ≤ FirstOrderCompiler.eval meaning t.right ρ)

def compile (t : Test Prim Γ) (ρ : Val Nat (context Γ)) : Measured Bool Nat :=
  bind (FirstOrderCompiler.compile (FoldCompiler.scalar meaning charge) t.left ρ) fun l =>
  bind (FirstOrderCompiler.compile (FoldCompiler.scalar meaning charge) t.right ρ) fun r =>
  (decide (l ≤ r), 1)

def cost (t : Test Prim Γ) : Nat :=
  FoldCompiler.bodyCost charge t.left + FoldCompiler.bodyCost charge t.right + 1

theorem compile_eq (t : Test Prim Γ) (ρ : Val Nat (context Γ)) :
    compile meaning charge t ρ = (eval meaning t ρ, cost charge t) := by
  apply Prod.ext
  · simp only [compile, bind, eval]
    have hl : (FirstOrderCompiler.compile (FoldCompiler.scalar meaning charge) t.left ρ).1 =
        FirstOrderCompiler.eval meaning t.left ρ :=
      FirstOrderCompiler.compile_sound _ (FoldCompiler.scalarSound meaning charge) _ _
    have hr : (FirstOrderCompiler.compile (FoldCompiler.scalar meaning charge) t.right ρ).1 =
        FirstOrderCompiler.eval meaning t.right ρ :=
      FirstOrderCompiler.compile_sound _ (FoldCompiler.scalarSound meaning charge) _ _
    rw [hl, hr]
  · simp [compile, bind, FoldCompiler.scalar_cost, cost, Nat.add_assoc]
end Test

structure Program (Prim : Ty → Ty → Type) (input state output : Ty) where
  seed : Term Prim [input] state
  test : Test Prim [state]
  body : Term Prim [state] state
  post : Term Prim [state] output

namespace Program
variable {Prim : Ty → Ty → Type} {i s o : Ty}
variable (meaning : {a b : Ty} → Prim a b → Val Nat a → Val Nat b)
variable (charge : {a b : Ty} → Prim a b → Nat)
variable (p : Program Prim i s o)

def start (x : Val Nat i) := FirstOrderCompiler.eval meaning p.seed ((), x)
def done (x : Val Nat s) := p.test.eval meaning ((), x)
def step (x : Val Nat s) := FirstOrderCompiler.eval meaning p.body ((), x)
def finish (x : Val Nat s) := FirstOrderCompiler.eval meaning p.post ((), x)
def guard (x : Val Nat s) := p.test.compile meaning charge ((), x)
def compiledBody (x : Val Nat s) := FirstOrderCompiler.compile (FoldCompiler.scalar meaning charge) p.body ((), x)

@[simp] theorem guard_value (x : Val Nat s) : (guard meaning charge p x).1 = done meaning p x := by
  rw [guard, Test.compile_eq]; rfl
@[simp] theorem body_value (x : Val Nat s) : (compiledBody meaning charge p x).1 = step meaning p x :=
  FirstOrderCompiler.compile_sound _ (FoldCompiler.scalarSound meaning charge) p.body _

theorem targetDecrease (rank : Val Nat s → Nat)
    (decreases : ∀ x, done meaning p x = false → rank (step meaning p x) < rank x) :
    ∀ x, (guard meaning charge p x).1 = false → rank (compiledBody meaning charge p x).1 < rank x := by
  exact rank_pullback (done meaning p) (fun x => (guard meaning charge p x).1)
    (step meaning p) (fun x => (compiledBody meaning charge p x).1) id rank
    (by intro x; simp) (by intro x _; simp) decreases

/-- No target proof is supplied by a client: scalar laws discharge guard and
body compatibility, and source decrease justifies actual measured execution. -/
def execute (rank : Val Nat s → Nat)
    (decreases : ∀ x, done meaning p x = false → rank (step meaning p x) < rank x)
    (x : Val Nat i) : Measured (Val Nat o) Nat :=
  bind (FirstOrderCompiler.compile (FoldCompiler.scalar meaning charge) p.seed ((), x)) fun initial =>
  bind (run (guard meaning charge p) (compiledBody meaning charge p) rank
    (targetDecrease meaning charge p rank decreases) initial) fun final =>
  FirstOrderCompiler.compile (FoldCompiler.scalar meaning charge) p.post ((), final)

/-- A source finite execution determines the complete compiled bill and result. -/
theorem execute_of_steps (rank : Val Nat s → Nat)
    (decreases : ∀ x, done meaning p x = false → rank (step meaning p x) < rank x)
    (x : Val Nat i) {n y} (h : Steps (done meaning p) (step meaning p) n (start meaning p x) y) :
    execute meaning charge p rank decreases x =
      (finish meaning p y, FoldCompiler.bodyCost charge p.seed +
        ((n+1)*(Test.cost charge p.test+1)+n*FoldCompiler.bodyCost charge p.body) +
        FoldCompiler.bodyCost charge p.post) := by
  have hs : (FirstOrderCompiler.compile (FoldCompiler.scalar meaning charge) p.seed ((), x)).1 =
      start meaning p x := FirstOrderCompiler.compile_sound _ (FoldCompiler.scalarSound meaning charge) _ _
  have hr := run_of_steps (guard meaning charge p) (compiledBody meaning charge p) rank
    (targetDecrease meaning charge p rank decreases) (Test.cost charge p.test)
    (FoldCompiler.bodyCost charge p.body)
    (by intro z; simp [guard, Test.compile_eq])
    (by intro z; exact FoldCompiler.scalar_cost _ _ _ _) (by simpa only [guard_value, body_value] using h)
  simp only [execute, bind, hs, hr]
  apply Prod.ext
  · exact FirstOrderCompiler.compile_sound _ (FoldCompiler.scalarSound meaning charge) _ _
  · simp [FoldCompiler.scalar_cost, Nat.add_assoc]
end Program

/-- Step compatibility alone cannot preserve a finite stopping execution. -/
theorem guard_disagreement : UntilSpec (fun _ : Nat => true) id 0 0 ∧
    ¬ UntilSpec (fun _ : Nat => false) id 0 0 :=
  ⟨.stop rfl, identity_loop_has_no_result 0 0⟩
end Resources.MeasuredLoop
