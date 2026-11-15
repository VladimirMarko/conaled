import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Nat.Cast.Basic
import Applications.Resources.FIFOContracts
import Applications.Resources.Persistent.History
import Applications.Resources.Persistent.Realization

/-! A FIFO client that executes a stem once and retains its version for two
independent suffixes. Costs count the declared structural visits, initialization
and endpoint observations, not host allocation or elapsed time. -/
namespace Resources.Persistent.FIFOClient
open Sequences.AbstractFIFO Resources.FIFOContracts
universe u
variable {α Q : Type u}

structure Result (α Q : Type u) where
  retained : Q
  left : Q
  right : Q
  observations : Option α × Option α

/-- Both suffixes start from the retained stem result, not from each other.
Each endpoint head costs one unit. Acquiring the supplied input is external. -/
def execute {ops : Ops α Q} (m : Instrumentation ops)
    (stem left right : List (Command α)) (q : Q) : Measured (Result α Q) Nat :=
  let p := Resources.run m.measured stem q
  let l := Resources.run m.measured left p.1
  let r := Resources.run m.measured right p.1
  (⟨p.1, l.1, r.1, (ops.head l.1, ops.head r.1)⟩, p.2 + l.2 + r.2 + 2)

/-- Initialization of the empty queue is charged once. No hidden conversion from
an ordinary input list is performed. -/
def fromEmpty {ops : Ops α Q} (m : Instrumentation ops)
    (stem left right : List (Command α)) : Measured (Result α Q) Nat :=
  Resources.bind (ops.empty, 1) (execute m stem left right)

theorem execute_cost {ops : Ops α Q} (m : Instrumentation ops)
    (stem left right : List (Command α)) (q : Q) :
    (execute m stem left right q).2 =
      (Resources.run m.measured stem q).2 +
      (Resources.run m.measured left (Resources.run m.measured stem q).1).2 +
      (Resources.run m.measured right (Resources.run m.measured stem q).1).2 + 2 := rfl

/-- The old version and both branch results have independent ordinary-list
meanings. The representation proof is reused for both branch observations. -/
theorem observations {ops : Ops α Q} {m : Instrumentation ops}
    {decode : Q → List α}
    (correct : Simulation ops (lists α) (fun q xs => decode q = xs))
    (stem left right : List (Command α)) (q : Q) :
    let input := Sequences.AbstractFIFO.run (lists α) stem (decode q)
    decode (execute m stem left right q).1.retained = input ∧
    decode (execute m stem left right q).1.left =
      Sequences.AbstractFIFO.run (lists α) left input ∧
    decode (execute m stem left right q).1.right =
      Sequences.AbstractFIFO.run (lists α) right input ∧
    (execute m stem left right q).1.observations =
      (client (lists α) left input, client (lists α) right input) := by
  dsimp only [execute]
  simp only [run_erases]
  have hp := correct.run_preserves stem (q := q) (r := decode q) rfl
  refine ⟨hp, correct.run_preserves left hp, correct.run_preserves right hp, ?_⟩
  exact Prod.ext (correct.client_eq left hp) (correct.client_eq right hp)

/-- A signed exact boundary follows from the shared mapped potential theorem.
The extra fork potential is essential: both suffixes can spend it. -/
theorem signed_boundary {ops : Ops α Q} (m : Instrumentation ops)
    (potential : Q → Int) (stem left right : List (Command α)) (q : Q) :
    let p := Resources.run m.measured stem q
    let l := Resources.run m.measured left p.1
    let r := Resources.run m.measured right p.1
    let charge := fun c s => (m.measured c s).2 + potential (m.measured c s).1 - potential s
    ((execute m stem left right q).2 : Int) + potential l.1 + potential r.1 =
      potential q + potential p.1 +
      budget m.measured charge stem q + budget m.measured charge left p.1 +
      budget m.measured charge right p.1 + 2 := by
  dsimp only
  have hp := budget_amortized m.measured potential (Nat.castAddMonoidHom Int) stem q
  have hl := budget_amortized m.measured potential (Nat.castAddMonoidHom Int)
    left (Resources.run m.measured stem q).1
  have hr := budget_amortized m.measured potential (Nat.castAddMonoidHom Int)
    right (Resources.run m.measured stem q).1
  simp only [Nat.coe_castAddMonoidHom] at hp hl hr
  rw [execute_cost]
  push_cast
  omega

def credit (q : ValidQueue α) : Nat := 2 * SymmetricCosts.potential q.val

private theorem symmetric_run_boundary (cs : List (Command α)) (q : ValidQueue α) :
    (Resources.run symmetricMeasure.measured cs q).2 +
      credit (Resources.run symmetricMeasure.measured cs q).1 ≤ credit q + 8 * cs.length := by
  apply run_constant_charge symmetricMeasure.measured credit 8
  intro c s
  exact SymmetricCosts.execute_work_potential (commandOperation c) s.val

/-- This bound is for the actual strict branch executions. It does not treat
repeated use of an immutable root as memoization of its operations. -/
theorem symmetric_bound (stem left right : List (Command α)) (q : ValidQueue α) :
    (execute symmetricMeasure stem left right q).2 +
      credit (execute symmetricMeasure stem left right q).1.left +
      credit (execute symmetricMeasure stem left right q).1.right ≤
      credit q + credit (execute symmetricMeasure stem left right q).1.retained +
      8 * (stem.length + left.length + right.length) + 2 := by
  have hp := symmetric_run_boundary stem q
  have hl := symmetric_run_boundary left (Resources.run symmetricMeasure.measured stem q).1
  have hr := symmetric_run_boundary right (Resources.run symmetricMeasure.measured stem q).1
  simp only [execute]
  omega

theorem symmetric_fromEmpty_bound (stem left right : List (Command α)) :
    (fromEmpty symmetricMeasure stem left right).2 ≤
      credit (fromEmpty symmetricMeasure stem left right).1.retained +
      8 * (stem.length + left.length + right.length) + 3 := by
  have h := symmetric_bound stem left right (validOps : Ops α (ValidQueue α)).empty
  have hz : credit (validOps : Ops α (ValidQueue α)).empty = 0 := rfl
  simp only [hz] at h
  simp only [fromEmpty, Resources.bind]
  omega

/-- Three distinct block occurrences, even when the two suffix words are equal. -/
inductive Phase where
  | stem | left | right
  deriving DecidableEq

inductive Use : Phase → Phase → Type where
  | left : Use .stem .left
  | right : Use .stem .right

instance : Quiver Phase := ⟨Use⟩

theorem prefix_in_left_history : Phase.stem ∈ history Phase.left :=
  history_of_edge Use.left

theorem prefix_in_right_history : Phase.stem ∈ history Phase.right :=
  history_of_edge Use.right

theorem right_not_in_left_history : Phase.right ∉ history Phase.left := by
  intro h
  have absent : ∀ w, (Phase.right ⟶ w) → False := by
    intro w edge
    cases edge
  have impossible : Phase.right = Phase.left := history_eq_of_no_outgoing absent h
  cases impossible

theorem complete_history_closed : HistoryClosed ({.stem, .left, .right} : Finset Phase) := by
  intro v _ u _
  cases u <;> simp

/-- Actual input and output versions for the three operation blocks. -/
def blockInput {ops : Ops α Q} (m : Instrumentation ops)
    (stem : List (Command α)) : Phase → Q
  | .stem => ops.empty
  | .left | .right => (Resources.run m.measured stem ops.empty).1

def blockOutput {ops : Ops α Q} (m : Instrumentation ops)
    (stem left right : List (Command α)) : Phase → Q
  | .stem => (Resources.run m.measured stem ops.empty).1
  | .left => (Resources.run m.measured left (blockInput m stem .left)).1
  | .right => (Resources.run m.measured right (blockInput m stem .right)).1

/-- Every argument-use edge in this history is realized by the actual input
version of its consumer. Equal outputs do not identify the two occurrences. -/
theorem use_input {ops : Ops α Q} (m : Instrumentation ops)
    (stem left right : List (Command α)) {before after : Phase} (use : Use before after) :
    blockInput m stem after = blockOutput m stem left right before := by
  cases use <;> rfl

/-- The block interpreter is priced from the actual queue runs. Initialization
belongs to the stem occurrence; each branch includes its endpoint head. -/
def blockWork {ops : Ops α Q} (m : Instrumentation ops)
    (stem left right : List (Command α)) : Phase → Nat
  | .stem => 1 + (Resources.run m.measured stem ops.empty).2
  | .left => (Resources.run m.measured left
      (Resources.run m.measured stem ops.empty).1).2 + 1
  | .right => (Resources.run m.measured right
      (Resources.run m.measured stem ops.empty).1).2 + 1

/-- This strict client has no shared evaluation debits. Its history shares the
input version; its realization still pays for every branch execution. -/
theorem realization_cost {ops : Ops α Q} (m : Instrumentation ops)
    (stem left right : List (Command α)) :
    (Resources.run (realizeStep (blockWork m stem left right)
      (fun _ => (∅ : Finset Nat))) [.stem, .left, .right] ∅).2 =
      (fromEmpty m stem left right).2 := by
  rw [realize_run_cost]
  simp [realizationSupport, blockWork, fromEmpty, execute, Resources.bind]
  omega

end Resources.Persistent.FIFOClient
