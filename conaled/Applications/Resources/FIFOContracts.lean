import Applications.Sequences.AbstractFIFO
import Applications.Resources.SymmetricCosts

/-! Public FIFO budgets with existential implementation accounting witnesses.
The endpoint head observation is uncharged. -/
namespace Resources.FIFOContracts
open Sequences.AbstractFIFO
universe u
variable {α Q : Type u}

structure Instrumentation (ops : Ops α Q) where
  measured : Command α → Q → Measured Q Nat
  erases : ∀ c q, (measured c q).1 = step ops c q

def abstractBudget (profile : Command α → List α → Nat) :=
  budget (fun c xs => (step (lists α) c xs, 0)) profile

structure Accounting (ops : Ops α Q) (m : Instrumentation ops)
    (decode : Q → List α) (profile : Command α → List α → Nat)
    (initialized : Q → Nat → Prop) : Prop where
  behavior : Simulation ops (lists α) (fun q xs => decode q = xs)
  /-- The witness is an implementation obligation; no formula is a client parameter. -/
  certificate : ∃ potential : Q → Nat,
    (∀ q credit, initialized q credit → potential q ≤ credit) ∧
    (∀ c q, (m.measured c q).2 + potential (m.measured c q).1 ≤
      potential q + profile c (decode q))

theorem run_erases {ops : Ops α Q} (m : Instrumentation ops)
    (cs : List (Command α)) (q : Q) :
    (Resources.run m.measured cs q).1 = Sequences.AbstractFIFO.run ops cs q := by
  induction cs generalizing q with
  | nil => rfl
  | cons c cs ih => simp only [Resources.run, bind, Sequences.AbstractFIFO.run, ih, m.erases]

theorem budget_abstract {ops : Ops α Q} (m : Instrumentation ops) (decode : Q → List α)
    (h : Simulation ops (lists α) (fun q xs => decode q = xs))
    (profile : Command α → List α → Nat) (cs : List (Command α)) (q : Q) :
    budget m.measured (fun c q => profile c (decode q)) cs q =
      abstractBudget profile cs (decode q) := by
  induction cs generalizing q with
  | nil => rfl
  | cons c cs ih =>
    have hs : decode (step ops c q) = step (lists α) c (decode q) := by
      cases c with
      | enqueue x => exact h.snoc x q (decode q) rfl
      | delete => exact h.tail q (decode q) rfl
    change decode (step ops c q) = step (lists α) c (decode q) at hs
    simp only [budget, abstractBudget, ih, m.erases, hs]

/-- One public bound, with neither an implementation potential nor its final value
in the caller's statement. Behavior and resource conclusions remain separate. -/
theorem client_bound {ops : Ops α Q} {m : Instrumentation ops} {decode : Q → List α}
    {profile : Command α → List α → Nat} {initialized : Q → Nat → Prop}
    (h : Accounting ops m decode profile initialized)
    (cs : List (Command α)) (q : Q) (credit : Nat) (hi : initialized q credit) :
    (Resources.run m.measured cs q).2 ≤ credit + abstractBudget profile cs (decode q) := by
  obtain ⟨potential, initial, hstep⟩ := h.certificate
  have hr := run_potential m.measured (fun c q => profile c (decode q)) potential hstep cs q
  rw [budget_abstract m decode h.behavior] at hr
  have hb := initial q credit hi
  omega

/-- Cost-blind word clients cannot distinguish any two instrumentations. -/
theorem cost_noninterference {ops : Ops α Q} (m n : Instrumentation ops)
    (cs : List (Command α)) (q : Q) :
    ops.head (Resources.run m.measured cs q).1 =
      ops.head (Resources.run n.measured cs q).1 := by rw [run_erases, run_erases]

theorem abstractBudget_append (profile : Command α → List α → Nat)
    (xs ys : List (Command α)) (s : List α) :
    abstractBudget profile (xs ++ ys) s = abstractBudget profile xs s +
      abstractBudget profile ys (Sequences.AbstractFIFO.run (lists α) xs s) := by
  let e : Instrumentation (lists α) := ⟨fun c s => (step (lists α) c s, 0), fun _ _ => rfl⟩
  simpa only [abstractBudget, run_erases e, e] using budget_append e.measured profile xs ys s

/-- Sequential clients use the original initialization credit once. The proof
uses the retained final potential in run_potential before dropping it. -/
theorem sequential_bound {ops : Ops α Q} {m : Instrumentation ops} {decode : Q → List α}
    {profile : Command α → List α → Nat} {initialized : Q → Nat → Prop}
    (h : Accounting ops m decode profile initialized)
    (xs ys : List (Command α)) (q : Q) (credit : Nat) (hi : initialized q credit) :
    (Resources.bind (Resources.run m.measured xs q) (Resources.run m.measured ys)).2 ≤
      credit + (abstractBudget profile xs (decode q) +
        abstractBudget profile ys (Sequences.AbstractFIFO.run (lists α) xs (decode q))) := by
  have hb := client_bound h (xs ++ ys) q credit hi
  rw [Resources.run_append, abstractBudget_append] at hb
  exact hb

/-- Additivity transports sequencing; monotonicity separately transports bounds. -/
theorem reobserved_bound {ops : Ops α Q} {m : Instrumentation ops} {decode : Q → List α}
    {profile : Command α → List α → Nat} {initialized : Q → Nat → Prop}
    (h : Accounting ops m decode profile initialized)
    (f : Nat →+ Nat) (hf : Monotone f) (cs : List (Command α))
    (q : Q) (credit : Nat) (hi : initialized q credit) :
    (Resources.run (fun c q => reweight f (m.measured c q)) cs q).2 ≤
      f (credit + abstractBudget profile cs (decode q)) := by
  rw [← reweight_run]
  exact reweight_bound f hf _ _ (client_bound h cs q credit hi)

/-- Recursive append visits the terminating nil as well as each cons. -/
def appendRun (x : α) : List α → Measured (List α) Nat
  | [] => ([x], 1)
  | y :: ys => let r := appendRun x ys; (y :: r.1, r.2 + 1)

theorem appendRun_exact (x : α) (xs : List α) :
    appendRun x xs = (xs ++ [x], xs.length + 1) := by
  induction xs with
  | nil => rfl
  | cons y ys ih => simp [appendRun, ih]

def listMeasure : Instrumentation (lists α) where
  measured
    | .enqueue x, xs => appendRun x xs
    | .delete, xs => (xs.tail, 1)
  erases c xs := by cases c <;> simp [appendRun_exact, step, lists]

def listProfile : Command α → List α → Nat
  | .enqueue _, xs => xs.length + 1
  | .delete, _ => 1

theorem list_accounting : Accounting (lists α) listMeasure id listProfile (fun _ _ => True) where
  behavior := lists_correct α
  certificate := ⟨fun _ => 0, by simp, by intro c q; cases c <;> simp [listMeasure, appendRun_exact, listProfile]⟩

open Sequences.Symmetric
abbrev ValidQueue (α : Type u) := {q : SymList α // Inv q}

def validOps : Ops α (ValidQueue α) where
  empty := ⟨nilSL, inv_nilSL⟩
  snoc x q := ⟨snocSL x q.val, (symmetric_correct α).snoc x q.val (fromSL q.val) ⟨q.property, rfl⟩ |>.1⟩
  tail q := ⟨tailSL q.val, (symmetric_correct α).tail q.val (fromSL q.val) ⟨q.property, rfl⟩ |>.1⟩
  head q := headSL q.val

def commandOperation : Command α → SymmetricCosts.Operation α
  | .enqueue x => .snoc x
  | .delete => .tail

def symmetricMeasure : Instrumentation (validOps : Ops α (ValidQueue α)) where
  measured c q :=
    let r := SymmetricCosts.execute (commandOperation c) q.val
    (⟨r.state, SymmetricCosts.execute_inv _ _ q.property⟩, r.work)
  erases c q := by
    apply Subtype.ext
    cases c <;> simp [commandOperation, SymmetricCosts.execute, step, validOps, SymmetricCosts.tailRun_value]

theorem valid_correct : Simulation (validOps : Ops α (ValidQueue α)) (lists α)
    (fun q xs => fromSL q.val = xs) where
  empty := rfl
  snoc x q xs h := ((symmetric_correct α).snoc x q.val xs ⟨q.property, h⟩).2
  tail q xs h := ((symmetric_correct α).tail q.val xs ⟨q.property, h⟩).2
  head q xs h := (symmetric_correct α).head q.val xs ⟨q.property, h⟩

private def stored (q : ValidQueue α) : Nat := 2 * SymmetricCosts.potential q.val

/-- Public initialization evidence; callers need not unfold its implementation. -/
def symmetricInitialized (q : ValidQueue α) (credit : Nat) : Prop := stored q ≤ credit

theorem symmetric_empty_initialized :
    symmetricInitialized (validOps : Ops α (ValidQueue α)).empty 0 := by exact Nat.le_refl 0

theorem symmetric_accounting : Accounting (validOps : Ops α (ValidQueue α)) symmetricMeasure
    (fun q => fromSL q.val) (fun _ _ => 8) symmetricInitialized where
  behavior := valid_correct
  certificate := ⟨stored, fun _ _ h => h, by
    intro c q
    exact SymmetricCosts.execute_work_potential (commandOperation c) q.val⟩

end Resources.FIFOContracts
