import Applications.FRP.BoundedFoldRegional

/-! Selected evidence is tied to the executor returned by admission. Arbitrary
semantic carriers remain available without a storage-analysis claim. -/
namespace FRPSpec.BoundedFold
open Progress Progress.Feedback

structure Realization (capacity : Nat) where
  State : Type
  machine : Initialized (Batch capacity) Bool State
  observe : State → Bool
  initial : observe machine.initial = false
  step : ∀ xs s, (machine.step (xs,s)).1 = observe s ∧
    observe (machine.step (xs,s)).2 = parity (observe s) xs.val

def selected (capacity : Nat) : Realization capacity where
  State := Bool
  machine := BoundedFold.machine capacity
  observe := id
  initial := rfl
  step xs s := ⟨rfl,execute_correct s xs.val⟩

structure BoundEvidence (r : Realization capacity) (available : Nat) : Prop where
  /-- Identifies the analyzed executable, not just its value denotation. -/
  executor : r = selected capacity
  fits : storage capacity ≤ available

inductive Guarantee where
  | semantic
  | bounded (available : Nat)
  deriving Repr

inductive Evidence (r : Realization capacity) : Guarantee → Prop where
  | semantic : Evidence r .semantic
  | bounded : BoundEvidence r n → Evidence r (.bounded n)

inductive Admission (capacity : Nat) (g : Guarantee) where
  | accepted (realization : Realization capacity) (evidence : Evidence realization g)
  | rejected (required available : Nat)
  | unsupportedAnalysis

/-- `analyzed = false` preserves the semantic route but makes no space claim. -/
def assess (capacity : Nat) (analyzed : Bool) (g : Guarantee) : Admission capacity g :=
  match g with
  | .semantic => .accepted (selected capacity) .semantic
  | .bounded n =>
    if analyzed then
      if h : storage capacity ≤ n then
        .accepted (selected capacity) (.bounded ⟨rfl,h⟩)
      else .rejected (storage capacity) n
    else .unsupportedAnalysis

inductive Status where
  | accepted | rejected | unsupported
  deriving Repr, DecidableEq

def Admission.status : Admission c g → Status
  | .accepted _ _ => .accepted
  | .rejected _ _ => .rejected
  | .unsupportedAnalysis => .unsupported

/-- The accepted package's actual runner is consumed here. No fallback silently
bypasses a rejected/unknown requested guarantee. -/
def Admission.run (a : Admission capacity g) (xs : List (Batch capacity)) : Option (List Bool × Bool) :=
  match a with
  | .accepted r _ =>
    let result := Progress.Feedback.run r.machine.mealy r.machine.initial xs
    some (result.1,r.observe result.2)
  | _ => none

theorem admitted_iff (c available : Nat) :
    (assess c true (.bounded available)).status = .accepted ↔ storage c ≤ available := by
  by_cases h : storage c ≤ available <;> simp [assess, Admission.status, h]

theorem admitted_execution (r : Realization capacity) (h : BoundEvidence r available)
    (xs : Batch capacity) (s : r.State) :
    ∃ trace, Executes xs.val.length xs.val (r.observe s)
      (r.observe (r.machine.step (xs,s)).2) (work xs.val.length) trace ∧
      ∀ v ∈ trace, v ≤ available := by
  obtain ⟨rfl,hfit⟩ := h
  exact ⟨_,executes _ _ _ (Nat.le_refl _),fun v hv =>
    (trace_bound xs.property _ _ v hv).trans hfit⟩

/-- Accepted evidence also exposes the conditional service theorem for the
identified runner, rather than merely a numerical capacity comparison. -/
theorem admitted_service (r : Realization capacity) (h : BoundEvidence r available)
    (env : Environment) (input : Stream (Batch capacity)) (deadline : Nat) :
    ∃ n, deadline < starts env input (n+1) ∧
      Round (env.inputWait n) (env.schedulerWait n) (env.sinkWait n)
        (starts env input n) (input n).val (r.observe (state r.machine input n))
        (output r.machine input n) (r.observe (state r.machine input (n+1)))
        (starts env input (n+1)) := by
  obtain ⟨rfl,_⟩ := h
  exact productive env input deadline

theorem unknown_not_impossible (c available : Nat) :
    (assess c false .semantic).status = .accepted ∧
    (assess c false (.bounded available)).status = .unsupported := ⟨rfl,rfl⟩

end FRPSpec.BoundedFold
