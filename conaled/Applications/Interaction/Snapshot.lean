import SquareKit.InteractionContracts

/-!
# Captured inputs under permitted live-source mutation

Arbitrary input collections are mathematical values. The environment may
change live inputs but preserves the sealed collection and any compilation
receipt. `CompileCaptured` assumes compilation uses that collection; no
filesystem implementation of this assumption is supplied here.
-/
namespace Interaction.Snapshot
universe u

structure State (Inputs : Type u) where
  live : Inputs
  captured : Inputs
  compiled : Option Inputs

/-- A permitted actor can change live inputs while leaving owned evidence alone. -/
def Environment {I : Type u} (s t : State I) : Prop :=
  t.captured = s.captured ∧ t.compiled = s.compiled

/-- Seal an already collected value, not an atomic snapshot of the live world. -/
def Seal {I : Type u} (inputs : I) (s t : State I) : Prop :=
  t.live = s.live ∧ t.captured = inputs ∧ t.compiled = none

def CompileCaptured {I : Type u} (s t : State I) : Prop :=
  t.captured = s.captured ∧ t.compiled = some s.captured

theorem captured_stable {I : Type u} (inputs : I) :
    Stable Environment (fun s : State I => s.captured = inputs) := by
  intro s t hs h
  exact h.1.trans hs

theorem compile_sealed {I : Type u} (inputs : I) :
    Safe (fun _ => True)
      (Relation.Comp (Seal inputs)
        (Relation.Comp (Relation.ReflTransGen Environment) CompileCaptured))
      (fun t => t.compiled = some inputs) := by
  refine safe_interference_seq (S := State I)
    (P := fun _ => True) (Q := fun s => s.captured = inputs)
    (U := fun t => t.compiled = some inputs)
    (C := Seal inputs) (R := Environment) (D := CompileCaptured) ?_ ?_ ?_
  · intro s t _ h
    exact h.2.1
  · exact captured_stable inputs
  · intro s t hs h
    exact h.2.trans (congrArg some hs)

/-- A concrete history: A changes before B. -/
def history : List (Bool × Bool) := [(false, false), (true, false), (true, true)]
def mixed : Bool × Bool := (false, true)

/-- The first component is read before either update; the second after both. -/
theorem ordered_capture : mixed = ((history[0]'(by decide)).1,
    (history[2]'(by decide)).2) := rfl

theorem individually_observed :
    (∃ s ∈ history, s.1 = mixed.1) ∧ (∃ s ∈ history, s.2 = mixed.2) := by
  exact ⟨⟨(false, false), by simp [history], rfl⟩,
    ⟨(true, true), by simp [history], rfl⟩⟩

theorem never_coexisted : mixed ∉ history := by decide

/-- Scanned bytes are false, but permitted mutation makes a later live read true. -/
def scanned : State Bool := ⟨false, false, none⟩
def changed : State Bool := ⟨true, false, none⟩
def compiledLive : State Bool := ⟨true, false, some true⟩

def CompileLive (s t : State Bool) : Prop :=
  t.compiled = some s.live

theorem live_read_counterexample :
    Environment scanned changed ∧ CompileLive changed compiledLive ∧
      compiledLive.compiled ≠ some scanned.captured := by
  exact ⟨⟨rfl, rfl⟩, rfl, by decide⟩

/-- Ordinary endpoint triples do not justify insertion of arbitrary interference. -/
theorem missing_stability_counterexample :
    Safe (fun b : Bool => b = false) (fun _ t => t = false) (fun b => b = false) ∧
    Safe (fun b : Bool => b = false) Eq (fun b => b = false) ∧
    ¬ Safe (fun b : Bool => b = false)
      (Relation.Comp (fun _ t => t = false)
        (Relation.Comp (Relation.ReflTransGen (fun _ _ : Bool => True)) Eq))
      (fun b => b = false) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s t _ h
    exact h
  · intro s t hs h
    exact h ▸ hs
  · intro h
    have bad := h (s := false) (t := true) rfl
      ⟨false, rfl, true, Relation.ReflTransGen.single trivial, rfl⟩
    cases bad
end Interaction.Snapshot
