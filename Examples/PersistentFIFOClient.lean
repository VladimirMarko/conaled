import Applications.Resources.Persistent.FIFOClient

/-! Representation choice for a FIFO fork, under a complete declared tariff.
See `docs/research/pfds-library-client.md` for cost and persistence boundaries. -/
namespace Examples.PersistentFIFOClient
open Sequences.AbstractFIFO Resources Resources.FIFOContracts Resources.Persistent.FIFOClient

example : (fromEmpty (listMeasure : Instrumentation (lists Nat)) [] [] []).1.observations =
    (none, none) ∧ (fromEmpty (listMeasure : Instrumentation (lists Nat)) [] [] []).2 = 3 := by
  decide

example : (fromEmpty (symmetricMeasure : Instrumentation (validOps : Ops Nat (ValidQueue Nat)))
    [] [] []).1.observations = (none, none) ∧
    (fromEmpty (symmetricMeasure : Instrumentation (validOps : Ops Nat (ValidQueue Nat)))
      [] [] []).2 = 3 := by decide

/-- Four enqueues run once. Two empty suffixes observe the same retained queue. -/
def enqueues : List (Command Nat) := [.enqueue 1, .enqueue 2, .enqueue 3, .enqueue 4]

example : (fromEmpty listMeasure enqueues [] []).1.observations = (some 1, some 1) ∧
    (fromEmpty listMeasure enqueues [] []).2 = 13 := by decide

example : (fromEmpty symmetricMeasure enqueues [] []).1.observations = (some 1, some 1) ∧
    (fromEmpty symmetricMeasure enqueues [] []).2 = 7 := by decide

/-- Rebalancing can make the symmetric representation more expensive. -/
def shortPrefix : List (Command Nat) := [.enqueue 1, .enqueue 2]

example : (fromEmpty listMeasure shortPrefix [.delete] [.delete]).1.observations =
    (some 2, some 2) ∧ (fromEmpty listMeasure shortPrefix [.delete] [.delete]).2 = 8 := by decide

example : (fromEmpty symmetricMeasure shortPrefix [.delete] [.delete]).1.observations =
    (some 2, some 2) ∧ (fromEmpty symmetricMeasure shortPrefix [.delete] [.delete]).2 = 17 := by decide

/-- Both observations are obtained from the common representation theorem,
not just by evaluating the concrete examples. -/
theorem symmetric_observations (stem left right : List (Command Nat)) :
    let input := Sequences.AbstractFIFO.run (lists Nat) stem []
    (fromEmpty symmetricMeasure stem left right).1.observations =
      (client (lists Nat) left input, client (lists Nat) right input) := by
  exact (observations valid_correct stem left right
    (validOps : Ops Nat (ValidQueue Nat)).empty).2.2.2

example (stem left right : List (Command Nat)) :
    (fromEmpty symmetricMeasure stem left right).2 ≤
      credit (fromEmpty symmetricMeasure stem left right).1.retained +
      8 * (stem.length + left.length + right.length) + 3 :=
  symmetric_fromEmpty_bound stem left right

/-- An already built input needs twelve units of stored credit. Each strict
branch spends that credit separately; equal results do not make the work shared. -/
def loaded : ValidQueue Nat :=
  ⟨([0], [1, 2, 3, 4, 5, 6, 7]), by simp [Sequences.Symmetric.Inv]⟩

example : credit loaded = 12 ∧
    (execute symmetricMeasure [] [.delete] [.delete] loaded).2 = 38 ∧
    (execute symmetricMeasure [] [.delete] [.delete] loaded).1.observations =
      (some 7, some 7) := by decide

example : ¬ (execute symmetricMeasure [] [.delete] [.delete] loaded).2 ≤
    credit loaded + 8 * 2 + 2 := by decide

/-- The actual work is represented by three occurrence charges, with no invented
shared identities for the equal suffix computations. -/
example :
    (Resources.run (Resources.Persistent.realizeStep
      (blockWork symmetricMeasure shortPrefix [.delete] [.delete])
      (fun _ => (∅ : Finset Nat))) [.stem, .left, .right] ∅).2 = 17 := by
  rw [realization_cost]
  decide

example : (execute symmetricMeasure [] [.delete] [.delete] loaded).1.retained = loaded := rfl

/-- Signed mapped accounting retains the extra credit at the fork. -/
example :
    let potential := fun q : ValidQueue Nat => (credit q : Int)
    let charge := fun c q => (symmetricMeasure.measured c q).2 +
      potential (symmetricMeasure.measured c q).1 - potential q
    ((execute symmetricMeasure [] [.delete] [.delete] loaded).2 : Int) +
      potential (execute symmetricMeasure [] [.delete] [.delete] loaded).1.left +
      potential (execute symmetricMeasure [] [.delete] [.delete] loaded).1.right =
      potential loaded + potential loaded +
      budget symmetricMeasure.measured charge [.delete] loaded +
      budget symmetricMeasure.measured charge [.delete] loaded + 2 := by
  simpa only [execute, Resources.run, Resources.pure, budget, add_zero] using
    signed_boundary symmetricMeasure (fun q => (credit q : Int)) [] [.delete] [.delete] loaded

end Examples.PersistentFIFOClient
