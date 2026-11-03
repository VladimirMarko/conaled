import Applications.Resources.FIFOContracts

namespace Examples.FIFOContracts
open Resources Resources.FIFOContracts Sequences.AbstractFIFO

def edits : List (Command Nat) := [.enqueue 1, .enqueue 2, .delete, .enqueue 3]

/-- The ordinary client uses only public accounting evidence and initialization. -/
theorem ordinary_bound {α Q : Type} {ops : Ops α Q} {m : Instrumentation ops}
    {decode : Q → List α} {profile : Command α → List α → Nat}
    {initialized : Q → Nat → Prop} (h : Accounting ops m decode profile initialized)
    (cs : List (Command α)) (q : Q) (credit : Nat) (hi : initialized q credit) :
    (Resources.run m.measured cs q).2 ≤ credit + abstractBudget profile cs (decode q) :=
  client_bound h cs q credit hi

example : (Resources.run listMeasure.measured edits ([] : List Nat)).2 ≤
    abstractBudget listProfile edits [] := by
  exact ordinary_bound list_accounting edits [] 0 trivial

example : (Resources.run symmetricMeasure.measured edits
    (validOps : Ops Nat (ValidQueue Nat)).empty).2 ≤ abstractBudget (fun _ _ => 8) edits [] := by
  exact ordinary_bound symmetric_accounting edits validOps.empty 0 symmetric_empty_initialized

example (cs : List (Command Nat)) :
    (Resources.run symmetricMeasure.measured cs (validOps : Ops Nat (ValidQueue Nat)).empty).2 ≤
      8 * cs.length := by
  simpa [abstractBudget, budget_constant] using
    ordinary_bound symmetric_accounting cs validOps.empty 0 symmetric_empty_initialized

example : (Resources.run listMeasure.measured edits ([] : List Nat)) = ([2, 3], 6) := by decide

example : (Resources.run symmetricMeasure.measured edits
    (validOps : Ops Nat (ValidQueue Nat)).empty).2 = 9 := by decide

/-- The endpoint observations agree although structural work differs. -/
example :
    client (lists Nat) edits [] = client validOps edits (validOps : Ops Nat (ValidQueue Nat)).empty ∧
    (Resources.run listMeasure.measured edits ([] : List Nat)).2 ≠
      (Resources.run symmetricMeasure.measured edits (validOps : Ops Nat (ValidQueue Nat)).empty).2 := by
  constructor
  · exact (valid_correct.client_empty edits).symm
  · decide

example (xs ys : List (Command Nat)) :
    (bind (Resources.run symmetricMeasure.measured xs (validOps : Ops Nat (ValidQueue Nat)).empty)
      (Resources.run symmetricMeasure.measured ys)).2 ≤ 8 * xs.length + 8 * ys.length := by
  simpa [abstractBudget, budget_constant] using
    sequential_bound symmetric_accounting xs ys validOps.empty 0 symmetric_empty_initialized

/-- Rescaling structural visits is an additive and monotone resource observation. -/
def doubleWork : Nat →+ Nat where
  toFun n := 2 * n
  map_zero' := by simp
  map_add' _ _ := Nat.mul_add _ _ _

example (cs : List (Command Nat)) :
    (Resources.run (fun c q => reweight doubleWork (symmetricMeasure.measured c q)) cs
      (validOps : Ops Nat (ValidQueue Nat)).empty).2 ≤ 2 * (8 * cs.length) := by
  simpa [abstractBudget, budget_constant, doubleWork] using
    reobserved_bound symmetric_accounting doubleWork (by intro a b h; change 2 * a ≤ 2 * b; omega)
      cs validOps.empty 0 symmetric_empty_initialized

/-- An arbitrary measured observer can see costs; the theorem quantifies only
operation-only clients followed by the shared head observation. -/
def freeMeasure : Instrumentation (lists Nat) :=
  ⟨fun c q => (step (lists Nat) c q, 0), fun _ _ => rfl⟩

example (cs : List (Command Nat)) (xs : List Nat) :
    (lists Nat).head (Resources.run listMeasure.measured cs xs).1 =
      (lists Nat).head (Resources.run freeMeasure.measured cs xs).1 :=
  cost_noninterference listMeasure freeMeasure cs xs

example : (Resources.run listMeasure.measured [.enqueue 1] []).2 ≠
    (Resources.run freeMeasure.measured [.enqueue 1] []).2 := by decide

def paidObservation (r : Measured (List Nat) Nat) : Bool := decide (0 < r.2)

example : paidObservation (Resources.run listMeasure.measured [.enqueue 1] []) = true ∧
    paidObservation (Resources.run freeMeasure.measured [.enqueue 1] []) = false := by decide

/-- A persisted queue can be branched, but its stored credit cannot be spent
once in each branch while counted once in their combined resource bound. -/
def chargedQueue : ValidQueue Nat := ⟨([0], [1, 2, 3, 4, 5, 6, 7]), by simp [Sequences.Symmetric.Inv]⟩

example : symmetricInitialized chargedQueue 12 := by unfold symmetricInitialized; decide

example :
    (Resources.run symmetricMeasure.measured [.delete] chargedQueue).2 ≤ 12 + 8 ∧
    2 * (Resources.run symmetricMeasure.measured [.delete] chargedQueue).2 > 12 + 2 * 8 := by
  decide

end Examples.FIFOContracts
