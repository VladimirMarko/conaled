import Examples.IndexedPartialComputation

/-! Selected partial results with varying finite fibers and strict value embeddings. -/
noncomputable section
namespace VaryingPartialCertificates
open OmegaCompletePartialOrder SelectedFixedPoint
open IndexedPartialComputation (trace)

/-- All bounded values are valid; the selector is not a field of this specification. -/
structure Cert (n k : Nat) where
  value : Fin (n+k+1)
  steps : List Nat
  steps_eq : steps = trace k

@[ext] theorem Cert.ext {n k : Nat} {a b : Cert n k}
    (h : a.value = b.value) : a = b := by
  cases a; cases b; simp_all

/-- The fiber has exactly its bounded values, with the trace recovered independently. -/
def certEquiv (n k : Nat) : Cert n k ≃ Fin (n+k+1) where
  toFun := Cert.value
  invFun v := ⟨v, trace k, rfl⟩
  left_inv _ := Cert.ext rfl
  right_inv _ := rfl

/-- No single fixed tag type trivializes all these fibers. -/
theorem no_fixed_tags : ¬ ∃ A : Type, ∀ n k, Nonempty (Cert n k ≃ A) := by
  rintro ⟨A, h⟩
  have e := (certEquiv 0 0).symm.trans ((h 0 0).some.trans
    ((h 1 0).some.symm.trans (certEquiv 1 0)))
  have hc := Fintype.card_congr e
  simp at hc

/-- A separately chosen seed determines the successful result after k increments. -/
def selected (n j k : Nat) (hj : j ≤ n) : Cert n k :=
  ⟨⟨j+k, by omega⟩, trace k, rfl⟩

def step {n k : Nat} (c : Cert n k) : Cert n (k+1) :=
  ⟨⟨c.value.val+1, by have := c.value.isLt; omega⟩,
    (k+1)::c.steps, by rw [c.steps_eq]; rfl⟩

@[simp] theorem step_selected (n j k : Nat) (hj : j ≤ n) :
    step (selected n j k hj) = selected n j (k+1) hj := by
  apply Cert.ext; apply Fin.ext; simp [step, selected, Nat.add_assoc]

abbrev State (n : Nat) := (k : Nat) → Part (Cert n k)

def runStep (enabled : Bool) (n j : Nat) (hj : j ≤ n) (q : State n) : State n :=
  fun k => if enabled then match k with
    | 0 => Part.some (selected n j 0 hj)
    | k+1 => Part.map step (q k)
  else q k

def functional (enabled : Bool) (n j : Nat) (hj : j ≤ n) : State n →𝒄 State n :=
  ContinuousHom.ofFun (runStep enabled n j hj) (by
    apply ωScottContinuous.of_apply₂
    intro k
    cases enabled <;> simp only [runStep, Bool.false_eq_true, ↓reduceIte]
    · exact ωScottContinuous.apply k
    · cases k with
      | zero => exact ωScottContinuous.const
      | succ k => exact ContinuousHom.ωScottContinuous.map (ωScottContinuous.apply k))

def bounded (enabled : Bool) (n j : Nat) (hj : j ≤ n) (fuel : Nat) : State n :=
  fun k => if enabled = true ∧ k < fuel then Part.some (selected n j k hj) else Part.none

def meaning (enabled : Bool) (n j : Nat) (hj : j ≤ n) : State n :=
  fun k => if enabled then Part.some (selected n j k hj) else Part.none

theorem approximants_eq_bounded (enabled : Bool) (n j : Nat) (hj : j ≤ n) (fuel : Nat) :
    approximants (functional enabled n j hj) fuel = bounded enabled n j hj fuel := by
  induction fuel with
  | zero => funext k; simp [approximants, fixedPoints.iterateChain, bounded]; rfl
  | succ fuel ih =>
    change (functional enabled n j hj)^[fuel+1] ⊥ = _
    rw [Function.iterate_succ_apply']
    change runStep enabled n j hj (approximants (functional enabled n j hj) fuel) = _
    rw [ih]
    funext k
    cases enabled <;> cases k <;> simp [runStep, bounded]
    split_ifs <;> simp_all

theorem solution_eq_meaning (enabled : Bool) (n j : Nat) (hj : j ≤ n) :
    solution (functional enabled n j hj) = meaning enabled n j hj := by
  apply le_antisymm
  · apply solution_le
    intro k
    cases enabled <;> cases k <;> simp [functional, runStep, meaning]
  · intro k
    cases enabled
    · simp [meaning]; exact bot_le
    · have hl := le_ωSup (approximants (functional true n j hj)) (k+1)
      change approximants (functional true n j hj) (k+1) ≤ solution (functional true n j hj) at hl
      rw [approximants_eq_bounded] at hl
      simpa [bounded, meaning] using hl k

/-- Capacity expansion can also translate the selected value; it preserves the trace. -/
def embed {n m : Nat} (d : Nat) (h : n+d ≤ m) {k : Nat} (c : Cert n k) : Cert m k :=
  ⟨⟨c.value.val+d, by have := c.value.isLt; omega⟩, c.steps, c.steps_eq⟩

theorem embed_injective {n m : Nat} (d : Nat) (h : n+d ≤ m) (k : Nat) :
    Function.Injective (embed d h : Cert n k → Cert m k) := by
  intro a b hab
  apply Cert.ext; apply Fin.ext
  have hv := congrArg (fun c => c.value.val) hab
  simpa [embed] using hv

@[simp] theorem embed_selected {n m : Nat} (d j k : Nat) (h : n+d ≤ m) (hj : j ≤ n) :
    embed d h (selected n j k hj) = selected m (j+d) k (by omega) := by
  apply Cert.ext; apply Fin.ext; simp [embed, selected]; omega

@[simp] theorem embed_step {n m : Nat} (d : Nat) (h : n+d ≤ m) {k : Nat} (c : Cert n k) :
    embed d h (step c) = step (embed d h c) := by
  apply Cert.ext; apply Fin.ext; simp [embed, step]; omega

def transport {n m : Nat} (d : Nat) (h : n+d ≤ m) : State n →𝒄 State m :=
  ContinuousHom.ofFun (fun q k => Part.map (embed d h) (q k)) (by
    apply ωScottContinuous.of_apply₂
    intro k
    exact ContinuousHom.ωScottContinuous.map (ωScottContinuous.apply k))

theorem transport_strict {n m : Nat} (d : Nat) (h : n+d ≤ m) : transport d h ⊥ = ⊥ := by
  funext k; exact Part.map_none _

theorem transport_step (enabled : Bool) {n m : Nat} (d j : Nat)
    (h : n+d ≤ m) (hj : j ≤ n) (q : State n) :
    transport d h (functional enabled n j hj q) =
      functional enabled m (j+d) (by omega) (transport d h q) := by
  funext k
  cases enabled <;> cases k <;>
    simp [transport, functional, runStep, Part.map_map, Function.comp_def]

theorem transport_solution (enabled : Bool) {n m : Nat} (d j : Nat)
    (h : n+d ≤ m) (hj : j ≤ n) :
    transport d h (solution (functional enabled n j hj)) =
      solution (functional enabled m (j+d) (by omega)) :=
  map_solution _ _ _ (transport_strict d h) (transport_step enabled d j h hj)

/-- Sequential and composite changes agree on every partial state, before selection. -/
theorem transport_comp {n m r : Nat} (d e : Nat) (h : n+d ≤ m) (h' : m+e ≤ r)
    (q : State n) :
    transport e h' (transport d h q) = transport (d+e) (by omega) q := by
  funext k
  change Part.map (embed e h') (Part.map (embed d h) (q k)) =
    Part.map (embed (d+e) _) (q k)
  rw [Part.map_map]
  congr 1
  funext c
  apply Cert.ext; apply Fin.ext; simp [embed, Nat.add_assoc]

/-- First add one slot, then add two slots and shift each retained value by one. -/
theorem two_changes (enabled : Bool) (n j : Nat) (hj : j ≤ n) :
    transport 1 (show n+1+1 ≤ n+3 by omega)
      (transport 0 (show n+0 ≤ n+1 by omega) (solution (functional enabled n j hj))) =
    solution (functional enabled (n+3) (j+1) (by omega)) := by
  rw [transport_solution, transport_solution]

/-- Both proper inclusions discard possible target values from their image. -/
theorem first_not_surjective (n k : Nat) :
    ¬ Function.Surjective (embed 0 (show n+0 ≤ n+1 by omega) : Cert n k → Cert (n+1) k) := by
  intro h
  obtain ⟨c, hc⟩ := h ⟨⟨n+k+1, by omega⟩, trace k, rfl⟩
  have hv := congrArg (fun c => c.value.val) hc
  have := c.value.isLt
  simp [embed] at hv
  omega

theorem second_not_surjective (n k : Nat) :
    ¬ Function.Surjective (embed 1 (show n+1+1 ≤ n+3 by omega) : Cert (n+1) k → Cert (n+3) k) := by
  intro h
  obtain ⟨c, hc⟩ := h ⟨⟨0, by omega⟩, trace k, rfl⟩
  have hv := congrArg (fun c => c.value.val) hc
  simp [embed] at hv

/-- Independent calculation: 0+2 becomes 3 after the two changes, with the same trace. -/
example : transport 1 (show 1+1+1 ≤ 1+3 by omega)
    (transport 0 (show 1+0 ≤ 1+1 by omega) (solution (functional true 1 0 (by omega)))) 2 =
    Part.some (selected 4 1 2 (by omega)) := by
  rw [two_changes, solution_eq_meaning]; rfl

example : (selected 4 1 2 (by omega)).value.val = 3 ∧
    (selected 4 1 2 (by omega)).steps = [2,1,0] := by decide

/-- Equal termination domains do not identify different seed selections. -/
theorem same_domain (enabled : Bool) (n i j : Nat) (hi : i ≤ n) (hj : j ≤ n) (k : Nat) :
    (solution (functional enabled n i hi) k).Dom ↔
      (solution (functional enabled n j hj) k).Dom := by
  rw [solution_eq_meaning, solution_eq_meaning]
  cases enabled <;> simp [meaning]

theorem different_selection : solution (functional true 1 0 (by omega)) 2 ≠
    solution (functional true 1 1 (by omega)) 2 := by
  rw [solution_eq_meaning, solution_eq_meaning]
  intro h
  have hc : selected 1 0 2 (by omega) = selected 1 1 2 (by omega) := Part.some_injective h
  have hv := congrArg (fun c => c.value.val) hc
  contradiction

example : bounded true 1 0 (by omega) 2 2 = Part.none ∧
    solution (functional true 1 0 (by omega)) 2 = Part.some (selected 1 0 2 (by omega)) := by
  constructor
  · simp [bounded]
  · rw [solution_eq_meaning]; rfl

example : solution (functional false 1 0 (by omega)) 2 = Part.none := by
  rw [solution_eq_meaning]; rfl

end VaryingPartialCertificates
