import Applications.Probability.PermutationTail
import Examples.PermutationOrder
import Examples.PermutationTailBoundary
import Mathlib.Tactic

/-!
# Revealing a head and reusing the observed tail law

The actual order of `{0, 2, 3}` comes from the same global permutation as
the earlier whole-order example. Conditioning its first key to `0` gives
two tails, each of mass `1/2`. The source-fiber theorem and the existing
HasLaw/map semantics give separate connections to the new public results.

The full environment measure changes after the first reveal. Its actual
tail nevertheless has the uniform remaining-order law. That HasLaw is the
premise for a second reveal of key `2`, after which `[3]` is the sole tail.
The second measure retains the actual nested conditioning explicitly.

Filtering the first remaining list to `{3}` also uses the generic law and
the pointwise on-event projection bridge. These cases do not assume branch
independence or prove an arbitrary execution-history invariant or cost law.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.PermutationTail

open MeasureTheory ProbabilityTheory
open Applications.Probability.PermutationOrder
open Applications.Probability.PermutationTail
open Examples.PermutationOrder (positions positions_nodup positions_complete selected law)
open scoped ENNReal

local instance : MeasurableSpace (Equiv.Perm (Fin 4)) := ⊤
local instance : MeasurableSpace (List (Fin 4)) := ⊤

def observedOrder (π : Equiv.Perm (Fin 4)) : List (Fin 4) :=
  restrictedOrder positions selected π

def remaining : Finset (Fin 4) := selected.erase 0

def tailOrder (π : Equiv.Perm (Fin 4)) : List (Fin 4) :=
  (observedOrder π).tail

noncomputable def afterFirst : Measure (Equiv.Perm (Fin 4)) :=
  law[|firstEvent observedOrder 0]

/-- The initial premise is the actual whole-order map law from XU02. -/
theorem observed_hasLaw :
    HasLaw observedOrder
      (uniformOn (orders positions selected : Set (List (Fin 4)))) law where
  aemeasurable := (measurable_of_finite _).aemeasurable
  map_eq := Examples.PermutationOrder.observed_law

/-- The generic head theorem is applied to a proved whole-observation law. -/
theorem first_mass : law (firstEvent observedOrder 0) = 1 / 3 := by
  calc
    _ = (selected.card : ℝ≥0∞)⁻¹ :=
      head_mass_of_hasLaw positions positions_nodup positions_complete
        selected 0 (by decide) observed_hasLaw
    _ = 1 / 3 := by norm_num [selected, one_div]

/-- This identity concerns the original uniform environment specifically. -/
theorem afterFirst_eq_uniformOn :
    afterFirst = uniformOn (firstEvent observedOrder 0) := by
  exact cond_uniformOn_firstEvent positions positions_complete selected 0

/-- The actual tail, under the changed environment, has the remaining-order law. -/
theorem tail_hasLaw :
    HasLaw tailOrder
      (uniformOn (orders positions remaining : Set (List (Fin 4)))) afterFirst := by
  exact hasLaw_tail_cond_first positions positions_nodup positions_complete
    selected 0 (by decide) observed_hasLaw

/-- A concrete use of the public map specialization, in the original sample space. -/
theorem tail_map :
    afterFirst.map tailOrder =
      uniformOn (orders positions remaining : Set (List (Fin 4))) := by
  exact map_tail_cond_first positions positions_nodup positions_complete
    selected 0 (by decide)

private theorem mass_of_law {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {Y : Ω → List (Fin 4)} {S : Finset (Fin 4)}
    (hY : HasLaw Y (uniformOn (orders positions S : Set (List (Fin 4)))) μ)
    (xs : List (Fin 4)) (hxs : xs ∈ orders positions S) :
    μ {ω | Y ω = xs} = (Nat.factorial S.card : ℝ≥0∞)⁻¹ := by
  calc
    _ = uniformOn (orders positions S : Set (List (Fin 4))) {xs} :=
      hY.measure_eq (measurableSet_singleton xs)
    _ = (((orders positions S) ∩ {xs}).card : ℝ≥0∞) /
        ((orders positions S).card : ℝ≥0∞) := by
      simpa only [Finset.coe_singleton] using
        (uniformOn_apply_finset (s := orders positions S) (t := {xs}))
    _ = (Nat.factorial S.card : ℝ≥0∞)⁻¹ := by
      simp [Finset.inter_singleton_of_mem hxs,
        orders_card positions positions_nodup positions_complete S, one_div]

/-- The first supported tail mass uses the new universal source-fiber formula. -/
theorem tail_23_mass : afterFirst {π | tailOrder π = [2, 3]} = 1 / 2 := by
  have hmem : ([2, 3] : List (Fin 4)) ∈ orders positions (selected.erase 0) := by
    decide
  calc
    _ = if ([2, 3] : List (Fin 4)) ∈ orders positions (selected.erase 0)
        then (Nat.factorial (selected.erase 0).card : ℝ≥0∞)⁻¹ else 0 :=
      cond_tail_eq positions positions_nodup positions_complete
        selected 0 (by decide) [2, 3]
    _ = 1 / 2 := by rw [if_pos hmem]; norm_num [selected, one_div]

/-- The other tail mass is obtained through the generic conditional HasLaw. -/
theorem tail_32_mass : afterFirst {π | tailOrder π = [3, 2]} = 1 / 2 := by
  calc
    _ = (Nat.factorial remaining.card : ℝ≥0∞)⁻¹ :=
      mass_of_law tail_hasLaw [3, 2] (by decide)
    _ = 1 / 2 := by norm_num [remaining, selected, one_div]

/-- A repeated output is outside the conditional tail support. -/
theorem repeated_tail_mass_zero : afterFirst {π | tailOrder π = [2, 2]} = 0 := by
  have hbad : ([2, 2] : List (Fin 4)) ∉ orders positions (selected.erase 0) := by
    decide
  calc
    _ = if ([2, 2] : List (Fin 4)) ∈ orders positions (selected.erase 0)
        then (Nat.factorial (selected.erase 0).card : ℝ≥0∞)⁻¹ else 0 :=
      cond_tail_eq positions positions_nodup positions_complete
        selected 0 (by decide) [2, 2]
    _ = 0 := if_neg hbad

def filteredTail (π : Equiv.Perm (Fin 4)) : List (Fin 4) :=
  (tailOrder π).filter (fun b => decide (b ∈ ({3} : Finset (Fin 4))))

/-- Filtering the actual conditional tail retains its observed-law meaning. -/
theorem filtered_tail_hasLaw :
    HasLaw filteredTail
      (uniformOn (orders positions {3} : Set (List (Fin 4)))) afterFirst := by
  exact hasLaw_filter_tail_cond_first positions positions_nodup positions_complete
    selected 0 (by decide) observed_hasLaw {3} (by decide)

/-- The filter equals the original same-sample projection on the head event. -/
theorem filtered_tail_eq_projection (π : Equiv.Perm (Fin 4))
    (hπ : π ∈ firstEvent observedOrder 0) :
    filteredTail π = restrictedOrder positions {3} π := by
  exact filter_tail_restrictedOrder_eq positions positions_nodup
    selected 0 π hπ {3} (by decide)

theorem filtered_tail_mass : afterFirst {π | filteredTail π = [3]} = 1 := by
  simpa using mass_of_law filtered_tail_hasLaw [3] (by decide)

/-- The actual remaining-subset projection has that law in the same environment. -/
theorem remaining_projection_map :
    afterFirst.map (restrictedOrder positions {3}) =
      uniformOn (orders positions {3} : Set (List (Fin 4))) := by
  exact map_restrictedOrder_cond_first positions positions_nodup positions_complete
    selected 0 (by decide) {3} (by decide)

/-- Conditioning changes the full environment, even though a tail stays uniform. -/
theorem afterFirst_first_event_mass : afterFirst (firstEvent observedOrder 0) = 1 := by
  apply cond_apply_self
  · rw [first_mass]
    norm_num
  · rw [first_mass]
    norm_num

theorem environment_changed : afterFirst ≠ law := by
  intro h
  have hmass := congrArg
    (fun μ : Measure (Equiv.Perm (Fin 4)) => μ (firstEvent observedOrder 0)) h
  rw [afterFirst_first_event_mass, first_mass] at hmass
  norm_num at hmass

/-- A second head law is derived under afterFirst, using only its tail HasLaw. -/
theorem second_head_mass : afterFirst (firstEvent tailOrder 2) = 1 / 2 := by
  calc
    _ = (remaining.card : ℝ≥0∞)⁻¹ :=
      head_mass_of_hasLaw positions positions_nodup positions_complete
        remaining 2 (by decide) tail_hasLaw
    _ = 1 / 2 := by norm_num [remaining, selected, one_div]

noncomputable def afterSecond : Measure (Equiv.Perm (Fin 4)) :=
  afterFirst[|firstEvent tailOrder 2]

def lastTail (π : Equiv.Perm (Fin 4)) : List (Fin 4) := (tailOrder π).tail

/-- The generic law is reused with the changed source measure and smaller set. -/
theorem last_tail_hasLaw :
    HasLaw lastTail
      (uniformOn (orders positions (remaining.erase 2) : Set (List (Fin 4))))
      afterSecond := by
  exact hasLaw_tail_cond_first positions positions_nodup positions_complete
    remaining 2 (by decide) tail_hasLaw

theorem last_tail_mass : afterSecond {π | lastTail π = [3]} = 1 := by
  calc
    _ = (Nat.factorial (remaining.erase 2).card : ℝ≥0∞)⁻¹ :=
      mass_of_law last_tail_hasLaw [3] (by decide)
    _ = 1 := by norm_num [remaining, selected]

end Examples.PermutationTail
