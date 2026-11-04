import Applications.Probability.PermutationMinimum
import Examples.PermutationMinimumBoundary
import Mathlib.Tactic

/-!
# Subset minima under one global random ranking

One uniformly sampled permutation of three key indices determines every
priority in this example. The two subsets `{0, 1}` and `{1, 2}` share index
one and the same sampled ranking. Each subset gives that index probability
`1/2` of being first, while the intersection has probability `1/3`.

These claims use the public minimum law and its event-intersection bridge.
They do not replace the shared environment by independently chosen subset
orders. A second specialization uses injective, nonmonotone integer priorities
with a negative value and unequal gaps: numeric priority values need not be
ordinal positions, and the priority target need not be finite.

The examples supply no treap construction or sorting execution. Those clients
still need deterministic minimum/root/comparison bridges and their actual
conditional sampling and resource observations.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Examples.PermutationMinimum

open MeasureTheory ProbabilityTheory
open Applications.Probability.PermutationMinimum
open scoped ENNReal

local instance : MeasurableSpace (Equiv.Perm (Fin 3)) := ⊤
local instance : MeasurableSingletonClass (Equiv.Perm (Fin 3)) :=
  ⟨fun _ => trivial⟩

/-- One common random permutation, mapping key indices to priority labels. -/
noncomputable def law : Measure (Equiv.Perm (Fin 3)) := uniformOn Set.univ

local instance : IsProbabilityMeasure law := by
  unfold law
  infer_instance

def firstSubset : Finset (Fin 3) := {0, 1}
def secondSubset : Finset (Fin 3) := {1, 2}

theorem first_minimum_mass :
    law (minimumEvent id firstSubset 1) = 1 / 2 := by
  simpa [law, firstSubset, one_div] using
    (uniformOn_minimumEvent (id : Fin 3 → Fin 3) Function.injective_id
      firstSubset 1 (by simp [firstSubset]))

theorem second_minimum_mass :
    law (minimumEvent id secondSubset 1) = 1 / 2 := by
  simpa [law, secondSubset, one_div] using
    (uniformOn_minimumEvent (id : Fin 3 → Fin 3) Function.injective_id
      secondSubset 1 (by simp [secondSubset]))

/-- The two observations ask about the same minimum on the union. -/
theorem overlap_event :
    minimumEvent id firstSubset 1 ∩ minimumEvent id secondSubset 1 =
      minimumEvent id Finset.univ 1 := by
  rw [minimumEvent_inter id firstSubset secondSubset 1
    (by simp [firstSubset]) (by simp [secondSubset])]
  have hcover : firstSubset ∪ secondSubset = Finset.univ := by
    ext a
    fin_cases a <;> simp [firstSubset, secondSubset]
  rw [hcover]

theorem full_minimum_mass (a : Fin 3) :
    law (minimumEvent id Finset.univ a) = 1 / 3 := by
  simpa [law, one_div] using
    (uniformOn_minimumEvent (id : Fin 3 → Fin 3) Function.injective_id
      Finset.univ a (Finset.mem_univ a))

theorem overlap_mass :
    law (minimumEvent id firstSubset 1 ∩ minimumEvent id secondSubset 1) =
      1 / 3 := by
  rw [overlap_event]
  exact full_minimum_mass 1

theorem marginal_product :
    law (minimumEvent id firstSubset 1) *
      law (minimumEvent id secondSubset 1) = 1 / 4 := by
  rw [first_minimum_mass, second_minimum_mass]
  norm_num [← ENNReal.coe_div, ← ENNReal.coe_mul]

/-- Uniform marginals on overlapping subsets do not assert their independence. -/
theorem overlap_mass_ne_product :
    law (minimumEvent id firstSubset 1 ∩ minimumEvent id secondSubset 1) ≠
      law (minimumEvent id firstSubset 1) *
        law (minimumEvent id secondSubset 1) := by
  rw [overlap_mass, marginal_product]
  norm_num [← ENNReal.coe_div]

theorem singleton_minimum_mass (a : Fin 3) :
    law (minimumEvent id {a} a) = 1 := by
  simpa [law] using
    (uniformOn_minimumEvent (id : Fin 3 → Fin 3) Function.injective_id
      {a} a (Finset.mem_singleton_self a))

/-- Distinct integer labels with a negative value and unequal ordered gaps. -/
def spacedPriority (a : Fin 3) : Int :=
  if a.val = 0 then -7 else if a.val = 1 then 100 else 4

theorem spacedPriority_values :
    spacedPriority 0 = -7 ∧ spacedPriority 1 = 100 ∧ spacedPriority 2 = 4 := by
  decide

theorem spacedPriority_injective : Function.Injective spacedPriority := by
  intro a b hab
  fin_cases a <;> fin_cases b <;> norm_num [spacedPriority] at hab ⊢

theorem spacedPriority_not_monotone : ¬ Monotone spacedPriority := by
  intro h
  have h12 := h (show (1 : Fin 3) ≤ 2 by decide)
  norm_num [spacedPriority] at h12

/-- Only injectivity and the target's linear order matter for the minimum law. -/
theorem spaced_minimum_mass :
    law (minimumEvent spacedPriority secondSubset 2) = 1 / 2 := by
  simpa [law, secondSubset, one_div] using
    (uniformOn_minimumEvent spacedPriority spacedPriority_injective
      secondSubset 2 (by simp [secondSubset]))

end Examples.PermutationMinimum
