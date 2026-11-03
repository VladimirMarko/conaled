import Applications.EditAlignment.Cached
import Applications.Optimization.Relations

/-! Ordered witnesses and attained optimum costs share an independent feasible set. -/
set_option autoImplicit false
set_option warningAsError true

namespace EditAlignment
variable {α : Type}

abbrev Problem (α : Type) := List α × List α

def feasible (i : Problem α) : Set (Script α) := {es | Aligns es i.1 i.2}

theorem minimumEdit_iff_minimizer (xs ys : List α) (es : Script α) :
    MinimumEdit es xs ys ↔ es ∈ Optimization.minimizers (feasible (xs, ys)) costE :=
  Iff.rfl

theorem minimumEdit_cost_unique {xs ys : List α} {es fs : Script α}
    (he : MinimumEdit es xs ys) (hf : MinimumEdit fs xs ys) : costE es = costE fs :=
  Nat.le_antisymm (he.2 _ hf.1) (hf.2 _ he.1)

/-- Either implementation can realize the same independent optimal-witness contract. -/
def witnessSquare (solve : Problem α → Script α)
    (correct : ∀ i, MinimumEdit (solve i) i.1 i.2) :
    Relational.RelSquare (Optimization.inputRep (Problem α))
      (Optimization.membershipRep (I := Problem α) (id : Script α → Script α)) :=
  Optimization.selectionSquare feasible (fun _ => costE) id solve
    (fun i => (minimumEdit_iff_minimizer ..).mp (correct i))

def costSquare (solve : Problem α → Script α)
    (correct : ∀ i, MinimumEdit (solve i) i.1 i.2) :
    Relational.RelSquare (Optimization.inputRep (Problem α))
      (Optimization.membershipRep (I := Problem α) (id : Nat → Nat)) :=
  Relational.compose (Optimization.observationSquare costE) (witnessSquare solve correct)

variable [DecidableEq α]

def uncachedWitnessSquare := witnessSquare (fun i : Problem α => mce2 i.1 i.2)
  (fun i => mce2_spec i.1 i.2)

def cachedWitnessSquare := witnessSquare (fun i : Problem α => mce3 i.1 i.2)
  (fun i => mce3_spec i.1 i.2)

def uncachedCostSquare := costSquare (fun i : Problem α => mce2 i.1 i.2)
  (fun i => mce2_spec i.1 i.2)

/-- The executable observation reads the maintained cache. Its specification and
proof come from the shared cost observation composed with witness selection. -/
def cachedCostSquare : Relational.RelSquare (Optimization.inputRep (Problem α))
    (Optimization.membershipRep (I := Problem α) (id : Nat → Nat)) where
  impl i := (i, (mce3Result i.1 i.2).1)
  spec := (costSquare (fun i => mce3 i.1 i.2) (fun i => mce3_spec i.1 i.2)).spec
  preserves := by
    intro i j h
    change i = j at h
    subst j
    have hc := (costSquare (fun i : Problem α => mce3 i.1 i.2)
      (fun i => mce3_spec i.1 i.2)).preserves (r := i) (s := i) rfl
    change i = i ∧ (mce3Result i.1 i.2).1 ∈ _
    rw [mce3_cache_correct]
    exact hc

theorem selected_witness (i : Problem α) :
    MinimumEdit (uncachedWitnessSquare.impl i).2 i.1 i.2 ∧
      MinimumEdit (cachedWitnessSquare.impl i).2 i.1 i.2 := by
  exact ⟨(minimumEdit_iff_minimizer ..).mpr
    (uncachedWitnessSquare.preserves (r := i) (s := i) rfl).2,
    (minimumEdit_iff_minimizer ..).mpr
    (cachedWitnessSquare.preserves (r := i) (s := i) rfl).2⟩

theorem uncached_cost_attained (i : Problem α) :
    ∃ es, MinimumEdit es i.1 i.2 ∧ costE es = (uncachedCostSquare.impl i).2 := by
  obtain ⟨es, he, hc⟩ := (uncachedCostSquare.preserves (r := i) (s := i) rfl).2
  exact ⟨es, (minimumEdit_iff_minimizer ..).mpr he, hc⟩

theorem cached_cost_attained (i : Problem α) :
    ∃ es, MinimumEdit es i.1 i.2 ∧ costE es = (cachedCostSquare.impl i).2 := by
  obtain ⟨es, he, hc⟩ := (cachedCostSquare.preserves (r := i) (s := i) rfl).2
  exact ⟨es, (minimumEdit_iff_minimizer ..).mpr he, hc⟩

theorem observed_cost_agreement (i : Problem α) :
    (uncachedCostSquare.impl i).2 = (cachedCostSquare.impl i).2 := by
  obtain ⟨es, he, hc⟩ := uncached_cost_attained i
  obtain ⟨fs, hf, hd⟩ := cached_cost_attained i
  exact hc.symm.trans ((minimumEdit_cost_unique he hf).trans hd)

theorem cached_cost_eq_of_minimum (i : Problem α) (es : Script α)
    (he : MinimumEdit es i.1 i.2) : (cachedCostSquare.impl i).2 = costE es := by
  obtain ⟨fs, hf, hc⟩ := cached_cost_attained i
  exact hc.symm.trans (minimumEdit_cost_unique hf he)

end EditAlignment
