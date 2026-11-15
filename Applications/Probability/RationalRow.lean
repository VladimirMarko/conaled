import Applications.Probability.FiniteKernel
import Mathlib.Algebra.BigOperators.Fin

/-!
# Prepared finite rows

Natural multiplicities represent an exact row. Selection uses cumulative finite
intervals, not a materialized list of tickets. An executable enumeration is
explicit whenever a rational table is prepared; no arbitrary finite enumeration
is selected by classical choice.
-/
namespace Applications.Probability
open scoped BigOperators ENNReal

structure PreparedRow (β : Type) where
  size : ℕ
  weight : Fin size → ℕ
  outcome : Fin size → β
  total : ℕ
  total_eq : total = ∑ i, weight i
  positive : 0 < total

namespace PreparedRow
variable {β : Type} (p : PreparedRow β)

def select (i : Fin p.total) : β := p.outcome (finSigmaFinEquiv.symm (Fin.cast p.total_eq i)).1

theorem sum_select (f : β → ℝ≥0∞) :
    ∑ i : Fin p.total, f (p.select i) = ∑ j, (p.weight j : ℝ≥0∞)*f (p.outcome j) := by
  let e : ((j : Fin p.size) × Fin (p.weight j)) ≃ Fin p.total :=
    finSigmaFinEquiv.trans (finCongr p.total_eq.symm)
  calc
    _ = ∑ j : (i : Fin p.size) × Fin (p.weight i), f (p.select (e j)) :=
      (Equiv.sum_comp e (fun i => f (p.select i))).symm
    _ = _ := by simp [e,select,Fintype.sum_sigma]

end PreparedRow
namespace RationalWeights
variable {m : ℕ}

def denominator (q : Fin m → ℚ) : ℕ := ∏ i, (q i).den
def weight (q : Fin m → ℚ) (i : Fin m) : ℕ :=
  (q i).num.toNat * (denominator q / (q i).den)

theorem denominator_pos (q : Fin m → ℚ) : 0 < denominator q :=
  Finset.prod_pos (fun i _ => (q i).den_pos)

theorem weight_cast (q : Fin m → ℚ) (hq : ∀ i, 0≤q i) (i : Fin m) :
    (weight q i : ℚ)=q i * denominator q := by
  have hd : (q i).den ∣ denominator q := Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hc : ((denominator q / (q i).den : ℕ) : ℚ)*(q i).den=denominator q := by
    exact_mod_cast Nat.div_mul_cancel hd
  have hn : ((q i).num.toNat : ℚ)=(q i).num := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hq i))
  have hz : ((q i).den : ℚ)≠0 := by exact_mod_cast (q i).den_nz
  apply mul_right_cancel₀ hz
  simp only [weight,Nat.cast_mul,hn]
  rw [mul_assoc,hc, mul_right_comm (q i),Rat.mul_den_eq_num]

theorem sum_weight (q : Fin m → ℚ) (hq : ∀ i, 0≤q i) (hs : ∑ i,q i=1) :
    ∑ i,weight q i=denominator q := by
  have he : ((∑ i,weight q i : ℕ) : ℚ)=denominator q := by
    simp only [Nat.cast_sum,weight_cast q hq,← Finset.sum_mul,hs,one_mul]
  exact_mod_cast he

theorem weight_mass (q : Fin m → ℚ) (hq : ∀ i, 0≤q i) (i : Fin m) :
    (weight q i : ℝ≥0∞)*(denominator q : ℝ≥0∞)⁻¹=mass (q i) := by
  have hn (k : ℕ) : mass (k : ℚ)=(k : ℝ≥0∞) := by simp [mass]
  have h := congrArg mass (weight_cast q hq i)
  rw [hn,mass_mul _ _ (hq i),hn] at h
  rw [h,mul_assoc,ENNReal.mul_inv_cancel,mul_one]
  · exact_mod_cast Nat.ne_of_gt (denominator_pos q)
  · simp

end RationalWeights

namespace Table
variable {α β : Type} [Fintype β] {m : ℕ}

/-- Preparation computes a common denominator and integer multiplicities.
The supplied equivalence is part of the executable finite representation. -/
def prepare (t : Table α β) (e : Fin m ≃ β) (x : α) : PreparedRow β :=
  let q := fun i => t.entry x (e i)
  let d := RationalWeights.denominator q
  let data := Array.ofFn (fun i => (q i).num.toNat*(d/(q i).den))
  { size := m
    weight := fun i => data[i.val]'(by simp [data])
    outcome := e
    total := d
    total_eq := by
      dsimp [data]
      simp only [Array.getElem_ofFn]
      exact (RationalWeights.sum_weight q (fun i => t.nonneg x (e i))
        ((e.sum_comp (t.entry x)).trans (t.sum_row x))).symm
    positive := RationalWeights.denominator_pos q }

theorem prepare_total (t : Table α β) (e : Fin m ≃ β) (x : α) :
    (t.prepare e x).total=RationalWeights.denominator (fun i => t.entry x (e i)) := rfl

theorem prepare_weight (t : Table α β) (e : Fin m ≃ β) (x : α) (i : Fin m) :
    (t.prepare e x).weight i=RationalWeights.weight (fun i => t.entry x (e i)) i := by
  simp [prepare,RationalWeights.weight]

/-- Materialize all rows once when an executable input enumeration is supplied. -/
def compile {l : ℕ} (t : Table α β) (input : Fin l ≃ α) (output : Fin m ≃ β) :
    α → PreparedRow β :=
  let rows := Array.ofFn (fun i => t.prepare output (input i))
  fun x => rows[(input.symm x).val]'(by simp [rows])

theorem compile_eq {l : ℕ} (t : Table α β) (input : Fin l ≃ α) (output : Fin m ≃ β)
    (x : α) : t.compile input output x=t.prepare output x := by
  simp [compile]

end Table
end Applications.Probability
