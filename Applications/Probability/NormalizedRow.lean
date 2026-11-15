import Applications.Probability.TableSampler

/-! LCM preparation preserves rational weights while reducing the ticket range. -/
namespace Applications.Probability.NormalizedWeights
open scoped BigOperators ENNReal

/-- A finite reverse fold. The operation count records actual LCM applications. -/
def common : (m : ℕ) → (Fin m → ℕ) → ℕ × ℕ
  | 0, _ => (1, 0)
  | n+1, f =>
    let r := common n (fun i => f i.castSucc)
    (Nat.lcm r.1 (f (Fin.last n)), r.2+1)

theorem common_count (m : ℕ) (f : Fin m → ℕ) : (common m f).2=m := by
  induction m with
  | zero => rfl
  | succ n ih => simp [common, ih]

theorem common_pos (m : ℕ) (f : Fin m → ℕ) (hf : ∀ i, 0<f i) :
    0<(common m f).1 := by
  induction m with
  | zero => simp [common]
  | succ n ih => exact Nat.lcm_pos (ih _ (fun i => hf i.castSucc)) (hf _)

theorem dvd_common (m : ℕ) (f : Fin m → ℕ) (i : Fin m) : f i ∣ (common m f).1 := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    induction i using Fin.lastCases with
    | last => exact Nat.dvd_lcm_right _ _
    | cast i => exact (ih _ i).trans (Nat.dvd_lcm_left _ _)

theorem common_dvd (m : ℕ) (f : Fin m → ℕ) (d : ℕ) (hd : ∀ i, f i ∣ d) :
    (common m f).1 ∣ d := by
  induction m with
  | zero => exact one_dvd _
  | succ n ih => exact Nat.lcm_dvd (ih _ (fun i => hd i.castSucc)) (hd _)

variable {m : ℕ}
def denominator (q : Fin m → ℚ) : ℕ := (common m (fun i => (q i).den)).1
def weight (q : Fin m → ℚ) (i : Fin m) : ℕ :=
  (q i).num.toNat * (denominator q / (q i).den)

theorem denominator_pos (q : Fin m → ℚ) : 0<denominator q :=
  common_pos _ _ (fun i => (q i).den_pos)

theorem denominator_dvd_product (q : Fin m → ℚ) :
    denominator q ∣ RationalWeights.denominator q :=
  common_dvd _ _ _ (fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i))

theorem denominator_le_product (q : Fin m → ℚ) :
    denominator q ≤ RationalWeights.denominator q :=
  Nat.le_of_dvd (RationalWeights.denominator_pos q) (denominator_dvd_product q)

theorem weight_cast (q : Fin m → ℚ) (hq : ∀ i, 0≤q i) (i : Fin m) :
    (weight q i : ℚ)=q i * denominator q := by
  have hd : (q i).den ∣ denominator q := dvd_common _ _ i
  have hc : ((denominator q / (q i).den : ℕ) : ℚ)*(q i).den=denominator q := by
    exact_mod_cast Nat.div_mul_cancel hd
  have hn : ((q i).num.toNat : ℚ)=(q i).num := by
    exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hq i))
  have hz : ((q i).den : ℚ)≠0 := by exact_mod_cast (q i).den_nz
  apply mul_right_cancel₀ hz
  simp only [weight,Nat.cast_mul,hn]
  rw [mul_assoc,hc,mul_right_comm (q i),Rat.mul_den_eq_num]

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
end Applications.Probability.NormalizedWeights

namespace Applications.Probability.Table
open CoinPaths MeasureTheory
open scoped BigOperators ENNReal
variable {α β : Type} [Fintype β] {m : ℕ}

def prepareNormalized (t : Table α β) (e : Fin m ≃ β) (x : α) : PreparedRow β :=
  let q := fun i => t.entry x (e i)
  let d := NormalizedWeights.denominator q
  let data := Array.ofFn (fun i => (q i).num.toNat*(d/(q i).den))
  { size := m
    weight := fun i => data[i.val]'(by simp [data])
    outcome := e
    total := d
    total_eq := by
      dsimp [data]
      simp only [Array.getElem_ofFn]
      exact (NormalizedWeights.sum_weight q (fun i => t.nonneg x (e i))
        ((e.sum_comp (t.entry x)).trans (t.sum_row x))).symm
    positive := NormalizedWeights.denominator_pos q }

theorem prepareNormalized_weight (t : Table α β) (e : Fin m ≃ β) (x : α) (i : Fin m) :
    (t.prepareNormalized e x).weight i=NormalizedWeights.weight (fun i => t.entry x (e i)) i := by
  simp [prepareNormalized,NormalizedWeights.weight]

theorem prepareNormalized_total_le (t : Table α β) (e : Fin m ≃ β) (x : α) :
    (t.prepareNormalized e x).total≤(t.prepare e x).total :=
  NormalizedWeights.denominator_le_product _

theorem prepareNormalized_returns_mass [DecidableEq β]
    (t : Table α β) (e : Fin m ≃ β) (x : α) (s : ℕ) (b : β) :
    law ((t.prepareNormalized e x).returns s b)=mass (t.entry x b) := by
  rw [PreparedRow.returns_mass]
  rw [(t.prepareNormalized e x).sum_select
    (fun y => if y=b then ((t.prepareNormalized e x).total : ℝ≥0∞)⁻¹ else 0)]
  change (∑ i : Fin m, ((t.prepareNormalized e x).weight i : ℝ≥0∞)*
    (if e i=b then ((t.prepareNormalized e x).total : ℝ≥0∞)⁻¹ else 0))=_
  simp only [prepareNormalized_weight,mul_ite,mul_zero]
  have hw (i : Fin m) :
      (NormalizedWeights.weight (fun i => t.entry x (e i)) i : ℝ≥0∞)*
        ((t.prepareNormalized e x).total : ℝ≥0∞)⁻¹=mass (t.entry x (e i)) :=
    NormalizedWeights.weight_mass _ (fun i => t.nonneg x (e i)) i
  simp_rw [hw]
  exact (e.sum_comp (fun y => if y=b then mass (t.entry x y) else 0)).trans (by simp)
end Applications.Probability.Table
