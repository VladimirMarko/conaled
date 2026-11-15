import Applications.Probability.CoinPaths
import Mathlib.Probability.Independence.InfinitePi

/-!
# Independent finite prefixes and infinite coin suffixes

Shared fixed-cut facts for bit-consuming samplers. Random-cursor uses must
separately prove their operational stopping events depend on consumed prefixes.
-/
namespace Applications.Probability.CoinSuffix
open CoinPaths MeasureTheory
open scoped ENNReal

/-- Reindex the entire unused suffix, with no finite truncation. -/
def suffix (n : ℕ) (ω : Tape) : Tape := fun i => ω (n+i)

theorem measurable_suffix (n : ℕ) : Measurable (suffix n) := by
  unfold suffix
  fun_prop

theorem suffix_law (n : ℕ) : law.map (suffix n) = law := by
  exact Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => fairCoin)
    (f := fun i => n+i) (by intro i j h; exact Nat.add_left_cancel h)

/-- The finite prefix is independent of the entire infinite suffix. -/
theorem prefix_suffix_independent (n : ℕ) :
    ProbabilityTheory.IndepFun (fun ω : Tape => fun i : Fin n => ω i)
      (suffix n) law := by
  have hi : ProbabilityTheory.iIndepFun (fun i (ω : Tape) => ω i) law :=
    ProbabilityTheory.iIndepFun_infinitePi (X := fun _ (b : Bool) => b)
      (fun _ => measurable_id)
  have hd : Disjoint {i : ℕ | i < n} {i : ℕ | n ≤ i} := by
    rw [Set.disjoint_left]
    intro i h1 h2
    exact Nat.not_lt_of_ge h2 h1
  have h := hi.indepFun_set {i | i < n} {i | n ≤ i} hd
    (fun i => measurable_pi_apply i)
  exact h.comp
    (φ := fun f => fun i : Fin n => f ⟨i, i.isLt⟩)
    (ψ := fun f : ({i : ℕ | n ≤ i} → Bool) => fun i : ℕ => f ⟨n+i, Nat.le_add_right n i⟩)
    (by fun_prop) (by fun_prop)

theorem prefix_suffix_mass (n : ℕ) (E : Set (Fin n → Bool)) (B : Set Tape)
    (hB : MeasurableSet B) :
    law ({ω | (fun i : Fin n => ω i) ∈ E} ∩ suffix n ⁻¹' B) =
      law {ω | (fun i : Fin n => ω i) ∈ E} * law B := by
  have h := (prefix_suffix_independent n).measure_inter_preimage_eq_mul E B
    (Set.to_countable E).measurableSet hB
  rw [← Measure.map_apply (measurable_suffix n) hB, suffix_law] at h
  exact h

/-- Event membership is determined by the first `cut` tape coordinates. -/
def PrefixEvent (cut : ℕ) (E : Set Tape) : Prop :=
  ∀ ω η, (∀ i, i<cut → ω i=η i) → (ω ∈ E ↔ η ∈ E)

/-- A prefix-dependent event factors against any measurable infinite suffix
observation. Callers must establish prefix dependence for their actual event. -/
theorem prefix_event_mass (cut : ℕ) (E B : Set Tape) (hE : PrefixEvent cut E)
    (hB : MeasurableSet B) :
    law (E ∩ suffix cut ⁻¹' B)=law E*law B := by
  let extend (f : Fin cut → Bool) : Tape := fun i => if h : i<cut then f ⟨i,h⟩ else false
  let F : Set (Fin cut → Bool) := {f | extend f ∈ E}
  have he : {ω : Tape | (fun i : Fin cut => ω i) ∈ F}=E := by
    ext ω
    exact (hE ω (extend (fun i => ω i)) (by intro i hi; simp [extend,hi])).symm
  have h := prefix_suffix_mass cut F B hB
  rwa [he] at h

end Applications.Probability.CoinSuffix
