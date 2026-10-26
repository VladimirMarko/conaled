import Applications.Connectivity.ParentArray

set_option autoImplicit false
set_option warningAsError true

/-! Concrete ParentForest proofs adapted from adwh-checkpoint-233.
Source members and declaration dispositions: docs/research/adwh-connectivity-provenance.tsv.
Operations retain the source failure and representative-selection behavior. -/

namespace Connectivity.ParentForest

open ParentArray

abbrev capacity (ds : DSA) : Nat := ds.namesA.size

def Valid (ds : DSA) (v : Int) : Prop :=
  0 < v ∧ v.toNat ≤ capacity ds

instance (ds : DSA) (v : Int) : Decidable (Valid ds v) :=
  inferInstanceAs (Decidable (0 < v ∧ v.toNat ≤ capacity ds))

/-- A specification accessor. Forest dimensions make the read successful. -/
def cache (ds : DSA) (v : Int) : Int :=
  (readCell ds.sizesA v).getD 0

def SelfRoot (ds : DSA) (r : Int) : Prop :=
  readCell ds.namesA r = some r

instance (ds : DSA) (r : Int) : Decidable (SelfRoot ds r) :=
  inferInstanceAs (Decidable (readCell ds.namesA r = some r))

def Root (ds : DSA) (v r : Int) : Prop :=
  ∃ k, RootSteps ds v r k

structure Forest (ds : DSA) : Prop where
  dimensions : ds.sizesA.size = ds.namesA.size
  parents_valid : ∀ v p, Valid ds v →
    readCell ds.namesA v = some p → Valid ds p
  cache_positive : ∀ v, Valid ds v → 0 < cache ds v
  cache_bounded : ∀ v, Valid ds v → cache ds v ≤ (capacity ds : Int)
  cache_grows : ∀ v p, Valid ds v →
    readCell ds.namesA v = some p → p ≠ v → cache ds v < cache ds p

structure WeightedForest (ds : DSA) : Prop extends Forest ds where
  cache_doubles : ∀ v p, Valid ds v →
    readCell ds.namesA v = some p → p ≠ v → 2 * cache ds v ≤ cache ds p

theorem valid_of_parent_read {ds : DSA} {v p : Int}
    (h : readCell ds.namesA v = some p) : Valid ds v := by
  obtain ⟨hv, hi, _⟩ := (readCell_some_iff ds.namesA v p).mp h
  constructor
  · exact hv
  · unfold capacity
    omega

theorem valid_iff_parent_read (ds : DSA) (v : Int) :
    Valid ds v ↔ ∃ p, readCell ds.namesA v = some p := by
  constructor
  · intro hv
    cases hr : readCell ds.namesA v with
    | none =>
        have hn := (readCell_none_iff ds.namesA v).mp hr
        unfold Valid capacity at hv
        omega
    | some p => exact ⟨p, rfl⟩
  · rintro ⟨p, hp⟩
    exact valid_of_parent_read hp

theorem cache_eq_of_read {ds : DSA} {v s : Int}
    (h : readCell ds.sizesA v = some s) : cache ds v = s := by
  simp [cache, h]

theorem cache_read_of_dimensions {ds : DSA}
    (hd : ds.sizesA.size = ds.namesA.size) {v : Int}
    (hv : Valid ds v) : readCell ds.sizesA v = some (cache ds v) := by
  cases hr : readCell ds.sizesA v with
  | none =>
      have hn := (readCell_none_iff ds.sizesA v).mp hr
      unfold Valid capacity at hv
      omega
  | some s => simp [cache, hr]

theorem Forest.cache_read {ds : DSA} (hF : Forest ds) {v : Int}
    (hv : Valid ds v) : readCell ds.sizesA v = some (cache ds v) :=
  cache_read_of_dimensions hF.dimensions hv

theorem rootSteps_valid_start {ds : DSA} {v r : Int} {k : Nat}
    (h : RootSteps ds v r k) : Valid ds v := by
  cases h with
  | root read => exact valid_of_parent_read read
  | step read _ _ => exact valid_of_parent_read read

theorem rootSteps_selfRoot {ds : DSA} {v r : Int} {k : Nat}
    (h : RootSteps ds v r k) : SelfRoot ds r := by
  induction h with
  | root read => exact read
  | step _ _ _ ih => exact ih

theorem Root.valid_start {ds : DSA} {v r : Int}
    (h : Root ds v r) : Valid ds v := by
  obtain ⟨k, hk⟩ := h
  exact rootSteps_valid_start hk

theorem Root.selfRoot {ds : DSA} {v r : Int}
    (h : Root ds v r) : SelfRoot ds r := by
  obtain ⟨k, hk⟩ := h
  exact rootSteps_selfRoot hk

theorem Root.valid_root {ds : DSA} {v r : Int}
    (h : Root ds v r) : Valid ds r := valid_of_parent_read h.selfRoot

theorem root_self {ds : DSA} {r : Int} (h : SelfRoot ds r) : Root ds r r :=
  ⟨0, RootSteps.root h⟩

theorem Root.unique {ds : DSA} {v r s : Int}
    (hr : Root ds v r) (hs : Root ds v s) : r = s := by
  obtain ⟨k, hk⟩ := hr
  obtain ⟨l, hl⟩ := hs
  exact (hk.unique hl).1

theorem findDSA_invalid {ds : DSA} {v : Int} (hv : ¬ Valid ds v) :
    findDSA ds v = none := by
  cases hf : findDSA ds v with
  | none => rfl
  | some r =>
      obtain ⟨k, hk, _⟩ := (findDSA_some_iff_rootSteps ds v r).mp hf
      exact False.elim (hv (rootSteps_valid_start hk))

theorem Forest.path_below_fuel {ds : DSA} (hF : Forest ds)
    (fuel : Nat) {v : Int} (hv : Valid ds v)
    (enough : (capacity ds : Int) < cache ds v + (fuel : Int)) :
    ∃ r k, RootSteps ds v r k ∧ k < fuel := by
  induction fuel generalizing v with
  | zero =>
      have hb := hF.cache_bounded v hv
      omega
  | succ fuel ih =>
      obtain ⟨p, hp⟩ := (valid_iff_parent_read ds v).mp hv
      by_cases he : p = v
      · subst p
        exact ⟨v, 0, RootSteps.root hp, Nat.zero_lt_succ _⟩
      · have hpv := hF.parents_valid v p hv hp
        have hg := hF.cache_grows v p hv hp he
        obtain ⟨r, k, hk, hlt⟩ := ih hpv (by omega)
        exact ⟨r, k + 1, RootSteps.step hp he hk, by omega⟩

theorem Forest.path_cache_growth {ds : DSA} (hF : Forest ds)
    {v r : Int} {k : Nat} (path : RootSteps ds v r k) :
    cache ds v + (k : Int) ≤ cache ds r := by
  induction path with
  | root _ => omega
  | @step v p r k read nonself tail ih =>
      have hv : Valid ds v := valid_of_parent_read read
      have hg := hF.cache_grows v p hv read nonself
      omega

theorem Forest.path_lt_capacity {ds : DSA} (hF : Forest ds)
    {v r : Int} {k : Nat} (path : RootSteps ds v r k) : k < capacity ds := by
  have hp := hF.cache_positive v (rootSteps_valid_start path)
  have hb := hF.cache_bounded r (valid_of_parent_read (rootSteps_selfRoot path))
  have hg := hF.path_cache_growth path
  omega

theorem Forest.valid_path {ds : DSA} (hF : Forest ds) {v : Int}
    (hv : Valid ds v) : ∃ r k, RootSteps ds v r k ∧ k < capacity ds := by
  apply hF.path_below_fuel (capacity ds) hv
  have hp := hF.cache_positive v hv
  omega

theorem Forest.valid_root_exists {ds : DSA} (hF : Forest ds) {v : Int}
    (hv : Valid ds v) : ∃ r, Root ds v r := by
  obtain ⟨r, k, hk, _⟩ := hF.valid_path hv
  exact ⟨r, k, hk⟩

theorem Forest.findDSA_iff_Root {ds : DSA} (hF : Forest ds) (v r : Int) :
    findDSA ds v = some r ↔ Root ds v r := by
  constructor
  · intro h
    obtain ⟨k, hk, _⟩ := (findDSA_some_iff_rootSteps ds v r).mp h
    exact ⟨k, hk⟩
  · rintro ⟨k, hk⟩
    exact (findDSA_some_iff_rootSteps ds v r).mpr ⟨k, hk, hF.path_lt_capacity hk⟩

theorem Forest.find_complete {ds : DSA} (hF : Forest ds) {v : Int}
    (hv : Valid ds v) : ∃ r, findDSA ds v = some r := by
  obtain ⟨r, hr⟩ := hF.valid_root_exists hv
  exact ⟨r, (hF.findDSA_iff_Root v r).mpr hr⟩

theorem Forest.find_none_iff_invalid {ds : DSA} (hF : Forest ds) (v : Int) :
    findDSA ds v = none ↔ ¬ Valid ds v := by
  constructor
  · intro hn hv
    obtain ⟨r, hr⟩ := hF.find_complete hv
    rw [hn] at hr
    cases hr
  · exact findDSA_invalid

theorem Forest.find_source_recurrence {ds : DSA} (hF : Forest ds) {v : Int}
    (hv : Valid ds v) :
    findDSA ds v =
      match readCell ds.namesA v with
      | none => none
      | some p => if p = v then some v else findDSA ds p := by
  obtain ⟨r, k, hk, hlt⟩ := hF.valid_path hv
  exact findDSA_source_recurrence hk hlt

theorem valid_startDSA_iff (n v : Int) :
    Valid (startDSA n) v ↔ 0 < v ∧ v ≤ n := by
  have hs := (startDSA_sizes n).1
  unfold Valid capacity
  rw [hs]
  omega

theorem cache_startDSA {n v : Int} (hv : Valid (startDSA n) v) :
    cache (startDSA n) v = 1 := by
  obtain ⟨hpos, hle⟩ := (valid_startDSA_iff n v).mp hv
  exact cache_eq_of_read (startDSA_cache n v hpos hle)

theorem startDSA_forest (n : Int) : Forest (startDSA n) := by
  constructor
  · exact (startDSA_sizes n).2.trans (startDSA_sizes n).1.symm
  · intro v p hv hp
    obtain ⟨hpos, hle⟩ := (valid_startDSA_iff n v).mp hv
    have he := startDSA_parent n v hpos hle
    have h : p = v := Option.some.inj (hp.symm.trans he)
    simpa [h] using hv
  · intro v hv
    rw [cache_startDSA hv]
    omega
  · intro v hv
    rw [cache_startDSA hv]
    have hs := (startDSA_sizes n).1
    have hv' := hv
    unfold Valid capacity at hv'
    change (1 : Int) ≤ ((startDSA n).namesA.size : Int)
    rw [hs]
    omega
  · intro v p hv hp hne
    obtain ⟨hpos, hle⟩ := (valid_startDSA_iff n v).mp hv
    have he := startDSA_parent n v hpos hle
    exact False.elim (hne (Option.some.inj (hp.symm.trans he)))

theorem startDSA_weightedForest (n : Int) : WeightedForest (startDSA n) := by
  refine ⟨startDSA_forest n, ?_⟩
  intro v p hv hp hne
  obtain ⟨hpos, hle⟩ := (valid_startDSA_iff n v).mp hv
  have he := startDSA_parent n v hpos hle
  exact False.elim (hne (Option.some.inj (hp.symm.trans he)))

theorem root_start_iff (n v r : Int) :
    Root (startDSA n) v r ↔ Valid (startDSA n) v ∧ r = v := by
  constructor
  · intro hr
    have hv := hr.valid_start
    obtain ⟨hpos, hle⟩ := (valid_startDSA_iff n v).mp hv
    exact ⟨hv, hr.unique (root_self (startDSA_parent n v hpos hle))⟩
  · rintro ⟨hv, he⟩
    subst r
    obtain ⟨hpos, hle⟩ := (valid_startDSA_iff n v).mp hv
    exact root_self (startDSA_parent n v hpos hle)

end Connectivity.ParentForest
