import Applications.Search.Incremental.Core

/-! Local order facts used by the finite expansion argument. -/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Incremental
variable {n : Nat}

def priority (a : Cost) (h : ℚ) : Key := toLex (a + (h : Cost), a)

@[simp] theorem priority_le_iff (a b : Cost) (h : ℚ) :
    priority a h ≤ priority b h ↔ a ≤ b := by
  unfold priority
  rw [Prod.Lex.le_iff']
  induction a using WithTop.recTopCoe <;> induction b using WithTop.recTopCoe <;>
    simp +contextual [← WithTop.coe_add]


@[simp] theorem priority_lt_iff (a b : Cost) (h : ℚ) :
    priority a h < priority b h ↔ a < b := by
  rw [lt_iff_le_not_ge, priority_le_iff, priority_le_iff, ← lt_iff_le_not_ge]

theorem priority_mono {a b : Cost} (hab : a ≤ b) (h : ℚ) :
    priority a h ≤ priority b h := (priority_le_iff a b h).mpr hab

theorem priority_edge_lt {a c : Cost} {hu hv : ℚ}
    (ha : a ≠ ⊤) (hc : 0 < c) (hh : (hu : Cost) ≤ c + (hv : Cost)) :
    priority a hu < priority (a+c) hv := by
  induction a using WithTop.recTopCoe with
  | top => exact False.elim (ha rfl)
  | coe a =>
    induction c using WithTop.recTopCoe with
    | top => simp [priority, Prod.Lex.lt_iff]
    | coe c =>
      have hc' : (0 : ℚ) < c := by exact_mod_cast hc
      have hh' : hu ≤ c + hv := by exact_mod_cast hh
      rw [Prod.Lex.lt_iff]
      change ((a : Cost) + (hu : Cost) < ((a : Cost)+(c : Cost))+(hv : Cost)) ∨
        ((a : Cost)+(hu : Cost) = ((a : Cost)+(c : Cost))+(hv : Cost) ∧
          (a : Cost) < (a : Cost)+(c : Cost))
      simp only [← WithTop.coe_add, WithTop.coe_lt_coe, WithTop.coe_eq_coe]
      rcases lt_or_eq_of_le hh' with ht | he
      · exact Or.inl (by linarith)
      · exact Or.inr ⟨by linarith, by linarith⟩

theorem rhsValue_mono (w : Graph n) (start : Fin n) {g g' : Labels n}
    (hg : ∀ u, g u ≤ g' u) (v : Fin n) :
    rhsValue w start g v ≤ rhsValue w start g' v := by
  unfold rhsValue
  split
  · exact le_rfl
  · apply (le_predecessorMinimum_iff _ _ _ _).mpr
    intro u
    exact (predecessorMinimum_le w g u v).trans (add_le_add (hg u) le_rfl)

theorem rhsValue_change_decrease (w : Graph n) (start : Fin n)
    (g : Labels n) (u v : Fin n) (a : Cost)
    (hlt : rhsValue w start (Function.update g u a) v < rhsValue w start g v) :
    rhsValue w start (Function.update g u a) v = a + w u v := by
  have hv : v ≠ start := by intro he; subst v; simp at hlt
  simp only [rhsValue, ite_eq_right hv] at hlt ⊢
  obtain ⟨z, _, hz⟩ := Finset.exists_mem_eq_inf Finset.univ
    ⟨start, Finset.mem_univ start⟩ (fun z => Function.update g u a z + w z v)
  change predecessorMinimum w (Function.update g u a) v = _ at hz
  by_cases hzu : z = u
  · subst z; simpa using hz
  · have he : Function.update g u a z = g z := Function.update_of_ne hzu _ _
    rw [he] at hz
    exact False.elim (not_lt_of_ge (predecessorMinimum_le w g z v) (hz ▸ hlt))

theorem rhsValue_change_increase (w : Graph n) (start : Fin n)
    (g : Labels n) (u v : Fin n) (a : Cost)
    (hlt : rhsValue w start g v < rhsValue w start (Function.update g u a) v) :
    rhsValue w start g v = g u + w u v := by
  have hv : v ≠ start := by intro he; subst v; simp at hlt
  simp only [rhsValue, ite_eq_right hv] at hlt ⊢
  obtain ⟨z, _, hz⟩ := Finset.exists_mem_eq_inf Finset.univ
    ⟨start, Finset.mem_univ start⟩ (fun z => g z + w z v)
  change predecessorMinimum w g v = _ at hz
  by_cases hzu : z = u
  · subst z; exact hz
  · have he : Function.update g u a z = g z := Function.update_of_ne hzu _ _
    have hb := predecessorMinimum_le w (Function.update g u a) z v
    rw [he, ← hz] at hb
    exact False.elim (not_lt_of_ge hb hlt)

theorem update_le {g : Labels n} {u : Fin n} {a : Cost} (ha : a ≤ g u) :
    ∀ v, Function.update g u a v ≤ g v := by
  intro v
  by_cases hv : v = u
  · subst v; simpa using ha
  · simp [Function.update_of_ne hv]

theorem le_update {g : Labels n} {u : Fin n} {a : Cost} (ha : g u ≤ a) :
    ∀ v, g v ≤ Function.update g u a v := by
  intro v
  by_cases hv : v = u
  · subst v; simpa using ha
  · simp [Function.update_of_ne hv]

/-- Positive self-loops cannot disturb the newly attained one-step value. -/
theorem overconsistent_rhs (w : Graph n) (hw : Positive w) (start : Fin n)
    (g : Labels n) (u : Fin n) (hu : rhsValue w start g u < g u) :
    rhsValue w start (Function.update g u (rhsValue w start g u)) u = rhsValue w start g u := by
  apply le_antisymm
  · exact rhsValue_mono w start (update_le (le_of_lt hu)) u
  · by_cases hs : u = start
    · subst u; simp
    · simp only [rhsValue, ite_eq_right hs]
      apply (le_predecessorMinimum_iff _ _ _ _).mpr
      intro v
      by_cases hv : v = u
      · subst v
        simp only [Function.update_self]
        exact le_add_of_nonneg_right (le_of_lt (hw u u))
      · rw [Function.update_of_ne hv]
        exact predecessorMinimum_le w g v u

theorem overconsistent_key (w : Graph n) (hw : Positive w) (start : Fin n)
    (h : Fin n → ℚ) (g : Labels n) (u : Fin n) (hu : rhsValue w start g u < g u) :
    key w start h (Function.update g u (rhsValue w start g u)) u = key w start h g u := by
  unfold key labelKey
  rw [Function.update_self, overconsistent_rhs w hw start g u hu]
  simp [min_eq_right (le_of_lt hu)]

theorem decrease_new_key (w : Graph n) (hw : Positive w) (start : Fin n)
    (h : Fin n → ℚ) (hh : ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost))
    (g : Labels n) (u v : Fin n) (hu : rhsValue w start g u < g u)
    (hc : g v = rhsValue w start g v)
    (hn : Function.update g u (rhsValue w start g u) v ≠
      rhsValue w start (Function.update g u (rhsValue w start g u)) v) :
    key w start h g u < key w start h (Function.update g u (rhsValue w start g u)) v := by
  have hv : v ≠ u := by intro he; subst v; exact (ne_of_lt hu) hc.symm
  have hv' := Function.update_of_ne hv (rhsValue w start g u) g
  have hrle := rhsValue_mono w start (update_le (le_of_lt hu)) v
  have hrlt : rhsValue w start (Function.update g u (rhsValue w start g u)) v <
      rhsValue w start g v := by
    apply lt_of_le_of_ne hrle
    intro he
    exact hn (hv'.trans (hc.trans he.symm))
  have he := rhsValue_change_decrease w start g u v (rhsValue w start g u) hrlt
  have hf : rhsValue w start g u ≠ ⊤ := ne_top_of_lt hu
  have hp := priority_edge_lt hf (hw u v) (hh u v)
  change priority (min (g u) (rhsValue w start g u)) (h u) <
    priority (min (Function.update g u (rhsValue w start g u) v)
      (rhsValue w start (Function.update g u (rhsValue w start g u)) v)) (h v)
  rw [min_eq_right (le_of_lt hu), hv', hc, min_eq_right (le_of_lt hrlt), he]
  exact hp

theorem increase_new_key (w : Graph n) (hw : Positive w) (start : Fin n)
    (h : Fin n → ℚ) (hh : ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost))
    (g : Labels n) (u v : Fin n) (hu : g u < rhsValue w start g u)
    (hc : g v = rhsValue w start g v)
    (hn : Function.update g u ⊤ v ≠ rhsValue w start (Function.update g u ⊤) v) :
    key w start h g u < key w start h (Function.update g u ⊤) v := by
  have hv : v ≠ u := by intro he; subst v; exact (ne_of_lt hu) hc
  have hv' := Function.update_of_ne hv (⊤ : Cost) g
  have hrle := rhsValue_mono w start (le_update (le_top : g u ≤ ⊤)) v
  have hrlt : rhsValue w start g v < rhsValue w start (Function.update g u ⊤) v := by
    apply lt_of_le_of_ne hrle
    intro he
    exact hn (hv'.trans (hc.trans he))
  have he := rhsValue_change_increase w start g u v ⊤ hrlt
  have hf : g u ≠ ⊤ := ne_top_of_lt hu
  have hp := priority_edge_lt hf (hw u v) (hh u v)
  change priority (min (g u) (rhsValue w start g u)) (h u) <
    priority (min (Function.update g u ⊤ v) (rhsValue w start (Function.update g u ⊤) v)) (h v)
  rw [min_eq_left (le_of_lt hu), hv', hc, min_eq_left (le_of_lt hrlt), he]
  exact hp

theorem le_priority_min (k : Key) (a b : Cost) (h : ℚ)
    (ha : k ≤ priority a h) (hb : k ≤ priority b h) : k ≤ priority (min a b) h := by
  rcases le_total a b with hab | hba
  · simpa [min_eq_left hab] using ha
  · simpa [min_eq_right hba] using hb

theorem key_mono (w : Graph n) (start : Fin n) (h : Fin n → ℚ)
    {g g' : Labels n} (hg : ∀ v, g v ≤ g' v) (v : Fin n) :
    key w start h g v ≤ key w start h g' v :=
  priority_mono (min_le_min (hg v) (rhsValue_mono w start hg v)) (h v)

theorem decrease_remaining_key (w : Graph n) (hw : Positive w) (start : Fin n)
    (h : Fin n → ℚ) (hh : ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost))
    (g : Labels n) (u v : Fin n) (hu : rhsValue w start g u < g u)
    (hv : v ≠ u) (hmin : key w start h g u ≤ key w start h g v) :
    key w start h g u ≤ key w start h (Function.update g u (rhsValue w start g u)) v := by
  apply le_priority_min
  · rw [Function.update_of_ne hv]
    exact hmin.trans (priority_mono (min_le_left _ _) (h v))
  · by_cases hr : rhsValue w start g v ≤
        rhsValue w start (Function.update g u (rhsValue w start g u)) v
    · exact hmin.trans (priority_mono ((min_le_right _ _).trans hr) (h v))
    · have he := rhsValue_change_decrease w start g u v (rhsValue w start g u) (lt_of_not_ge hr)
      rw [he]
      have hp := priority_edge_lt (ne_top_of_lt hu) (hw u v) (hh u v)
      simpa only [priority, key, labelKey, min_eq_right (le_of_lt hu)] using le_of_lt hp

def nextLabels (w : Graph n) (start : Fin n) (g : Labels n) (u : Fin n) : Labels n :=
  Function.update g u (if rhsValue w start g u < g u then rhsValue w start g u else ⊤)

def Selected (w : Graph n) (start : Fin n) (h : Fin n → ℚ) (g : Labels n) (u : Fin n) : Prop :=
  g u ≠ rhsValue w start g u ∧
    ∀ v, g v ≠ rhsValue w start g v → key w start h g u ≤ key w start h g v

theorem nextLabels_of_ne (w : Graph n) (start : Fin n) (g : Labels n)
    (u v : Fin n) (hv : v ≠ u) : nextLabels w start g u v = g v :=
  Function.update_of_ne hv _ _

/-- Newly inconsistent vertices are strictly behind the expansion key. -/
theorem newly_inconsistent_key (w : Graph n) (hw : Positive w) (start : Fin n)
    (h : Fin n → ℚ) (hh : ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost))
    (g : Labels n) (u v : Fin n) (hu : Selected w start h g u)
    (hc : g v = rhsValue w start g v)
    (hn : nextLabels w start g u v ≠ rhsValue w start (nextLabels w start g u) v) :
    key w start h g u < key w start h (nextLabels w start g u) v := by
  by_cases ho : rhsValue w start g u < g u
  · simpa only [nextLabels, ite_eq_left ho] using
      decrease_new_key w hw start h hh g u v ho hc (by simpa [nextLabels, ho] using hn)
  · have hl : g u < rhsValue w start g u := lt_of_le_of_ne (le_of_not_gt ho) hu.1
    simpa only [nextLabels, ite_eq_right ho] using
      increase_new_key w hw start h hh g u v hl hc (by simpa [nextLabels, ho] using hn)

/-- Every remaining inconsistency has key at least the expansion key. -/
theorem next_inconsistent_key (w : Graph n) (hw : Positive w) (start : Fin n)
    (h : Fin n → ℚ) (hh : ∀ u v, (h u : Cost) ≤ w u v + (h v : Cost))
    (g : Labels n) (u v : Fin n) (hu : Selected w start h g u)
    (hn : nextLabels w start g u v ≠ rhsValue w start (nextLabels w start g u) v) :
    key w start h g u ≤ key w start h (nextLabels w start g u) v := by
  by_cases hc : g v = rhsValue w start g v
  · exact le_of_lt (newly_inconsistent_key w hw start h hh g u v hu hc hn)
  · by_cases ho : rhsValue w start g u < g u
    · have hv : v ≠ u := by
        intro he; subst v
        apply hn
        simp only [nextLabels, ite_eq_left ho, Function.update_self]
        exact (overconsistent_rhs w hw start g u ho).symm
      simpa only [nextLabels, ite_eq_left ho] using
        decrease_remaining_key w hw start h hh g u v ho hv (hu.2 v hc)
    · exact (hu.2 v hc).trans (key_mono w start h
        (by simpa only [nextLabels, ite_eq_right ho] using (le_update (le_top : g u ≤ ⊤))) v)

end Search.Incremental
