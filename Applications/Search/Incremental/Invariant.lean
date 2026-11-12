import Applications.Search.Incremental.Trace
import Applications.Search.Incremental.Rows

/-! Exact cache/worklist coherence for literal local refresh operations. -/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Incremental
variable {n : Nat}

def Ready (w : Graph n) (start : Fin n) (s : State n) (v : Fin n) : Prop :=
  s.rhs v = rhsValue w start s.g v ∧ (v ∈ s.queue ↔ s.g v ≠ s.rhs v)

theorem refresh_ready (w : Graph n) (start : Fin n) (s : State n) (v : Fin n) :
    Ready w start (refresh w start s v) v := by
  unfold Ready refresh
  simp only [Function.update_self]
  constructor
  · exact True.intro
  · by_cases he : s.g v = rhsValue w start s.g v <;> simp [he]

theorem refresh_ready_of_ne (w : Graph n) (start : Fin n) (s : State n) (u v : Fin n)
    (hv : v ≠ u) (hr : Ready w start s v) : Ready w start (refresh w start s u) v := by
  unfold Ready refresh
  simp only [Function.update_of_ne hv]
  constructor
  · exact hr.1
  · by_cases he : s.g u = rhsValue w start s.g u <;> simpa [he, hv] using hr.2

theorem refresh_nodup (w : Graph n) (start : Fin n) (s : State n) (v : Fin n)
    (hn : s.queue.Nodup) : (refresh w start s v).queue.Nodup := by
  unfold refresh
  by_cases he : s.g v = rhsValue w start s.g v
  · simpa [he] using hn.filter (fun u => u != v)
  · simp only [ite_eq_right he]
    apply List.Nodup.append
    · exact hn.filter _
    · simp
    · intro a ha hb
      have hav : a = v := by simpa using hb
      subst a
      simp at ha

theorem refreshMany_nodup (w : Graph n) (start : Fin n) (s : State n) (vs : List (Fin n))
    (hn : s.queue.Nodup) : (refreshMany w start s vs).queue.Nodup := by
  induction vs generalizing s with
  | nil => exact hn
  | cons v vs ih => exact ih (refresh w start s v) (refresh_nodup w start s v hn)

theorem refreshMany_ready (w : Graph n) (start : Fin n) (s : State n) (vs : List (Fin n))
    (v : Fin n) (hr : v ∈ vs ∨ Ready w start s v) : Ready w start (refreshMany w start s vs) v := by
  induction vs generalizing s with
  | nil => exact hr.resolve_left (by simp)
  | cons u us ih =>
    apply ih
    by_cases hv : v = u
    · subst v
      exact Or.inr (refresh_ready w start s u)
    · rcases hr with hm | hr
      · exact Or.inl ((List.mem_cons.mp hm).resolve_left hv)
      · exact Or.inr (refresh_ready_of_ne w start s u v hv hr)

theorem valid_iff_ready (w : Graph n) (start : Fin n) (s : State n) :
    Valid w start s ↔ (∀ v, Ready w start s v) ∧ s.queue.Nodup ∧ Nonnegative s.g := by
  constructor
  · rintro ⟨hr, hq, hm, hg⟩
    exact ⟨fun v => ⟨congrFun hr v, hm v⟩, hq, hg⟩
  · rintro ⟨hr, hq, hg⟩
    exact ⟨funext (fun v => (hr v).1), hq, fun v => (hr v).2, hg⟩

theorem initial_valid (w : Graph n) (start : Fin n) : Valid w start (initial start) := by
  apply (valid_iff_ready w start _).mpr
  refine ⟨?_, by simp [initial], fun _ => le_top⟩
  intro v
  unfold Ready initial rhsValue predecessorMinimum
  by_cases hv : v = start <;> simp [hv]

theorem rhsValue_update_blocked (w : Graph n) (start : Fin n) (g : Labels n)
    (u v : Fin n) (a : Cost) (hb : w u v = ⊤) :
    rhsValue w start (Function.update g u a) v = rhsValue w start g v := by
  apply rhsValue_congr_inputs
  intro z
  by_cases hz : z = u
  · subst z; simp [hb]
  · simp [Function.update_of_ne hz]

theorem select_selected (w : Graph n) (start : Fin n) (h : Fin n → ℚ) (s : State n)
    (hs : Valid w start s) (u : Fin n) (hu : select h s = some u) : Selected w start h s.g u := by
  obtain ⟨hum, hmin⟩ := select_spec h s u hu
  refine ⟨?_, ?_⟩
  · simpa [← hs.1] using (hs.2.2.1 u).mp hum
  · intro v hv
    have hvm : v ∈ s.queue := (hs.2.2.1 v).mpr (by simpa [hs.1] using hv)
    simpa [key, hs.1] using hmin v hvm

theorem expand_valid (w : Graph n) (hw : Positive w) (start : Fin n)
    (s : State n) (hs : Valid w start s) (u : Fin n) : Valid w start (expand w start s u) := by
  let a := if s.rhs u < s.g u then s.rhs u else ⊤
  let base : State n := { s with g := Function.update s.g u a, queue := s.queue.filter (· != u) }
  let vs := if s.rhs u < s.g u then successors w u else u :: successors w u
  change Valid w start (refreshMany w start base vs)
  have hg : Nonnegative base.g := by
    intro v
    by_cases hv : v = u
    · subst v
      dsimp only [base]
      rw [Function.update_self]
      dsimp [a]
      split
      · rw [hs.1]; exact rhsValue_nonnegative hw start hs.2.2.2 u
      · exact le_top
    · simpa [base, Function.update_of_ne hv] using hs.2.2.2 v
  apply (valid_iff_ready w start _).mpr
  refine ⟨?_, refreshMany_nodup w start base vs (hs.2.1.filter _), ?_⟩
  · intro v
    apply refreshMany_ready
    by_cases hm : v ∈ vs
    · exact Or.inl hm
    · apply Or.inr
      have hsucc : v ∉ successors w u := by
        intro hv
        apply hm
        dsimp [vs]
        split
        · exact hv
        · exact List.mem_cons_of_mem u hv
      have hb : w u v = ⊤ := by simpa [successors] using hsucc
      by_cases hv : v = u
      · subst v
        have ho : s.rhs u < s.g u := by
          by_contra hn
          exact hm (by simp [vs, hn])
        have he := overconsistent_rhs w hw start s.g u (by simpa [hs.1] using ho)
        unfold Ready
        dsimp [base, a]
        simp only [ite_eq_left ho, Function.update_self]
        constructor
        · simpa [hs.1] using he.symm
        · simp
      · unfold Ready
        dsimp [base]
        rw [Function.update_of_ne hv]
        constructor
        · rw [rhsValue_update_blocked w start s.g u v a hb]
          exact congrFun hs.1 v
        · simpa [hv] using hs.2.2.1 v
  · simpa only [refreshMany_g] using hg

theorem expand_nextLabels (w : Graph n) (start : Fin n) (s : State n)
    (hs : Valid w start s) (u : Fin n) : (expand w start s u).g = nextLabels w start s.g u := by
  simp only [expand_g, nextLabels, hs.1]

theorem no_select_not_active (w : Graph n) (start goal : Fin n) (h : Fin n → ℚ)
    (s : State n) (hs : Valid w start s) (hn : select h s = none) : ¬ active goal h s := by
  have hq := (select_none h s).mp hn
  have hc : s.g goal = s.rhs goal := by
    by_contra he
    have hm := (hs.2.2.1 goal).mpr he
    simp [hq] at hm
  simp only [active, topKey, hn, Option.map_none, Option.getD_none, hc, ne_eq, not_true_eq_false, or_false]
  change ¬ toLex (⊤, ⊤) < toLex _
  rw [Prod.Lex.lt_iff]
  simp

end Search.Incremental
