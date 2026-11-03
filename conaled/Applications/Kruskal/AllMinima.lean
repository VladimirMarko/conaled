import Applications.Optimization.SelectionTies

/-! The selected source all-minima fold, with exact ordered-filter semantics.
Only the fold used by the forest-state diagnostic is retained. -/
set_option autoImplicit false
set_option warningAsError true
namespace ForestKruskalSource.AllMinima
variable {α : Type*} {β : Type*} [LinearOrder β]

private abbrev MinimumIn (f : α → β) (xs : List α) (a : α) : Prop :=
  a ∈ xs ∧ ∀ b ∈ xs, f a ≤ f b

def minsStep  (p : β × α) :
    List (β × α) → List (β × α)
  | [] => [p]
  | q :: qs =>
    if p.1 < q.1 then [p]
    else if p.1 = q.1 then p :: q :: qs
    else if q.1 < p.1 then q :: qs
    else []

def minsPairs
    (f : α → β) (xs : List α) : List (β × α) :=
  (xs.map (fun x => (f x, x))).foldr minsStep []

def minsWith
    (f : α → β) (xs : List α) : List α := (minsPairs f xs).map Prod.snd

private def atScore (f : α → β) (a : α) (xs : List α) : List α :=
  xs.filter (fun b => decide (f b = f a))

private theorem minimum_score_eq (f : α → β) (xs : List α) (a b : α)
    (ha : MinimumIn f xs a) (hb : MinimumIn f xs b) : f a = f b :=
  le_antisymm (ha.2 b hb.1) (hb.2 a ha.1)

private theorem first_exists (f : α → β) (xs : List α) (hne : xs ≠ []) :
    ∃ a, MinimumIn f xs a ∧ Optimization.FirstMinimum f xs a := by
  cases h : Optimization.Thinning.argmin f xs with
  | none => exact False.elim (hne ((Optimization.Thinning.argmin_eq_none_iff f xs).mp h))
  | some a =>
      have hm := Optimization.Thinning.argmin_correct f xs a h
      exact ⟨a, ⟨hm.1, fun b hb => hm.2 hb⟩, Optimization.argmin_firstMinimum f xs a h⟩

private theorem atScore_first (f : α → β) (xs : List α) (a : α)
    (ha : Optimization.FirstMinimum f xs a) : ∃ rest, atScore f a xs = a :: rest := by
  rcases ha with ⟨pre, post, rfl, hp, _⟩
  have he : pre.filter (fun b => decide (f b = f a)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro b hb
    simp only [decide_eq_true_eq]
    exact fun h => ne_of_lt (hp b hb) h.symm
  exact ⟨post.filter (fun b => decide (f b = f a)), by simp [atScore, he]⟩

private theorem minsPairs_eq_atScore (f : α → β) (xs : List α) (a : α)
    (ha : MinimumIn f xs a) :
    minsPairs f xs = (atScore f a xs).map (fun b => (f b, b)) := by
  induction xs generalizing a with
  | nil => simp [MinimumIn] at ha
  | cons x xs ih =>
    cases xs with
    | nil =>
      have he : a = x := List.mem_singleton.mp ha.1
      subst a
      simp [minsPairs, minsStep, atScore]
    | cons y ys =>
      obtain ⟨b, hb, hfirst⟩ := first_exists f (y :: ys) (by simp)
      obtain ⟨rest, hr⟩ := atScore_first f (y :: ys) b hfirst
      have hi := ih b hb
      rw [hr] at hi
      have hstep : minsPairs f (x :: y :: ys) =
          minsStep (f x, x) ((f b, b) :: rest.map (fun c => (f c, c))) := by
        change minsStep (f x, x) (minsPairs f (y :: ys)) = _
        simp only [hi, List.map_cons]
      rcases lt_trichotomy (f x) (f b) with h | he | h
      · have hx : MinimumIn f (x :: y :: ys) x := by
          refine ⟨by simp, ?_⟩
          intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact le_refl _
          · exact le_trans (le_of_lt h) (hb.2 c hc)
        have he := minimum_score_eq f (x :: y :: ys) a x ha hx
        have hz : atScore f x (y :: ys) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro c hc
          simp only [decide_eq_true_eq]
          exact fun e => ne_of_lt (lt_of_lt_of_le h (hb.2 c hc)) e.symm
        have hf : atScore f a (x :: y :: ys) = [x] := by
          change (x :: y :: ys).filter (fun c => decide (f c = f a)) = [x]
          rw [List.filter_cons, ite_eq_left (by simp [he])]
          change x :: atScore f a (y :: ys) = [x]
          have ht : atScore f a (y :: ys) = [] := by simpa only [atScore, he] using hz
          rw [ht]
        rw [hstep, hf]
        simp [minsStep, h]
      · have hb' : MinimumIn f (x :: y :: ys) b := by
          refine ⟨by simp [hb.1], ?_⟩
          intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact le_of_eq he.symm
          · exact hb.2 c hc
        have hea := minimum_score_eq f (x :: y :: ys) a b ha hb'
        have hf : atScore f a (x :: y :: ys) = x :: b :: rest := by
          change (x :: y :: ys).filter (fun c => decide (f c = f a)) = x :: b :: rest
          rw [List.filter_cons, ite_eq_left (by simp [he, hea])]
          have ht : atScore f a (y :: ys) = b :: rest := by simpa only [atScore, hea] using hr
          change x :: atScore f a (y :: ys) = x :: b :: rest
          rw [ht]
        rw [hstep, hf]
        simp [minsStep, he]
      · have hb' : MinimumIn f (x :: y :: ys) b := by
          refine ⟨by simp [hb.1], ?_⟩
          intro c hc
          rcases List.mem_cons.mp hc with rfl | hc
          · exact le_of_lt h
          · exact hb.2 c hc
        have hea := minimum_score_eq f (x :: y :: ys) a b ha hb'
        have hlt : ¬ f x < f b := not_lt_of_ge (le_of_lt h)
        have he : f x ≠ f b := fun e => ne_of_lt h e.symm
        have hf : atScore f a (x :: y :: ys) = b :: rest := by
          change (x :: y :: ys).filter (fun c => decide (f c = f a)) = b :: rest
          rw [List.filter_cons, ite_eq_right (by simpa only [decide_eq_true_eq, hea] using he)]
          simpa only [atScore, hea] using hr
        rw [hstep, hf]
        simp [minsStep, hlt, he, h]

/-- Exact list equality retains order and multiplicity, including empty inputs. -/
theorem minsWith_eq_filter (f : α → β) (xs : List α) :
    minsWith f xs = xs.filter (fun a => xs.all (fun b => decide (f a ≤ f b))) := by
  by_cases hn : xs = []
  · subst xs; rfl
  obtain ⟨a, ha, _⟩ := first_exists f xs hn
  rw [minsWith, minsPairs_eq_atScore f xs a ha]
  simp only [List.map_map, Function.comp_def, List.map_id', atScore]
  apply List.filter_congr
  intro b hb
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, decide_eq_true_eq]
  exact ⟨fun h c hc => h ▸ ha.2 c hc,
    fun h => le_antisymm (h a ha.1) (ha.2 b hb)⟩

end ForestKruskalSource.AllMinima
