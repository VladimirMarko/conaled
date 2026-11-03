import Applications.Selection.ThreeWay

/-! Lower medians and monotone relabeling consume independent occurrence ranks. -/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Selection
universe u v
variable {α : Type u} {β : Type v} [LinearOrder α]

/-- On distinct inputs the occurrence-based specification specializes to the
book's exact strict rank. No distinctness is imposed on the general selector. -/
theorem ranked_strict_counts (xs : List α) (k : Nat) (a : α)
    (hn : xs.Nodup) (h : RankedAt xs k a) :
    xs.countP (fun x=>decide (x<a))=k ∧
      xs.countP (fun x=>decide (a<x))=xs.length-k-1 := by
  obtain ⟨pre,post,hp,hk,hlo,hhi⟩:=h
  have hd: (pre++a::post).Nodup := hp.nodup_iff.mpr hn
  obtain ⟨_,hpost,hdiff⟩:=List.nodup_append.mp hd
  have ha:=List.nodup_cons.mp hpost
  have hpre : ∀x∈pre,x<a := by
    intro x hx
    exact Std.lt_of_le_of_ne (hlo x hx) (hdiff x hx a (by simp))
  have hpost : ∀x∈post,a<x := by
    intro x hx
    apply Std.lt_of_le_of_ne (hhi x hx)
    intro he
    exact ha.1 (he ▸ hx)
  have hpl:pre.countP (fun x=>decide (x<a))=pre.length :=
    List.countP_eq_length.mpr (fun x hx=>by simp [hpre x hx])
  have hpr:pre.countP (fun x=>decide (a<x))=0 :=
    List.countP_eq_zero.mpr (fun x hx=>by
      simp only [decide_eq_true_eq]
      exact fun hh=>Std.lt_irrefl (Std.lt_trans (hpre x hx) hh))
  have hql:post.countP (fun x=>decide (x<a))=0 :=
    List.countP_eq_zero.mpr (fun x hx=>by
      simp only [decide_eq_true_eq]
      exact fun hh=>Std.lt_irrefl (Std.lt_trans (hpost x hx) hh))
  have hqr:post.countP (fun x=>decide (a<x))=post.length :=
    List.countP_eq_length.mpr (fun x hx=>by simp [hpost x hx])
  have hl:=hp.countP_eq (fun x=>decide (x<a))
  have hr:=hp.countP_eq (fun x=>decide (a<x))
  have hlen:=hp.length_eq
  simp only [List.countP_append,List.countP_cons,show decide (a<a)=false by simp,Bool.false_eq_true,↓reduceIte,hpl,hpr,hql,hqr,List.length_append,List.length_cons] at hl hr hlen
  omega


/-- Lower of the two central occurrences on an even nonempty input. -/
def lowerMedianWith (choose : List α → Option α) (xs : List α) : Option α :=
  selectWith choose ((xs.length + 1) / 2) xs

theorem lowerMedian_none (choose : List α → Option α) (hv : PivotValid choose)
    (xs : List α) : lowerMedianWith choose xs = none ↔ xs = [] := by
  rw [lowerMedianWith, selectWith_none choose hv]
  constructor
  · intro h
    apply List.length_eq_zero_iff.mp
    omega
  · rintro rfl
    simp

theorem lowerMedian_ranked (choose : List α → Option α) (hv : PivotValid choose)
    (xs : List α) (a : α) (ha : lowerMedianWith choose xs = some a) :
    RankedAt xs ((xs.length + 1) / 2 - 1) a :=
  ((selectWith_some_iff choose hv xs _ a).mp ha).2

theorem lowerMedian_odd_index (choose : List α → Option α) (hv : PivotValid choose)
    (xs : List α) (r : Nat) (hl : xs.length = 2 * r + 1) :
    lowerMedianWith choose xs = (ordered xs)[r]? := by
  unfold lowerMedianWith
  rw [selectWith_value choose hv xs _ (by omega)]
  congr 1
  omega

theorem lowerMedian_even_index (choose : List α → Option α) (hv : PivotValid choose)
    (xs : List α) (r : Nat) (hr : 0 < r) (hl : xs.length = 2 * r) :
    lowerMedianWith choose xs = (ordered xs)[r - 1]? := by
  unfold lowerMedianWith
  rw [selectWith_value choose hv xs _ (by omega)]
  congr 1
  omega

theorem lowerMedian_strict_counts (choose : List α → Option α) (hv : PivotValid choose)
    (xs : List α) (a : α) (hn : xs.Nodup) (ha : lowerMedianWith choose xs = some a) :
    xs.countP (fun x => decide (x < a)) = (xs.length + 1) / 2 - 1 ∧
      xs.countP (fun x => decide (a < x)) = xs.length - (xs.length + 1) / 2 := by
  have h := ranked_strict_counts xs _ a hn (lowerMedian_ranked choose hv xs a ha)
  have hk := ((selectWith_some_iff choose hv xs _ a).mp ha).1
  omega

theorem lowerMedian_odd_counts (choose : List α → Option α) (hv : PivotValid choose)
    (xs : List α) (a : α) (r : Nat) (hn : xs.Nodup) (hl : xs.length = 2 * r + 1)
    (ha : lowerMedianWith choose xs = some a) :
    xs.countP (fun x => decide (x < a)) = r ∧
      xs.countP (fun x => decide (a < x)) = r := by
  have h := lowerMedian_strict_counts choose hv xs a hn ha
  omega

theorem lowerMedian_even_counts (choose : List α → Option α) (hv : PivotValid choose)
    (xs : List α) (a : α) (r : Nat) (hn : xs.Nodup) (hl : xs.length = 2 * r)
    (ha : lowerMedianWith choose xs = some a) :
    xs.countP (fun x => decide (x < a)) = r - 1 ∧
      xs.countP (fun x => decide (a < x)) = r := by
  have h := lowerMedian_strict_counts choose hv xs a hn ha
  omega

/-- Noninjective monotone maps preserve selected values, for any valid policies. -/
theorem selectWith_map [LinearOrder β] (choose : List α → Option α)
    (choose' : List β → Option β) (hv : PivotValid choose) (hv' : PivotValid choose')
    (f : α → β) (hf : Monotone f) (xs : List α) (k : Nat) :
    selectWith choose' k (xs.map f) = (selectWith choose k xs).map f := by
  cases h : selectWith choose k xs with
  | none =>
    simp only [Option.map_none]
    apply (selectWith_none choose' hv' _ k).mpr
    simpa using (selectWith_none choose hv xs k).mp h
  | some a =>
    simp only [Option.map_some]
    obtain ⟨hk, hr⟩ := (selectWith_some_iff choose hv xs k a).mp h
    exact (selectWith_some_iff choose' hv' _ k (f a)).mpr ⟨hk, hr.map f hf⟩

end Applications.Selection
