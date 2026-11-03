import Applications.Selection.Rank

/-! Three-way selection with operations separated from pivot validity. -/
set_option autoImplicit false
set_option warningAsError true

namespace Applications.Selection
universe u
variable {α : Type u} [LinearOrder α]

/-- Standard stable partitions retain every equal occurrence in input order. -/
def partition3 (p : α) (xs : List α) : List α × List α × List α :=
  let sides := xs.partition (fun x => decide (x < p))
  let upper := sides.2.partition (fun x => decide (x = p))
  (sides.1, upper.1, upper.2)

theorem partition3_eq_filters (p : α) (xs : List α) :
    partition3 p xs = (xs.filter (fun x => decide (x < p)),
      xs.filter (fun x => decide (x = p)), xs.filter (fun x => decide (p < x))) := by
  simp only [partition3, List.partition_eq_filter_filter, List.filter_filter]
  congr 2 <;> apply List.filter_congr <;> intro x hx <;>
    apply Bool.eq_iff_iff.mpr <;>
    simp only [Function.comp_def, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
      decide_eq_true_eq] <;> constructor <;> intro h
  · exact h.1
  · subst x; simp
  · exact lt_of_le_of_ne (le_of_not_gt h.2) (Ne.symm h.1)
  · exact ⟨ne_of_gt h, not_lt_of_gt h⟩

theorem partition3_perm (p : α) (xs : List α) :
    ((partition3 p xs).1 ++ (partition3 p xs).2.1 ++ (partition3 p xs).2.2).Perm xs := by
  simp only [partition3, List.partition_eq_filter_filter]
  rw [List.append_assoc]
  exact (List.Perm.append_left _ (List.filter_append_perm _ _)).trans
    (List.filter_append_perm _ _)

theorem partition_left_mem (p : α) (xs : List α) (x : α) :
    x∈(partition3 p xs).1 ↔ x∈xs ∧ x<p := by
  simp [partition3_eq_filters]

theorem partition_equal_mem (p : α) (xs : List α) (x : α) :
    x∈(partition3 p xs).2.1 ↔ x∈xs ∧ x=p := by
  simp [partition3_eq_filters]

theorem partition_right_mem (p : α) (xs : List α) (x : α) :
    x∈(partition3 p xs).2.2 ↔ x∈xs ∧ p<x := by
  simp [partition3_eq_filters]

theorem partition_lengths (p : α) (xs : List α) :
    (partition3 p xs).1.length+(partition3 p xs).2.1.length+
      (partition3 p xs).2.2.length=xs.length := by
  simpa [Nat.add_assoc] using (partition3_perm p xs).length_eq

theorem partition_strict_sizes (p : α) (xs : List α) (hp : p∈xs) :
    (partition3 p xs).1.length<xs.length ∧
      (partition3 p xs).2.2.length<xs.length := by
  have he : p∈(partition3 p xs).2.1 := (partition_equal_mem p xs p).mpr ⟨hp,rfl⟩
  have hn : 0<(partition3 p xs).2.1.length := List.length_pos_iff.mpr (List.ne_nil_of_mem he)
  have hl:=partition_lengths p xs
  omega

theorem sorted_partition (p : α) (xs : List α) :
    ordered xs=ordered (partition3 p xs).1++(partition3 p xs).2.1++ordered (partition3 p xs).2.2 := by
  let t:=partition3 p xs
  have hleft : ∀x∈ordered t.1,x<p := by
    intro x hx
    exact ((partition_left_mem p xs x).mp ((ordered_perm t.1).mem_iff.mp hx)).2
  have hequal : ∀x∈t.2.1,x=p := by
    intro x hx
    exact ((partition_equal_mem p xs x).mp hx).2
  have hright : ∀x∈ordered t.2.2,p<x := by
    intro x hx
    exact ((partition_right_mem p xs x).mp ((ordered_perm t.2.2).mem_iff.mp hx)).2
  apply List.Perm.eq_of_pairwise (fun _ _ _ _ hab hba => Std.le_antisymm hab hba)
  · exact (ordered_pairwise xs)
  · rw [List.pairwise_append,List.pairwise_append]
    refine ⟨⟨(ordered_pairwise t.1),?_,?_⟩,(ordered_pairwise t.2.2),?_⟩
    · exact List.pairwise_of_forall_mem_list (fun a ha b hb => by rw [hequal a ha,hequal b hb])
    · intro a ha b hb
      rw [hequal b hb]
      exact Std.le_of_lt (hleft a ha)
    · intro a ha b hb
      rcases List.mem_append.mp ha with ha|ha
      · exact Std.le_trans (Std.le_of_lt (hleft a ha)) (Std.le_of_lt (hright b hb))
      · rw [hequal a ha]; exact Std.le_of_lt (hright b hb)
  · exact (ordered_perm xs).trans
      (((ordered_perm t.1).append (List.Perm.refl t.2.1)).append (ordered_perm t.2.2) |>.trans (partition3_perm p xs)).symm

/-- Zero-based form of the literal three source branches. The middle branch
retains positional indexing in the equal block. -/
def dispatch (recur : Nat→List α→Option α) (p : α) (k : Nat) (xs : List α) : Option α :=
  let t:=partition3 p xs
  if k<t.1.length then recur k t.1
  else if k<t.1.length+t.2.1.length then t.2.1[k-t.1.length]?
  else recur (k-t.1.length-t.2.1.length) t.2.2

theorem dispatch_value (recur : Nat→List α→Option α) (p : α) (k : Nat) (xs : List α)
    (hl : ∀j,recur j (partition3 p xs).1=(ordered (partition3 p xs).1)[j]?)
    (hr : ∀j,recur j (partition3 p xs).2.2=(ordered (partition3 p xs).2.2)[j]?) :
    dispatch recur p k xs=(ordered xs)[k]? := by
  rw [sorted_partition p xs]
  unfold dispatch
  let t:=partition3 p xs
  change (if k<t.1.length then _ else if k<t.1.length+t.2.1.length then _ else _)=_
  have ll := (ordered_perm t.1).length_eq
  dsimp only [t] at *
  by_cases h:k<(partition3 p xs).1.length
  · rw [ite_eq_left h,hl,List.getElem?_append_left (by simp only [List.length_append,ll];omega),List.getElem?_append_left (by omega)]
  · rw [ite_eq_right h]
    by_cases he:k<(partition3 p xs).1.length+(partition3 p xs).2.1.length
    · rw [ite_eq_left he,List.getElem?_append_left (by simp only [List.length_append,ll];omega),List.getElem?_append_right (by omega),ll]
    · rw [ite_eq_right he,hr,List.getElem?_append_right (by simp only [List.length_append,ll];omega),List.length_append,ll]
      simp only [Nat.sub_sub]

/-- The choose operation must produce an input occurrence on every nonempty list. -/
def PivotValid (choose : List α→Option α) : Prop :=
  ∀xs,xs≠[]→∃p,choose xs=some p ∧ p∈xs

/-- Administrative depth fuel totalizes source partiality. The adequacy theorem
proves input length sufficient, so it never truncates a valid source run. -/
def runWith (choose : List α→Option α) : Nat→Nat→List α→Option α
  | 0,_,_ => none
  | _+1,_,[] => none
  | fuel+1,k,x::xs =>
    match choose (x::xs) with
    | none => none
    | some p => dispatch (runWith choose fuel) p k (x::xs)

theorem runWith_value (choose : List α→Option α) (hv : PivotValid choose)
    (fuel : Nat) (xs : List α) (hf : xs.length≤fuel) (k : Nat) :
    runWith choose fuel k xs=(ordered xs)[k]? := by
  induction fuel generalizing xs k with
  | zero =>
    have hx:xs=[] := List.length_eq_zero_iff.mp (by omega)
    subst xs; simp [runWith,ordered]
  | succ fuel ih =>
    cases xs with
    | nil => simp [runWith,ordered]
    | cons x xs =>
      obtain ⟨p,hp,hm⟩:=hv (x::xs) (by simp)
      rw [runWith,hp]
      have hh:=partition_strict_sizes p (x::xs) hm
      exact dispatch_value _ p k _
        (fun j=>ih _ (by simp only [List.length_cons] at hf hh;omega) j)
        (fun j=>ih _ (by simp only [List.length_cons] at hf hh;omega) j)

def selectWith (choose : List α→Option α) (k : Nat) (xs : List α) : Option α :=
  if k=0 then none else runWith choose xs.length (k-1) xs

theorem selectWith_value (choose : List α→Option α) (hv : PivotValid choose)
    (xs : List α) (k : Nat) (hk : 0<k) :
    selectWith choose k xs=(ordered xs)[k-1]? := by
  simp only [selectWith,show k≠0 by omega,↓reduceIte]
  exact runWith_value choose hv xs.length xs (by omega) (k-1)

theorem selectWith_ranked (choose : List α→Option α) (hv : PivotValid choose)
    (xs : List α) (k : Nat) (a : α) (hk : 0<k)
    (ha : selectWith choose k xs=some a) : RankedAt xs (k-1) a := by
  rw [selectWith_value choose hv xs k hk] at ha
  exact pairwise_ranked (ordered_pairwise xs) (ordered_perm xs) ha

theorem selectWith_none (choose : List α→Option α) (hv : PivotValid choose)
    (xs : List α) (k : Nat) : selectWith choose k xs=none ↔ k=0 ∨ xs.length<k := by
  by_cases hk:k=0
  · simp [selectWith,hk]
  · rw [selectWith_value choose hv xs k (by omega),List.getElem?_eq_none_iff,(ordered_perm xs).length_eq]
    omega

omit [LinearOrder α] in
theorem head_pivot_valid : PivotValid (List.head? : List α→Option α) := by
  intro xs hn
  cases xs with
  | nil => contradiction
  | cons x xs => exact ⟨x,rfl,List.mem_cons_self⟩


/-- The second policy chooses the last input occurrence. -/
def lastPivot (xs : List α) : Option α := xs.reverse.head?

omit [LinearOrder α] in
theorem last_pivot_valid : PivotValid (lastPivot : List α → Option α) := by
  intro xs hn
  have hr : xs.reverse ≠ [] := by simpa using hn
  obtain ⟨p, hp, hm⟩ := head_pivot_valid xs.reverse hr
  exact ⟨p, hp, List.mem_reverse.mp hm⟩

/-- A successful public call is exactly a positive one-based occurrence rank. -/
theorem selectWith_some_iff (choose : List α → Option α) (hv : PivotValid choose)
    (xs : List α) (k : Nat) (a : α) :
    selectWith choose k xs = some a ↔ 0 < k ∧ RankedAt xs (k - 1) a := by
  by_cases hk : k = 0
  · simp [hk, selectWith]
  · rw [selectWith_value choose hv xs k (by omega), ← ranked_iff_index]
    simp [show 0 < k by omega]

/-- Policy independence concerns returned values, not recursion traces. -/
theorem selectWith_policy (choose choose' : List α → Option α)
    (hv : PivotValid choose) (hv' : PivotValid choose') (xs : List α) (k : Nat) :
    selectWith choose k xs = selectWith choose' k xs := by
  cases h : selectWith choose k xs with
  | none => exact ((selectWith_none choose' hv' xs k).mpr
      ((selectWith_none choose hv xs k).mp h)).symm
  | some a => exact ((selectWith_some_iff choose' hv' xs k a).mpr
      ((selectWith_some_iff choose hv xs k a).mp h)).symm

/-- One-based standard sort/index baseline, including rank zero. -/
def sortSelect (k : Nat) (xs : List α) : Option α :=
  if k = 0 then none else (ordered xs)[k - 1]?

theorem selectWith_eq_sortSelect (choose : List α → Option α) (hv : PivotValid choose)
    (xs : List α) (k : Nat) : selectWith choose k xs = sortSelect k xs := by
  by_cases hk : k = 0
  · simp [hk, selectWith, sortSelect]
  · simpa [sortSelect, hk] using selectWith_value choose hv xs k (by omega)

theorem sortSelect_some_iff (xs : List α) (k : Nat) (a : α) :
    sortSelect k xs = some a ↔ 0 < k ∧ RankedAt xs (k - 1) a := by
  rw [← selectWith_eq_sortSelect List.head? head_pivot_valid]
  exact selectWith_some_iff _ head_pivot_valid xs k a

theorem sortSelect_none (xs : List α) (k : Nat) :
    sortSelect k xs = none ↔ k = 0 ∨ xs.length < k := by
  rw [← selectWith_eq_sortSelect List.head? head_pivot_valid]
  exact selectWith_none _ head_pivot_valid xs k

end Applications.Selection
