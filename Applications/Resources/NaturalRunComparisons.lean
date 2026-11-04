import Applications.Sorting.NaturalRuns
import Applications.Resources.CallCount

/-!
The natural-run comparison recurrences from FDSA, Chapter 2, pp. 23–25,
and an execution that computes the actual scanner values while observing them.
Only tested adjacent pairs are charged. Builder creation/application, list
construction, scanner entries and key-evaluation work belong to other models.
In particular, these comparison counts assert no machine-runtime bound.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.NaturalRunComparisons
open Applications.Sorting

universe u v
variable {α : Type u} {κ : Type v}

mutual
  /-- The source's `Cruns` specification; its zero cases are uncharged. -/
  def runsCountBy (lt : α → α → Bool) : List α → Nat
    | [] => 0
    | [_] => 0
    | a :: b :: xs =>
        1 + (if lt b a then descCountBy lt b xs else ascCountBy lt b xs)
  termination_by xs => xs.length
  decreasing_by all_goals simp_wf

  /-- `Casc` does not inspect the already supplied builder. -/
  def ascCountBy (lt : α → α → Bool) (a : α) : List α → Nat
    | [] => 0
    | b :: bs =>
        1 + (if lt b a then runsCountBy lt (b :: bs) else ascCountBy lt b bs)
  termination_by ys => ys.length + 1
  decreasing_by all_goals simp_wf

  /-- `Cdesc` does not inspect the already supplied descending accumulator. -/
  def descCountBy (lt : α → α → Bool) (a : α) : List α → Nat
    | [] => 0
    | b :: bs =>
        1 + (if lt b a then descCountBy lt b bs else runsCountBy lt (b :: bs))
  termination_by ys => ys.length + 1
  decreasing_by all_goals simp_wf
end

@[simp] theorem runsCountBy_nil (lt : α → α → Bool) : runsCountBy lt [] = 0 := by
  rw [runsCountBy]

@[simp] theorem runsCountBy_singleton (lt : α → α → Bool) (a : α) :
    runsCountBy lt [a] = 0 := by
  rw [runsCountBy]

theorem runsCountBy_cons_cons (lt : α → α → Bool) (a b : α) (xs : List α) :
    runsCountBy lt (a :: b :: xs) =
      1 + (if lt b a then descCountBy lt b xs else ascCountBy lt b xs) := by
  rw [runsCountBy]

@[simp] theorem ascCountBy_nil (lt : α → α → Bool) (a : α) :
    ascCountBy lt a [] = 0 := by
  rw [ascCountBy]

theorem ascCountBy_cons (lt : α → α → Bool) (a b : α) (bs : List α) :
    ascCountBy lt a (b :: bs) =
      1 + (if lt b a then runsCountBy lt (b :: bs) else ascCountBy lt b bs) := by
  rw [ascCountBy]

@[simp] theorem descCountBy_nil (lt : α → α → Bool) (a : α) :
    descCountBy lt a [] = 0 := by
  rw [descCountBy]

theorem descCountBy_cons (lt : α → α → Bool) (a b : α) (bs : List α) :
    descCountBy lt a (b :: bs) =
      1 + (if lt b a then descCountBy lt b bs else runsCountBy lt (b :: bs)) := by
  rw [descCountBy]

mutual
  /-- Execute the comparison and exactly its selected recursive successor. -/
  def runsRunBy (lt : α → α → Bool) : List α → Measured (List (List α)) Nat
    | [] => pure []
    | [a] => pure [[a]]
    | a :: b :: xs =>
        bind (CallCount.tick (pure (lt b a))) (fun descending =>
          if descending then descRunBy lt b [a] xs
          else ascRunBy lt b (Batteries.DList.singleton a) xs)
  termination_by xs => xs.length
  decreasing_by all_goals simp_wf

  /-- The real builder supplies the emitted list; its application is uncharged here. -/
  def ascRunBy (lt : α → α → Bool) (a : α) (d : Batteries.DList α) :
      List α → Measured (List (List α)) Nat
    | [] => pure [d.apply [a]]
    | b :: bs =>
        bind (CallCount.tick (pure (lt b a))) (fun descending =>
          if descending then
            bind (runsRunBy lt (b :: bs)) (fun rest => pure (d.apply [a] :: rest))
          else ascRunBy lt b (d.push a) bs)
  termination_by ys => ys.length + 1
  decreasing_by all_goals simp_wf

  /-- The actual descending prefix is extended or emitted by the selected branch. -/
  def descRunBy (lt : α → α → Bool) (a : α) (acc : List α) :
      List α → Measured (List (List α)) Nat
    | [] => pure [a :: acc]
    | b :: bs =>
        bind (CallCount.tick (pure (lt b a))) (fun descending =>
          if descending then descRunBy lt b (a :: acc) bs
          else bind (runsRunBy lt (b :: bs)) (fun rest => pure ((a :: acc) :: rest)))
  termination_by ys => ys.length + 1
  decreasing_by all_goals simp_wf
end

@[simp] theorem runsRunBy_nil (lt : α → α → Bool) : runsRunBy lt [] = ([], 0) := by
  simp only [runsRunBy, pure]

@[simp] theorem runsRunBy_singleton (lt : α → α → Bool) (a : α) :
    runsRunBy lt [a] = ([[a]], 0) := by
  simp only [runsRunBy, pure]

theorem runsRunBy_cons_cons (lt : α → α → Bool) (a b : α) (xs : List α) :
    runsRunBy lt (a :: b :: xs) =
      bind (CallCount.tick (pure (lt b a))) (fun descending =>
        if descending then descRunBy lt b [a] xs
        else ascRunBy lt b (Batteries.DList.singleton a) xs) := by
  rw [runsRunBy]

@[simp] theorem ascRunBy_nil (lt : α → α → Bool) (a : α) (d : Batteries.DList α) :
    ascRunBy lt a d [] = ([d.apply [a]], 0) := by
  simp only [ascRunBy, pure]

theorem ascRunBy_cons (lt : α → α → Bool) (a b : α) (d : Batteries.DList α)
    (bs : List α) :
    ascRunBy lt a d (b :: bs) =
      bind (CallCount.tick (pure (lt b a))) (fun descending =>
        if descending then
          bind (runsRunBy lt (b :: bs)) (fun rest => pure (d.apply [a] :: rest))
        else ascRunBy lt b (d.push a) bs) := by
  rw [ascRunBy]

@[simp] theorem descRunBy_nil (lt : α → α → Bool) (a : α) (acc : List α) :
    descRunBy lt a acc [] = ([a :: acc], 0) := by
  simp only [descRunBy, pure]

theorem descRunBy_cons (lt : α → α → Bool) (a b : α) (acc bs : List α) :
    descRunBy lt a acc (b :: bs) =
      bind (CallCount.tick (pure (lt b a))) (fun descending =>
        if descending then descRunBy lt b (a :: acc) bs
        else bind (runsRunBy lt (b :: bs)) (fun rest => pure ((a :: acc) :: rest))) := by
  rw [descRunBy]

mutual
  /-- Joint refinement calculates both components from the actual measured branches. -/
  theorem runsRunBy_spec (lt : α → α → Bool) (xs : List α) :
      runsRunBy lt xs = (runsBy lt xs, runsCountBy lt xs) := by
    match xs with
    | [] => simp only [runsRunBy_nil, runsBy_nil, runsCountBy_nil]
    | [a] => simp only [runsRunBy_singleton, runsBy_singleton, runsCountBy_singleton]
    | a :: b :: bs =>
      rw [runsRunBy_cons_cons, runsBy_cons_cons, runsCountBy_cons_cons]
      cases h : lt b a with
      | false =>
        have hs := ascRunBy_spec lt b (Batteries.DList.singleton a) bs
        simp only [h, CallCount.tick, pure, bind, Bool.false_eq_true, ↓reduceIte, hs]
      | true =>
        have hs := descRunBy_spec lt b [a] bs
        simp only [h, CallCount.tick, pure, bind, ↓reduceIte, hs]
  termination_by xs.length
  decreasing_by all_goals simp_wf

  theorem ascRunBy_spec (lt : α → α → Bool) (a : α) (d : Batteries.DList α)
      (ys : List α) : ascRunBy lt a d ys = (ascBy lt a d ys, ascCountBy lt a ys) := by
    match ys with
    | [] => simp only [ascRunBy_nil, ascBy_nil, ascCountBy_nil]
    | b :: bs =>
      rw [ascRunBy_cons, ascBy_cons, ascCountBy_cons]
      cases h : lt b a with
      | false =>
        have hs := ascRunBy_spec lt b (d.push a) bs
        simp only [h, CallCount.tick, pure, bind, Bool.false_eq_true, ↓reduceIte, hs]
      | true =>
        have hs := runsRunBy_spec lt (b :: bs)
        simp only [h, CallCount.tick, pure, bind, ↓reduceIte, hs, Nat.add_zero]
  termination_by ys.length + 1
  decreasing_by all_goals simp_wf

  theorem descRunBy_spec (lt : α → α → Bool) (a : α) (acc ys : List α) :
      descRunBy lt a acc ys = (descBy lt a acc ys, descCountBy lt a ys) := by
    match ys with
    | [] => simp only [descRunBy_nil, descBy_nil, descCountBy_nil]
    | b :: bs =>
      rw [descRunBy_cons, descBy_cons, descCountBy_cons]
      cases h : lt b a with
      | false =>
        have hs := runsRunBy_spec lt (b :: bs)
        simp only [h, CallCount.tick, pure, bind, Bool.false_eq_true, ↓reduceIte, hs,
          Nat.add_zero]
      | true =>
        have hs := descRunBy_spec lt b (a :: acc) bs
        simp only [h, CallCount.tick, pure, bind, ↓reduceIte, hs]
  termination_by ys.length + 1
  decreasing_by all_goals simp_wf
end

theorem runsRunBy_value (lt : α → α → Bool) (xs : List α) :
    (runsRunBy lt xs).1 = runsBy lt xs := congrArg Prod.fst (runsRunBy_spec lt xs)

theorem ascRunBy_value (lt : α → α → Bool) (a : α) (d : Batteries.DList α) (ys : List α) :
    (ascRunBy lt a d ys).1 = ascBy lt a d ys := congrArg Prod.fst (ascRunBy_spec lt a d ys)

theorem descRunBy_value (lt : α → α → Bool) (a : α) (acc ys : List α) :
    (descRunBy lt a acc ys).1 = descBy lt a acc ys :=
  congrArg Prod.fst (descRunBy_spec lt a acc ys)

/-- Cost agreement follows from the measured branch calculation, not from value erasure. -/
theorem runsRunBy_cost (lt : α → α → Bool) (xs : List α) :
    (runsRunBy lt xs).2 = runsCountBy lt xs := congrArg Prod.snd (runsRunBy_spec lt xs)

theorem ascRunBy_cost (lt : α → α → Bool) (a : α) (d : Batteries.DList α) (ys : List α) :
    (ascRunBy lt a d ys).2 = ascCountBy lt a ys := congrArg Prod.snd (ascRunBy_spec lt a d ys)

theorem descRunBy_cost (lt : α → α → Bool) (a : α) (acc ys : List α) :
    (descRunBy lt a acc ys).2 = descCountBy lt a ys :=
  congrArg Prod.snd (descRunBy_spec lt a acc ys)

mutual
  /-- Every adjacent input boundary is tested once, including a run restart. -/
  theorem runsCountBy_exact (lt : α → α → Bool) (xs : List α) :
      runsCountBy lt xs = xs.length - 1 := by
    match xs with
    | [] => simp
    | [_] => simp
    | a :: b :: bs =>
      rw [runsCountBy_cons_cons]
      split
      · rw [descCountBy_exact lt b bs]
        simp only [List.length_cons]
        omega
      · rw [ascCountBy_exact lt b bs]
        simp only [List.length_cons]
        omega
  termination_by xs.length
  decreasing_by all_goals simp_wf

  theorem ascCountBy_exact (lt : α → α → Bool) (a : α) (ys : List α) :
      ascCountBy lt a ys = ys.length := by
    match ys with
    | [] => simp
    | b :: bs =>
      rw [ascCountBy_cons]
      split
      · rw [runsCountBy_exact lt (b :: bs)]
        simp only [List.length_cons]
        omega
      · rw [ascCountBy_exact lt b bs]
        simp only [List.length_cons]
        omega
  termination_by ys.length + 1
  decreasing_by all_goals simp_wf

  theorem descCountBy_exact (lt : α → α → Bool) (a : α) (ys : List α) :
      descCountBy lt a ys = ys.length := by
    match ys with
    | [] => simp
    | b :: bs =>
      rw [descCountBy_cons]
      split
      · rw [descCountBy_exact lt b bs]
        simp only [List.length_cons]
        omega
      · rw [runsCountBy_exact lt (b :: bs)]
        simp only [List.length_cons]
        omega
  termination_by ys.length + 1
  decreasing_by all_goals simp_wf
end

theorem runsCountBy_le (lt : α → α → Bool) (xs : List α) :
    runsCountBy lt xs ≤ xs.length - 1 := le_of_eq (runsCountBy_exact lt xs)

theorem ascCountBy_le (lt : α → α → Bool) (a : α) (ys : List α) :
    ascCountBy lt a ys ≤ ys.length := le_of_eq (ascCountBy_exact lt a ys)

theorem descCountBy_le (lt : α → α → Bool) (a : α) (ys : List α) :
    descCountBy lt a ys ≤ ys.length := le_of_eq (descCountBy_exact lt a ys)

theorem runsRunBy_cost_exact (lt : α → α → Bool) (xs : List α) :
    (runsRunBy lt xs).2 = xs.length - 1 :=
  (runsRunBy_cost lt xs).trans (runsCountBy_exact lt xs)

theorem ascRunBy_cost_exact (lt : α → α → Bool) (a : α) (d : Batteries.DList α)
    (ys : List α) : (ascRunBy lt a d ys).2 = ys.length :=
  (ascRunBy_cost lt a d ys).trans (ascCountBy_exact lt a ys)

theorem descRunBy_cost_exact (lt : α → α → Bool) (a : α) (acc ys : List α) :
    (descRunBy lt a acc ys).2 = ys.length :=
  (descRunBy_cost lt a acc ys).trans (descCountBy_exact lt a ys)

/-- The comparison observation does not require a construction history for the raw builder. -/
abbrev ascSourceRunBy (lt : α → α → Bool) (a : α) (f : List α → List α)
    (h : DListLaw f) (ys : List α) : Measured (List (List α)) Nat :=
  ascRunBy lt a (dListOfLaw f h) ys

theorem ascSourceRunBy_value (lt : α → α → Bool) (a : α) (f : List α → List α)
    (h : DListLaw f) (ys : List α) :
    (ascSourceRunBy lt a f h ys).1 = ascSourceBy lt a f h ys :=
  ascRunBy_value lt a (dListOfLaw f h) ys

theorem ascSourceRunBy_cost (lt : α → α → Bool) (a : α) (f : List α → List α)
    (h : DListLaw f) (ys : List α) : (ascSourceRunBy lt a f h ys).2 = ys.length :=
  ascRunBy_cost_exact lt a (dListOfLaw f h) ys

/-- The sorted best-case scan still compares each adjacent pair. Merge work is separate. -/
theorem runsRunBy_of_sorted [LinearOrder κ] (key : α → κ) (xs : List α)
    (hs : KeySorted key xs) (hne : xs ≠ []) :
    runsRunBy (fun x y => decide (key x < key y)) xs = ([xs], xs.length - 1) := by
  apply Prod.ext
  · rw [runsRunBy_value]
    exact runsOn_of_sorted key xs hs hne
  · exact runsRunBy_cost_exact _ xs

theorem runsRunBy_of_strictly_descending [LT κ] [DecidableLT κ]
    (key : α → κ) (xs : List α) (hs : xs.Pairwise (fun x y => key y < key x))
    (hne : xs ≠ []) :
    runsRunBy (fun x y => decide (key x < key y)) xs = ([xs.reverse], xs.length - 1) := by
  apply Prod.ext
  · rw [runsRunBy_value]
    exact runsOn_of_strictly_descending key xs hs hne
  · exact runsRunBy_cost_exact _ xs

end Resources.NaturalRunComparisons
