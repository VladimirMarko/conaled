import Applications.Segments.Candidates
import SquareKit.ListFusion

/-! Source cut/dropWhile prefix frontier, with standard right-scan realization. -/
set_option autoImplicit false
set_option warningAsError true

namespace Segments
universe u v
variable {α : Type u} {β : Type v}

/-! ## The source scan relation and a separately named derived scan variant -/

/-- The standard inclusive right scan has the source's order and seed. -/
abbrev scanrTotal (f : α → β → β) (z : β) (xs : List α) : List β := xs.scanr f z

theorem scanrTotal_head (f : α → β → β) (z : β) (xs : List α) :
    (scanrTotal f z xs).headD z = xs.foldr f z := by
  cases xs <;> simp [scanrTotal, List.scanr_cons]

theorem scanrTotal_source_cons (f : α → β → β) (z : β) (x : α) (xs : List α) :
    scanrTotal f z (x :: xs) = f x ((scanrTotal f z xs).headD z) :: scanrTotal f z xs := by
  rw [scanrTotal_head]
  exact List.scanr_cons

theorem scanrTotal_eq (f : α → β → β) (z : β) (xs : List α) :
    scanrTotal f z xs = (tails xs).map (fun suf => suf.foldr f z) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [scanrTotal, List.scanr_cons, tails, List.tails_cons,
      List.map_cons, ← ih]

theorem scanrTotal_ne_nil (f : α → β → β) (z : β) (xs : List α) :
    scanrTotal f z xs ≠ [] := by
  have h := List.length_scanr (f := f) (init := z) (as := xs)
  intro he
  change xs.scanr f z = [] at he
  rw [he] at h
  simp at h

theorem scanrTotal_length (f : α → β → β) (z : β) (xs : List α) :
    (scanrTotal f z xs).length = xs.length + 1 := List.length_scanr

def mss0Scan (bound : Nat) (xs : List Int) : List (List Int) :=
  maxsWith List.sum ((scanrTotal prefixStep [[]] xs).flatMap
    (fun ps => maxsWith List.sum (ps.filter (short bound))))

/-- This derived scan variant equals source mss0 exactly; it is not the later thinned algorithm. -/
theorem mss0Scan_eq (bound : Nat) (xs : List Int) : mss0Scan bound xs = mss0 bound xs := by
  rw [mss0Scan, scanrTotal_eq]
  simp only [List.flatMap_map, ← inits_eq_foldr]
  rfl

theorem mem_mss0Scan (bound : Nat) (xs p : List Int) :
    p ∈ mss0Scan bound xs ↔ SegmentOptimal bound xs p := by
  rw [mss0Scan_eq, mem_mss0]

example : msp0 4 [-2, 4, 4, -5, 8, -2, 3, 1] = [[-2, 4, 4]] := by decide
example : msp0 1 [0] = [[], [0]] := by decide
example : mss0 1 [0] = [[], [0], []] := by decide

/-! ## Actual source cut/op and the bounded-prefix fold -/

/-- Strict length order is the reachable-state condition used by source `cut`. -/
def LengthOrdered (ps : List (List α)) : Prop :=
  ps.Pairwise (fun p q => p.length < q.length)

/-- Source LINE742. The last/default and dropLast totalize last/init on empty input. -/
def cut (bound : Nat) (ps : List (List α)) : List (List α) :=
  if (ps.getLastD []).length = bound then ps.dropLast else ps

/-- Actual source LINE741; this uses the last/init cut, not a filter implementation. -/
def op (bound : Nat) (x : α) (ps : List (List α)) : List (List α) :=
  [] :: (cut bound ps).map (List.cons x)

/-- The historical filter-based step is retained as a distinct derived variant. -/
def boundedStep (bound : Nat) (x : α) (ps : List (List α)) : List (List α) :=
  [] :: (ps.filter (fun p => decide (p.length < bound))).map (List.cons x)

def boundedStates (bound : Nat) (xs : List α) : List (List α) :=
  xs.foldr (boundedStep bound) [[]]

/-- The actual book fold obtained by fusing the bounded-prefix filter. -/
def boundedPrefixes (bound : Nat) (xs : List α) : List (List α) :=
  xs.foldr (op bound) [[]]

theorem lengthOrdered_inits (xs : List α) : LengthOrdered (inits xs) := by
  induction xs with
  | nil => simp [LengthOrdered]
  | cons x xs ih =>
    simp only [inits_cons, LengthOrdered, List.pairwise_cons, List.mem_map]
    constructor
    · rintro p ⟨q, _, rfl⟩
      simp
    · apply List.pairwise_map.mpr
      exact ih.imp (fun h => Nat.succ_lt_succ h)

theorem cut_concat_eq_filter (bound : Nat) (ps : List (List α)) (last : List α)
    (hbefore : ∀ p ∈ ps, p.length < last.length) (hb : last.length ≤ bound) :
    cut bound (ps ++ [last]) =
      (ps ++ [last]).filter (fun p => decide (p.length < bound)) := by
  have hf : ps.filter (fun p => decide (p.length < bound)) = ps := by
    apply List.filter_eq_self.mpr
    intro p hp
    simpa using Nat.lt_of_lt_of_le (hbefore p hp) hb
  by_cases he : last.length = bound
  · simp [cut, he, hf]
  · have hl : last.length < bound := by omega
    simp [cut, he, hf, hl]

/-- On strictly length-ordered bounded candidates, source cut equals a strict-length filter. -/
theorem cut_eq_filter (bound : Nat) (ps : List (List α))
    (ho : LengthOrdered ps) (hb : ∀ p ∈ ps, p.length ≤ bound) :
    cut bound ps = ps.filter (fun p => decide (p.length < bound)) := by
  by_cases hn : ps = []
  · simp [hn, cut]
  · have he := List.dropLast_concat_getLast hn
    have hpair : LengthOrdered (ps.dropLast ++ [ps.getLast hn]) := he.symm ▸ ho
    have hbefore : ∀ p ∈ ps.dropLast, p.length < (ps.getLast hn).length := by
      have h := (List.pairwise_append.mp hpair).2.2
      exact fun p hp => h p hp _ (by simp)
    have hlast := hb _ (List.getLast_mem hn)
    simpa only [he] using cut_concat_eq_filter bound ps.dropLast (ps.getLast hn) hbefore hlast

theorem op_eq_boundedStep (bound : Nat) (x : α) (ps : List (List α))
    (ho : LengthOrdered ps) (hb : ∀ p ∈ ps, p.length ≤ bound) :
    op bound x ps = boundedStep bound x ps := by
  simp only [op, boundedStep, cut_eq_filter bound ps ho hb]

/-- A filter-fusion equation independent of the particular prefix contents. -/
theorem boundedStep_filter (bound : Nat) (x : α) (ps : List (List α)) :
    boundedStep bound x (ps.filter (short bound)) =
      (prefixStep x ps).filter (short bound) := by
  have hp : (fun p : List α => decide (p.length < bound) && decide (p.length ≤ bound)) =
      (fun p : List α => decide ((x :: p).length ≤ bound)) := by
    funext p
    simp only [← Bool.decide_and, decide_eq_decide, List.length_cons]
    omega
  simp only [boundedStep, short, List.filter_filter, prefixStep, List.filter_cons,
    List.length_nil, Nat.zero_le, decide_true, List.filter_map, hp, ite_true]
  rfl

/-- Exact order and multiplicities, strengthening the historical membership-only relation. -/
theorem boundedStates_eq_filter (bound : Nat) (xs : List α) :
    boundedStates bound xs = (inits xs).filter (short bound) := by
  have fusion := SquareKit.ListFusion.foldr_reachable prefixStep (boundedStep bound)
    (fun ps => ps.filter (short bound)) (fun _ => True) ([[]] : List (List α))
    True.intro (fun _ _ _ => True.intro)
    (fun x ps _ => (boundedStep_filter bound x ps).symm) xs
  unfold boundedStates
  simpa only [← inits_eq_foldr, List.filter_cons, short, List.length_nil,
    Nat.zero_le, decide_true, ite_true, List.filter_nil] using fusion.symm

theorem boundedStates_ordered (bound : Nat) (xs : List α) :
    LengthOrdered (boundedStates bound xs) := by
  rw [boundedStates_eq_filter]
  exact (lengthOrdered_inits xs).filter _

theorem boundedStates_bound (bound : Nat) (xs p : List α)
    (hp : p ∈ boundedStates bound xs) : p.length ≤ bound := by
  rw [boundedStates_eq_filter] at hp
  exact of_decide_eq_true (List.mem_filter.mp hp).2

/-- The actual last/init fold equals the independently retained filter fold exactly. -/
theorem boundedPrefixes_eq_boundedStates (bound : Nat) (xs : List α) :
    boundedPrefixes bound xs = boundedStates bound xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change op bound x (boundedPrefixes bound xs) =
      boundedStep bound x (boundedStates bound xs)
    rw [ih]
    exact op_eq_boundedStep bound x _ (boundedStates_ordered bound xs)
      (boundedStates_bound bound xs)

theorem boundedPrefixes_eq_filter (bound : Nat) (xs : List α) :
    boundedPrefixes bound xs = (inits xs).filter (short bound) := by
  rw [boundedPrefixes_eq_boundedStates, boundedStates_eq_filter]

theorem mem_boundedPrefixes (bound : Nat) (xs p : List α) :
    p ∈ boundedPrefixes bound xs ↔ IsPrefix p xs ∧ p.length ≤ bound := by
  simp [boundedPrefixes_eq_filter, short]

theorem boundedPrefixes_ordered (bound : Nat) (xs : List α) :
    LengthOrdered (boundedPrefixes bound xs) := by
  rw [boundedPrefixes_eq_boundedStates]
  exact boundedStates_ordered bound xs

theorem boundedPrefixes_ne_nil (bound : Nat) (xs : List α) :
    boundedPrefixes bound xs ≠ [] := by
  have hm : [] ∈ boundedPrefixes bound xs :=
    (mem_boundedPrefixes bound xs []).mpr ⟨⟨xs, rfl⟩, by simp⟩
  intro h
  simp [h] at hm

theorem cut_boundedPrefixes_eq_filter (bound : Nat) (xs : List α) :
    cut bound (boundedPrefixes bound xs) =
      (boundedPrefixes bound xs).filter (fun p => decide (p.length < bound)) := by
  apply cut_eq_filter _ _ (boundedPrefixes_ordered bound xs)
  intro p hp
  exact ((mem_boundedPrefixes bound xs p).mp hp).2

theorem boundedPrefixes_zero (xs : List α) : boundedPrefixes 0 xs = [[]] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change op 0 x (boundedPrefixes 0 xs) = [[]]
    simp [ih, op, cut]

theorem boundedPrefixes_cons_succ (bound : Nat) (x : α) (xs : List α) :
    boundedPrefixes (bound + 1) (x :: xs) =
      [] :: (boundedPrefixes bound xs).map (List.cons x) := by
  simp [boundedPrefixes_eq_filter, short, List.filter_map, Function.comp_def]
  rfl

/-- Exact retained-candidate count, not an evaluator work or space bound. -/
theorem boundedPrefixes_length (bound : Nat) (xs : List α) :
    (boundedPrefixes bound xs).length = min bound xs.length + 1 := by
  induction xs generalizing bound with
  | nil => simp [boundedPrefixes]
  | cons x xs ih =>
    cases bound with
    | zero => simp [boundedPrefixes_zero]
    | succ bound =>
      rw [boundedPrefixes_cons_succ]
      simp only [List.length_cons, List.length_map, ih]
      omega

theorem boundedPrefixes_nodup (bound : Nat) (xs : List α) :
    (boundedPrefixes bound xs).Nodup := by
  apply (boundedPrefixes_ordered bound xs).imp
  intro p q hlt heq
  subst q
  exact Nat.lt_irrefl _ hlt

def mspBounded (bound : Nat) (xs : List Int) : List (List Int) :=
  maxsWith List.sum (boundedPrefixes bound xs)

theorem mspBounded_eq (bound : Nat) (xs : List Int) :
    mspBounded bound xs = msp0 bound xs := by
  simp only [mspBounded, boundedPrefixes_eq_filter, msp0]

theorem mem_mspBounded (bound : Nat) (xs p : List Int) :
    p ∈ mspBounded bound xs ↔ PrefixOptimal bound xs p := by
  rw [mspBounded_eq, mem_msp0]

/-- Derived all-optima segment reduction using the actual bounded-prefix fold. -/
def mssBoundedScan (bound : Nat) (xs : List Int) : List (List Int) :=
  maxsWith List.sum ((scanrTotal (op bound) [[]] xs).flatMap (maxsWith List.sum))

theorem boundedPrefixes_scan (bound : Nat) (xs : List α) :
    scanrTotal (op bound) [[]] xs = (tails xs).map (boundedPrefixes bound) := by
  exact scanrTotal_eq _ _ _

theorem mssBoundedScan_eq (bound : Nat) (xs : List Int) :
    mssBoundedScan bound xs = mss0 bound xs := by
  rw [mssBoundedScan, boundedPrefixes_scan]
  simp only [List.flatMap_map]
  change maxsWith List.sum ((tails xs).flatMap (mspBounded bound)) = mss0 bound xs
  simp only [funext (mspBounded_eq bound), mss0]

theorem mem_mssBoundedScan (bound : Nat) (xs p : List Int) :
    p ∈ mssBoundedScan bound xs ↔ SegmentOptimal bound xs p := by
  rw [mssBoundedScan_eq, mem_mss0]

example : boundedPrefixes 2 [1, 2, 3] = [[], [1], [1, 2]] := by decide
example : boundedPrefixes 0 [1, 2, 3] = [[]] := by decide
example : mssBoundedScan 1 [0] = [[], [0], []] := by decide

/-! ## Actual source order-preserving thinning -/

def SumOrdered (ps : List (List Int)) : Prop :=
  ps.Pairwise (fun p q => p.sum < q.sum)

/-- An independent comparison of candidate quality and resource use. -/
def PrefixDominates (representative candidate : List Int) : Prop :=
  candidate.sum ≤ representative.sum ∧ representative.length ≤ candidate.length

/-- Actual source LINE775. This is dropWhile, not an arbitrary frontier insertion routine. -/
def thin (ps : List (List Int)) : List (List Int) :=
  ps.dropWhile (fun p => decide (p.sum ≤ 0))

/-- Actual source LINE774. -/
def op2 (bound : Nat) (x : Int) (ps : List (List Int)) : List (List Int) :=
  [] :: thin ((cut bound ps).map (List.cons x))

def thinnedPrefixes (bound : Nat) (xs : List Int) : List (List Int) :=
  xs.foldr (op2 bound) [[]]

/-- Actual source LINE773, with an unused total last default on reachable states. -/
def msp1 (bound : Nat) (xs : List Int) : List Int :=
  (thinnedPrefixes bound xs).getLastD []

theorem cut_sublist (bound : Nat) (ps : List (List α)) : List.Sublist (cut bound ps) ps := by
  unfold cut
  split
  · exact List.dropLast_sublist ps
  · exact List.Sublist.refl ps

theorem thin_sublist (ps : List (List Int)) : List.Sublist (thin ps) ps :=
  List.dropWhile_sublist _

/-- This replacement by a filter is conditional on the ordered-score invariant. -/
theorem thin_eq_filter (ps : List (List Int)) (hs : SumOrdered ps) :
    thin ps = ps.filter (fun p => decide (0 < p.sum)) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨hfirst, hrest⟩ := List.pairwise_cons.mp hs
    by_cases hp : p.sum ≤ 0
    · have hn : ¬ 0 < p.sum := by omega
      simpa [thin, hp, hn] using ih hrest
    · have hpos : 0 < p.sum := by omega
      have hf : ps.filter (fun q => decide (0 < q.sum)) = ps := by
        apply List.filter_eq_self.mpr
        intro q hq
        have hlt := hfirst q hq
        simpa using (show 0 < q.sum by omega)
      simp [thin, hp, hpos, hf]

theorem sumOrdered_map_cons (x : Int) (ps : List (List Int)) (hs : SumOrdered ps) :
    SumOrdered (ps.map (List.cons x)) := by
  apply List.pairwise_map.mpr
  apply hs.imp
  intro p q h
  simp only [List.sum_cons]
  omega

theorem op2_eq_filtered_map (bound : Nat) (x : Int) (ps : List (List Int))
    (hs : SumOrdered ps) :
    op2 bound x ps = [] :: ((cut bound ps).map (List.cons x)).filter
      (fun p => decide (0 < p.sum)) := by
  rw [op2, thin_eq_filter]
  exact sumOrdered_map_cons x _ (hs.sublist (cut_sublist bound ps))

theorem op2_lengthOrdered (bound : Nat) (x : Int) (ps : List (List Int))
    (hl : LengthOrdered ps) : LengthOrdered (op2 bound x ps) := by
  apply List.pairwise_cons.mpr
  constructor
  · intro p hp
    have hmap := (thin_sublist _).subset hp
    obtain ⟨q, _, rfl⟩ := List.mem_map.mp hmap
    simp
  · apply List.Pairwise.sublist (thin_sublist _)
    apply List.pairwise_map.mpr
    exact (hl.sublist (cut_sublist bound ps)).imp (fun h => Nat.succ_lt_succ h)

theorem op2_sumOrdered (bound : Nat) (x : Int) (ps : List (List Int))
    (hs : SumOrdered ps) : SumOrdered (op2 bound x ps) := by
  rw [op2_eq_filtered_map bound x ps hs]
  apply List.pairwise_cons.mpr
  constructor
  · intro p hp
    simpa using of_decide_eq_true (List.mem_filter.mp hp).2
  · exact (sumOrdered_map_cons x _ (hs.sublist (cut_sublist bound ps))).filter _

theorem op2_bound (bound : Nat) (x : Int) (ps : List (List Int))
    (hl : LengthOrdered ps) (hb : ∀ p ∈ ps, p.length ≤ bound) :
    ∀ p ∈ op2 bound x ps, p.length ≤ bound := by
  intro p hp
  rcases List.mem_cons.mp hp with rfl | hp
  · simp
  · have hmap := (thin_sublist _).subset hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hmap
    rw [cut_eq_filter bound ps hl hb] at hq
    have hlt : q.length < bound := of_decide_eq_true (List.mem_filter.mp hq).2
    simp only [List.length_cons]
    omega

theorem thinnedPrefixes_invariants (bound : Nat) (xs : List Int) :
    LengthOrdered (thinnedPrefixes bound xs) ∧ SumOrdered (thinnedPrefixes bound xs) ∧
      ∀ p ∈ thinnedPrefixes bound xs, p.length ≤ bound := by
  induction xs with
  | nil => simp [thinnedPrefixes, LengthOrdered, SumOrdered]
  | cons x xs ih =>
    change LengthOrdered (op2 bound x (thinnedPrefixes bound xs)) ∧
      SumOrdered (op2 bound x (thinnedPrefixes bound xs)) ∧ _
    exact ⟨op2_lengthOrdered _ _ _ ih.1, op2_sumOrdered _ _ _ ih.2.1,
      op2_bound _ _ _ ih.1 ih.2.2⟩

@[simp] theorem empty_mem_thinnedPrefixes (bound : Nat) (xs : List Int) :
    [] ∈ thinnedPrefixes bound xs := by
  cases xs <;> simp [thinnedPrefixes, op2]

theorem thinnedPrefixes_ne_nil (bound : Nat) (xs : List Int) :
    thinnedPrefixes bound xs ≠ [] := by
  intro h
  have hm := empty_mem_thinnedPrefixes bound xs
  simp [h] at hm

theorem thinnedPrefixes_feasible (bound : Nat) (xs p : List Int)
    (hp : p ∈ thinnedPrefixes bound xs) : IsPrefix p xs ∧ p.length ≤ bound := by
  refine ⟨?_, (thinnedPrefixes_invariants bound xs).2.2 p hp⟩
  induction xs generalizing p with
  | nil =>
    have he : p = [] := by simpa [thinnedPrefixes] using hp
    exact ⟨[], by simp [he]⟩
  | cons x xs ih =>
    change p ∈ [] :: thin ((cut bound (thinnedPrefixes bound xs)).map (List.cons x)) at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨x :: xs, rfl⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp ((thin_sublist _).subset hp)
      obtain ⟨after, hafter⟩ := ih q ((cut_sublist _ _).subset hq)
      exact ⟨after, by simp [hafter]⟩

theorem thinnedPrefixes_covers (bound : Nat) (xs candidate : List Int)
    (hc : IsPrefix candidate xs) (hb : candidate.length ≤ bound) :
    ∃ representative ∈ thinnedPrefixes bound xs, PrefixDominates representative candidate := by
  induction xs generalizing candidate with
  | nil =>
    obtain ⟨after, hafter⟩ := hc
    have he := (List.append_eq_nil_iff.mp hafter).1
    subst candidate
    exact ⟨[], empty_mem_thinnedPrefixes bound [], by simp [PrefixDominates]⟩
  | cons x xs ih =>
    cases candidate with
    | nil => exact ⟨[], empty_mem_thinnedPrefixes bound _, by simp [PrefixDominates]⟩
    | cons y candidate =>
      obtain ⟨after, hafter⟩ := hc
      have he : y = x ∧ candidate ++ after = xs := by simpa using hafter
      have hy : y = x := he.1
      subst y
      have hcat := he.2
      have hshort : candidate.length < bound := by
        simp only [List.length_cons] at hb
        omega
      obtain ⟨p, hp, hdom⟩ := ih candidate ⟨after, hcat⟩ (by omega)
      have hcut : p ∈ cut bound (thinnedPrefixes bound xs) := by
        rw [cut_eq_filter _ _ (thinnedPrefixes_invariants bound xs).1
          (thinnedPrefixes_invariants bound xs).2.2]
        apply List.mem_filter.mpr
        exact ⟨hp, by simpa using (show p.length < bound by have := hdom.2; omega)⟩
      by_cases hpositive : 0 < (x :: p).sum
      · refine ⟨x :: p, ?_, ?_⟩
        · change x :: p ∈ op2 bound x (thinnedPrefixes bound xs)
          rw [op2_eq_filtered_map _ _ _ (thinnedPrefixes_invariants bound xs).2.1]
          exact List.mem_cons_of_mem [] (List.mem_filter.mpr
            ⟨List.mem_map.mpr ⟨p, hcut, rfl⟩, by simpa only [decide_eq_true_eq] using hpositive⟩)
        · obtain ⟨hscore, hlen⟩ := hdom
          constructor
          · simp only [List.sum_cons]
            omega
          · simp only [List.length_cons]
            omega
      · refine ⟨[], empty_mem_thinnedPrefixes bound _, ?_⟩
        obtain ⟨hscore, _⟩ := hdom
        constructor
        · simp only [List.sum_cons, List.sum_nil] at hpositive ⊢
          omega
        · simp

/-- In a nonempty strictly sum-ordered list, an earlier member has strictly smaller sum. -/
theorem sumOrdered_last (ps : List (List Int)) (hs : SumOrdered ps) (hn : ps ≠ []) :
    ps.getLastD [] ∈ ps ∧ ∀ p ∈ ps, p = ps.getLastD [] ∨ p.sum < (ps.getLastD []).sum := by
  have he := List.dropLast_concat_getLast hn
  have hpair : SumOrdered (ps.dropLast ++ [ps.getLast hn]) := he.symm ▸ hs
  have hbefore := (List.pairwise_append.mp hpair).2.2
  have hg : ps.getLastD [] = ps.getLast hn := by
    calc
      ps.getLastD [] = (ps.dropLast ++ [ps.getLast hn]).getLastD [] :=
        congrArg (fun qs => qs.getLastD []) he.symm
      _ = ps.getLast hn := List.getLastD_concat
  rw [hg]
  refine ⟨List.getLast_mem hn, ?_⟩
  intro p hp
  rw [← he] at hp
  rcases List.mem_append.mp hp with hp | hp
  · exact Or.inr (hbefore p hp _ (by simp))
  · exact Or.inl (by simpa using hp)

/-- Source thinning preserves the relative order of the surviving bounded prefixes. -/
theorem thinnedPrefixes_sublist (bound : Nat) (xs : List Int) :
    List.Sublist (thinnedPrefixes bound xs) (boundedPrefixes bound xs) := by
  induction xs with
  | nil => exact List.Sublist.refl _
  | cons x xs ih =>
    change List.Sublist ([] :: thin ((cut bound (thinnedPrefixes bound xs)).map (List.cons x)))
      ([] :: (cut bound (boundedPrefixes bound xs)).map (List.cons x))
    apply List.Sublist.cons_cons
    apply List.Sublist.trans (thin_sublist _)
    apply List.Sublist.map
    rw [cut_eq_filter _ _ (thinnedPrefixes_invariants bound xs).1
      (thinnedPrefixes_invariants bound xs).2.2, cut_boundedPrefixes_eq_filter]
    exact ih.filter _

/-- Actual source frontier, with shared origin/order/coverage semantics. -/
theorem thinnedPrefixes_refinement (bound : Nat) (xs : List Int) :
    Optimization.Thinning.IsThinning PrefixDominates
      (boundedPrefixes bound xs) (thinnedPrefixes bound xs) := by
  refine ⟨thinnedPrefixes_sublist bound xs, ?_⟩
  intro candidate hc
  have h := (mem_boundedPrefixes bound xs candidate).mp hc
  exact thinnedPrefixes_covers bound xs candidate h.1 h.2

theorem msp1_optimal (bound : Nat) (xs : List Int) : PrefixOptimal bound xs (msp1 bound xs) := by
  let cost : List Int → OrderDual Int := fun p => OrderDual.toDual p.sum
  have hs := sumOrdered_last _ (thinnedPrefixes_invariants bound xs).2.1
    (thinnedPrefixes_ne_nil bound xs)
  have localOpt : msp1 bound xs ∈ Optimization.minimizers
      {p | p ∈ thinnedPrefixes bound xs} cost := by
    refine ⟨hs.1, ?_⟩
    intro p hp
    rcases hs.2 p hp with he | hlt
    · change p.sum ≤ ((thinnedPrefixes bound xs).getLastD []).sum
      rw [he]
    · exact Int.le_of_lt hlt
  have globalOpt := Optimization.Thinning.minimizer_of_represents
    (thinnedPrefixes_refinement bound xs).represents cost
    (fun _ _ _ _ h => h.1) localOpt
  have feasible := (mem_boundedPrefixes bound xs _).mp globalOpt.1
  exact ⟨feasible.1, feasible.2, fun candidate hc hb =>
    globalOpt.2 ((mem_boundedPrefixes bound xs candidate).mpr ⟨hc, hb⟩)⟩

theorem msp1_mem_msp0 (bound : Nat) (xs : List Int) : msp1 bound xs ∈ msp0 bound xs :=
  (mem_msp0 bound xs _).mpr (msp1_optimal bound xs)

/-- The source thinning policy chooses a shortest globally optimal prefix. -/
theorem msp1_shortest_optimum (bound : Nat) (xs candidate : List Int)
    (hc : PrefixOptimal bound xs candidate) : (msp1 bound xs).length ≤ candidate.length := by
  obtain ⟨p, hp, hdom⟩ := thinnedPrefixes_covers bound xs candidate hc.1 hc.2.1
  have hs := sumOrdered_last _ (thinnedPrefixes_invariants bound xs).2.1
    (thinnedPrefixes_ne_nil bound xs)
  rcases hs.2 p hp with he | hlt
  · change ((thinnedPrefixes bound xs).getLastD []).length ≤ candidate.length
    rw [← he]
    exact hdom.2
  · have hm := msp1_optimal bound xs
    have hmax := hc.2.2 _ hm.1 hm.2.1
    change ((thinnedPrefixes bound xs).getLastD []).sum ≤ candidate.sum at hmax
    have hscore := hdom.1
    omega

theorem thinnedPrefixes_nodup (bound : Nat) (xs : List Int) :
    (thinnedPrefixes bound xs).Nodup :=
  (thinnedPrefixes_sublist bound xs).nodup (boundedPrefixes_nodup bound xs)

/-- A bound on the number of stored candidate lists, not a runtime/space-complexity theorem. -/
theorem thinnedPrefixes_length_le (bound : Nat) (xs : List Int) :
    (thinnedPrefixes bound xs).length ≤ min bound xs.length + 1 := by
  have h := (thinnedPrefixes_sublist bound xs).length_le
  simpa only [boundedPrefixes_length] using h

theorem thinnedPrefixes_antichain (bound : Nat) (xs : List Int) :
    (thinnedPrefixes bound xs).Pairwise (fun p q =>
      ¬ PrefixDominates p q ∧ ¬ PrefixDominates q p) := by
  have hi := thinnedPrefixes_invariants bound xs
  apply (hi.1.and hi.2.1).imp
  intro p q h
  constructor
  · intro hd
    have hscore := h.2
    have hreverse := hd.1
    omega
  · intro hd
    exact Nat.not_le_of_lt h.1 hd.2

theorem msp1_zero (xs : List Int) : msp1 0 xs = [] := by
  have hb := (msp1_optimal 0 xs).2.1
  exact List.eq_nil_iff_length_eq_zero.mpr (by omega)

theorem msp1_sum_eq_optimum (bound : Nat) (xs p : List Int)
    (hp : PrefixOptimal bound xs p) : (msp1 bound xs).sum = p.sum := by
  have hm := msp1_optimal bound xs
  exact Int.le_antisymm (hp.2.2 _ hm.1 hm.2.1) (hm.2.2 _ hp.1 hp.2.1)

example : msp1 4 [-2, 4, 4, -5, 8, -2, 3, 1] = [-2, 4, 4] := by decide
example : msp1 1 [0] = [] := by decide
example : msp1 2 [1, 0] = [1] := by decide
example : msp1 0 [1, 2, 3] = [] := by decide

end Segments
