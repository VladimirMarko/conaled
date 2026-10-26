import Applications.Optimization.Thinning
import Mathlib.Data.List.Infix

/-! Bounded segment candidates and independent global optima.
Source: adwh-checkpoint-233; see docs/research/adwh-bounded-segments.md. -/
set_option autoImplicit false
set_option warningAsError true

namespace Segments

universe u v
variable {α : Type u} {β : Type v}

abbrev IsPrefix (pre xs : List α) : Prop := pre.IsPrefix xs
abbrev IsSegment (segment xs : List α) : Prop := segment.IsInfix xs

def prefixStep (x : α) (ps : List (List α)) : List (List α) :=
  [] :: ps.map (List.cons x)

abbrev inits (xs : List α) : List (List α) := xs.inits
abbrev tails (xs : List α) : List (List α) := xs.tails

def segments (xs : List α) : List (List α) := (tails xs).flatMap inits

@[simp] theorem inits_nil : inits ([] : List α) = [[]] := rfl
@[simp] theorem inits_cons (x : α) (xs : List α) :
    inits (x :: xs) = [] :: (inits xs).map (List.cons x) := List.inits_cons x xs

theorem inits_eq_foldr (xs : List α) : inits xs = xs.foldr prefixStep [[]] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [inits_cons, List.foldr_cons, prefixStep, ih]

theorem mem_inits (xs pre : List α) : pre ∈ inits xs ↔ IsPrefix pre xs := List.mem_inits pre xs

theorem mem_tails (xs suf : List α) :
    suf ∈ tails xs ↔ ∃ before, before ++ suf = xs := List.mem_tails suf xs

theorem mem_segments (xs segment : List α) :
    segment ∈ segments xs ↔ IsSegment segment xs := by
  simp only [segments, List.mem_flatMap]
  constructor
  · rintro ⟨suf, hs, hp⟩
    obtain ⟨before, hbefore⟩ := (mem_tails xs suf).mp hs
    obtain ⟨after, hafter⟩ := (mem_inits suf segment).mp hp
    exact ⟨before, after, by rw [List.append_assoc, hafter, hbefore]⟩
  · rintro ⟨before, after, hcat⟩
    refine ⟨segment ++ after, (mem_tails xs _).mpr ⟨before, ?_⟩,
      (mem_inits _ _).mpr ⟨after, rfl⟩⟩
    simpa [List.append_assoc] using hcat

@[simp] theorem empty_mem_inits (xs : List α) : [] ∈ inits xs := by
  exact (mem_inits xs []).mpr ⟨xs, rfl⟩

@[simp] theorem empty_mem_segments (xs : List α) : [] ∈ segments xs := by
  exact (mem_segments xs []).mpr ⟨[], xs, rfl⟩

@[simp] theorem self_mem_tails (xs : List α) : xs ∈ tails xs := by
  exact (mem_tails xs xs).mpr ⟨[], rfl⟩

theorem length_inits (xs : List α) : (inits xs).length = xs.length + 1 := by
  exact List.length_inits xs

theorem length_tails (xs : List α) : (tails xs).length = xs.length + 1 := by
  exact List.length_tails xs

/-! ## The source all-maxima selector with cached scores -/

def maximumFrom (seed : Int) : List (Int × α) → Int
  | [] => seed
  | p :: ps => max p.1 (maximumFrom seed ps)

theorem maximumFrom_le_iff (seed : Int) (ps : List (Int × α)) (bound : Int) :
    maximumFrom seed ps ≤ bound ↔ seed ≤ bound ∧ ∀ p ∈ ps, p.1 ≤ bound := by
  induction ps with
  | nil => simp [maximumFrom]
  | cons p ps ih =>
    simp [maximumFrom, ih, and_left_comm]

def selectScore (best : Int) (scored : List (Int × α)) : List α :=
  scored.filterMap (fun p => if p.1 = best then some p.2 else none)

/-- The source `bas` score cache is preserved; empty input emits [] without computing a maximum. -/
def maxsWith (score : α → Int) (xs : List α) : List α :=
  let scored := xs.map (fun x => (score x, x))
  match scored with
  | [] => []
  | p :: ps => selectScore (maximumFrom p.1 ps) scored

theorem selectScore_map (score : α → Int) (best : Int) (xs : List α) :
    selectScore best (xs.map (fun x => (score x, x))) =
      xs.filter (fun x => decide (score x = best)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : score x = best <;> simpa [selectScore, h] using ih

@[simp] theorem maxsWith_nil (score : α → Int) : maxsWith score [] = [] := rfl

/-- Exact filtering equation: all occurrences of tied maxima are kept in source order. -/
theorem maxsWith_cons (score : α → Int) (x : α) (xs : List α) :
    maxsWith score (x :: xs) = (x :: xs).filter (fun y =>
      decide (score y = maximumFrom (score x) (xs.map (fun z => (score z, z))))) := by
  change selectScore _ ((x :: xs).map (fun z => (score z, z))) = _
  exact selectScore_map _ _ _

theorem mem_maxsWith (score : α → Int) (xs : List α) (x : α) :
    x ∈ maxsWith score xs ↔ x ∈ xs ∧ ∀ y ∈ xs, score y ≤ score x := by
  cases xs with
  | nil => simp
  | cons first rest =>
    let best := maximumFrom (score first) (rest.map (fun y => (score y, y)))
    have hb := (maximumFrom_le_iff (score first)
      (rest.map (fun y => (score y, y))) best).mp (Int.le_refl best)
    have hbound : ∀ y ∈ first :: rest, score y ≤ best := by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hb.1
      · exact hb.2 (score y, y) (List.mem_map.mpr ⟨y, hy, rfl⟩)
    rw [maxsWith_cons]
    simp only [List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨hx, heq⟩
      exact ⟨hx, fun y hy => heq ▸ hbound y hy⟩
    · rintro ⟨hx, hmax⟩
      have hu : best ≤ score x := by
        apply (maximumFrom_le_iff _ _ _).mpr
        refine ⟨hmax first (by simp), ?_⟩
        intro p hp
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hp
        exact hmax y (by simp [hy])
      exact ⟨hx, Int.le_antisymm (hbound x hx) hu⟩

theorem exists_maximum (score : α → Int) (first : α) (rest : List α) :
    ∃ x ∈ first :: rest, ∀ y ∈ first :: rest, score y ≤ score x := by
  let cost : α → OrderDual Int := fun x => OrderDual.toDual (score x)
  cases h : Optimization.Thinning.argmin cost (first :: rest) with
  | none => have := (Optimization.Thinning.argmin_eq_none_iff cost _).mp h; contradiction
  | some x =>
    have hx := Optimization.Thinning.argmin_correct cost _ x h
    exact ⟨x, hx.1, fun y hy => hx.2 hy⟩

theorem maxsWith_covers (score : α → Int) (xs : List α) (x : α) (hx : x ∈ xs) :
    ∃ y ∈ maxsWith score xs, score x ≤ score y := by
  cases xs with
  | nil => cases hx
  | cons first rest =>
    obtain ⟨y, hy, hm⟩ := exists_maximum score first rest
    exact ⟨y, (mem_maxsWith score _ y).mpr ⟨hy, hm⟩, hm x hx⟩

theorem maxsWith_ne_nil (score : α → Int) (xs : List α) (hx : xs ≠ []) :
    maxsWith score xs ≠ [] := by
  cases xs with
  | nil => exact False.elim (hx rfl)
  | cons first rest =>
    obtain ⟨y, hy, _⟩ := maxsWith_covers score (first :: rest) first (by simp)
    intro he
    simp [he] at hy

/-! ## Independent prefix and segment optimality -/

def short (bound : Nat) (xs : List α) : Bool := decide (xs.length ≤ bound)

def PrefixOptimal (bound : Nat) (xs result : List Int) : Prop :=
  IsPrefix result xs ∧ result.length ≤ bound ∧
    ∀ candidate, IsPrefix candidate xs → candidate.length ≤ bound → candidate.sum ≤ result.sum

def SegmentOptimal (bound : Nat) (xs result : List Int) : Prop :=
  IsSegment result xs ∧ result.length ≤ bound ∧
    ∀ candidate, IsSegment candidate xs → candidate.length ≤ bound → candidate.sum ≤ result.sum

/-- Exact source LINE662–664: all maximizing short prefixes. -/
def msp0 (bound : Nat) (xs : List Int) : List (List Int) :=
  maxsWith List.sum ((inits xs).filter (short bound))

/-- Exact source LINE662–663: all maximizing prefix optima across all suffixes. -/
def mss0 (bound : Nat) (xs : List Int) : List (List Int) :=
  maxsWith List.sum ((tails xs).flatMap (msp0 bound))

/-- Direct all-optima interpretation of the independent book segment specification. -/
def maxSegmentExhaustive (bound : Nat) (xs : List Int) : List (List Int) :=
  maxsWith List.sum ((segments xs).filter (short bound))

theorem mem_msp0 (bound : Nat) (xs p : List Int) :
    p ∈ msp0 bound xs ↔ PrefixOptimal bound xs p := by
  simp only [msp0, mem_maxsWith, List.mem_filter, mem_inits, short, decide_eq_true_eq,
    PrefixOptimal, and_assoc]
  constructor
  · rintro ⟨hp, hb, hmax⟩
    exact ⟨hp, hb, fun q hq hqb => hmax q ⟨hq, hqb⟩⟩
  · rintro ⟨hp, hb, hmax⟩
    exact ⟨hp, hb, fun q ⟨hq, hqb⟩ => hmax q hq hqb⟩

theorem prefix_of_suffix_isSegment (xs suf p : List α)
    (hs : suf ∈ tails xs) (hp : IsPrefix p suf) : IsSegment p xs := by
  obtain ⟨before, hbefore⟩ := (mem_tails xs suf).mp hs
  obtain ⟨after, hafter⟩ := hp
  exact ⟨before, after, by rw [List.append_assoc, hafter, hbefore]⟩

theorem msp0_covers (bound : Nat) (xs p : List Int)
    (hp : IsPrefix p xs) (hb : p.length ≤ bound) :
    ∃ q ∈ msp0 bound xs, p.sum ≤ q.sum := by
  apply maxsWith_covers List.sum _ p
  simp [short, hp, hb]

theorem msp0_ne_nil (bound : Nat) (xs : List Int) : msp0 bound xs ≠ [] := by
  obtain ⟨q, hq, _⟩ := msp0_covers bound xs [] ⟨xs, rfl⟩ (by simp)
  intro he
  simp [he] at hq

theorem mem_mss0 (bound : Nat) (xs p : List Int) :
    p ∈ mss0 bound xs ↔ SegmentOptimal bound xs p := by
  rw [mss0, mem_maxsWith]
  constructor
  · rintro ⟨hp, hmax⟩
    obtain ⟨suf, hs, hpre⟩ := List.mem_flatMap.mp hp
    obtain ⟨hprefix, hb, _⟩ := (mem_msp0 bound suf p).mp hpre
    refine ⟨prefix_of_suffix_isSegment xs suf p hs hprefix, hb, ?_⟩
    intro candidate hseg hc
    obtain ⟨before, after, hcat⟩ := hseg
    have hsuf : candidate ++ after ∈ tails xs :=
      (mem_tails xs _).mpr ⟨before, by simpa [List.append_assoc] using hcat⟩
    obtain ⟨q, hq, hscore⟩ := msp0_covers bound (candidate ++ after) candidate ⟨after, rfl⟩ hc
    exact Int.le_trans hscore (hmax q (List.mem_flatMap.mpr ⟨_, hsuf, hq⟩))
  · rintro ⟨hseg, hb, hmax⟩
    obtain ⟨before, after, hcat⟩ := hseg
    have hsuf : p ++ after ∈ tails xs :=
      (mem_tails xs _).mpr ⟨before, by simpa [List.append_assoc] using hcat⟩
    have hpref : PrefixOptimal bound (p ++ after) p := by
      refine ⟨⟨after, rfl⟩, hb, ?_⟩
      intro q hq hqb
      exact hmax q (prefix_of_suffix_isSegment xs _ q hsuf hq) hqb
    refine ⟨List.mem_flatMap.mpr ⟨_, hsuf, (mem_msp0 bound _ p).mpr hpref⟩, ?_⟩
    intro q hq
    obtain ⟨suf, hs, hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨hprefix, hqb, _⟩ := (mem_msp0 bound suf q).mp hq
    exact hmax q (prefix_of_suffix_isSegment xs suf q hs hprefix) hqb

theorem mem_maxSegmentExhaustive (bound : Nat) (xs p : List Int) :
    p ∈ maxSegmentExhaustive bound xs ↔ SegmentOptimal bound xs p := by
  simp only [maxSegmentExhaustive, mem_maxsWith, List.mem_filter, mem_segments,
    short, decide_eq_true_eq, SegmentOptimal, and_assoc]
  constructor
  · rintro ⟨hp, hb, hm⟩
    exact ⟨hp, hb, fun q hq hqb => hm q ⟨hq, hqb⟩⟩
  · rintro ⟨hp, hb, hm⟩
    exact ⟨hp, hb, fun q ⟨hq, hqb⟩ => hm q hq hqb⟩

/-- Membership equality does not assert equality of all-optima multiplicities. -/
theorem mss0_membership_refinement (bound : Nat) (xs p : List Int) :
    p ∈ mss0 bound xs ↔ p ∈ maxSegmentExhaustive bound xs := by
  rw [mem_mss0, mem_maxSegmentExhaustive]

theorem optimal_segment_sum_unique (bound : Nat) (xs p q : List Int)
    (hp : SegmentOptimal bound xs p) (hq : SegmentOptimal bound xs q) : p.sum = q.sum := by
  exact Int.le_antisymm (hq.2.2 p hp.1 hp.2.1) (hp.2.2 q hq.1 hq.2.1)

theorem optimal_segment_nonnegative (bound : Nat) (xs p : List Int)
    (hp : SegmentOptimal bound xs p) : 0 ≤ p.sum := by
  have := hp.2.2 [] ⟨[], xs, rfl⟩ (by simp)
  simpa using this

theorem optimal_segment_zero_bound (xs p : List Int) (hp : SegmentOptimal 0 xs p) : p = [] := by
  have hb := hp.2.1
  exact List.eq_nil_iff_length_eq_zero.mpr (by omega)

theorem mss0_ne_nil (bound : Nat) (xs : List Int) : mss0 bound xs ≠ [] := by
  apply maxsWith_ne_nil
  intro he
  have hx := msp0_ne_nil bound xs
  have hh : msp0 bound xs = [] :=
    (List.flatMap_eq_nil_iff.mp he) xs (self_mem_tails xs)
  exact hx hh

end Segments
