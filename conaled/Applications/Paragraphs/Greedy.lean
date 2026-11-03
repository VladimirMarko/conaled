import Applications.Paragraphs.Candidates
import Mathlib.Order.Prod.Lex.Basic

/-! Actual greedy layout and its global lexicographic objective. -/
set_option autoImplicit false
set_option warningAsError true
namespace Paragraphs
open OrderedPartitions

/-- Literal filtered candidate expression for greedy: bind comes first. -/
def addCandidates (maximum : Nat) (p : Para) (w : Word) : List Para :=
  [bindRight w p, snocBlock w p].filter (lastOk (fits maximum))

/-- Actual source body, with a total head default only when its source domain fails. -/
def add (maximum : Nat) (p : Para) (w : Word) : Para :=
  match p with
  | [] => snocBlock w []
  | _ :: _ => (addCandidates maximum p w).headD []

def greedy (maximum : Nat) (ws : Text) : Para := ws.foldl (add maximum) []

/-- Every tested paragraph/last line and the selected head are source-defined. -/
def AddDomain (maximum : Nat) (p : Para) (w : Word) : Prop :=
  p ≠ [] →
    (∀ q ∈ [bindRight w p, snocBlock w p], q ≠ [] ∧ q.getLastD [] ≠ []) ∧
    addCandidates maximum p w ≠ [] ∧
    (addCandidates maximum p w).headD [] ≠ [] ∧
    ((addCandidates maximum p w).headD []).getLastD [] ≠ []

/-- Source-call obligations follow the actual intermediate accumulator states. -/
def FoldDomain (maximum : Nat) : Para → Text → Prop
  | _, [] => True
  | p, w :: ws => AddDomain maximum p w ∧ FoldDomain maximum (add maximum p w) ws

theorem addCandidates_ne_nil (maximum : Nat) (p : Para) (w : Word)
    (hw : w.length ≤ maximum) : addCandidates maximum p w ≠ [] := by
  apply List.ne_nil_of_mem (a := snocBlock w p)
  apply List.mem_filter.mpr
  refine ⟨by simp, ?_⟩
  simp [snocBlock, lastOk_append_singleton, fits, hw]

theorem addDomain_of_word_fits (maximum : Nat) (p : Para) (w : Word)
    (hw : w.length ≤ maximum) : AddDomain maximum p w := by
  intro _
  have tested : ∀ q ∈ [bindRight w p, snocBlock w p],
      q ≠ [] ∧ q.getLastD [] ≠ [] := by
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl <;> simp [bindRight, snocBlock]
  have hn := addCandidates_ne_nil maximum p w hw
  have hm : (addCandidates maximum p w).headD [] ∈ addCandidates maximum p w := by
    cases he : addCandidates maximum p w with
    | nil => exact False.elim (hn he)
    | cons q qs => simp
  have hh := tested _ (List.mem_filter.mp hm).1
  exact ⟨tested, hn, hh.1, hh.2⟩

theorem foldDomain_of_allWordsFit (maximum : Nat) (p : Para) (ws : Text)
    (hw : AllWordsFit maximum ws) : FoldDomain maximum p ws := by
  induction ws generalizing p with
  | nil => trivial
  | cons w ws ih =>
    exact ⟨addDomain_of_word_fits maximum p w (hw w (by simp)),
      ih _ (fun v hv => hw v (by simp [hv]))⟩

theorem greedy_source_domain (maximum : Nat) (ws : Text)
    (hw : AllWordsFit maximum ws) : FoldDomain maximum [] ws :=
  foldDomain_of_allWordsFit maximum [] ws hw

theorem add_head_fallback_irrelevant (maximum : Nat) (p : Para) (w : Word)
    (hp : p ≠ []) (hd : AddDomain maximum p w) (fallback : Para) :
    (addCandidates maximum p w).headD fallback = add maximum p w := by
  have hn := (hd hp).2.1
  cases p with
  | nil => exact False.elim (hp rfl)
  | cons line rest =>
    change (addCandidates maximum (line :: rest) w).headD fallback =
      (addCandidates maximum (line :: rest) w).headD []
    cases he : addCandidates maximum (line :: rest) w with
    | nil => exact False.elim (hn he)
    | cons q qs => rfl

@[simp] theorem add_nil (maximum : Nat) (w : Word) : add maximum [] w = [[w]] := rfl

@[simp] theorem greedy_nil (maximum : Nat) : greedy maximum [] = [] := rfl

theorem greedy_append_singleton (maximum : Nat) (ws : Text) (w : Word) :
    greedy maximum (ws ++ [w]) = add maximum (greedy maximum ws) w := by
  simp [greedy]

/-- Derived conditional equation; the executor above retains its filtered-head expression. -/
theorem add_append_last (maximum : Nat) (p : Para) (line : Line) (w : Word)
    (hw : w.length ≤ maximum) :
    add maximum (p ++ [line]) w =
      if fits maximum (line ++ [w]) then p ++ [line ++ [w]] else p ++ [line, [w]] := by
  have he : add maximum (p ++ [line]) w =
      (addCandidates maximum (p ++ [line]) w).headD [] := by cases p <;> rfl
  rw [he]
  simp only [addCandidates, bindRight_append_singleton, snocBlock]
  rw [List.filter_cons, lastOk_append_singleton, List.filter_cons, lastOk_append_singleton]
  have hs : fits maximum [w] = true := by simp [hw]
  rw [hs]
  cases hg : fits maximum (line ++ [w]) <;> simp [List.append_assoc]

theorem add_mem_fitExtend (maximum : Nat) (p : Para) (w : Word)
    (hw : w.length ≤ maximum) : add maximum p w ∈ fitExtend maximum w p := by
  induction p using snoc_induction with
  | nil => simp [fitExtend, extendRight, snocBlock, lastOk, fits, hw]
  | snoc p line _ =>
    rw [add_append_last maximum p line w hw]
    simp only [fitExtend, extendRight_append_singleton]
    have hs : lastOk (fits maximum) (p ++ [line, [w]]) = true := by
      have he := lastOk_append_singleton (fits maximum) (p ++ [line]) [w]
      simpa [List.append_assoc, hw] using he
    cases hg : fits maximum (line ++ [w]) with
    | false => simp [hg, hs, List.append_assoc]
    | true => simp [hg]

theorem greedy_fitPartition (maximum : Nat) (ws : Text) (hw : AllWordsFit maximum ws) :
    FitPartition maximum ws (greedy maximum ws) := by
  induction ws using snoc_induction with
  | nil => simp [FitPartition, IsPartition]
  | snoc ws w ih =>
    have hp := (allWordsFit_append maximum ws [w]).mp hw
    rw [greedy_append_singleton]
    exact fitExtend_preserves maximum ws _ _ w (ih hp.1)
      (add_mem_fitExtend maximum _ w (hp.2 w (by simp)))

theorem fitParts_nonempty (maximum : Nat) (ws : Text) (hw : AllWordsFit maximum ws) :
    fitParts maximum ws ≠ [] :=
  List.ne_nil_of_mem ((mem_fitParts maximum ws _).mpr (greedy_fitPartition maximum ws hw))

/-! ## Independent global line-count and last-width objectives -/

def cost1 (p : Para) : Nat := p.length

/-- Empty last-width zero is a total extension of the source last call. -/
def lastWidth (p : Para) : Nat := width (p.getLastD [])

def cost1Prime (p : Para) : Nat × Nat := (cost1 p, lastWidth p)

/-- Lexicographic order, not the componentwise product order. -/
def CostLE (p q : Para) : Prop :=
  cost1 p < cost1 q ∨ (cost1 p = cost1 q ∧ lastWidth p ≤ lastWidth q)

instance (p q : Para) : Decidable (CostLE p q) :=
  inferInstanceAs (Decidable (cost1 p < cost1 q ∨
    (cost1 p = cost1 q ∧ lastWidth p ≤ lastWidth q)))

def MinimumLines (maximum : Nat) (ws : Text) (p : Para) : Prop :=
  FitPartition maximum ws p ∧ ∀ q, FitPartition maximum ws q → cost1 p ≤ cost1 q

def MinimumLex (maximum : Nat) (ws : Text) (p : Para) : Prop :=
  FitPartition maximum ws p ∧ ∀ q, FitPartition maximum ws q → CostLE p q

theorem costLE_iff_pair (p q : Para) : CostLE p q ↔
    (cost1Prime p).1 < (cost1Prime q).1 ∨
      ((cost1Prime p).1 = (cost1Prime q).1 ∧ (cost1Prime p).2 ≤ (cost1Prime q).2) := Iff.rfl

/-- Standard lexicographic score; the ordinary pair order would be incorrect. -/
def lexCost (p : Para) : Nat ×ₗ Nat := toLex (cost1Prime p)

theorem costLE_iff_lex (p q : Para) : CostLE p q ↔ lexCost p ≤ lexCost q := by
  exact (Prod.Lex.toLex_le_toLex (x := cost1Prime p) (y := cost1Prime q)).symm

theorem costLE_refl (p : Para) : CostLE p p :=
  (costLE_iff_lex p p).mpr (le_refl _)

theorem costLE_trans (p q r : Para) (hpq : CostLE p q) (hqr : CostLE q r) :
    CostLE p r :=
  (costLE_iff_lex p r).mpr (le_trans ((costLE_iff_lex p q).mp hpq)
    ((costLE_iff_lex q r).mp hqr))

theorem costLE_count (p q : Para) (h : CostLE p q) : cost1 p ≤ cost1 q := by
  unfold CostLE at h
  omega

theorem costLE_last_of_count_eq (p q : Para) (h : CostLE p q) (he : cost1 p = cost1 q) :
    lastWidth p ≤ lastWidth q := by
  unfold CostLE at h
  omega

@[simp] theorem lastWidth_nil : lastWidth [] = 0 := rfl

@[simp] theorem lastWidth_append_singleton (p : Para) (line : Line) :
    lastWidth (p ++ [line]) = width line := by simp [lastWidth]

theorem add_cost_le_fitExtend (maximum : Nat) (p q : Para) (w : Word)
    (hw : w.length ≤ maximum) (hq : q ∈ fitExtend maximum w p) :
    CostLE (add maximum p w) q := by
  induction p using snoc_induction with
  | nil =>
    have he : q = [[w]] := by simpa [fitExtend, extendRight, snocBlock, lastOk, fits, hw] using hq
    subst q
    exact costLE_refl _
  | snoc p line _ =>
    have hm := (List.mem_filter.mp hq).1
    have hf := (List.mem_filter.mp hq).2
    rw [extendRight_append_singleton] at hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · rw [add_append_last maximum p line w hw]
      cases hg : fits maximum (line ++ [w]) with
      | false => simpa [List.append_assoc] using costLE_refl (p ++ [line, [w]])
      | true => exact Or.inl (by simp [cost1])
    · have hg : fits maximum (line ++ [w]) = true := by simpa using hf
      rw [add_append_last maximum p line w hw, hg]
      exact costLE_refl _

/-- The source monotonicity condition is contextual: both inputs partition the same text. -/
theorem add_cost_mono (maximum : Nat) (ws : Text) (p q : Para) (w : Word)
    (hp : IsPartition ws p) (hq : IsPartition ws q) (hw : w.length ≤ maximum)
    (hle : CostLE p q) : CostLE (add maximum p w) (add maximum q w) := by
  induction p using snoc_induction with
  | nil =>
    have he : ws = [] := hp.1.symm
    subst ws
    have hqn : q = [] := (partition_nil_iff q).mp hq
    subst q
    exact costLE_refl _
  | snoc p line _ =>
    induction q using snoc_induction with
    | nil =>
      have he : ws = [] := hq.1.symm
      subst ws
      have hn := (partition_nil_iff (p ++ [line])).mp hp
      simp at hn
    | snoc q last _ =>
      have hl : line ≠ [] := hp.2 line (by simp)
      have hk : last ≠ [] := hq.2 last (by simp)
      have hlw := width_append_singleton line w hl
      have hkw := width_append_singleton last w hk
      have hc : p.length + 1 < q.length + 1 ∨
          (p.length + 1 = q.length + 1 ∧ width line ≤ width last) := by
        simpa [CostLE, cost1] using hle
      rw [add_append_last maximum p line w hw, add_append_last maximum q last w hw]
      by_cases ha : width (line ++ [w]) ≤ maximum <;>
        by_cases hb : width (last ++ [w]) ≤ maximum <;>
        simp [fits, ha, hb, CostLE, cost1, lastWidth] <;> omega

/-- Proof-only predecessor enumeration ranges over every independently feasible competitor. -/
theorem greedy_cost_le (maximum : Nat) (ws : Text) (hw : AllWordsFit maximum ws)
    (q : Para) (hq : FitPartition maximum ws q) : CostLE (greedy maximum ws) q := by
  induction ws using snoc_induction generalizing q with
  | nil =>
    have hqn := (partition_nil_iff q).mp hq.1
    subst q
    exact costLE_refl _
  | snoc ws w ih =>
    have bounds := (allWordsFit_append maximum ws [w]).mp hw
    have hw' : w.length ≤ maximum := bounds.2 w (by simp)
    have hm := (mem_fitParts maximum (ws ++ [w]) q).mpr hq
    rw [fitParts_append_singleton] at hm
    obtain ⟨p, hp, hqp⟩ := List.mem_flatMap.mp hm
    have hpf := (mem_fitParts maximum ws p).mp hp
    have hgp := ih bounds.1 p hpf
    rw [greedy_append_singleton]
    exact costLE_trans _ (add maximum p w) _
      (add_cost_mono maximum ws _ p w (greedy_fitPartition maximum ws bounds.1).1
        hpf.1 hw' hgp)
      (add_cost_le_fitExtend maximum p q w hw' hqp)

theorem greedy_minimumLex (maximum : Nat) (ws : Text) (hw : AllWordsFit maximum ws) :
    MinimumLex maximum ws (greedy maximum ws) :=
  ⟨greedy_fitPartition maximum ws hw, greedy_cost_le maximum ws hw⟩

theorem greedy_minimumLines (maximum : Nat) (ws : Text) (hw : AllWordsFit maximum ws) :
    MinimumLines maximum ws (greedy maximum ws) :=
  ⟨greedy_fitPartition maximum ws hw,
    fun q hq => costLE_count _ q (greedy_cost_le maximum ws hw q hq)⟩

theorem greedy_minimumLastWidth (maximum : Nat) (ws : Text) (hw : AllWordsFit maximum ws)
    (q : Para) (hq : FitPartition maximum ws q)
    (hc : cost1 (greedy maximum ws) = cost1 q) :
    lastWidth (greedy maximum ws) ≤ lastWidth q :=
  costLE_last_of_count_eq _ q (greedy_cost_le maximum ws hw q hq) hc


end Paragraphs
