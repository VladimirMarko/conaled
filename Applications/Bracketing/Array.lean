import Applications.Bracketing.TableSupport
import Applications.Bracketing.Selection

set_option autoImplicit false
set_option warningAsError true

/-! Exercise14.3: the actual cached all-cut array for a generalized child-cost
combiner h. The second cached field is leaf count. Exact source cut order and
recursive first ties are retained. Every finite valid cell refines the cached
recursion and its equations have a unique solution. Coordinatewise monotone h
then gives an independent all-tree optimum; associativity of h is not required.
-/
namespace Bracketing.Array

open Bracketing (Tree fringeSpec)
open Bracketing
open Cached
open Bracketing (interval interval_length interval_nonempty interval_singleton interval_whole)
open Bracketing (cellIndex cellIndex_lt cellIndex_injective option_mapM_of_map option_mapM_congr)

variable {α : Type} (hcost : Nat → Nat → Nat) (fcost : Nat → Nat → Nat)

theorem interval_splitsn (ws : List α) (i j : Nat) (hij : i ≤ j)
    (hj : j < ws.length) :
    Bracketing.splitsn (interval ws i j) = (List.range (j-i)).map
      (fun r => (interval ws i (i+r), interval ws (i+r+1) j)) := by
  rw [Bracketing.splitsn_eq_cuts, interval_length ws i j hij hj,
    show j+1-i-1=j-i by omega]
  apply List.map_congr_left
  intro r hr
  have hr' := List.mem_range.mp hr
  have htake := Bracketing.interval_take_cut ws i j (i+r) (by omega) (by omega)
  have hdrop := Bracketing.interval_drop_cut ws i j (i+r) (by omega)
  rw [show i+r+1-i=r+1 by omega] at htake hdrop
  rw [htake,hdrop]

def tableRead (n : Nat) (a : Array (Option (Triple α))) (i j : Nat) : Option (Triple α) :=
  if i < n ∧ j < n then (a[cellIndex n i j]?).join else none
theorem tableRead_in_bounds (n : Nat) (a : Array (Option (Triple α))) (i j : Nat)
    (hi : i < n) (hj : j < n) :
    tableRead n a i j = (a[cellIndex n i j]?).join := by
  simp only [tableRead, hi, hj, and_self, ite_true]
theorem tableRead_outside (n : Nat) (a : Array (Option (Triple α))) (i j : Nat)
    (h : ¬ (i < n ∧ j < n)) : tableRead n a i j = none := by
  simp only [tableRead, h, ite_false]
def minimumTriple (xs : List (Triple α)) : Option (Triple α) :=
  Optimization.Thinning.argmin costT xs

theorem minimumTriple_nonempty (xs : List (Triple α)) (hn : xs ≠ []) :
    minimumTriple xs = some (Bracketing.sourceMinWith costT xs hn) :=
  argmin_eq_sourceMinWith costT xs hn

def tableFork (n : Nat) (old : Array (Option (Triple α))) (i j r : Nat) : Option (Triple α) := do
  let left ← tableRead n old i (i + r)
  let right ← tableRead n old (i + r + 1) j
  pure (forkT hcost fcost left right)
def tableCandidates (n : Nat) (old : Array (Option (Triple α))) (i j : Nat) :
    Option (List (Triple α)) := (List.range (j - i)).mapM (tableFork hcost fcost n old i j)
def tableCell (weights : Array α) (old : Array (Option (Triple α))) (i j : Nat) :
    Option (Triple α) :=
  if i < weights.size ∧ j < weights.size then
    if i = j then do
      let w ← weights[i]?
      pure (0, 1, Tree.leaf w)
    else if i < j then do
      let candidates ← tableCandidates hcost fcost weights.size old i j
      minimumTriple candidates
    else none
  else none
def diagonalAssociations (weights : Array α) (old : Array (Option (Triple α)))
    (width : Nat) : List (Nat × Option (Triple α)) :=
  (List.range (weights.size - width)).map (fun i =>
    (cellIndex weights.size i (i + width), tableCell hcost fcost weights old i (i + width)))
def diagonalStep (weights : Array α) (old : Array (Option (Triple α))) (width : Nat) :
    Array (Option (Triple α)) :=
  DynamicProgramming.arrayAssign old (diagonalAssociations hcost fcost weights old width)
def emptyTable (n : Nat) : Array (Option (Triple α)) := (List.replicate (n * n) none).toArray
def buildTable (hcost : Nat → Nat → Nat) (fcost : Nat → Nat → Nat) (weights : Array α) : Nat → Array (Option (Triple α))
  | 0 => emptyTable weights.size
  | width + 1 => diagonalStep hcost fcost weights (buildTable hcost fcost weights width) width
def fullTable (ws : List α) : Array (Option (Triple α)) :=
  buildTable hcost fcost ws.toArray ws.length
def mct3Tuple (ws : List α) : Option (Triple α) :=
  tableCell hcost fcost ws.toArray (fullTable hcost fcost ws) 0 (ws.length - 1)
def mct3Option (ws : List α) : Option (Tree α) := (mct3Tuple hcost fcost ws).map treeT
theorem triple_domain_congr (xs ys : List α) (hx : xs ≠ []) (hy : ys ≠ [])
    (he : xs = ys) :
    triple hcost fcost xs hx = triple hcost fcost ys hy := by
  cases he
  rfl
def referenceCell (ws : List α) (i j : Nat) : Option (Triple α) :=
  if h : i ≤ j ∧ j < ws.length then
    some (triple hcost fcost (interval ws i j) (interval_nonempty ws i j h.1 h.2))
  else none
theorem referenceCell_valid (ws : List α) (i j : Nat)
    (hij : i ≤ j) (hj : j < ws.length) :
    referenceCell hcost fcost ws i j = some (triple hcost fcost (interval ws i j)
      (interval_nonempty ws i j hij hj) ) := by
  simp only [referenceCell, dite_eq_left (show i ≤ j ∧ j < ws.length from ⟨hij, hj⟩)]
theorem referenceCell_invalid (ws : List α) (i j : Nat)
    (h : ¬ (i ≤ j ∧ j < ws.length)) : referenceCell hcost fcost ws i j = none := by
  simp only [referenceCell, dite_eq_right h]
theorem referenceCell_diagonal (ws : List α) (i : Nat)
    (hi : i < ws.length) : referenceCell hcost fcost ws i i = some (0, 1, Tree.leaf ws[i]) := by
  rw [referenceCell_valid hcost fcost ws i i (by omega) hi]
  apply congrArg some
  exact (triple_domain_congr hcost fcost _ _ _ (List.cons_ne_nil _ _)
    (interval_singleton ws i hi)).trans (triple_singleton hcost fcost _ _)

noncomputable def referenceSplit (ws : List α) 
    (p : List α × List α) : Option (Triple α) := by
  classical
  exact if hs : p ∈ Bracketing.splitsn ws then
    some (forkT hcost fcost
      (triple hcost fcost p.1 ((Bracketing.mem_splitsn_iff _ _ _).mp hs).1)
      (triple hcost fcost p.2 ((Bracketing.mem_splitsn_iff _ _ _).mp hs).2.1))
  else none
theorem referenceSplit_of_mem (ws us vs : List α)
    (hs : (us, vs) ∈ Bracketing.splitsn ws) :
    referenceSplit hcost fcost ws (us, vs) = some (forkT hcost fcost
      (triple hcost fcost us ((Bracketing.mem_splitsn_iff _ _ _).mp hs).1)
      (triple hcost fcost vs ((Bracketing.mem_splitsn_iff _ _ _).mp hs).2.1)) := by
  simp only [referenceSplit, dite_eq_left hs]

theorem referenceSplit_map (ws : List α) :
    (Bracketing.splitsn ws).map (referenceSplit hcost fcost ws) =
      (tripleCandidates hcost fcost ws).map some := by
  rw [← List.attach_map_val]
  simp only [tripleCandidates, List.map_map]
  apply List.map_congr_left
  intro p _
  simp only [referenceSplit, dite_eq_left p.property, Function.comp_def]
theorem tableCell_diagonal (ws : List α) (old : Array (Option (Triple α)))
    (i : Nat) (hi : i < ws.length) :
    tableCell hcost fcost ws.toArray old i i = some (0, 1, Tree.leaf ws[i]) := by
  simp [tableCell, hi]
theorem tableCell_lower (weights : Array α) (old : Array (Option (Triple α)))
    (i j : Nat) (h : j < i) : tableCell hcost fcost weights old i j = none := by
  simp only [tableCell, show i ≠ j by omega, ite_false, show ¬ i < j by omega]
  split <;> rfl
theorem tableCell_outside (weights : Array α) (old : Array (Option (Triple α)))
    (i j : Nat) (h : ¬ (i < weights.size ∧ j < weights.size)) :
    tableCell hcost fcost weights old i j = none := by
  simp only [tableCell, h, ite_false]
theorem tableFork_eq_referenceSplit (ws : List α) 
    (old : Array (Option (Triple α))) (i j r : Nat) (hij : i < j) (hj : j < ws.length)
    (hr : r < j - i)
    (hl : tableRead ws.length old i (i + r) = referenceCell hcost fcost ws i (i + r))
    (hh : tableRead ws.length old (i + r + 1) j = referenceCell hcost fcost ws (i + r + 1) j) :
    tableFork hcost fcost ws.length old i j r = referenceSplit hcost fcost (interval ws i j)
       (interval ws i (i + r), interval ws (i + r + 1) j) := by
  have hs : (interval ws i (i + r), interval ws (i + r + 1) j) ∈
      Bracketing.splitsn (interval ws i j) := by
    rw [interval_splitsn ws i j (by omega) hj]
    exact List.mem_map.mpr ⟨r, List.mem_range.mpr hr, rfl⟩
  rw [referenceSplit_of_mem hcost fcost _ _ _ hs]
  simp only [tableFork, hl, hh,
    referenceCell_valid hcost fcost ws i (i + r) (by omega) (by omega),
    referenceCell_valid hcost fcost ws (i + r + 1) j (by omega) hj]
  rfl
theorem tableCandidates_eq_reference (ws : List α) 
    (old : Array (Option (Triple α))) (i j : Nat) (hij : i < j) (hj : j < ws.length)
    (hr : ∀ r < j - i,
      tableRead ws.length old i (i + r) = referenceCell hcost fcost ws i (i + r) ∧
      tableRead ws.length old (i + r + 1) j = referenceCell hcost fcost ws (i + r + 1) j) :
    tableCandidates hcost fcost ws.length old i j =
      some (tripleCandidates hcost fcost (interval ws i j) ) := by
  apply option_mapM_of_map
  rw [← referenceSplit_map hcost fcost, interval_splitsn ws i j (by omega) hj, List.map_map]
  apply List.map_congr_left
  intro r hm
  have hb := List.mem_range.mp hm
  exact tableFork_eq_referenceSplit hcost fcost ws old i j r hij hj hb (hr r hb).1 (hr r hb).2
theorem tableCell_eq_reference (ws : List α) 
    (old : Array (Option (Triple α))) (i j : Nat) (hij : i ≤ j) (hj : j < ws.length)
    (hr : ∀ r < j - i,
      tableRead ws.length old i (i + r) = referenceCell hcost fcost ws i (i + r) ∧
      tableRead ws.length old (i + r + 1) j = referenceCell hcost fcost ws (i + r + 1) j) :
    tableCell hcost fcost ws.toArray old i j = referenceCell hcost fcost ws i j := by
  by_cases he : i = j
  · subst j
    rw [tableCell_diagonal hcost fcost ws old i hj, referenceCell_diagonal hcost fcost ws i hj]
  · have hlt : i < j := by omega
    have hl : 2 ≤ (interval ws i j).length := by
      rw [interval_length ws i j hij hj]
      omega
    simp only [tableCell, List.size_toArray, show i < ws.length by omega, hj, and_self,
      ite_true, he, ite_false, hlt]
    rw [tableCandidates_eq_reference hcost fcost ws old i j hlt hj hr]
    change minimumTriple (tripleCandidates hcost fcost (interval ws i j) ) = _
    rw [minimumTriple_nonempty _ (tripleCandidates_ne_nil hcost fcost _ hl),
      referenceCell_valid hcost fcost ws i j hij hj, triple_long hcost fcost _ _ hl]
theorem diagonalAssociations_length (weights : Array α) (old : Array (Option (Triple α)))
    (width : Nat) : (diagonalAssociations hcost fcost weights old width).length = weights.size - width := by
  simp only [diagonalAssociations, List.length_map, List.length_range]
theorem diagonalAssociations_keys_nodup (weights : Array α)
    (old : Array (Option (Triple α))) (width : Nat) :
    ((diagonalAssociations hcost fcost weights old width).map Prod.fst).Nodup := by
  simp only [diagonalAssociations, List.map_map]
  apply List.pairwise_map.mpr
  apply (show (List.range (weights.size - width)).Nodup from List.nodup_range).imp_of_mem
  intro a b ha hb hab he
  have ha' := List.mem_range.mp ha
  have hb' := List.mem_range.mp hb
  exact hab (cellIndex_injective weights.size a (a + width) b (b + width)
    (by omega) (by omega) he).1
theorem diagonalAssociations_bounds (weights : Array α)
    (old : Array (Option (Triple α))) (width : Nat) (p : Nat × Option (Triple α))
    (hp : p ∈ diagonalAssociations hcost fcost weights old width) : p.1 < weights.size * weights.size := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
  have h := List.mem_range.mp hi
  exact cellIndex_lt weights.size i (i + width) (by omega) (by omega)
theorem diagonalStep_batch (weights : Array α) (old : Array (Option (Triple α)))
    (width : Nat) (hs : old.size = weights.size * weights.size) :
    DynamicProgramming.ArrayBatch old (diagonalStep hcost fcost weights old width)
      (diagonalAssociations hcost fcost weights old width) := by
  apply DynamicProgramming.arrayAssign_batch
  · exact diagonalAssociations_keys_nodup hcost fcost weights old width
  · intro p hp
    rw [hs]
    exact diagonalAssociations_bounds hcost fcost weights old width p hp
theorem diagonalStep_size (weights : Array α) (old : Array (Option (Triple α)))
    (width : Nat) : (diagonalStep hcost fcost weights old width).size = old.size :=
  DynamicProgramming.arrayAssign_size old _
theorem tableRead_diagonalStep (weights : Array α) (old : Array (Option (Triple α)))
    (width i j : Nat) (hs : old.size = weights.size * weights.size)
    (hi : i < weights.size) (hj : j < weights.size) :
    tableRead weights.size (diagonalStep hcost fcost weights old width) i j =
      if j = i + width then tableCell hcost fcost weights old i j else tableRead weights.size old i j := by
  rw [tableRead_in_bounds _ _ _ _ hi hj]
  have hb := diagonalStep_batch hcost fcost weights old width hs
  by_cases he : j = i + width
  · rw [ite_eq_left he]
    have hm : (cellIndex weights.size i j, tableCell hcost fcost weights old i j) ∈
        diagonalAssociations hcost fcost weights old width := by
      apply List.mem_map.mpr
      refine ⟨i, List.mem_range.mpr (by omega), ?_⟩
      simp only [he]
    rw [hb.2.1 _ _ hm]
    rfl
  · rw [ite_eq_right he, hb.2.2 _ (by
      intro p hp hidx
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp
      have hr' := List.mem_range.mp hr
      have hsame := cellIndex_injective weights.size r (r + width) i j
        (by omega) hj hidx
      exact he (by omega))]
    exact (tableRead_in_bounds _ _ _ _ hi hj).symm
theorem emptyTable_size (n : Nat) : (emptyTable (α := α) n).size = n * n := by
  simp only [emptyTable, List.size_toArray, List.length_replicate]
theorem emptyTable_read (n i j : Nat) : tableRead n (emptyTable (α := α) n) i j = none := by
  by_cases hb : i < n ∧ j < n
  · rw [tableRead_in_bounds _ _ _ _ hb.1 hb.2]
    simp only [emptyTable, List.getElem?_toArray,
      List.getElem?_replicate_of_lt (cellIndex_lt n i j hb.1 hb.2)]
    rfl
  · exact tableRead_outside _ _ _ _ hb
def SolvedThrough (ws : List α) (width : Nat)
    (a : Array (Option (Triple α))) : Prop :=
  a.size = ws.length * ws.length ∧ ∀ i j, i < ws.length → j < ws.length →
    tableRead ws.length a i j =
      if i ≤ j ∧ j - i < width then referenceCell hcost fcost ws i j else none
theorem emptyTable_solved (ws : List α) :
    SolvedThrough hcost fcost ws 0 (emptyTable ws.length) := by
  refine ⟨emptyTable_size _, ?_⟩
  intro i j _ _
  simp only [emptyTable_read, Nat.not_lt_zero, and_false, ite_false]
theorem SolvedThrough.read (ws : List α) (width : Nat)
    (a : Array (Option (Triple α))) (hs : SolvedThrough hcost fcost ws width a) (i j : Nat)
    (hij : i ≤ j) (hj : j < ws.length) (hw : j - i < width) :
    tableRead ws.length a i j = referenceCell hcost fcost ws i j := by
  rw [hs.2 i j (by omega) hj, ite_eq_left ⟨hij, hw⟩]
theorem diagonalStep_solved (ws : List α) (width : Nat)
    (old : Array (Option (Triple α))) (hs : SolvedThrough hcost fcost ws width old) :
    SolvedThrough hcost fcost ws (width + 1) (diagonalStep hcost fcost ws.toArray old width) := by
  refine ⟨(diagonalStep_size hcost fcost _ _ _).trans hs.1, ?_⟩
  intro i j hi hj
  have hd := tableRead_diagonalStep hcost fcost ws.toArray old width i j
    (by simpa only [List.size_toArray] using hs.1)
    (by simpa only [List.size_toArray] using hi) (by simpa only [List.size_toArray] using hj)
  simp only [List.size_toArray] at hd
  rw [hd]
  by_cases he : j = i + width
  · rw [ite_eq_left he, ite_eq_left (show i ≤ j ∧ j - i < width + 1 by omega)]
    apply tableCell_eq_reference hcost fcost ws old i j (by omega) hj
    intro r hr
    constructor
    · exact SolvedThrough.read hcost fcost ws width old hs i (i + r) (by omega) (by omega) (by omega)
    · exact SolvedThrough.read hcost fcost ws width old hs (i + r + 1) j (by omega) hj (by omega)
  · rw [ite_eq_right he, hs.2 i j hi hj]
    have hh : (i ≤ j ∧ j - i < width) ↔ (i ≤ j ∧ j - i < width + 1) := by omega
    simp only [hh]
theorem buildTable_solved (ws : List α) (width : Nat) :
    SolvedThrough hcost fcost ws width (buildTable hcost fcost ws.toArray width) := by
  induction width with
  | zero => exact emptyTable_solved hcost fcost ws
  | succ width ih => exact diagonalStep_solved hcost fcost ws width _ ih
theorem fullTable_solved (ws : List α) :
    SolvedThrough hcost fcost ws ws.length (fullTable hcost fcost ws) := buildTable_solved hcost fcost ws ws.length
theorem fullTable_size (ws : List α) :
    (fullTable hcost fcost ws).size = ws.length * ws.length := by
  have aux : ∀ width, (buildTable hcost fcost ws.toArray width).size = ws.length * ws.length := by
    intro width
    induction width with
    | zero => exact emptyTable_size _
    | succ width ih => exact (diagonalStep_size hcost fcost _ _ width).trans ih
  exact aux ws.length
theorem fullTable_read (ws : List α) (i j : Nat)
    (hij : i ≤ j) (hj : j < ws.length) :
    tableRead ws.length (fullTable hcost fcost ws) i j = referenceCell hcost fcost ws i j :=
  SolvedThrough.read hcost fcost ws ws.length _ (fullTable_solved hcost fcost ws) i j hij hj (by omega)
theorem fullTable_lower (ws : List α) (i j : Nat)
    (hi : i < ws.length) (hji : j < i) :
    tableRead ws.length (fullTable hcost fcost ws) i j = none := by
  rw [(fullTable_solved hcost fcost ws).2 i j hi (by omega)]
  simp only [show ¬ i ≤ j by omega, false_and, ite_false]
theorem tableCell_congr (weights : Array α) (a b : Array (Option (Triple α)))
    (i j : Nat) (hr : ∀ r < j - i,
      tableRead weights.size a i (i + r) = tableRead weights.size b i (i + r) ∧
      tableRead weights.size a (i + r + 1) j = tableRead weights.size b (i + r + 1) j) :
    tableCell hcost fcost weights a i j = tableCell hcost fcost weights b i j := by
  have he : tableCandidates hcost fcost weights.size a i j = tableCandidates hcost fcost weights.size b i j := by
    apply option_mapM_congr
    intro r hm
    have h := hr r (List.mem_range.mp hm)
    simp only [tableFork, h.1, h.2]
  simp only [tableCell, he]
def SourceTableEquations (ws : List α) (a : Array (Option (Triple α))) : Prop :=
  ∀ i j, i ≤ j → j < ws.length →
    tableRead ws.length a i j = tableCell hcost fcost ws.toArray a i j
theorem fullTable_sourceEquations (ws : List α) :
    SourceTableEquations hcost fcost ws (fullTable hcost fcost ws) := by
  intro i j hij hj
  rw [fullTable_read hcost fcost ws i j hij hj]
  symm
  apply tableCell_eq_reference hcost fcost ws _ i j hij hj
  intro r hr
  exact ⟨fullTable_read hcost fcost ws i (i + r) (by omega) (by omega),
    fullTable_read hcost fcost ws (i + r + 1) j (by omega) hj⟩
theorem sourceTableEquations_unique (ws : List α) (a b : Array (Option (Triple α)))
    (ha : SourceTableEquations hcost fcost ws a) (hb : SourceTableEquations hcost fcost ws b)
    (i j : Nat) (hij : i ≤ j) (hj : j < ws.length) :
    tableRead ws.length a i j = tableRead ws.length b i j := by
  have aux : ∀ d, ∀ p q, q - p = d → p ≤ q → q < ws.length →
      tableRead ws.length a p q = tableRead ws.length b p q := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro p q hd hpq hq
      rw [ha p q hpq hq, hb p q hpq hq]
      apply tableCell_congr hcost fcost
      intro r hr
      simp only [List.size_toArray]
      constructor
      · exact ih r (by omega) p (p + r) (by omega) (by omega) (by omega)
      · exact ih (q - (p + r + 1)) (by omega) (p + r + 1) q rfl (by omega) hq
  exact aux (j - i) i j rfl hij hj
theorem fullTable_unique_solution (ws : List α) :
    SourceTableEquations hcost fcost ws (fullTable hcost fcost ws) ∧
      ∀ a, SourceTableEquations hcost fcost ws a → ∀ i j, i ≤ j → j < ws.length →
        tableRead ws.length a i j = tableRead ws.length (fullTable hcost fcost ws) i j := by
  refine ⟨fullTable_sourceEquations hcost fcost ws, ?_⟩
  intro a ha i j hij hj
  exact sourceTableEquations_unique hcost fcost ws a _ ha (fullTable_sourceEquations hcost fcost ws) i j hij hj
theorem mct3Tuple_eq_triple (ws : List α) (hn : ws ≠ []) :
    mct3Tuple hcost fcost ws = some (triple hcost fcost ws hn) := by
  have hp : 0 < ws.length := List.length_pos_iff.mpr hn
  rw [mct3Tuple, tableCell_eq_reference hcost fcost ws _ 0 (ws.length - 1) (by omega) (by omega) (by
    intro r hr
    exact ⟨fullTable_read hcost fcost ws 0 (0+r) (by omega) (by omega),
      fullTable_read hcost fcost ws (0+r+1) (ws.length-1) (by omega) (by omega)⟩),
    referenceCell_valid hcost fcost ws 0 (ws.length-1) (by omega) (by omega)]
  exact congrArg some (triple_domain_congr hcost fcost _ ws _ hn (interval_whole ws hn))

theorem mct3Tuple_eq_root_read (ws : List α) (hn : ws ≠ []) :
    mct3Tuple hcost fcost ws = tableRead ws.length (fullTable hcost fcost ws) 0 (ws.length-1) := by
  have hp : 0 < ws.length := List.length_pos_iff.mpr hn
  exact (fullTable_sourceEquations hcost fcost ws 0 (ws.length-1) (by omega) (by omega)).symm

theorem mct3Option_eq_some_mct2 (ws : List α) (hn : ws ≠ []) :
    mct3Option hcost fcost ws = some (mct2 hcost fcost ws hn) := by
  simp only [mct3Option, mct3Tuple_eq_triple hcost fcost ws hn, Option.map_some, mct2]

def mct3 (ws : List α) (hn : ws ≠ []) : Tree α :=
  (mct3Option hcost fcost ws).get (by rw [mct3Option_eq_some_mct2 hcost fcost ws hn]; rfl)

theorem mct3_eq_mct2 (ws : List α) (hn : ws ≠ []) : mct3 hcost fcost ws hn = mct2 hcost fcost ws hn :=
  Option.get_of_eq_some _ (mct3Option_eq_some_mct2 hcost fcost ws hn)

theorem mct3_eq_mct (ws : List α) (hn : ws ≠ []) : mct3 hcost fcost ws hn = Recursive.mctH hcost fcost ws hn :=
  (mct3_eq_mct2 hcost fcost ws hn).trans (mct2_eq_mct hcost fcost ws hn)

theorem mct3_fringe (ws : List α) (hn : ws ≠ []) : fringeSpec (mct3 hcost fcost ws hn) = ws := by
  rw [mct3_eq_mct2]
  exact mct2_fringe hcost fcost ws hn

theorem mct3_minimum (ha : Recursive.Monotone2 hcost)
    (ws : List α) (hn : ws ≠ []) : Recursive.MinimumH hcost fcost ws (mct3 hcost fcost ws hn) := by
  rw [mct3_eq_mct2]
  exact mct2_minimum hcost fcost ha ws hn

theorem mct3Option_nil : mct3Option hcost fcost ([] : List α) = none := rfl

theorem fullTable_entry_minimum (ha : Recursive.Monotone2 hcost)
    (ws : List α) (i j : Nat) (hij : i ≤ j) (hj : j < ws.length) (v : Triple α)
    (hv : tableRead ws.length (fullTable hcost fcost ws) i j = some v) :
    Recursive.MinimumH hcost fcost (interval ws i j) (treeT v) := by
  rw [fullTable_read hcost fcost ws i j hij hj, referenceCell_valid hcost fcost ws i j hij hj] at hv
  cases Option.some.inj hv
  exact mct2_minimum hcost fcost ha _ _

theorem fullTable_entry_cached (ws : List α) (i j : Nat) (hij : i ≤ j)
    (hj : j < ws.length) (v : Triple α)
    (hv : tableRead ws.length (fullTable hcost fcost ws) i j = some v) : Cached hcost fcost v := by
  rw [fullTable_read hcost fcost ws i j hij hj, referenceCell_valid hcost fcost ws i j hij hj] at hv
  cases Option.some.inj hv
  exact triple_cached hcost fcost _ _

theorem fullTable_candidates (ws : List α) (i j : Nat) (hij : i < j) (hj : j < ws.length) :
    tableCandidates hcost fcost ws.length (fullTable hcost fcost ws) i j =
      some (tripleCandidates hcost fcost (interval ws i j)) := by
  apply tableCandidates_eq_reference hcost fcost ws _ i j hij hj
  intro r hr
  exact ⟨fullTable_read hcost fcost ws i (i+r) (by omega) (by omega),
    fullTable_read hcost fcost ws (i+r+1) j (by omega) hj⟩

end Bracketing.Array
