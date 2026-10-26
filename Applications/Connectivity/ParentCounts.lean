import Applications.Connectivity.ParentHistory

set_option autoImplicit false
set_option warningAsError true

/-! Concrete ParentCounts proofs adapted from adwh-checkpoint-233.
Source members and declaration dispositions: docs/research/adwh-connectivity-provenance.tsv.
Operations retain the source failure and representative-selection behavior. -/

namespace Connectivity.ParentCounts

open ParentArray ParentForest ParentComponents
open ParentUnion ParentHistory

def roots (ds : DSA) : List Int :=
  (vertexUniverse ds).filter (fun r => decide (readCell ds.namesA r = some r))

def rootCount (ds : DSA) : Nat := (roots ds).length

theorem mem_roots_iff (ds : DSA) (r : Int) :
    r ∈ roots ds ↔ Valid ds r ∧ SelfRoot ds r := by
  simp [roots, mem_vertexUniverse, SelfRoot]

theorem roots_nodup (ds : DSA) : (roots ds).Nodup :=
  List.Pairwise.filter _ (vertexUniverse_nodup ds)

theorem roots_sublist_universe (ds : DSA) : List.Sublist (roots ds) (vertexUniverse ds) :=
  List.filter_sublist

theorem rootCount_le_capacity (ds : DSA) : rootCount ds ≤ capacity ds := by
  have bound := (roots_sublist_universe ds).length_le
  simpa only [vertexUniverse_length, rootCount] using bound

theorem roots_startDSA (n : Int) :
    roots (startDSA n) = vertexUniverse (startDSA n) := by
  apply List.filter_eq_self.mpr
  intro r hr
  have hv := (valid_startDSA_iff n r).mp ((mem_vertexUniverse _ r).mp hr)
  simpa only [decide_eq_true_eq] using startDSA_parent n r hv.1 hv.2

theorem rootCount_startDSA (n : Int) : rootCount (startDSA n) = n.toNat := by
  rw [rootCount, roots_startDSA, vertexUniverse_length]
  exact (startDSA_sizes n).1

theorem union_loser_mem_roots {ds : DSA} {n1 n2 : Int}
    (h1 : SelfRoot ds n1) (h2 : SelfRoot ds n2) : loser ds n1 n2 ∈ roots ds := by
  by_cases hlt : cache ds n1 < cache ds n2
  · simp only [loser, ite_eq_left hlt]
    exact (mem_roots_iff ds n1).mpr ⟨valid_of_parent_read h1, h1⟩
  · simp only [loser, ite_eq_right hlt]
    exact (mem_roots_iff ds n2).mpr ⟨valid_of_parent_read h2, h2⟩

theorem union_winner_mem_roots {ds : DSA} {n1 n2 : Int}
    (h1 : SelfRoot ds n1) (h2 : SelfRoot ds n2) : winner ds n1 n2 ∈ roots ds := by
  by_cases hlt : cache ds n1 < cache ds n2
  · simp only [winner, ite_eq_left hlt]
    exact (mem_roots_iff ds n2).mpr ⟨valid_of_parent_read h2, h2⟩
  · simp only [winner, ite_eq_right hlt]
    exact (mem_roots_iff ds n1).mpr ⟨valid_of_parent_read h1, h1⟩

theorem roots_union {ds out : DSA} {n1 n2 : Int}
    (hF : Forest ds) (h1 : SelfRoot ds n1) (h2 : SelfRoot ds n2) (hne : n1 ≠ n2)
    (hu : unionDSA n1 n2 ds = some out) :
    roots out = (roots ds).filter (fun r => decide (r ≠ loser ds n1 n2)) := by
  have sameUniverse : vertexUniverse out = vertexUniverse ds := by
    simp only [vertexUniverse, union_capacity hu]
  unfold roots
  rw [sameUniverse, List.filter_filter]
  apply List.filter_congr
  intro r _
  have effect := union_selfRoot hF h1 h2 hne hu r
  apply Bool.eq_iff_iff.mpr
  simpa only [Bool.and_eq_true, decide_eq_true_eq, SelfRoot, and_comm] using effect

theorem roots_union_of_lt {ds out : DSA} {n1 n2 : Int}
    (hF : Forest ds) (h1 : SelfRoot ds n1) (h2 : SelfRoot ds n2) (hne : n1 ≠ n2)
    (hu : unionDSA n1 n2 ds = some out) (hlt : cache ds n1 < cache ds n2) :
    roots out = (roots ds).filter (fun r => decide (r ≠ n1)) := by
  simpa only [loser, ite_eq_left hlt] using roots_union hF h1 h2 hne hu

theorem roots_union_of_not_lt {ds out : DSA} {n1 n2 : Int}
    (hF : Forest ds) (h1 : SelfRoot ds n1) (h2 : SelfRoot ds n2) (hne : n1 ≠ n2)
    (hu : unionDSA n1 n2 ds = some out) (hlt : ¬ cache ds n1 < cache ds n2) :
    roots out = (roots ds).filter (fun r => decide (r ≠ n2)) := by
  simpa only [loser, ite_eq_right hlt] using roots_union hF h1 h2 hne hu

private theorem length_filter_ne_add_one {xs : List Int} {a : Int}
    (hn : xs.Nodup) (ha : a ∈ xs) :
    (xs.filter (fun r => decide (r ≠ a))).length + 1 = xs.length := by
  induction xs with
  | nil => simp at ha
  | cons b rest ih =>
      obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hn
      by_cases hba : b = a
      · subst b
        have same : rest.filter (fun r => decide (r ≠ a)) = rest := by
          apply List.filter_eq_self.mpr
          intro r hr
          simp only [decide_eq_true_eq]
          intro he
          subst r
          exact hnot hr
        rw [List.filter_cons_of_neg (by simp), same]
        rfl
      · have member : a ∈ rest := (List.mem_cons.mp ha).resolve_left (Ne.symm hba)
        have smaller := ih htail member
        rw [List.filter_cons_of_pos (by simpa using hba)]
        simp only [List.length_cons]
        omega

theorem rootCount_union {ds out : DSA} {n1 n2 : Int}
    (hF : Forest ds) (h1 : SelfRoot ds n1) (h2 : SelfRoot ds n2) (hne : n1 ≠ n2)
    (hu : unionDSA n1 n2 ds = some out) : rootCount out + 1 = rootCount ds := by
  unfold rootCount
  rw [roots_union hF h1 h2 hne hu]
  exact length_filter_ne_add_one (roots_nodup ds) (union_loser_mem_roots h1 h2)

theorem roots_nonempty {ds : DSA} (hF : Forest ds) (hpos : 0 < capacity ds) :
    roots ds ≠ [] := by
  have valid : Valid ds 1 := by
    constructor
    · omega
    · change (1 : Nat) ≤ capacity ds
      omega
  obtain ⟨r, hr⟩ := hF.valid_root_exists valid
  exact List.ne_nil_of_mem ((mem_roots_iff ds r).mpr ⟨hr.valid_root, hr.selfRoot⟩)

theorem rootCount_positive {ds : DSA} (hF : Forest ds) (hpos : 0 < capacity ds) :
    0 < rootCount ds := by
  exact List.length_pos_iff.mpr (roots_nonempty hF hpos)

theorem requestHistory_rootCount {n : Int} {requests : List (Int × Int)} {ds : DSA}
    (h : RequestHistory n requests ds) : rootCount ds + requests.length = n.toNat := by
  induction h with
  | start => simp [rootCount_startDSA]
  | @snoc prior old out u v before step ih =>
      obtain ⟨a, b, ha, hb, hne, hu⟩ := step
      have forest := requestHistory_forest before
      have h1 := ((forest.findDSA_iff_Root u a).mp ha).selfRoot
      have h2 := ((forest.findDSA_iff_Root v b).mp hb).selfRoot
      have change := rootCount_union forest h1 h2 hne hu
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega

theorem requestHistory_length_le {n : Int} {requests : List (Int × Int)} {ds : DSA}
    (h : RequestHistory n requests ds) : requests.length ≤ n.toNat := by
  have conserved := requestHistory_rootCount h
  omega

theorem requestHistory_length_add_one_le {n : Int} {requests : List (Int × Int)} {ds : DSA}
    (h : RequestHistory n requests ds) (hpos : 0 < n) : requests.length + 1 ≤ n.toNat := by
  have sizes := requestHistory_sizes h
  have capacity_pos : 0 < capacity ds := by
    change 0 < ds.namesA.size
    rw [sizes.1]
    omega
  have positive := rootCount_positive (requestHistory_forest h) capacity_pos
  have conserved := requestHistory_rootCount h
  omega

end Connectivity.ParentCounts
