import Applications.Connectivity.ParentCounts
import Applications.Connectivity.ParentConnectivity
import Applications.Connectivity.ListPartition

set_option autoImplicit false
set_option warningAsError true

/-! Concrete Refinement proofs adapted from adwh-checkpoint-233.
Source members and declaration dispositions: docs/research/adwh-connectivity-provenance.tsv.
Operations retain the source failure and representative-selection behavior. -/

namespace Connectivity.Refinement

open ParentArray ParentForest ParentComponents
open ParentUnion ParentHistory ParentCounts
open ParentConnectivity

def ComponentRefines (array : DSA) (list : ListPartition.DS) : Prop :=
  ListPartition.IsPartitionOf (vertexUniverse array) list ∧
    ∀ u v, SameComponent array u v ↔ ListPartition.SameBlock list u v

def ListRequestStep (ds : ListPartition.DS) (u v : Int) (out : ListPartition.DS) : Prop :=
  ∃ a b, ListPartition.findDS ds u = some a ∧
    ListPartition.findDS ds v = some b ∧ a ≠ b ∧
    ListPartition.unionDS a b ds = some out

inductive JointHistory (n : Int) : List (Int × Int) → DSA → ListPartition.DS → Prop where
  | start : JointHistory n [] (startDSA n) (ListPartition.startDS n)
  | snoc {requests : List (Int × Int)} {array arrayOut : DSA}
      {list listOut : ListPartition.DS} {u v : Int} :
      JointHistory n requests array list → RequestStep array u v arrayOut →
      ListRequestStep list u v listOut →
      JointHistory n (requests ++ [(u, v)]) arrayOut listOut

private theorem list_partition_find {vs : List Int} {ds : ListPartition.DS}
    (h : ListPartition.IsPartitionOf vs ds) {u : Int} (hu : u ∈ vs) :
    ∃ a, ListPartition.findDS ds u = some a :=
  (ListPartition.findDS_defined_iff ds u).mpr (h.2.1.mem_iff.mpr hu)

private theorem list_find_isName {vs : List Int} {ds : ListPartition.DS}
    (h : ListPartition.IsPartitionOf vs ds) {u a : Int}
    (success : ListPartition.findDS ds u = some a) : ListPartition.IsName ds a := by
  obtain ⟨xs, member, _⟩ := (ListPartition.findDS_partition_iff h u a).mp success
  exact List.mem_map.mpr ⟨(a, xs), member, rfl⟩

private theorem list_head_member {xs : List Int} {a : Int} (h : xs.head? = some a) :
    a ∈ xs := by
  obtain ⟨tail, rfl⟩ := List.head?_eq_some_iff.mp h
  simp

private theorem list_find_sameBlock {vs : List Int} {ds : ListPartition.DS}
    (h : ListPartition.IsPartitionOf vs ds) {u a : Int}
    (success : ListPartition.findDS ds u = some a) : ListPartition.SameBlock ds u a := by
  obtain ⟨xs, member, hu⟩ := (ListPartition.findDS_partition_iff h u a).mp success
  exact ⟨a, xs, member, hu, list_head_member (h.2.2 a xs member)⟩

private theorem list_sameBlock_symm {ds : ListPartition.DS} {u v : Int}
    (h : ListPartition.SameBlock ds u v) : ListPartition.SameBlock ds v u := by
  obtain ⟨name, xs, member, hu, hv⟩ := h
  exact ⟨name, xs, member, hv, hu⟩

private theorem list_sameBlock_trans {vs : List Int} {ds : ListPartition.DS}
    (h : ListPartition.IsPartitionOf vs ds) {u v w : Int}
    (huv : ListPartition.SameBlock ds u v) (hvw : ListPartition.SameBlock ds v w) :
    ListPartition.SameBlock ds u w :=
  (ListPartition.sameBlock_equivalence_on h).2.2.1 u v w huv hvw

private theorem list_sameBlock_to_name {vs : List Int} {ds : ListPartition.DS}
    (h : ListPartition.IsPartitionOf vs ds) {u a : Int}
    (success : ListPartition.findDS ds u = some a) (x : Int) :
    ListPartition.SameBlock ds x a ↔ ListPartition.SameBlock ds x u := by
  have together := list_find_sameBlock h success
  exact ⟨fun hx => list_sameBlock_trans h hx (list_sameBlock_symm together),
    fun hx => list_sameBlock_trans h hx together⟩

private theorem list_sameBlock_from_name {vs : List Int} {ds : ListPartition.DS}
    (h : ListPartition.IsPartitionOf vs ds) {u a : Int}
    (success : ListPartition.findDS ds u = some a) (x : Int) :
    ListPartition.SameBlock ds a x ↔ ListPartition.SameBlock ds u x := by
  have together := list_find_sameBlock h success
  exact ⟨fun hx => list_sameBlock_trans h together hx,
    fun hx => list_sameBlock_trans h (list_sameBlock_symm together) hx⟩

private theorem list_sameBlock_start (n u v : Int) :
    ListPartition.SameBlock (ListPartition.startDS n) u v ↔
      u = v ∧ u ∈ ListPartition.vertices n := by
  constructor
  · rintro ⟨name, xs, member, hu, hv⟩
    obtain ⟨w, hw, he⟩ := List.mem_map.mp member
    cases he
    have hu' := List.mem_singleton.mp hu
    have hv' := List.mem_singleton.mp hv
    exact ⟨hu'.trans hv'.symm, by simpa [hu'] using hw⟩
  · rintro ⟨rfl, hu⟩
    exact ⟨u, [u], List.mem_map.mpr ⟨u, hu, rfl⟩, by simp, by simp⟩

theorem componentRefines_start (n : Int) :
    ComponentRefines (startDSA n) (ListPartition.startDS n) := by
  have universeEq := requestHistory_universe (RequestHistory.start (n := n))
  have domain (v : Int) : Valid (startDSA n) v ↔ v ∈ ListPartition.vertices n := by
    rw [← universeEq]
    exact (mem_vertexUniverse (startDSA n) v).symm
  constructor
  · rw [universeEq]
    exact ListPartition.startDS_partition n
  · intro u v
    rw [sameComponent_start, list_sameBlock_start, domain]
    exact and_comm

theorem componentRefines_find_decision {array : DSA} {list : ListPartition.DS}
    (hF : Forest array) (refines : ComponentRefines array list) {u v : Int}
    (hu : Valid array u) (hv : Valid array v) :
    (findDSA array u = findDSA array v) ↔
      ListPartition.findDS list u = ListPartition.findDS list v :=
  ((sameComponent_iff_find_eq hF hu hv).symm.trans (refines.2 u v)).trans
    (ListPartition.findDS_equal_iff_sameBlock refines.1
      ((mem_vertexUniverse array u).mpr hu) ((mem_vertexUniverse array v).mpr hv)).symm

theorem requestStep_refines {array arrayOut : DSA} {list listOut : ListPartition.DS}
    {u v : Int} (hF : Forest array) (refines : ComponentRefines array list)
    (arrayStep : RequestStep array u v arrayOut)
    (listStep : ListRequestStep list u v listOut) : ComponentRefines arrayOut listOut := by
  obtain ⟨a, b, ha, hb, hne, hunion⟩ := listStep
  have hna := list_find_isName refines.1 ha
  have hnb := list_find_isName refines.1 hb
  have sizes := requestStep_sizes arrayStep
  have universeEq : vertexUniverse arrayOut = vertexUniverse array := by
    simp only [vertexUniverse, capacity, sizes.1]
  constructor
  · rw [universeEq]
    exact ListPartition.unionDS_partition refines.1 hna hnb hne hunion
  · intro x y
    rw [requestStep_sameComponent_iff hF arrayStep x y,
      ListPartition.unionDS_sameBlock_iff refines.1 hna hnb hne hunion x y,
      list_sameBlock_to_name refines.1 ha x, list_sameBlock_from_name refines.1 hb y,
      list_sameBlock_to_name refines.1 hb x, list_sameBlock_from_name refines.1 ha y,
      refines.2 x y, refines.2 x u, refines.2 v y, refines.2 x v, refines.2 u y]

theorem requestStep_list_exists {array arrayOut : DSA} {list : ListPartition.DS}
    {u v : Int} (hF : Forest array) (refines : ComponentRefines array list)
    (arrayStep : RequestStep array u v arrayOut) :
    ∃ listOut, ListRequestStep list u v listOut ∧ ComponentRefines arrayOut listOut := by
  have step := arrayStep
  obtain ⟨r, s, hr, hs, hrs, _⟩ := step
  have hu := ((hF.findDSA_iff_Root u r).mp hr).valid_start
  have hv := ((hF.findDSA_iff_Root v s).mp hs).valid_start
  obtain ⟨a, ha⟩ := list_partition_find refines.1 ((mem_vertexUniverse array u).mpr hu)
  obtain ⟨b, hb⟩ := list_partition_find refines.1 ((mem_vertexUniverse array v).mpr hv)
  have hne : a ≠ b := by
    intro he
    have listEq : ListPartition.findDS list u = ListPartition.findDS list v := by
      rw [ha, hb, he]
    have arrayEq := (componentRefines_find_decision hF refines hu hv).mpr listEq
    exact hrs (Option.some.inj (hr.symm.trans (arrayEq.trans hs)))
  obtain ⟨listOut, hunion⟩ := (ListPartition.unionDS_defined_iff a b list).mpr
    ⟨list_find_isName refines.1 ha, list_find_isName refines.1 hb⟩
  have listStep : ListRequestStep list u v listOut := ⟨a, b, ha, hb, hne, hunion⟩
  exact ⟨listOut, listStep, requestStep_refines hF refines arrayStep listStep⟩

theorem componentRefines_union {array arrayOut : DSA} {list : ListPartition.DS}
    {n1 n2 : Int} (hF : Forest array) (refines : ComponentRefines array list)
    (h1 : SelfRoot array n1) (h2 : SelfRoot array n2) (hne : n1 ≠ n2)
    (hunion : unionDSA n1 n2 array = some arrayOut) :
    ∃ a b listOut, ListPartition.findDS list n1 = some a ∧
      ListPartition.findDS list n2 = some b ∧
      ListPartition.IsName list a ∧ ListPartition.IsName list b ∧ a ≠ b ∧
      ListPartition.unionDS a b list = some listOut ∧ ComponentRefines arrayOut listOut := by
  have arrayStep : RequestStep array n1 n2 arrayOut :=
    ⟨n1, n2, (hF.findDSA_iff_Root n1 n1).mpr (root_self h1),
      (hF.findDSA_iff_Root n2 n2).mpr (root_self h2), hne, hunion⟩
  obtain ⟨listOut, listStep, outRefines⟩ := requestStep_list_exists hF refines arrayStep
  obtain ⟨a, b, ha, hb, hab, hu⟩ := listStep
  exact ⟨a, b, listOut, ha, hb, list_find_isName refines.1 ha,
    list_find_isName refines.1 hb, hab, hu, outRefines⟩

theorem jointHistory_array {n : Int} {requests : List (Int × Int)}
    {array : DSA} {list : ListPartition.DS} (h : JointHistory n requests array list) :
    RequestHistory n requests array := by
  induction h with
  | start => exact RequestHistory.start
  | snoc _ arrayStep _ ih => exact RequestHistory.snoc ih arrayStep

theorem jointHistory_refines {n : Int} {requests : List (Int × Int)}
    {array : DSA} {list : ListPartition.DS} (h : JointHistory n requests array list) :
    ComponentRefines array list := by
  induction h with
  | start => exact componentRefines_start n
  | snoc before arrayStep listStep ih =>
      exact requestStep_refines (requestHistory_forest (jointHistory_array before))
        ih arrayStep listStep

theorem jointHistory_invariants {n : Int} {requests : List (Int × Int)}
    {array : DSA} {list : ListPartition.DS} (h : JointHistory n requests array list) :
    Forest array ∧ WeightedForest array ∧ RootSizesExact array := by
  have hist := jointHistory_array h
  exact ⟨requestHistory_forest hist, requestHistory_weighted hist,
    requestHistory_rootSizesExact hist⟩

theorem jointHistory_partition {n : Int} {requests : List (Int × Int)}
    {array : DSA} {list : ListPartition.DS} (h : JointHistory n requests array list) :
    ListPartition.IsPartitionOf (ListPartition.vertices n) list := by
  have partition := (jointHistory_refines h).1
  rw [requestHistory_universe (jointHistory_array h)] at partition
  exact partition

theorem jointHistory_list_history {n : Int} {requests : List (Int × Int)}
    {array : DSA} {list : ListPartition.DS} (h : JointHistory n requests array list) :
    ∃ calls, ListPartition.MergeHistory n calls list ∧ calls.length = requests.length := by
  induction h with
  | start => exact ⟨[], ListPartition.MergeHistory.start, rfl⟩
  | @snoc requests array arrayOut list listOut u v before arrayStep listStep ih =>
      obtain ⟨calls, namedHistory, lengthEq⟩ := ih
      obtain ⟨a, b, ha, hb, hne, hunion⟩ := listStep
      have partition := ListPartition.mergeHistory_partition namedHistory
      refine ⟨calls ++ [(a, b)], ListPartition.MergeHistory.snoc namedHistory
        (list_find_isName partition ha) (list_find_isName partition hb) hne hunion, ?_⟩
      simp only [List.length_append, List.length_singleton, lengthEq]

theorem jointHistory_counts {n : Int} {requests : List (Int × Int)}
    {array : DSA} {list : ListPartition.DS} (h : JointHistory n requests array list) :
    list.length + requests.length = n.toNat ∧ rootCount array = list.length := by
  obtain ⟨calls, namedHistory, lengthEq⟩ := jointHistory_list_history h
  have listCount := ListPartition.mergeHistory_block_count namedHistory
  rw [lengthEq] at listCount
  have arrayCount := requestHistory_rootCount (jointHistory_array h)
  exact ⟨listCount, by omega⟩

theorem requestHistory_realized {n : Int} {requests : List (Int × Int)} {array : DSA}
    (h : RequestHistory n requests array) : ∃ list, JointHistory n requests array list := by
  induction h with
  | start => exact ⟨ListPartition.startDS n, JointHistory.start⟩
  | snoc before step ih =>
      obtain ⟨list, joint⟩ := ih
      obtain ⟨listOut, listStep, _⟩ := requestStep_list_exists
        (requestHistory_forest before) (jointHistory_refines joint) step
      exact ⟨listOut, JointHistory.snoc joint step listStep⟩

theorem jointHistory_find_decision {n : Int} {requests : List (Int × Int)}
    {array : DSA} {list : ListPartition.DS} (h : JointHistory n requests array list)
    {u v : Int} (hu : u ∈ ListPartition.vertices n) (hv : v ∈ ListPartition.vertices n) :
    (findDSA array u = findDSA array v) ↔
      ListPartition.findDS list u = ListPartition.findDS list v := by
  have hist := jointHistory_array h
  have universeEq := requestHistory_universe hist
  have hu' : Valid array u := (mem_vertexUniverse array u).mp (by simpa only [universeEq] using hu)
  have hv' : Valid array v := (mem_vertexUniverse array v).mp (by simpa only [universeEq] using hv)
  exact componentRefines_find_decision (requestHistory_forest hist) (jointHistory_refines h) hu' hv'

theorem jointHistory_list_connected {n : Int} {requests : List (Int × Int)}
    {array : DSA} {list : ListPartition.DS} (h : JointHistory n requests array list)
    (u v : Int) :
    ListPartition.SameBlock list u v ↔ ListPartition.Connected (ListPartition.vertices n) requests u v :=
  ((jointHistory_refines h).2 u v).symm.trans
    (requestHistory_connected_iff (jointHistory_array h) u v)

private theorem listRequestStep_deterministic {ds out₁ out₂ : ListPartition.DS} {u v : Int}
    (h₁ : ListRequestStep ds u v out₁) (h₂ : ListRequestStep ds u v out₂) : out₁ = out₂ := by
  obtain ⟨a, b, ha, hb, _, hu⟩ := h₁
  obtain ⟨c, d, hc, hd, _, hv⟩ := h₂
  have hac : a = c := Option.some.inj (ha.symm.trans hc)
  have hbd : b = d := Option.some.inj (hb.symm.trans hd)
  subst c
  subst d
  exact Option.some.inj (hu.symm.trans hv)

private theorem jointHistory_nil {n : Int} {array : DSA} {list : ListPartition.DS}
    (h : JointHistory n [] array list) :
    array = startDSA n ∧ list = ListPartition.startDS n := by
  have empty_result : ∀ {requests : List (Int × Int)} {a : DSA} {l : ListPartition.DS},
      JointHistory n requests a l → requests = [] →
      a = startDSA n ∧ l = ListPartition.startDS n := by
    intro requests a l hist
    induction hist with
    | start => intro _; exact ⟨rfl, rfl⟩
    | snoc _ _ _ _ => intro empty; simp at empty
  exact empty_result h rfl

private theorem jointHistory_snoc {n : Int} {requests : List (Int × Int)}
    {array : DSA} {list : ListPartition.DS} {u v : Int}
    (h : JointHistory n (requests ++ [(u, v)]) array list) :
    ∃ oldArray oldList, JointHistory n requests oldArray oldList ∧
      RequestStep oldArray u v array ∧ ListRequestStep oldList u v list := by
  have peel : ∀ {all : List (Int × Int)} {a : DSA} {l : ListPartition.DS},
      JointHistory n all a l → ∀ earlier u v, all = earlier ++ [(u, v)] →
      ∃ oldArray oldList, JointHistory n earlier oldArray oldList ∧
        RequestStep oldArray u v a ∧ ListRequestStep oldList u v l := by
    intro all a l hist
    cases hist with
    | start =>
        intro earlier u v he
        have lengths := congrArg List.length he
        simp at lengths
    | @snoc prior oldArray arrayOut oldList listOut x y before arrayStep listStep =>
        intro earlier u v he
        obtain ⟨rfl, pairEq⟩ := List.append_singleton_inj.mp he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj pairEq
        exact ⟨oldArray, oldList, before, arrayStep, listStep⟩
  exact peel h requests u v rfl

theorem jointHistory_deterministic {n : Int} {requests : List (Int × Int)}
    {array otherArray : DSA} {list otherList : ListPartition.DS}
    (h : JointHistory n requests array list)
    (h' : JointHistory n requests otherArray otherList) :
    array = otherArray ∧ list = otherList := by
  induction h generalizing otherArray otherList with
  | start =>
      obtain ⟨ha, hl⟩ := jointHistory_nil h'
      exact ⟨ha.symm, hl.symm⟩
  | snoc _ arrayStep listStep ih =>
      obtain ⟨oldArray, oldList, before', arrayStep', listStep'⟩ := jointHistory_snoc h'
      obtain ⟨rfl, rfl⟩ := ih before'
      exact ⟨requestStep_deterministic arrayStep arrayStep',
        listRequestStep_deterministic listStep listStep'⟩

end Connectivity.Refinement
