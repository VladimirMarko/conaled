import Applications.Connectivity.ParentUnion

set_option autoImplicit false
set_option warningAsError true

/-! Concrete ParentHistory proofs adapted from adwh-checkpoint-233.
Source members and declaration dispositions: docs/research/adwh-connectivity-provenance.tsv.
Operations retain the source failure and representative-selection behavior. -/

namespace Connectivity.ParentHistory

open ParentArray ParentForest ParentComponents
open ParentUnion

def RequestStep (ds : DSA) (u v : Int) (out : DSA) : Prop :=
  ∃ a b, findDSA ds u = some a ∧ findDSA ds v = some b ∧
    a ≠ b ∧ unionDSA a b ds = some out

inductive RequestHistory (n : Int) : List (Int × Int) → DSA → Prop where
  | start : RequestHistory n [] (startDSA n)
  | snoc {requests : List (Int × Int)} {ds out : DSA} {u v : Int} :
      RequestHistory n requests ds → RequestStep ds u v out →
      RequestHistory n (requests ++ [(u, v)]) out

theorem requestStep_deterministic {ds out₁ out₂ : DSA} {u v : Int}
    (h₁ : RequestStep ds u v out₁) (h₂ : RequestStep ds u v out₂) : out₁ = out₂ := by
  obtain ⟨a, b, ha, hb, _, hu⟩ := h₁
  obtain ⟨c, d, hc, hd, _, hv⟩ := h₂
  have hac : a = c := Option.some.inj (ha.symm.trans hc)
  have hbd : b = d := Option.some.inj (hb.symm.trans hd)
  subst c
  subst d
  exact Option.some.inj (hu.symm.trans hv)

theorem requestStep_sizes {ds out : DSA} {u v : Int}
    (h : RequestStep ds u v out) :
    out.namesA.size = ds.namesA.size ∧ out.sizesA.size = ds.sizesA.size := by
  obtain ⟨_, _, _, _, _, hu⟩ := h
  exact unionDSA_sizes hu

theorem requestHistory_nil_iff (n : Int) (ds : DSA) :
    RequestHistory n [] ds ↔ ds = startDSA n := by
  constructor
  · intro h
    have empty_result : ∀ {requests : List (Int × Int)} {state : DSA},
        RequestHistory n requests state → requests = [] → state = startDSA n := by
      intro requests state hist
      induction hist with
      | start => intro _; rfl
      | snoc _ _ _ => intro empty; simp at empty
    exact empty_result h rfl
  · rintro rfl
    exact RequestHistory.start

theorem requestHistory_snoc_iff (n : Int) (requests : List (Int × Int))
    (u v : Int) (out : DSA) :
    RequestHistory n (requests ++ [(u, v)]) out ↔
      ∃ ds, RequestHistory n requests ds ∧ RequestStep ds u v out := by
  constructor
  · intro h
    have peel : ∀ {all : List (Int × Int)} {state : DSA},
        RequestHistory n all state → ∀ earlier a b,
        all = earlier ++ [(a, b)] →
        ∃ old, RequestHistory n earlier old ∧ RequestStep old a b state := by
      intro all state hist
      cases hist with
      | start =>
          intro earlier a b he
          have lengths := congrArg List.length he
          simp at lengths
      | @snoc prior old state a b before step =>
          intro earlier u v he
          obtain ⟨rfl, pairEq⟩ := List.append_singleton_inj.mp he
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj pairEq
          exact ⟨old, before, step⟩
    exact peel h requests u v rfl
  · rintro ⟨ds, before, step⟩
    exact RequestHistory.snoc before step

theorem requestHistory_sizes {n : Int} {requests : List (Int × Int)} {ds : DSA}
    (h : RequestHistory n requests ds) :
    ds.namesA.size = n.toNat ∧ ds.sizesA.size = n.toNat := by
  induction h with
  | start => exact startDSA_sizes n
  | snoc _ step ih =>
      have sizes := requestStep_sizes step
      exact ⟨sizes.1.trans ih.1, sizes.2.trans ih.2⟩

private theorem history_invariants {n : Int} {requests : List (Int × Int)} {ds : DSA}
    (h : RequestHistory n requests ds) :
    Forest ds ∧ WeightedForest ds ∧ RootSizesExact ds := by
  induction h with
  | start =>
      exact ⟨startDSA_forest n, startDSA_weightedForest n, startDSA_rootSizesExact n⟩
  | snoc _ step ih =>
      obtain ⟨a, b, ha, hb, hne, hu⟩ := step
      have h1 := ((ih.1.findDSA_iff_Root _ a).mp ha).selfRoot
      have h2 := ((ih.1.findDSA_iff_Root _ b).mp hb).selfRoot
      exact ⟨union_forest ih.1 ih.2.2 h1 h2 hne hu,
        union_weightedForest ih.2.1 ih.2.2 h1 h2 hne hu,
        union_rootSizesExact ih.1 ih.2.2 h1 h2 hne hu⟩

theorem requestHistory_forest {n : Int} {requests : List (Int × Int)} {ds : DSA}
    (h : RequestHistory n requests ds) : Forest ds := (history_invariants h).1

theorem requestHistory_weighted {n : Int} {requests : List (Int × Int)} {ds : DSA}
    (h : RequestHistory n requests ds) : WeightedForest ds := (history_invariants h).2.1

theorem requestHistory_rootSizesExact {n : Int} {requests : List (Int × Int)} {ds : DSA}
    (h : RequestHistory n requests ds) : RootSizesExact ds := (history_invariants h).2.2

theorem requestHistory_valid_iff {n : Int} {requests : List (Int × Int)} {ds : DSA}
    (h : RequestHistory n requests ds) (v : Int) :
    Valid ds v ↔ 0 < v ∧ v ≤ n := by
  have sizes := requestHistory_sizes h
  unfold Valid capacity
  rw [sizes.1]
  omega

theorem requestHistory_find_domain {n : Int} {requests : List (Int × Int)} {ds : DSA}
    (h : RequestHistory n requests ds) (v : Int) :
    (∃ r, findDSA ds v = some r) ↔ 0 < v ∧ v ≤ n := by
  have forest := requestHistory_forest h
  constructor
  · rintro ⟨r, success⟩
    exact (requestHistory_valid_iff h v).mp
      ((forest.findDSA_iff_Root v r).mp success).valid_start
  · intro valid
    exact forest.find_complete ((requestHistory_valid_iff h v).mpr valid)

theorem requestHistory_find_root {n : Int} {requests : List (Int × Int)} {ds : DSA}
    (h : RequestHistory n requests ds) {v r : Int} (success : findDSA ds v = some r) :
    Root ds v r ∧ Valid ds r ∧ SelfRoot ds r := by
  have root := ((requestHistory_forest h).findDSA_iff_Root v r).mp success
  exact ⟨root, root.valid_root, root.selfRoot⟩

theorem requestHistory_request_endpoints {n : Int} {requests : List (Int × Int)} {ds : DSA}
    (h : RequestHistory n requests ds) (u v : Int) (member : (u, v) ∈ requests) :
    (0 < u ∧ u ≤ n) ∧ (0 < v ∧ v ≤ n) := by
  induction h with
  | start => simp at member
  | @snoc prior old out a b before step ih =>
      rcases List.mem_append.mp member with earlier | last
      · exact ih earlier
      · have pairEq := List.mem_singleton.mp last
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj pairEq
        obtain ⟨r, s, hr, hs, _, _⟩ := step
        exact ⟨(requestHistory_find_domain before u).mp ⟨r, hr⟩,
          (requestHistory_find_domain before v).mp ⟨s, hs⟩⟩

theorem requestHistory_deterministic {n : Int} {requests : List (Int × Int)} {ds other : DSA}
    (h : RequestHistory n requests ds) (h' : RequestHistory n requests other) : ds = other := by
  induction h generalizing other with
  | start => exact ((requestHistory_nil_iff n other).mp h').symm
  | @snoc prior old out u v before step ih =>
      obtain ⟨old', before', step'⟩ := (requestHistory_snoc_iff n prior u v other).mp h'
      have same := ih before'
      subst old'
      exact requestStep_deterministic step step'

theorem requestHistory_nonpositive_iff (n : Int) (requests : List (Int × Int))
    (ds : DSA) (nonpositive : n ≤ 0) :
    RequestHistory n requests ds ↔ requests = [] ∧ ds = ⟨#[], #[]⟩ := by
  constructor
  · intro h
    have empty : requests = [] := by
      cases requests with
      | nil => rfl
      | cons pair rest =>
          have endpoints := requestHistory_request_endpoints h pair.1 pair.2 (by simp)
          omega
    subst requests
    exact ⟨rfl, ((requestHistory_nil_iff n ds).mp h).trans (startDSA_nonpositive n nonpositive)⟩
  · rintro ⟨rfl, rfl⟩
    rw [← startDSA_nonpositive n nonpositive]
    exact RequestHistory.start

private def historyMid : DSA := ⟨#[1, 2, 2], #[1, 2, 1]⟩
private def historyFinal : DSA := ⟨#[2, 2, 2], #[1, 3, 1]⟩

private theorem historyExample : RequestHistory 3 [(2, 3), (1, 2)] historyFinal := by
  have first : RequestStep (startDSA 3) 2 3 historyMid := by
    refine ⟨2, 3, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
  have second : RequestStep historyMid 1 2 historyFinal := by
    refine ⟨1, 2, ?_, ?_, ?_, ?_⟩ <;> decide +kernel
  exact RequestHistory.snoc (RequestHistory.snoc RequestHistory.start first) second

end Connectivity.ParentHistory
