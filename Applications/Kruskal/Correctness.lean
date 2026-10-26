import Applications.Kruskal.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
set_option autoImplicit false
set_option warningAsError true
namespace Kruskal
open Connectivity.ListPartition
  (findDS lookupDS unionDS startDS FirstAssoc FirstContaining IsPartitionOf
   SameBlock IsName Connected)
theorem gstepK2_nil (ds : DS) (fs : List Edge) :
    gstepK2 (ds, fs, []) = none := by rw [gstepK2]

theorem gstepK2_take {ds out : DS} {fs es : List Edge} {e : Edge} {a b : Name}
    (ha : findDS ds (source e) = some a) (hb : findDS ds (target e) = some b)
    (hne : a ≠ b) (hu : unionDS a b ds = some out) :
    gstepK2 (ds, fs, e :: es) = some (out, e :: fs, es) := by
  simp only [gstepK2, ha, hb, ite_eq_left hne, hu, Option.map_some]

theorem gstepK2_skip {ds : DS} {fs es : List Edge} {e : Edge} {a : Name}
    (ha : findDS ds (source e) = some a) (hb : findDS ds (target e) = some a) :
    gstepK2 (ds, fs, e :: es) = gstepK2 (ds, fs, es) := by
  simp only [gstepK2, ha, hb, ne_eq, not_true_eq_false, ↓reduceIte]

private theorem sourceStep_value {s out : StateDS} (h : SourceStep s out) :
    gstepK2 s = some out := by
  induction h with
  | take ha hb hn hxs hys =>
      apply gstepK2_take
        ((Connectivity.ListPartition.findDS_first_iff _ _ _).mpr ha)
        ((Connectivity.ListPartition.findDS_first_iff _ _ _).mpr hb) hn
      rw [Connectivity.ListPartition.unionDS_eq_some_iff]
      exact ⟨_, _, hxs, hys, rfl⟩
  | skip ha hb _ ih =>
      rw [gstepK2_skip ((Connectivity.ListPartition.findDS_first_iff _ _ _).mpr ha)
        ((Connectivity.ListPartition.findDS_first_iff _ _ _).mpr hb)]
      exact ih

theorem gstepK2_source_iff (s out : StateDS) :
    gstepK2 s = some out ↔ SourceStep s out := by
  refine ⟨?_, sourceStep_value⟩
  rcases s with ⟨ds, fs, es⟩
  induction es with
  | nil => simp [gstepK2]
  | cons e es ih =>
      intro h
      rw [gstepK2] at h
      cases ha : findDS ds (source e) with
      | none => simp [ha] at h
      | some a =>
        cases hb : findDS ds (target e) with
        | none => simp [ha, hb] at h
        | some b =>
          simp only [ha, hb] at h
          by_cases hn : a ≠ b
          · rw [ite_eq_left hn, Option.map_eq_some_iff] at h
            obtain ⟨dsNext, hu, rfl⟩ := h
            obtain ⟨xs, ys, hx, hy, rfl⟩ :=
              (Connectivity.ListPartition.unionDS_eq_some_iff a b ds dsNext).mp hu
            exact SourceStep.take
              ((Connectivity.ListPartition.findDS_first_iff _ _ _).mp ha)
              ((Connectivity.ListPartition.findDS_first_iff _ _ _).mp hb) hn hx hy
          · have hab : a = b := by simpa using hn
            subst b
            rw [ite_eq_right (not_not_intro rfl)] at h
            exact SourceStep.skip
              ((Connectivity.ListPartition.findDS_first_iff _ _ _).mp ha)
              ((Connectivity.ListPartition.findDS_first_iff _ _ _).mp hb) (ih h)

theorem gstepK2_consumed_prefix {ds : DS} {fs es : List Edge} {out : StateDS}
    (h : gstepK2 (ds, fs, es) = some out) :
    ∃ pre e rest dsNext, es = pre ++ e :: rest ∧ out = (dsNext, e :: fs, rest) ∧
      (∀ f ∈ pre, ∃ a, FirstContaining ds (source f) a ∧
        FirstContaining ds (target f) a) ∧
      SourceStep (ds, fs, [e]) (dsNext, e :: fs, []) := by
  have hs := (gstepK2_source_iff _ _).mp h
  clear h
  generalize hsIn : (ds, fs, es) = input at hs
  induction hs generalizing ds fs es with
  | take ha hb hn hx hy =>
      cases hsIn
      exact ⟨[], _, _, _, rfl, rfl, by simp, SourceStep.take ha hb hn hx hy⟩
  | @skip ds0 fs0 es0 e0 a out0 ha hb _ ih =>
      cases hsIn
      obtain ⟨pre, e, rest, dsNext, he, ho, hp, ht⟩ := ih rfl
      refine ⟨e0 :: pre, e, rest, dsNext, ?_, ho, ?_, ht⟩
      · simp [he]
      · intro f hf
        rcases List.mem_cons.mp hf with rfl | hm
        · exact ⟨_, ha, hb⟩
        · exact hp f hm

theorem applyK_source_iff (k : Nat) (s out : StateDS) :
    applyK k s = some out ↔ SourceRun k s out := by
  induction k generalizing out with
  | zero =>
      constructor
      · intro h
        have he : s = out := Option.some.inj h
        subst out
        exact SourceRun.zero s
      · intro h
        cases h
        rfl
  | succ k ih =>
      rw [applyK, Option.bind_eq_some_iff]
      constructor
      · rintro ⟨middle, hm, ho⟩
        exact SourceRun.succ ((ih middle).mp hm) ((gstepK2_source_iff _ _).mp ho)
      · intro h
        cases h with
        | succ hm ho => exact ⟨_, (ih _).mpr hm, (gstepK2_source_iff _ _).mpr ho⟩

theorem reach_refl {vs : List Vertex} {es : List Edge} {u : Vertex}
    (h : u ∈ vs) : Reach vs es u u := Connected.refl h

theorem reach_symm {vs : List Vertex} {es : List Edge} {u v : Vertex}
    (h : Reach vs es u v) : Reach vs es v u := Connected.symm h

private theorem reach_trans {vs : List Vertex} {es : List Edge} {u v w : Vertex}
    (h : Reach vs es u v) (k : Reach vs es v w) : Reach vs es u w :=
  Connected.trans h k

private theorem reach_vertices {vs : List Vertex} {es : List Edge} {u v : Vertex}
    (h : Reach vs es u v) : u ∈ vs ∧ v ∈ vs := by
  induction h with
  | refl hv => exact ⟨hv, hv⟩
  | edge hu hv _ => exact ⟨hu, hv⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ⟨ih.1, ik.2⟩

theorem reach_edge {vs : List Vertex} {es : List Edge} {e : Edge}
    (he : e ∈ es) (hu : source e ∈ vs) (hv : target e ∈ vs) :
    Reach vs es (source e) (target e) :=
  Connected.edge hu hv (List.mem_map.mpr ⟨e, he, rfl⟩)

private theorem reach_of_edges {vs : List Vertex} {old new : List Edge}
    (he : ∀ e ∈ old, Reach vs new (source e) (target e)) {u v : Vertex}
    (h : Reach vs old u v) : Reach vs new u v := by
  induction h with
  | refl hv => exact reach_refl hv
  | edge hu hv hm =>
      obtain ⟨e, he', hh⟩ := List.mem_map.mp hm
      cases hh
      exact he e he'
  | symm _ ih => exact reach_symm ih
  | trans _ _ ih ik => exact reach_trans ih ik

theorem reach_mono {vs : List Vertex} {small large : List Edge} {u v : Vertex}
    (hsub : small ⊆ large) (h : Reach vs small u v) : Reach vs large u v := by
  apply Connectivity.ListPartition.connected_mono ?_ h
  intro pair hp
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hp
  exact List.mem_map.mpr ⟨e, hsub he, rfl⟩

theorem reach_cons_iff {vs : List Vertex} {fs : List Edge} {e : Edge}
    (hu : source e ∈ vs) (hv : target e ∈ vs) (u v : Vertex) :
    Reach vs (e :: fs) u v ↔ Reach vs fs u v ∨
      (Reach vs fs u (source e) ∧ Reach vs fs (target e) v) ∨
      (Reach vs fs u (target e) ∧ Reach vs fs (source e) v) := by
  constructor
  · intro h
    induction h with
    | refl hm => exact Or.inl (reach_refl hm)
    | edge hm hn hl =>
        rcases List.mem_cons.mp hl with hh | ht
        · cases hh
          exact Or.inr (Or.inl ⟨reach_refl hu, reach_refl hv⟩)
        · exact Or.inl (Connected.edge hm hn ht)
    | symm _ ih =>
        rcases ih with h | ⟨h, k⟩ | ⟨h, k⟩
        · exact Or.inl (reach_symm h)
        · exact Or.inr (Or.inr ⟨reach_symm k, reach_symm h⟩)
        · exact Or.inr (Or.inl ⟨reach_symm k, reach_symm h⟩)
    | trans _ _ ih ik =>
        rcases ih with h | ⟨h, k⟩ | ⟨h, k⟩ <;>
          rcases ik with l | ⟨l, m⟩ | ⟨l, m⟩
        · exact Or.inl (reach_trans h l)
        · exact Or.inr (Or.inl ⟨reach_trans h l, m⟩)
        · exact Or.inr (Or.inr ⟨reach_trans h l, m⟩)
        · exact Or.inr (Or.inl ⟨h, reach_trans k l⟩)
        · exact Or.inr (Or.inl ⟨h, m⟩)
        · exact Or.inl (reach_trans h m)
        · exact Or.inr (Or.inr ⟨h, reach_trans k l⟩)
        · exact Or.inl (reach_trans h m)
        · exact Or.inr (Or.inr ⟨h, m⟩)
  · intro h
    have sub : fs ⊆ e :: fs := fun _ hx => List.mem_cons_of_mem e hx
    have ed := reach_edge (by simp : e ∈ e :: fs) hu hv
    rcases h with h | ⟨h, k⟩ | ⟨h, k⟩
    · exact reach_mono sub h
    · exact reach_trans (reach_mono sub h) (reach_trans ed (reach_mono sub k))
    · exact reach_trans (reach_mono sub h)
        (reach_trans (reach_symm ed) (reach_mono sub k))

private theorem walk_vertices {vs : List Vertex} {es path : List Edge} {u v : Vertex}
    (h : Walk vs es u path v) : u ∈ vs ∧ v ∈ vs := by
  induction h with
  | nil hv => exact ⟨hv, hv⟩
  | cons _ hu _ _ _ ih => exact ⟨hu, ih.2⟩

private theorem walk_append {vs : List Vertex} {es p q : List Edge} {u v w : Vertex}
    (h : Walk vs es u p v) (k : Walk vs es v q w) : Walk vs es u (p ++ q) w := by
  induction h with
  | nil _ => exact k
  | cons he hu hv ho _ ih => exact Walk.cons he hu hv ho (ih k)

private theorem walk_reverse {vs : List Vertex} {es p : List Edge} {u v : Vertex}
    (h : Walk vs es u p v) : Walk vs es v p.reverse u := by
  induction h with
  | nil hu => exact Walk.nil hu
  | cons he hu hw ho _ ih =>
      rw [List.reverse_cons]
      apply walk_append ih
      apply Walk.cons he hw hu _ (Walk.nil hu)
      rcases ho with ⟨h, k⟩ | ⟨h, k⟩
      · exact Or.inr ⟨k, h⟩
      · exact Or.inl ⟨k, h⟩

theorem reach_iff_walk (vs : List Vertex) (es : List Edge) (u v : Vertex) :
    Reach vs es u v ↔ ∃ path, Walk vs es u path v := by
  constructor
  · intro h
    induction h with
    | refl hu => exact ⟨[], Walk.nil hu⟩
    | edge hu hv hm =>
        obtain ⟨e, he, hh⟩ := List.mem_map.mp hm
        cases hh
        exact ⟨[e], Walk.cons he hu hv (Or.inl ⟨rfl, rfl⟩) (Walk.nil hv)⟩
    | symm _ ih =>
        obtain ⟨p, hp⟩ := ih
        exact ⟨p.reverse, walk_reverse hp⟩
    | trans _ _ ih ik =>
        obtain ⟨p, hp⟩ := ih
        obtain ⟨q, hq⟩ := ik
        exact ⟨p ++ q, walk_append hp hq⟩
  · rintro ⟨p, hp⟩
    induction hp with
    | nil hu => exact reach_refl hu
    | cons he hu hw ho _ ih =>
        apply reach_trans _ ih
        rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact reach_edge he hu hw
        · exact reach_symm (reach_edge he hw hu)

theorem forest_nil {vs : List Vertex} (hvs : vs.Nodup) : EdgeForest vs [] := by
  exact ⟨hvs, by simp [EndpointsIn], by simp, by simp⟩

theorem forest_cons_iff (vs : List Vertex) (e : Edge) (fs : List Edge) :
    EdgeForest vs (e :: fs) ↔ EdgeForest vs fs ∧ source e ∈ vs ∧
      target e ∈ vs ∧ ¬ Reach vs fs (source e) (target e) := by
  constructor
  · rintro ⟨hn, he, hd, hb⟩
    have hnd := List.nodup_cons.mp hd
    refine ⟨⟨hn, fun f hf => he f (by simp [hf]), hnd.2, ?_⟩,
      (he e (by simp)).1, (he e (by simp)).2, ?_⟩
    · intro f hf hr
      have hne : e ≠ f := fun h => hnd.1 (h ▸ hf)
      apply hb f (by simp [hf])
      rw [List.erase_cons_tail (by simpa using hne)]
      exact reach_mono (fun _ hm => List.mem_cons_of_mem _ hm) hr
    · simpa using hb e (by simp)
  · rintro ⟨hf, hu, hv, hcross⟩
    have hnot : e ∉ fs := fun he => hcross (reach_edge he hu hv)
    refine ⟨hf.1, ?_, List.nodup_cons.mpr ⟨hnot, hf.2.2.1⟩, ?_⟩
    · intro f hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact ⟨hu, hv⟩
      · exact hf.2.1 f hm
    · intro f hm hr
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hcross (by simpa using hr)
      · have hne : e ≠ f := fun h => hnot (h ▸ hm)
        rw [List.erase_cons_tail (by simpa using hne)] at hr
        rcases (reach_cons_iff hu hv _ _).mp hr with hr | ⟨hp, hq⟩ | ⟨hp, hq⟩
        · exact hf.2.2.2 f hm hr
        · have fp := reach_mono List.erase_subset hp
          have fq := reach_mono List.erase_subset hq
          have ed := reach_edge hm (hf.2.1 f hm).1 (hf.2.1 f hm).2
          exact hcross (reach_trans (reach_symm fp) (reach_trans ed (reach_symm fq)))
        · have fp := reach_mono List.erase_subset hp
          have fq := reach_mono List.erase_subset hq
          have ed := reach_edge hm (hf.2.1 f hm).1 (hf.2.1 f hm).2
          exact hcross (reach_trans fq (reach_trans (reach_symm ed) fp))

theorem forest_perm {vs : List Vertex} {es fs : List Edge} (h : es.Perm fs) :
    EdgeForest vs es ↔ EdgeForest vs fs := by
  have one : ∀ {es fs : List Edge}, es.Perm fs → EdgeForest vs es → EdgeForest vs fs := by
    intro es fs hp hf
    refine ⟨hf.1, fun e he => hf.2.1 e (hp.mem_iff.mpr he), hp.nodup hf.2.2.1, ?_⟩
    intro e he hr
    apply hf.2.2.2 e (hp.mem_iff.mpr he)
    exact reach_mono (hp.erase e).symm.subset hr
  exact ⟨one h, one h.symm⟩

private theorem forest_sublist {vs : List Vertex} {es fs : List Edge}
    (hsub : es.Sublist fs) (hf : EdgeForest vs fs) : EdgeForest vs es := by
  induction hsub with
  | slnil => exact forest_nil hf.1
  | cons _ _ ih => exact ih ((forest_cons_iff _ _ _).mp hf).1
  | cons_cons _ hsub ih =>
      have hh := (forest_cons_iff _ _ _).mp hf
      refine (forest_cons_iff _ _ _).mpr ⟨ih hh.1, hh.2.1, hh.2.2.1, ?_⟩
      intro hr
      exact hh.2.2.2 (reach_mono hsub.subset hr)

private theorem forest_erase {vs : List Vertex} {es : List Edge} (hf : EdgeForest vs es)
    (e : Edge) : EdgeForest vs (es.erase e) := forest_sublist List.erase_sublist hf

/-- A spanning subforest with the same components already contains every edge
of an acyclic superforest. This also applies to disconnected graphs. -/
theorem same_components_subforest_eq_perm {vs : List Vertex} {fs ts : List Edge}
    (hf : EdgeForest vs fs) (ht : EdgeForest vs ts) (hsub : fs⊆ts)
    (hc : ∀e∈ts,Reach vs fs (source e) (target e)) : fs.Perm ts := by
  apply (List.perm_ext_iff_of_nodup hf.2.2.1 ht.2.2.1).mpr
  intro e
  refine ⟨fun he => hsub he,?_⟩
  intro he
  by_cases hn : e∈fs
  · exact hn
  apply False.elim
  have hr : fs⊆ts.erase e := by
    intro f hf
    exact (List.mem_erase_of_ne (fun (h : f=e) => hn (h ▸ hf))).mpr (hsub hf)
  exact ht.2.2.2 e he (reach_mono hr (hc e he))

theorem spanning_subforest_eq_perm {vs : List Vertex} {fs ts : List Edge}
    (hf : SpanningEdges vs fs) (ht : EdgeForest vs ts) (hsub : fs ⊆ ts) : fs.Perm ts :=
  same_components_subforest_eq_perm hf.2.1 ht hsub
    (fun e he => hf.2.2 _ (ht.2.1 e he).1 _ (ht.2.1 e he).2)

private theorem perm_sum_int {xs ys : List Int} (h : xs.Perm ys) : xs.sum = ys.sum :=
  h.sum_eq

theorem exchange_cost_identity (vs : List Vertex) (ts : List Edge) (e f : Edge)
    (hf : f ∈ ts) :
    costMCST (vs, e :: ts.erase f) = costMCST (vs, ts) + weight e - weight f := by
  have hs := perm_sum_int ((List.perm_cons_erase hf).map weight)
  simp only [List.map_cons, List.sum_cons] at hs
  simp only [costMCST, edges, List.map_cons, List.sum_cons]
  omega

theorem stableWeightSort_iff (input out : List Edge) :
    StableWeightSort input out ↔ Applications.Sorting.StableSort weight input out := by
  constructor
  · rintro ⟨hp, hs, hf⟩
    exact ⟨hs, hp, hf⟩
  · intro h
    exact ⟨h.perm, h.sorted, h.stable⟩

theorem sortEdges_spec (es : List Edge) : StableWeightSort es (sortEdges es) :=
  (stableWeightSort_iff ..).mpr (Applications.Sorting.sortOn_spec weight es)

theorem stableWeightSort_unique {input left right : List Edge}
    (hl : StableWeightSort input left) (hr : StableWeightSort input right) : left = right :=
  ((stableWeightSort_iff ..).mp hl).unique ((stableWeightSort_iff ..).mp hr)

theorem kruskal_source_iff (g t : Graph) : kruskal g = some t ↔ SourceResult g t := by
  unfold kruskal kruskalState
  by_cases hn : nodes g = []
  · simp [hn, SourceResult]
  · rw [ite_eq_right hn, Option.map_eq_some_iff]
    constructor
    · rintro ⟨s, hs, ht⟩
      exact ⟨hn, sortEdges (edges g), s, sortEdges_spec _,
        (applyK_source_iff _ _ _).mp hs, ht.symm⟩
    · rintro ⟨_, sorted, s, hsort, hs, rfl⟩
      have he := stableWeightSort_unique hsort (sortEdges_spec (edges g))
      subst sorted
      exact ⟨s, (applyK_source_iff _ _ _).mpr hs, rfl⟩

private theorem walk_split {vs : List Vertex} {es p q : List Edge} {u v : Vertex}
    (h : Walk vs es u (p ++ q) v) :
    ∃ w, Walk vs es u p w ∧ Walk vs es w q v := by
  induction p generalizing u with
  | nil => exact ⟨u, Walk.nil (walk_vertices h).1, h⟩
  | cons e p ih =>
      cases h with
      | cons he hu hw ho ht =>
          obtain ⟨a, ha, hb⟩ := ih ht
          exact ⟨a, Walk.cons he hu hw ho ha, hb⟩

private theorem walk_members {vs : List Vertex} {es p : List Edge} {u v : Vertex}
    (h : Walk vs es u p v) : p ⊆ es := by
  induction h with
  | nil => simp
  | cons he _ _ _ _ ih =>
      intro f hf
      rcases List.mem_cons.mp hf with rfl | hf
      · exact he
      · exact ih hf

private theorem walk_restrict {vs : List Vertex} {old new p : List Edge} {u v : Vertex}
    (h : Walk vs old u p v) (hsub : p ⊆ new) : Walk vs new u p v := by
  induction h with
  | nil hu => exact Walk.nil hu
  | cons _ hu hw ho _ ih =>
      exact Walk.cons (hsub (by simp)) hu hw ho
        (ih (fun _ hm => hsub (List.mem_cons_of_mem _ hm)))

/-- Repeated edges can be removed by joining the matching undirected endpoints.
This proof transforms a witness only; the Kruskal executor never searches paths. -/
private theorem walk_nodup {vs : List Vertex} {es p : List Edge} {u v : Vertex}
    (h : Walk vs es u p v) : ∃ q, Walk vs es u q v ∧ q.Nodup := by
  induction h with
  | nil hu => exact ⟨[], Walk.nil hu, by simp⟩
  | @cons u w v e p he hu hw ho ht ih =>
      obtain ⟨q, hq, hn⟩ := ih
      by_cases hm : e ∈ q
      · obtain ⟨pre, post, rfl⟩ := List.mem_iff_append.mp hm
        have hnt : (e :: post).Nodup := (List.nodup_append.mp hn).2.1
        obtain ⟨a, _, ha⟩ := walk_split hq
        cases ha with
        | cons _ ha hb hf hp =>
            rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
              rcases hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
            · exact ⟨e :: post, Walk.cons he hu hw (Or.inl ⟨rfl, rfl⟩) hp, hnt⟩
            · exact ⟨post, hp, hnt.tail⟩
            · exact ⟨post, hp, hnt.tail⟩
            · exact ⟨e :: post, Walk.cons he hu hw (Or.inr ⟨rfl, rfl⟩) hp, hnt⟩
      · exact ⟨e :: q, Walk.cons he hu hw ho hq, List.nodup_cons.mpr ⟨hm, hn⟩⟩

private theorem walk_connects_by {vs : List Vertex} {es other p : List Edge} {u v : Vertex}
    (h : Walk vs es u p v)
    (hedges : ∀ e ∈ p, Reach vs other (source e) (target e)) : Reach vs other u v := by
  induction h with
  | nil hu => exact reach_refl hu
  | @cons u w v e p _ _ _ ho _ ih =>
      have he := hedges e (by simp)
      have hh := ih (fun e hm => hedges e (List.mem_cons_of_mem _ hm))
      apply reach_trans _ hh
      rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact he
      · exact reach_symm he

private theorem walk_avoids {vs : List Vertex} {es p : List Edge} {u v : Vertex}
    (h : Walk vs es u p v) {f : Edge} (hf : f ∉ p) :
    Reach vs (es.erase f) u v := by
  apply (reach_iff_walk _ _ _ _).mpr
  refine ⟨p, walk_restrict h ?_⟩
  intro e he
  have hne : e ≠ f := fun hh => hf (hh ▸ he)
  exact (List.mem_erase_of_ne hne).mpr (walk_members h he)

private theorem tree_path_edge_cut {vs : List Vertex} {ts p : List Edge} {a b : Vertex}
    (ht : EdgeForest vs ts) (hp : Walk vs ts a p b) (hn : p.Nodup)
    {f : Edge} (hf : f ∈ p) :
    ¬ Reach vs (ts.erase f) a b ∧
      ∃ c d, ((c = source f ∧ d = target f) ∨ (c = target f ∧ d = source f)) ∧
        Reach vs (ts.erase f) a c ∧ Reach vs (ts.erase f) d b := by
  obtain ⟨pre, post, rfl⟩ := List.mem_iff_append.mp hf
  have hpre : f ∉ pre := by
    intro hm
    exact (List.nodup_append.mp hn).2.2 f hm f (by simp) rfl
  have hpost : f ∉ post := (List.nodup_cons.mp (List.nodup_append.mp hn).2.1).1
  obtain ⟨c, hc, hd⟩ := walk_split hp
  cases hd with
  | cons hfm _ _ ho hd =>
      have ra := walk_avoids hc hpre
      have rb := walk_avoids hd hpost
      refine ⟨?_, ⟨_, _, ho, ra, rb⟩⟩
      intro hr
      have hcd := reach_trans (reach_symm ra) (reach_trans hr (reach_symm rb))
      apply ht.2.2.2 f hfm
      rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hcd
      · exact reach_symm hcd

/-- Exchange within one component suffices; the ambient graph need not be connected. -/
theorem forest_exchange {vs : List Vertex} {fs ts : List Edge} {e : Edge}
    (hf : EdgeForest vs fs) (ht : EdgeForest vs ts) (hsub : fs⊆ts)
    (hu : source e∈vs) (hv : target e∈vs)
    (hcross : ¬Reach vs fs (source e) (target e))
    (hjoin : Reach vs ts (source e) (target e)) :
    ∃f,f∈ts ∧ f∉fs ∧ ¬Reach vs fs (source f) (target f) ∧
      EdgeForest vs (e::ts.erase f) ∧
      (∀u v,Reach vs (e::ts.erase f) u v ↔ Reach vs ts u v) ∧ fs⊆ts.erase f := by
  obtain ⟨p,hp⟩ := (reach_iff_walk _ _ _ _).mp hjoin
  obtain ⟨q,hq,hn⟩ := walk_nodup hp
  have hex : ∃f∈q,¬Reach vs fs (source f) (target f) := by
    classical
    by_cases hh : ∃f∈q,¬Reach vs fs (source f) (target f)
    · exact hh
    · apply False.elim
      apply hcross
      apply walk_connects_by hq
      intro f hm
      by_cases hr : Reach vs fs (source f) (target f)
      · exact hr
      · exact False.elim (hh ⟨f,hm,hr⟩)
  obtain ⟨f,hfm,hfcross⟩ := hex
  have hft : f∈ts := walk_members hq hfm
  have hff : f∉fs := fun hm => hfcross (reach_edge hm (hf.2.1 f hm).1 (hf.2.1 f hm).2)
  obtain ⟨hcut,c,d,ho,ra,rb⟩ := tree_path_edge_cut ht hq hn hfm
  have subrest : ts.erase f⊆e::ts.erase f := fun _ hm => List.mem_cons_of_mem e hm
  have hcd : Reach vs (e::ts.erase f) c d :=
    reach_trans (reach_symm (reach_mono subrest ra))
      (reach_trans (reach_edge (by simp) hu hv) (reach_symm (reach_mono subrest rb)))
  have hnewf : Reach vs (e::ts.erase f) (source f) (target f) := by
    rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact hcd
    · exact reach_symm hcd
  refine ⟨f,hft,hff,hfcross,?_,?_,?_⟩
  · exact (forest_cons_iff _ _ _).mpr ⟨forest_erase ht f,hu,hv,hcut⟩
  · intro u v
    constructor
    · apply reach_of_edges
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact hjoin
      · have hm := List.mem_of_mem_erase ha
        exact reach_edge hm (ht.2.1 a hm).1 (ht.2.1 a hm).2
    · apply reach_of_edges
      intro a ha
      by_cases he : a=f
      · simpa [he] using hnewf
      · exact reach_edge (subrest ((List.mem_erase_of_ne he).mpr ha))
          (ht.2.1 a ha).1 (ht.2.1 a ha).2
  · intro a ha
    exact (List.mem_erase_of_ne (fun (he : a=f) => hff (he ▸ ha))).mpr (hsub ha)

theorem cut_exchange {vs : List Vertex} {fs ts : List Edge} {e : Edge}
    (hf : EdgeForest vs fs) (ht : SpanningEdges vs ts) (hsub : fs ⊆ ts)
    (hu : source e ∈ vs) (hv : target e ∈ vs)
    (hcross : ¬ Reach vs fs (source e) (target e)) :
    ∃ f, f ∈ ts ∧ f ∉ fs ∧ ¬ Reach vs fs (source f) (target f) ∧
      SpanningEdges vs (e :: ts.erase f) ∧ fs ⊆ ts.erase f := by
  obtain ⟨f, hfmem, hfout, hfcross, hforest, hreach, hkeep⟩ :=
    forest_exchange hf ht.2.1 hsub hu hv hcross (ht.2.2 _ hu _ hv)
  exact ⟨f, hfmem, hfout, hfcross,
    ⟨ht.1, hforest, fun u hu v hv => (hreach u v).mpr (ht.2.2 u hu v hv)⟩, hkeep⟩

private theorem head_member {xs : List Vertex} {a : Vertex} (h : xs.head? = some a) : a ∈ xs :=
  Connectivity.ListPartition.head_member h

private theorem partition_vertex {vs : List Vertex} {ds : DS} (h : IsPartitionOf vs ds)
    {a : Name} {xs : List Vertex} (hx : (a, xs) ∈ ds) {u : Vertex} (hu : u ∈ xs) : u ∈ vs := by
  apply h.2.1.mem_iff.mp
  exact List.mem_flatten.mpr ⟨xs, List.mem_map.mpr ⟨(a, xs), hx, rfl⟩, hu⟩

private theorem partition_find {vs : List Vertex} {ds : DS} (h : IsPartitionOf vs ds)
    {u : Vertex} (hu : u ∈ vs) : ∃ a, findDS ds u = some a :=
  (Connectivity.ListPartition.findDS_defined_iff ds u).mpr (h.2.1.mem_iff.mpr hu)

private theorem find_isName {vs : List Vertex} {ds : DS} (h : IsPartitionOf vs ds)
    {u : Vertex} {a : Name} (hu : findDS ds u = some a) : IsName ds a := by
  obtain ⟨xs, hx, _⟩ := (Connectivity.ListPartition.findDS_partition_iff h u a).mp hu
  exact List.mem_map.mpr ⟨(a, xs), hx, rfl⟩

private theorem find_sameBlock {vs : List Vertex} {ds : DS} (h : IsPartitionOf vs ds)
    {u : Vertex} {a : Name} (hu : findDS ds u = some a) : SameBlock ds u a := by
  obtain ⟨xs, hx, hm⟩ := (Connectivity.ListPartition.findDS_partition_iff h u a).mp hu
  exact ⟨a, xs, hx, hm, head_member (h.2.2 a xs hx)⟩

private theorem sameBlock_symm {ds : DS} {u v : Vertex} (h : SameBlock ds u v) :
    SameBlock ds v u :=
  Connectivity.ListPartition.sameBlock_symm h

private theorem sameBlock_trans {vs : List Vertex} {ds : DS} (h : IsPartitionOf vs ds)
    {u v w : Vertex} (hu : SameBlock ds u v) (hv : SameBlock ds v w) : SameBlock ds u w :=
  (Connectivity.ListPartition.sameBlock_equivalence_on h).2.2.1 u v w hu hv

private theorem sameBlock_to_name {vs : List Vertex} {ds : DS} (h : IsPartitionOf vs ds)
    {u : Vertex} {a : Name} (hu : findDS ds u = some a) (v : Vertex) :
    SameBlock ds v a ↔ SameBlock ds v u := by
  have hm := find_sameBlock h hu
  exact ⟨fun hv => sameBlock_trans h hv (sameBlock_symm hm), fun hv => sameBlock_trans h hv hm⟩

private theorem sameBlock_from_name {vs : List Vertex} {ds : DS} (h : IsPartitionOf vs ds)
    {u : Vertex} {a : Name} (hu : findDS ds u = some a) (v : Vertex) :
    SameBlock ds a v ↔ SameBlock ds u v := by
  have hm := find_sameBlock h hu
  exact ⟨fun hv => sameBlock_trans h hm hv, fun hv => sameBlock_trans h (sameBlock_symm hm) hv⟩

theorem state_find_iff_connected {vs : List Vertex} {s : StateDS} (hs : StateRep vs s)
    {u v : Vertex} (hu : u ∈ vs) (hv : v ∈ vs) :
    (findDS (components s) u = findDS (components s) v) ↔ Reach vs (selected s) u v :=
  (Connectivity.ListPartition.findDS_equal_iff_sameBlock hs.1 hu hv).trans (hs.2.2 u v)

private theorem merge_rep {vs : List Vertex} {ds out : DS} {fs es rest : List Edge}
    {e : Edge} {a b : Name} (hs : StateRep vs (ds, fs, es))
    (hu : source e ∈ vs) (hv : target e ∈ vs)
    (ha : findDS ds (source e) = some a) (hb : findDS ds (target e) = some b)
    (hne : a ≠ b) (hunion : unionDS a b ds = some out) : StateRep vs (out, e :: fs, rest) := by
  have hna := find_isName hs.1 ha
  have hnb := find_isName hs.1 hb
  have hcross : ¬ Reach vs fs (source e) (target e) := by
    intro hr
    have he := (state_find_iff_connected hs hu hv).mpr hr
    exact hne (Option.some.inj (ha.symm.trans (he.trans hb)))
  refine ⟨Connectivity.ListPartition.unionDS_partition hs.1 hna hnb hne hunion,
    (forest_cons_iff _ _ _).mpr ⟨hs.2.1, hu, hv, hcross⟩, ?_⟩
  intro u v
  change SameBlock out u v ↔ Reach vs (e :: fs) u v
  rw [Connectivity.ListPartition.unionDS_sameBlock_iff hs.1 hna hnb hne hunion u v]
  rw [sameBlock_to_name hs.1 ha u, sameBlock_from_name hs.1 hb v,
    sameBlock_to_name hs.1 hb u, sameBlock_from_name hs.1 ha v]
  rw [hs.2.2 u v, hs.2.2 u (source e), hs.2.2 (target e) v,
    hs.2.2 u (target e), hs.2.2 (source e) v]
  exact (reach_cons_iff hu hv u v).symm

private theorem partition_length_pos {vs : List Vertex} {ds : DS}
    (h : IsPartitionOf vs ds) (hn : vs ≠ []) : 0 < ds.length := by
  cases ds with
  | nil =>
      have hp : ([] : List Vertex).Perm vs := by simpa [Connectivity.ListPartition.carrier] using h.2.1
      exact False.elim (hn hp.nil_eq.symm)
  | cons _ _ => simp

private theorem partition_one_iff {vs : List Vertex} {ds : DS}
    (h : IsPartitionOf vs ds) (hn : vs ≠ []) :
    ds.length = 1 ↔ ∀ u ∈ vs, ∀ v ∈ vs, SameBlock ds u v := by
  constructor
  · intro hl
    obtain ⟨⟨a, xs⟩, rfl⟩ := List.length_eq_one_iff.mp hl
    intro u hu v hv
    have hcu := h.2.1.mem_iff.mpr hu
    have hcv := h.2.1.mem_iff.mpr hv
    refine ⟨a, xs, by simp, ?_, ?_⟩
    · simpa [Connectivity.ListPartition.carrier] using hcu
    · simpa [Connectivity.ListPartition.carrier] using hcv
  · intro hall
    cases ds with
    | nil => have hh := partition_length_pos h hn; simp at hh
    | cons b bs =>
      cases bs with
      | nil => rfl
      | cons c cs =>
        have hb : (b.1, b.2) ∈ b :: c :: cs := by simp
        have hc : (c.1, c.2) ∈ b :: c :: cs := by simp
        have hbm := head_member (h.2.2 b.1 b.2 hb)
        have hcm := head_member (h.2.2 c.1 c.2 hc)
        have hbv := partition_vertex h hb hbm
        have hcv := partition_vertex h hc hcm
        have hfb := (Connectivity.ListPartition.findDS_partition_iff h b.1 b.1).mpr ⟨b.2, hb, hbm⟩
        have hfc := (Connectivity.ListPartition.findDS_partition_iff h c.1 c.1).mpr ⟨c.2, hc, hcm⟩
        have he := (Connectivity.ListPartition.findDS_equal_iff_sameBlock h hbv hcv).mpr
          (hall b.1 hbv c.1 hcv)
        have hbc : b.1 = c.1 := Option.some.inj (hfb.symm.trans (he.trans hfc))
        have hnames := Connectivity.ListPartition.partition_names_nodup h
        have hnmem := (List.nodup_cons.mp hnames).1
        exact False.elim (hnmem (by simp [hbc]))

private theorem reach_nil_iff (vs : List Vertex) (u v : Vertex) :
    Reach vs [] u v ↔ u = v ∧ u ∈ vs :=
  Connectivity.ListPartition.connected_nil_iff vs u v

private theorem carrier_singletons (vs : List Vertex) :
    Connectivity.ListPartition.carrier (vs.map (fun v => (v, [v]))) = vs :=
  Connectivity.ListPartition.carrier_singletons vs

private theorem singletons_rep (vs ws : List Vertex) (hp : ws.Perm vs) (hn : vs.Nodup)
    (rest : List Edge) : StateRep vs (ws.map (fun v => (v, [v])), [], rest) := by
  have hpart : IsPartitionOf vs (ws.map (fun v => (v, [v]))) := by
    refine ⟨hn, ?_, ?_⟩
    · rw [carrier_singletons]
      exact hp
    · intro a xs hm
      obtain ⟨v, _, he⟩ := List.mem_map.mp hm
      cases he
      rfl
  refine ⟨hpart, forest_nil hn, ?_⟩
  intro u v
  constructor
  · rintro ⟨a, xs, hm, hu, hv⟩
    obtain ⟨w, hw, he⟩ := List.mem_map.mp hm
    have hwa : w = a := congrArg Prod.fst he
    have hxs : [w] = xs := congrArg Prod.snd he
    subst a
    subst xs
    have huu : u = w := List.mem_singleton.mp hu
    have hvv : v = w := List.mem_singleton.mp hv
    subst u
    subst v
    exact reach_refl (hp.mem_iff.mp hw)
  · intro hr
    obtain ⟨rfl, hu⟩ := (reach_nil_iff vs u v).mp hr
    exact ⟨u, [u], List.mem_map.mpr ⟨u, hp.mem_iff.mpr hu, rfl⟩, by simp, by simp⟩

/-- Existence of a finite partition representing an independent forest is used
only in the cardinality proof; it is not part of the Kruskal executable. -/
private theorem forest_partition_exists {vs : List Vertex} {es : List Edge}
    (hf : EdgeForest vs es) :
    ∃ ds, StateRep vs (ds, es, []) ∧ ds.length + es.length = vs.length := by
  induction es with
  | nil =>
      exact ⟨vs.map (fun v => (v, [v])), singletons_rep vs vs (List.Perm.refl _) hf.1 [], by simp⟩
  | cons e es ih =>
      have hh := (forest_cons_iff vs e es).mp hf
      obtain ⟨ds, hs, hlen⟩ := ih hh.1
      obtain ⟨a, ha⟩ := partition_find hs.1 hh.2.1
      obtain ⟨b, hb⟩ := partition_find hs.1 hh.2.2.1
      change findDS ds (source e) = some a at ha
      change findDS ds (target e) = some b at hb
      have hne : a ≠ b := by
        intro he
        have hfind : findDS ds (source e) = findDS ds (target e) := by rw [ha, hb, he]
        exact hh.2.2.2 ((state_find_iff_connected hs hh.2.1 hh.2.2.1).mp hfind)
      have hna := find_isName hs.1 ha
      have hnb := find_isName hs.1 hb
      obtain ⟨out, ho⟩ := (Connectivity.ListPartition.unionDS_defined_iff a b ds).mpr ⟨hna, hnb⟩
      refine ⟨out, merge_rep hs hh.2.1 hh.2.2.1 ha hb hne ho, ?_⟩
      have hc := Connectivity.ListPartition.unionDS_block_count hs.1 hna hnb hne ho
      change out.length + 1 = ds.length at hc
      simp only [List.length_cons]
      omega

theorem forest_cardinality_bound {vs : List Vertex} {es : List Edge}
    (hn : vs ≠ []) (hf : EdgeForest vs es) : es.length + 1 ≤ vs.length := by
  obtain ⟨ds, hs, he⟩ := forest_partition_exists hf
  have hp := partition_length_pos hs.1 hn
  change 0 < ds.length at hp
  omega

theorem spanning_edges_length {vs : List Vertex} {es : List Edge}
    (ht : SpanningEdges vs es) : es.length + 1 = vs.length := by
  obtain ⟨ds, hs, he⟩ := forest_partition_exists ht.2.1
  have hc : ds.length = 1 := (partition_one_iff hs.1 ht.1).mpr
    (fun u hu v hv => (hs.2.2 u v).mpr (ht.2.2 u hu v hv))
  omega

theorem start_invariant {g : Graph} (hg : NumberedGraph g) : KInvariant g (startK g) := by
  have hn := hg.2.1.symm.nodup (Connectivity.ListPartition.startDS_partition (Int.ofNat (nodes g).length)).1
  have hr := singletons_rep (nodes g)
    (Connectivity.ListPartition.vertices (Int.ofNat (nodes g).length)) hg.2.1.symm hn (sortEdges (edges g))
  refine ⟨hr, [], rfl, by simp [selected, startK], by simp⟩

private theorem singleton_step_union {ds out : DS} {fs : List Edge} {e : Edge}
    (h : SourceStep (ds, fs, [e]) (out, e :: fs, [])) :
    ∃ a b, findDS ds (source e) = some a ∧ findDS ds (target e) = some b ∧
      a ≠ b ∧ unionDS a b ds = some out := by
  cases h with
  | take ha hb hn hx hy =>
      exact ⟨_, _, (Connectivity.ListPartition.findDS_first_iff _ _ _).mpr ha,
        (Connectivity.ListPartition.findDS_first_iff _ _ _).mpr hb, hn,
        (Connectivity.ListPartition.unionDS_eq_some_iff _ _ _ _).mpr ⟨_, _, hx, hy, rfl⟩⟩
  | skip _ _ ht =>
      have hh := sourceStep_value ht
      simp [gstepK2] at hh

private theorem find_vertex {vs : List Vertex} {ds : DS} {v a : Vertex}
    (h : IsPartitionOf vs ds) (hf : findDS ds v = some a) : v ∈ vs := by
  obtain ⟨xs, hm, hv⟩ := (Connectivity.ListPartition.findDS_partition_iff h v a).mp hf
  exact partition_vertex h hm hv

private theorem same_find_reach {vs : List Vertex} {s : StateDS} {u v a : Vertex}
    (hs : StateRep vs s) (hu : findDS (components s) u = some a)
    (hv : findDS (components s) v = some a) : Reach vs (selected s) u v :=
  (state_find_iff_connected hs (find_vertex hs.1 hu) (find_vertex hs.1 hv)).mp
    (hu.trans hv.symm)

private theorem invariant_rest_subset {g : Graph} {s : StateDS} (hs : KInvariant g s) :
    remaining s ⊆ edges g := by
  obtain ⟨pre, he, _, _⟩ := hs.2
  intro e hm
  apply (sortEdges_spec (edges g)).1.mem_iff.mp
  rw [he]
  exact List.mem_append.mpr (Or.inr hm)

private theorem invariant_selected_subset {g : Graph} {s : StateDS}
    (hs : KInvariant g s) : selected s ⊆ edges g := by
  obtain ⟨pre, he, hp, _⟩ := hs.2
  intro e hm
  apply (sortEdges_spec (edges g)).1.mem_iff.mp
  rw [he]
  exact List.mem_append.mpr (Or.inl (hp.subset (List.mem_reverse.mpr hm)))

private theorem invariant_rest_endpoints {g : Graph} {s : StateDS}
    (hg : NumberedGraph g) (hs : KInvariant g s) : EndpointsIn (nodes g) (remaining s) :=
  fun e hm => hg.2.2 e (invariant_rest_subset hs hm)

theorem gstepK2_invariant {g : Graph} {s out : StateDS}
    (hg : NumberedGraph g) (hs : KInvariant g s) (hstep : gstepK2 s = some out) :
    KInvariant g out := by
  rcases s with ⟨ds, fs, es⟩
  obtain ⟨skip, e, rest, dsNext, hes, rfl, hskip, hsingle⟩ :=
    gstepK2_consumed_prefix hstep
  obtain ⟨a, b, ha, hb, hn, hu⟩ := singleton_step_union hsingle
  have he : e ∈ es := by simp [hes]
  have hev := invariant_rest_endpoints hg hs e he
  have hr := merge_rep hs.1 hev.1 hev.2 ha hb hn hu (rest := rest)
  obtain ⟨pre, hpre, hsub, hdone⟩ := hs.2
  refine ⟨hr, pre ++ skip ++ [e], ?_, ?_, ?_⟩
  · change sortEdges (edges g) = (pre ++ skip ++ [e]) ++ rest
    change sortEdges (edges g) = pre ++ es at hpre
    rw [hpre, hes]
    simp only [List.append_assoc, List.singleton_append]
  · change (e :: fs).reverse.Sublist (pre ++ skip ++ [e])
    rw [List.reverse_cons]
    exact (List.sublist_append_of_sublist_left hsub).append_right [e]
  · intro f hf
    change Reach (nodes g) (e :: fs) (source f) (target f)
    simp only [List.mem_append, List.mem_singleton] at hf
    rcases hf with (hf | hf) | rfl
    · exact reach_mono (fun _ hm => List.mem_cons_of_mem e hm) (hdone f hf)
    · obtain ⟨c, hfc, htc⟩ := hskip f hf
      exact reach_mono (fun _ hm => List.mem_cons_of_mem e hm)
        (same_find_reach hs.1
          ((Connectivity.ListPartition.findDS_first_iff _ _ _).mpr hfc)
          ((Connectivity.ListPartition.findDS_first_iff _ _ _).mpr htc))
    · exact reach_edge (by simp) hev.1 hev.2

theorem gstepK2_sizes {g : Graph} {s out : StateDS}
    (hs : KInvariant g s) (hstep : gstepK2 s = some out) :
    (selected out).length = (selected s).length + 1 ∧
    (components out).length + 1 = (components s).length ∧
    (remaining out).length < (remaining s).length := by
  rcases s with ⟨ds, fs, es⟩
  obtain ⟨skip, e, rest, dsNext, hes, rfl, _, hsingle⟩ := gstepK2_consumed_prefix hstep
  obtain ⟨a, b, ha, hb, hn, hu⟩ := singleton_step_union hsingle
  have hcount := Connectivity.ListPartition.unionDS_block_count hs.1.1
    (find_isName hs.1.1 ha) (find_isName hs.1.1 hb) hn hu
  refine ⟨rfl, hcount, ?_⟩
  change rest.length < es.length
  rw [hes, List.length_append, List.length_cons]
  omega

theorem gstepK2_defined_iff_crossing_rest {vs : List Vertex} {s : StateDS}
    (hs : StateRep vs s) (he : EndpointsIn vs (remaining s)) :
    (∃ out, gstepK2 s = some out) ↔
      ∃ e ∈ remaining s, ¬ Reach vs (selected s) (source e) (target e) := by
  rcases s with ⟨ds, fs, es⟩
  induction es with
  | nil => simp [gstepK2, remaining]
  | cons e es ih =>
      have hev := he e (by simp [remaining])
      have het : EndpointsIn vs es := fun f hf => he f (List.mem_cons_of_mem e hf)
      have hst : StateRep vs (ds, fs, es) := hs
      obtain ⟨a, ha⟩ := partition_find hs.1 hev.1
      obtain ⟨b, hb⟩ := partition_find hs.1 hev.2
      change findDS ds (source e) = some a at ha
      change findDS ds (target e) = some b at hb
      by_cases hn : a = b
      · subst b
        have hcon := same_find_reach hs ha hb
        rw [gstepK2_skip ha hb, ih hst het]
        change (∃ f ∈ es, ¬ Reach vs fs (source f) (target f)) ↔
          ∃ f ∈ e :: es, ¬ Reach vs fs (source f) (target f)
        constructor
        · rintro ⟨f, hf, hc⟩
          exact ⟨f, List.mem_cons_of_mem e hf, hc⟩
        · rintro ⟨f, hf, hc⟩
          rcases List.mem_cons.mp hf with rfl | hf
          · exact False.elim (hc hcon)
          · exact ⟨f, hf, hc⟩
      · have hcross : ¬ Reach vs fs (source e) (target e) := by
          intro hc
          have hf := (state_find_iff_connected hs hev.1 hev.2).mpr hc
          exact hn (Option.some.inj (ha.symm.trans (hf.trans hb)))
        obtain ⟨out, ho⟩ := (Connectivity.ListPartition.unionDS_defined_iff a b ds).mpr
          ⟨find_isName hs.1 ha, find_isName hs.1 hb⟩
        constructor
        · intro _
          exact ⟨e, by simp [remaining], hcross⟩
        · intro _
          exact ⟨_, gstepK2_take ha hb hn ho⟩

theorem invariant_crossing_weight {g : Graph} {s : StateDS} {dsNext : DS}
    {e : Edge} {rest : List Edge} (hs : KInvariant g s)
    (hstep : gstepK2 s = some (dsNext, e :: selected s, rest)) :
    ∀ f ∈ edges g, ¬ Reach (nodes g) (selected s) (source f) (target f) →
      weight e ≤ weight f := by
  rcases s with ⟨ds, fs, es⟩
  obtain ⟨skip, chosen, tail, out, hes, hout, hskip, _⟩ := gstepK2_consumed_prefix hstep
  have hchosen : chosen = e := (List.cons.inj (congrArg (fun s : StateDS => s.2.1) hout)).1.symm
  subst chosen
  obtain ⟨pre, hpre, _, hdone⟩ := hs.2
  change sortEdges (edges g) = pre ++ es at hpre
  have hsorted := (sortEdges_spec (edges g)).2.1
  rw [hpre, hes] at hsorted
  have htail : (e :: tail).Pairwise (fun a b => weight a ≤ weight b) :=
    (List.pairwise_append.mp (List.pairwise_append.mp hsorted).2.1).2.1
  intro f hf hcross
  have hm := (sortEdges_spec (edges g)).1.mem_iff.mpr hf
  rw [hpre, hes] at hm
  rcases List.mem_append.mp hm with hm | hm
  · exact False.elim (hcross (hdone f hm))
  · rcases List.mem_append.mp hm with hm | hm
    · obtain ⟨a, ha, hb⟩ := hskip f hm
      exact False.elim (hcross (same_find_reach hs.1
        ((Connectivity.ListPartition.findDS_first_iff _ _ _).mpr ha)
        ((Connectivity.ListPartition.findDS_first_iff _ _ _).mpr hb)))
    · rcases List.mem_cons.mp hm with rfl | hm
      · exact Int.le_refl _
      · exact (List.pairwise_cons.mp htail).1 f hm

theorem gstepK2_available {g : Graph} {s : StateDS} (hg : NumberedGraph g)
    (hc : ConnectedGraph g) (hs : KInvariant g s) (hm : 1 < (components s).length) :
    ∃ out, gstepK2 s = some out := by
  classical
  apply (gstepK2_defined_iff_crossing_rest hs.1 (invariant_rest_endpoints hg hs)).mpr
  by_cases hx : ∃ e ∈ remaining s, ¬ Reach (nodes g) (selected s) (source e) (target e)
  · exact hx
  · have hr : ∀ e ∈ remaining s, Reach (nodes g) (selected s) (source e) (target e) := by
      intro e he
      by_cases hh : Reach (nodes g) (selected s) (source e) (target e)
      · exact hh
      · exact False.elim (hx ⟨e, he, hh⟩)
    obtain ⟨pre, hp, _, hpre⟩ := hs.2
    have hedge : ∀ e ∈ edges g, Reach (nodes g) (selected s) (source e) (target e) := by
      intro e he
      have hh := (sortEdges_spec (edges g)).1.mem_iff.mpr he
      rw [hp] at hh
      rcases List.mem_append.mp hh with hh | hh
      · exact hpre e hh
      · exact hr e hh
    have hall : ∀ u ∈ nodes g, ∀ v ∈ nodes g,
        SameBlock (components s) u v := by
      intro u hu v hv
      exact (hs.1.2.2 u v).mpr (reach_of_edges hedge (hc u hu v hv))
    have h1 := (partition_one_iff hs.1.1 hg.1).mpr hall
    omega

theorem applyK_invariant_and_sizes {g : Graph} {k : Nat} {out : StateDS}
    (hg : NumberedGraph g) (hrun : applyK k (startK g) = some out) :
    KInvariant g out ∧ (selected out).length = k ∧
      (components out).length + k = (nodes g).length := by
  induction k generalizing out with
  | zero =>
      have he : startK g = out := Option.some.inj hrun
      subst out
      refine ⟨start_invariant hg, rfl, ?_⟩
      simp [components, startK, Connectivity.ListPartition.startDS_length]
  | succ k ih =>
      rw [applyK, Option.bind_eq_some_iff] at hrun
      obtain ⟨middle, hm, ho⟩ := hrun
      obtain ⟨hinv, hsel, hcomp⟩ := ih hm
      obtain ⟨hsel', hcomp', _⟩ := gstepK2_sizes hinv ho
      exact ⟨gstepK2_invariant hg hinv ho, by omega, by omega⟩

theorem applyK_defined {g : Graph} (hg : NumberedGraph g) (hc : ConnectedGraph g)
    (k : Nat) (hk : k ≤ (nodes g).length - 1) :
    ∃ out, applyK k (startK g) = some out := by
  induction k with
  | zero => exact ⟨startK g, rfl⟩
  | succ k ih =>
      obtain ⟨middle, hm⟩ := ih (by omega)
      obtain ⟨hs, _, hl⟩ := applyK_invariant_and_sizes hg hm
      obtain ⟨out, ho⟩ := gstepK2_available hg hc hs (by omega)
      exact ⟨out, by simp only [applyK, hm, Option.bind_some, ho]⟩

private theorem final_state_invariant {g : Graph} {s : StateDS}
    (hg : NumberedGraph g) (h : kruskalState g = some s) :
    KInvariant g s ∧ (components s).length = 1 := by
  have hrun : applyK ((nodes g).length - 1) (startK g) = some s := by
    simpa only [kruskalState, ite_eq_right hg.1] using h
  obtain ⟨hi, _, hc⟩ := applyK_invariant_and_sizes hg hrun
  have hn : 0 < (nodes g).length := List.length_pos_iff.mpr hg.1
  exact ⟨hi, by omega⟩

theorem kruskal_spanning {g t : Graph} (hg : NumberedGraph g)
    (h : kruskal g = some t) : SpanningTree g t := by
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨hi, h1⟩ := final_state_invariant hg hs
  refine ⟨rfl, invariant_selected_subset hi, hg.1, hi.1.2.1, ?_⟩
  intro u hu v hv
  exact (hi.1.2.2 u v).mp ((partition_one_iff hi.1.1 hg.1).mp h1 u hu v hv)

theorem kruskal_defined_iff_connected {g : Graph} (hg : NumberedGraph g) :
    (∃ t, kruskal g = some t) ↔ ConnectedGraph g := by
  constructor
  · rintro ⟨t, ht⟩
    have hs := kruskal_spanning hg ht
    intro u hu v hv
    exact reach_mono hs.2.1 (hs.2.2.2.2 u hu v hv)
  · intro hc
    obtain ⟨s, hs⟩ := applyK_defined hg hc ((nodes g).length - 1) (Nat.le_refl _)
    exact ⟨(nodes g, selected s), by simp only [kruskal, kruskalState, ite_eq_right hg.1,
      hs, Option.map_some]⟩

theorem kruskal_order_and_residual {g : Graph} {s : StateDS}
    (hg : NumberedGraph g) (h : kruskalState g = some s) :
    (components s).length = 1 ∧ ∃ pre, sortEdges (edges g) = pre ++ remaining s ∧
      (selected s).reverse.Sublist pre ∧
      ∀ e ∈ remaining s, Reach (nodes g) (selected s) (source e) (target e) := by
  obtain ⟨hi, h1⟩ := final_state_invariant hg h
  obtain ⟨pre, hp, hsub, _⟩ := hi.2
  refine ⟨h1, pre, hp, hsub, ?_⟩
  intro e he
  have hev := invariant_rest_endpoints hg hi e he
  exact (hi.1.2.2 _ _).mp ((partition_one_iff hi.1.1 hg.1).mp h1
    (source e) hev.1 (target e) hev.2)

theorem gstepK2_at_one_component_none {vs : List Vertex} {s : StateDS}
    (hs : StateRep vs s) (he : EndpointsIn vs (remaining s))
    (h1 : (components s).length = 1) : gstepK2 s = none := by
  cases hh : gstepK2 s with
  | none => rfl
  | some out =>
      obtain ⟨e, hm, hcross⟩ := (gstepK2_defined_iff_crossing_rest hs he).mp ⟨out, hh⟩
      have hev := he e hm
      have hn : vs ≠ [] := by intro hv; simp [hv] at hev
      exact False.elim (hcross ((hs.2.2 _ _).mp
        ((partition_one_iff hs.1 hn).mp h1 _ hev.1 _ hev.2)))

theorem exchangeInv_nil (g : Graph) : ExchangeInv g [] := by
  intro t ht
  exact ⟨t, ht, by simp, Int.le_refl _⟩

theorem exchangeInv_step {g : Graph} {s out : StateDS} (hg : NumberedGraph g)
    (hs : KInvariant g s) (hx : ExchangeInv g (selected s))
    (hstep : gstepK2 s = some out) : ExchangeInv g (selected out) := by
  classical
  rcases s with ⟨ds, fs, es⟩
  obtain ⟨skip, e, rest, dsNext, _, rfl, _, _⟩ := gstepK2_consumed_prefix hstep
  have hi := gstepK2_invariant hg hs hstep
  have hh := (forest_cons_iff (nodes g) e fs).mp hi.1.2.1
  have he : e ∈ edges g := invariant_selected_subset hi (by simp [selected])
  intro t ht
  obtain ⟨r, hr, hsub, hcost⟩ := hx t ht
  by_cases hem : e ∈ edges r
  · refine ⟨r, hr, ?_, hcost⟩
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact hem
    · exact hsub hf
  · obtain ⟨f, hf, _, hcross, hspan, hkeep⟩ := cut_exchange hs.1.2.1 hr.2.2 hsub
      hh.2.1 hh.2.2.1 hh.2.2.2
    refine ⟨(nodes g, e :: (edges r).erase f), ?_, ?_, ?_⟩
    · refine ⟨rfl, ?_, hspan⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact he
      · exact hr.2.1 (List.mem_of_mem_erase ha)
    · intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem e (hkeep ha)
    · have hw : weight e ≤ weight f :=
        invariant_crossing_weight hs hstep f (hr.2.1 hf) hcross
      have hformula := exchange_cost_identity (nodes g) (edges r) e f hf
      calc
        costMCST (nodes g, e :: (edges r).erase f) =
            costMCST (nodes g, edges r) + weight e - weight f := hformula
        _ ≤ costMCST (nodes g, edges r) := by
          have hp := Int.sub_le_sub_right
            (Int.add_le_add_left hw (costMCST (nodes g, edges r))) (weight f)
          simpa only [Int.add_sub_cancel] using hp
        _ = costMCST r := rfl
        _ ≤ costMCST t := hcost

theorem exchangeInv_apply {g : Graph} {k : Nat} {s : StateDS}
    (hg : NumberedGraph g) (h : applyK k (startK g) = some s) :
    ExchangeInv g (selected s) := by
  induction k generalizing s with
  | zero =>
      have he : startK g = s := Option.some.inj h
      subst s
      exact exchangeInv_nil g
  | succ k ih =>
      rw [applyK, Option.bind_eq_some_iff] at h
      obtain ⟨middle, hm, hs⟩ := h
      exact exchangeInv_step hg (applyK_invariant_and_sizes hg hm).1 (ih hm) hs

theorem kruskal_minimum {g t : Graph} (hg : NumberedGraph g)
    (h : kruskal g = some t) : MinimumSpanningTree g t := by
  have ht := kruskal_spanning hg h
  obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.mp h
  have hrun : applyK ((nodes g).length - 1) (startK g) = some s := by
    simpa only [kruskalState, ite_eq_right hg.1] using hs
  have hx := exchangeInv_apply hg hrun
  refine ⟨ht, ?_⟩
  intro other ho
  obtain ⟨replacement, hr, hsub, hcost⟩ := hx other ho
  have hp := spanning_subforest_eq_perm ht.2.2 hr.2.2.2.1 hsub
  have heq : costMCST (nodes g, selected s) = costMCST replacement :=
    perm_sum_int (hp.map weight)
  exact Int.le_trans (Int.le_of_eq heq) hcost

theorem kruskal_exists_minimum {g : Graph} (hg : NumberedGraph g)
    (hc : ConnectedGraph g) : ∃ t, kruskal g = some t ∧ MinimumSpanningTree g t := by
  obtain ⟨t, ht⟩ := (kruskal_defined_iff_connected hg).mpr hc
  exact ⟨t, ht, kruskal_minimum hg ht⟩

theorem minimum_cost_eq {g left right : Graph}
    (hl : MinimumSpanningTree g left) (hr : MinimumSpanningTree g right) :
    costMCST left = costMCST right :=
  Int.le_antisymm (hl.2 right hr.1) (hr.2 left hl.1)

theorem perm_input_edges_equal_optimal_value {g1 g2 t1 t2 : Graph}
    (hn : nodes g1 = nodes g2) (he : (edges g1).Perm (edges g2))
    (hg1 : NumberedGraph g1) (hg2 : NumberedGraph g2)
    (h1 : kruskal g1 = some t1) (h2 : kruskal g2 = some t2) :
    costMCST t1 = costMCST t2 := by
  have hm1 := kruskal_minimum hg1 h1
  have hm2 := kruskal_minimum hg2 h2
  have h21 : SpanningTree g1 t2 := by
    refine ⟨hm2.1.1.trans hn.symm, ?_, ?_⟩
    · intro e hm
      exact he.mem_iff.mpr (hm2.1.2.1 hm)
    · rw [hn]
      exact hm2.1.2.2
  have h12 : SpanningTree g2 t1 := by
    refine ⟨hm1.1.1.trans hn, ?_, ?_⟩
    · intro e hm
      exact he.mem_iff.mp (hm1.1.2.1 hm)
    · rw [← hn]
      exact hm1.1.2.2
  exact Int.le_antisymm (hm1.2 t2 h21) (hm2.2 t1 h12)

theorem spanningEdges_perm {vs : List Vertex} {es fs : List Edge}
    (hp : es.Perm fs) (hs : SpanningEdges vs es) : SpanningEdges vs fs :=
  ⟨hs.1, (forest_perm hp).mp hs.2.1,
    fun u hu v hv => reach_mono hp.subset (hs.2.2 u hu v hv)⟩

/-! Public walk and partition interfaces for forest clients. -/

theorem reach_replace_edges {vs : List Vertex} {old new : List Edge}
    (he : ∀e∈old,Reach vs new (source e) (target e)) {u v : Vertex}
    (h : Reach vs old u v) : Reach vs new u v := reach_of_edges he h

theorem walk_vertices_mem {vs : List Vertex} {es path : List Edge} {u v : Vertex}
    (h : Walk vs es u path v) : u∈vs ∧ v∈vs := walk_vertices h

theorem walk_edges_subset {vs : List Vertex} {es path : List Edge} {u v : Vertex}
    (h : Walk vs es u path v) : path⊆es := walk_members h

theorem walk_without_repeated_edges {vs : List Vertex} {es path : List Edge} {u v : Vertex}
    (h : Walk vs es u path v) : ∃q,Walk vs es u q v ∧ q.Nodup := walk_nodup h

theorem walk_avoids_edge {vs : List Vertex} {es path : List Edge} {u v : Vertex}
    (h : Walk vs es u path v) {e : Edge} (he : e∉path) :
    Reach vs (es.erase e) u v := walk_avoids h he

theorem edgeForest_sublist {vs : List Vertex} {es fs : List Edge}
    (hsub : es.Sublist fs) (hf : EdgeForest vs fs) : EdgeForest vs es :=
  forest_sublist hsub hf

theorem reach_empty_iff (vs : List Vertex) (u v : Vertex) :
    Reach vs [] u v ↔ u=v ∧ u∈vs := reach_nil_iff vs u v

theorem singleton_stateRep (vs : List Vertex) (hn : vs.Nodup) (rest : List Edge) :
    StateRep vs (vs.map (fun v => (v,[v])),[],rest) :=
  singletons_rep vs vs (List.Perm.refl _) hn rest

theorem merge_stateRep {vs : List Vertex} {ds out : DS} {fs es rest : List Edge}
    {e : Edge} {a b : Name} (hs : StateRep vs (ds,fs,es))
    (hu : source e∈vs) (hv : target e∈vs)
    (ha : findDS ds (source e)=some a) (hb : findDS ds (target e)=some b)
    (hne : a≠b) (hunion : unionDS a b ds=some out) :
    StateRep vs (out,e::fs,rest) := merge_rep hs hu hv ha hb hne hunion

/-- The existing partition criterion, exposed for the arbitrary-label nested
forest client without duplicating its proof. -/
theorem partition_singleton_iff {vs : List Vertex} {ds : DS}
    (h : IsPartitionOf vs ds) (hn : vs ≠ []) :
    ds.length = 1 ↔ ∀ u ∈ vs, ∀ v ∈ vs, SameBlock ds u v :=
  partition_one_iff h hn

end Kruskal
