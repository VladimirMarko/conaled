import Applications.Prim.Exchange

set_option autoImplicit false
set_option warningAsError true

/-!
Independent correctness of the literal list Prim executor.  A growing tree is
connected on its own visited vertices and acyclic on the whole input carrier.
The residual list is a multiset complement, not an unordered set.  The all-tree
exchange invariant relates each greedy prefix to every independent competitor.
No numbering, positivity or distinct-weight assumption is needed.
-/

namespace Prim.Correctness

open Kruskal Prim.Core Prim.Exchange
open Connectivity.ListPartition (Connected)

structure Growing (vs : List Vertex) (t : Tree) : Prop where
  nonempty : nodes t ≠ []
  nodup : (nodes t).Nodup
  subset : nodes t ⊆ vs
  forest : EdgeForest vs (edges t)
  inside : EndpointsIn (nodes t) (edges t)
  connected : ∀ u ∈ nodes t, ∀ v ∈ nodes t, Reach vs (edges t) u v

structure Invariant (g : Graph) (s : StateP) : Prop where
  growing : Growing (nodes g) s.1
  partition : (chosen s ++ pending s).Perm (edges g)
  sorted : (pending s).Pairwise (fun e f => weight e ≤ weight f)

private theorem safe_not_inside {us : List Vertex} {e : Edge}
    (h : Safe us e) (hi : source e ∈ us ∧ target e ∈ us) : False := by
  rcases h with ⟨_, ht⟩ | ⟨_, hs⟩
  · exact ht hi.2
  · exact hs hi.1

theorem growing_add {vs : List Vertex} {t : Tree} {e : Edge}
    (hg : Growing vs t) (hu : source e ∈ vs) (hv : target e ∈ vs)
    (hs : Safe (nodes t) e) : Growing vs (addP e t) := by
  obtain ⟨v, hvnew, hvlist, hvendpoint⟩ := addP_new_vertex hs
  have hf : EdgeForest vs (e :: edges t) := by
    apply (forest_cons_iff _ _ _).mpr
    refine ⟨hg.forest, hu, hv, ?_⟩
    intro hr
    have hsame := reach_same_side (us := nodes t)
      (fun f hf hsafe => safe_not_inside hsafe (hg.inside f hf)) hr
    exact (safe_exactly_one _ _).mp hs hsame
  have he := (addP_sizes e t).2
  have hsub : edges t ⊆ e :: edges t := fun _ hm => List.mem_cons_of_mem _ hm
  have hnewvs : v ∈ vs := by
    rcases hvendpoint with rfl | rfl
    · exact hu
    · exact hv
  have hnewlink : ∀ a ∈ nodes t, Reach vs (e :: edges t) v a := by
    intro a ha
    rcases hs with ⟨hsource, htarget⟩ | ⟨htarget, hsource⟩
    · have hveq : v = target e := by
        have hh : nodes (addP e t) = target e :: nodes t := by
          rw [addP, ite_eq_left hsource]
          rfl
        exact List.cons.inj (hvlist.symm.trans hh) |>.1
      subst v
      exact Connected.trans (Connected.symm (reach_edge (by simp) hu hv))
        (reach_mono hsub (hg.connected _ hsource a ha))
    · have hveq : v = source e := by
        have hh : nodes (addP e t) = source e :: nodes t := by
          rw [addP, ite_eq_right hsource]
          rfl
        exact List.cons.inj (hvlist.symm.trans hh) |>.1
      subst v
      exact Connected.trans (reach_edge (by simp) hu hv)
        (reach_mono hsub (hg.connected _ htarget a ha))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hvlist]
    simp
  · rw [hvlist]
    exact List.nodup_cons.mpr ⟨hvnew, hg.nodup⟩
  · rw [hvlist]
    exact List.cons_subset.mpr ⟨hnewvs, hg.subset⟩
  · simpa only [he] using hf
  · rw [he]
    intro f hm
    rcases List.mem_cons.mp hm with rfl | hm
    · rcases hs with ⟨hsource, htarget⟩ | ⟨htarget, hsource⟩
      · rw [addP, ite_eq_left hsource]
        exact ⟨List.mem_cons_of_mem _ hsource, List.mem_cons_self⟩
      · rw [addP, ite_eq_right hsource]
        exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ htarget⟩
    · rw [hvlist]
      have hh := hg.inside f hm
      exact ⟨List.mem_cons_of_mem _ hh.1, List.mem_cons_of_mem _ hh.2⟩
  · rw [hvlist, he]
    intro a ha b hb
    rcases List.mem_cons.mp ha with ha | ha
    · subst a
      rcases List.mem_cons.mp hb with hb | hb
      · subst b
        exact Connected.refl hnewvs
      · exact hnewlink b hb
    · rcases List.mem_cons.mp hb with hb | hb
      · subst b
        exact Connected.symm (hnewlink a ha)
      · exact reach_mono hsub (hg.connected a ha b hb)

theorem invariant_chosen_subset {g : Graph} {s : StateP} (h : Invariant g s) :
    chosen s ⊆ edges g := by
  intro e he
  exact h.partition.subset (List.mem_append_left _ he)

theorem invariant_pending_subset {g : Graph} {s : StateP} (h : Invariant g s) :
    pending s ⊆ edges g := by
  intro e he
  exact h.partition.subset (List.mem_append_right _ he)

theorem invariant_safe_pending {g : Graph} {s : StateP} (h : Invariant g s)
    {e : Edge} (he : e ∈ edges g) (hs : Safe (visited s) e) : e ∈ pending s := by
  have hh := List.mem_append.mp (h.partition.mem_iff.mpr he)
  rcases hh with hchosen | hpending
  · exact False.elim (safe_not_inside hs (h.growing.inside e hchosen))
  · exact hpending

theorem branch_invariant {g : Graph} {s out : StateP}
    (hg : EndpointsIn (nodes g) (edges g)) (hs : Invariant g s)
    (hstep : out ∈ stepsP s) : Invariant g out := by
  have hp := step_edge_permutation hstep
  obtain ⟨pre, e, post, he, hsafe, rfl⟩ := (stepsP_members s out).mp hstep
  have hem : e ∈ pending s := by rw [he]; simp
  have hin := hg e (invariant_pending_subset hs hem)
  have hpw := hs.sorted
  rw [he, List.pairwise_append, List.pairwise_cons] at hpw
  refine ⟨growing_add hs.growing hin.1 hin.2 hsafe, hp.trans hs.partition, ?_⟩
  exact List.pairwise_append.mpr
    ⟨hpw.1, hpw.2.1.2, fun a ha b hb => hpw.2.2 a ha b (by simp [hb])⟩

theorem gstepP_invariant {g : Graph} {s out : StateP}
    (hg : EndpointsIn (nodes g) (edges g)) (hs : Invariant g s)
    (hstep : gstepP s = some out) : Invariant g out :=
  branch_invariant hg hs (gstepP_is_branch hstep)

theorem gstepP_defined_iff (s : StateP) :
    (∃ out, gstepP s = some out) ↔ ∃ e ∈ pending s, Safe (visited s) e := by
  rcases s with ⟨t, es⟩
  induction es with
  | nil => simp [gstepP_nil, pending]
  | cons e es ih =>
      by_cases hs : Safe (nodes t) e
      · constructor
        · intro _
          exact ⟨e, List.mem_cons_self, hs⟩
        · intro _
          exact ⟨_, gstepP_take hs⟩
      · rw [gstepP_skip hs]
        constructor
        · rintro ⟨out, ho⟩
          obtain ⟨middle, hm, _⟩ := Option.map_eq_some_iff.mp ho
          obtain ⟨f, hf, hfs⟩ := ih.mp ⟨middle, hm⟩
          exact ⟨f, List.mem_cons_of_mem _ hf, hfs⟩
        · rintro ⟨f, hf, hfs⟩
          rcases List.mem_cons.mp hf with rfl | hf
          · exact False.elim (hs hfs)
          · obtain ⟨middle, hm⟩ := ih.mpr ⟨f, hf, hfs⟩
            exact ⟨(middle.1, e :: middle.2), by rw [hm]; rfl⟩

theorem gstepP_available {g : Graph} {s : StateP}
    (hs : Invariant g s) (hc : ConnectedGraph g)
    (hlt : (visited s).length < (nodes g).length) : ∃ out, gstepP s = some out := by
  have hex : ∃ v ∈ nodes g, v ∉ visited s := by
    classical
    by_cases hex : ∃ v ∈ nodes g, v ∉ visited s
    · exact hex
    · have hsub : nodes g ⊆ visited s := by
        intro v hv
        by_cases hm : v ∈ visited s
        · exact hm
        · exact False.elim (hex ⟨v, hv, hm⟩)
      have hh := List.Nodup.length_le_of_subset hs.growing.forest.1 hsub
      omega
  obtain ⟨v, hv, hvout⟩ := hex
  obtain ⟨u, hu⟩ := List.exists_mem_of_ne_nil (visited s) hs.growing.nonempty
  have hconn := hc u (hs.growing.subset hu) v hv
  have hsafe : Safe (visited s) (u, v, 0) := Or.inl ⟨hu, hvout⟩
  obtain ⟨e, he, hse⟩ := reach_crossing (e := (u, v, 0)) hconn hsafe
  exact (gstepP_defined_iff s).mpr ⟨e, invariant_safe_pending hs he hse, hse⟩

theorem initial_invariant {g : Graph} {v : Vertex}
    (hn : (nodes g).Nodup) (hv : v ∈ nodes g) :
    Invariant g (([v], []), sortEdges (edges g)) := by
  have hsort := sortEdges_spec (edges g)
  refine ⟨⟨by simp [nodes], by simp [nodes], ?_, forest_nil hn, ?_, ?_⟩,
    ?_, hsort.2.1⟩
  · simpa [nodes] using hv
  · intro e he
    simp [edges] at he
  · intro a ha b hb
    have hae : a = v := by simpa [nodes] using ha
    have hbe : b = v := by simpa [nodes] using hb
    subst a
    subst b
    exact Connected.refl hv
  · simpa [chosen, pending, edges] using hsort.1

theorem startP_invariant {g : Graph} {s : StateP} (hn : (nodes g).Nodup)
    (h : startP g = some s) : Invariant g s ∧ (visited s).length = 1 := by
  obtain ⟨v, hv, he⟩ := Option.map_eq_some_iff.mp h
  subst s
  exact ⟨initial_invariant hn (List.mem_of_head? hv), rfl⟩

theorem applyP_invariant {g : Graph} {s out : StateP} {k : Nat}
    (hg : EndpointsIn (nodes g) (edges g)) (hs : Invariant g s)
    (h : applyP k s = some out) : Invariant g out := by
  induction k generalizing s with
  | zero => cases Option.some.inj h; exact hs
  | succ k ih =>
      obtain ⟨middle, hm, ho⟩ := Option.bind_eq_some_iff.mp h
      exact ih (gstepP_invariant hg hs hm) ho

theorem applyP_available {g : Graph} {s : StateP} {k : Nat}
    (hg : EndpointsIn (nodes g) (edges g)) (hc : ConnectedGraph g)
    (hs : Invariant g s) (hsize : (visited s).length + k ≤ (nodes g).length) :
    ∃ out, applyP k s = some out := by
  induction k generalizing s with
  | zero => exact ⟨s, rfl⟩
  | succ k ih =>
      obtain ⟨middle, hm⟩ := gstepP_available hs hc (by omega)
      have hi := gstepP_invariant hg hs hm
      have hz := (step_sizes (gstepP_is_branch hm)).1
      obtain ⟨out, ho⟩ := ih hi (by omega)
      exact ⟨out, by simp [applyP, hm, ho]⟩

theorem full_invariant_spanning {g : Graph} {s : StateP} (hs : Invariant g s)
    (hsize : (visited s).length = (nodes g).length) : SourceSpanningTree g s.1 := by
  have hback : nodes g ⊆ visited s := by
    intro v hv
    by_cases hm : v ∈ visited s
    · exact hm
    · have hnd : (v :: visited s).Nodup := List.nodup_cons.mpr ⟨hm, hs.growing.nodup⟩
      have hsub : v :: visited s ⊆ nodes g := List.cons_subset.mpr ⟨hv, hs.growing.subset⟩
      have hz := hnd.length_le_of_subset hsub
      simp only [List.length_cons] at hz
      omega
  have hp : (visited s).Perm (nodes g) :=
    (List.perm_ext_iff_of_nodup hs.growing.nodup hs.growing.forest.1).mpr
      (fun _ => ⟨fun hm => hs.growing.subset hm, fun hm => hback hm⟩)
  refine ⟨hp, rfl, invariant_chosen_subset hs, ?_, hs.growing.forest, ?_⟩
  · intro he
    have hz : visited s = [] := List.eq_nil_of_length_eq_zero (by
      have hh := hp.length_eq
      simp only [he, List.length_nil] at hh
      exact hh)
    exact hs.growing.nonempty hz
  · intro u hu v hv
    exact hs.growing.connected u (hp.mem_iff.mpr hu) v (hp.mem_iff.mpr hv)

theorem gstepP_exchange {g : Graph} {s out : StateP}
    (hg : EndpointsIn (nodes g) (edges g)) (hs : Invariant g s)
    (hx : ExchangeInv g (chosen s)) (h : gstepP s = some out) :
    ExchangeInv g (chosen out) := by
  obtain ⟨e, he, hsafe, hem, hleast, _⟩ := gstepP_least hs.sorted h
  rw [he]
  exact exchangeInv_cut_step hs.growing.inside hg (invariant_pending_subset hs hem)
    hsafe (fun f hf hsf => hleast f (invariant_safe_pending hs hf hsf) hsf) hx

theorem applyP_exchange {g : Graph} {s out : StateP} {k : Nat}
    (hg : EndpointsIn (nodes g) (edges g)) (hs : Invariant g s)
    (hx : ExchangeInv g (chosen s)) (h : applyP k s = some out) :
    ExchangeInv g (chosen out) := by
  induction k generalizing s with
  | zero => cases Option.some.inj h; exact hx
  | succ k ih =>
      obtain ⟨middle, hm, ho⟩ := Option.bind_eq_some_iff.mp h
      exact ih (gstepP_invariant hg hs hm) (gstepP_exchange hg hs hx hm) ho

theorem full_exchange_minimum {g : Graph} {s : StateP} (hs : Invariant g s)
    (hx : ExchangeInv g (chosen s))
    (hsize : (visited s).length = (nodes g).length) : SourceMinimum g s.1 := by
  have hsp := full_invariant_spanning hs hsize
  refine ⟨hsp.1, hsp.2, ?_⟩
  intro t ht
  obtain ⟨replacement, hr, hsub, hcost⟩ := hx t ht
  have hp := spanning_subforest_eq_perm hsp.2.2.2 hr.2.2.2.1 hsub
  calc
    costMCST (normalize g s.1) = costMCST (nodes g, edges replacement) := (hp.map weight).sum_eq
    _ = costMCST replacement := rfl
    _ ≤ costMCST t := hcost

theorem prim1_minimum {g t : Graph} (hn : (nodes g).Nodup)
    (hg : EndpointsIn (nodes g) (edges g)) (h : prim1 g = some t) :
    SourceMinimum g t := by
  obtain ⟨out, hout, ht⟩ := Option.map_eq_some_iff.mp h
  obtain ⟨s, hs, hrun⟩ := Option.bind_eq_some_iff.mp hout
  have hi := startP_invariant hn hs
  have ho := applyP_invariant hg hi.1 hrun
  have hx : ExchangeInv g (chosen s) := by
    obtain ⟨v, _, hvs⟩ := Option.map_eq_some_iff.mp hs
    subst s
    exact exchangeInv_nil g
  have hxout := applyP_exchange hg hi.1 hx hrun
  have hz := (applyP_sizes hrun).1
  have hnpos : 0 < (nodes g).length := by
    have hh : (visited s).length ≤ (nodes g).length :=
      List.Nodup.length_le_of_subset hi.1.growing.nodup hi.1.growing.subset
    rw [hi.2] at hh
    omega
  have hm := full_exchange_minimum ho hxout (by omega)
  simpa only [ht] using hm

theorem prim_minimum {g t : Graph} (hn : (nodes g).Nodup)
    (hg : EndpointsIn (nodes g) (edges g)) (h : prim g = some t) :
    SourceMinimum g t := by
  rw [prim_eq_prim1] at h
  exact prim1_minimum hn hg h

theorem prim_exists_minimum {g : Graph} (hn : (nodes g).Nodup)
    (hne : nodes g ≠ []) (hg : EndpointsIn (nodes g) (edges g))
    (hc : ConnectedGraph g) : ∃ t, prim g = some t ∧ SourceMinimum g t := by
  have hhead : ∃ v, (nodes g).head? = some v := by
    cases hvs : nodes g with
    | nil => exact False.elim (hne hvs)
    | cons a as => exact ⟨a, rfl⟩
  obtain ⟨v, hv⟩ := hhead
  have hs : startP g = some (([v], []), sortEdges (edges g)) := by
    simp [startP, hv]
  have hi := initial_invariant hn (List.mem_of_head? hv)
  have hpos := List.length_pos_of_mem (List.mem_of_head? hv)
  obtain ⟨out, hout⟩ := applyP_available hg hc hi (k := (nodes g).length - 1) (by
    change 1 + ((nodes g).length - 1) ≤ (nodes g).length
    omega)
  have hp : prim g = some out.1 := by
    rw [prim_eq_prim1]
    simp [prim1, prim1State, hs, hout]
  exact ⟨out.1, hp, prim_minimum hn hg hp⟩

theorem prim_defined_iff_connected {g : Graph} (hn : (nodes g).Nodup)
    (hne : nodes g ≠ []) (hg : EndpointsIn (nodes g) (edges g)) :
    (∃ t, prim g = some t) ↔ ConnectedGraph g := by
  constructor
  · rintro ⟨t, ht⟩
    have hsp := (prim_minimum hn hg ht).2.1
    intro u hu v hv
    exact reach_mono hsp.2.1 (hsp.2.2.2.2 u hu v hv)
  · intro hc
    obtain ⟨t, ht, _⟩ := prim_exists_minimum hn hne hg hc
    exact ⟨t, ht⟩

end Prim.Correctness
