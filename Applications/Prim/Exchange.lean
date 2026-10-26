import Applications.Prim.Core

set_option autoImplicit false
set_option warningAsError true

/-!
The visited-cut exchange argument for Prim.  Competitors are the independent
`Kruskal.SpanningTree` edge sets, not a generated list.  The chosen edge need only
be a least edge across the actual visited cut.  In particular the argument works
with signed weights, parallel edges and every tie choice.
-/

namespace Prim.Exchange

open Kruskal Prim.Core
open Connectivity.ListPartition (Connected)

/-- No edge across a cut implies that connectivity cannot cross that cut. -/
theorem reach_same_side {vs us : List Vertex} {es : List Edge}
    (he : ∀ e ∈ es, ¬ Safe us e) {u v : Vertex} (h : Reach vs es u v) :
    (u ∈ us ↔ v ∈ us) := by
  induction h with
  | refl _ => rfl
  | edge _ _ hmem =>
      obtain ⟨e, hm, heq⟩ := List.mem_map.mp hmem
      cases heq
      have hh := he e hm
      by_cases hs : source e ∈ us <;> by_cases ht : target e ∈ us <;>
        simp_all [Safe]
  | symm _ ih => exact ih.symm
  | trans _ _ ih ih' => exact ih.trans ih'

/-- Every path between opposite sides contains an edge across the same cut. -/
theorem reach_crossing {vs us : List Vertex} {es : List Edge} {e : Edge}
    (h : Reach vs es (source e) (target e)) (hs : Safe us e) :
    ∃ f ∈ es, Safe us f := by
  classical
  by_cases hnone : ∃ f ∈ es, Safe us f
  · exact hnone
  apply False.elim
  have hnot : ∀ f ∈ es, ¬ Safe us f := by
    intro f hf hsafe
    exact hnone ⟨f, hf, hsafe⟩
  exact (safe_exactly_one us e).mp hs (reach_same_side hnot h)

theorem visited_cut_exchange {vs us : List Vertex} {fs ts : List Edge} {e : Edge}
    (ht : SpanningEdges vs ts) (hsub : fs ⊆ ts)
    (hinside : EndpointsIn us fs) (hu : source e ∈ vs) (hv : target e ∈ vs)
    (hsafe : Safe us e) :
    ∃ f, f ∈ ts ∧ f ∉ fs ∧ Safe us f ∧
      SpanningEdges vs (e :: ts.erase f) ∧ fs ⊆ ts.erase f := by
  obtain ⟨p, hp⟩ := (reach_iff_walk _ _ _ _).mp (ht.2.2 _ hu _ hv)
  obtain ⟨q, hq, hn⟩ := walk_without_repeated_edges hp
  have hqreach : Reach vs q (source e) (target e) :=
    (reach_iff_walk _ _ _ _).mpr ⟨q, walk_restrict hq (fun _ hm => hm)⟩
  obtain ⟨f, hfm, hfcross⟩ := reach_crossing hqreach hsafe
  have hft : f ∈ ts := walk_edges_subset hq hfm
  have hff : f ∉ fs := by
    intro hm
    have hh := hinside f hm
    rcases hfcross with ⟨_, ht⟩ | ⟨_, hs⟩
    · exact ht hh.2
    · exact hs hh.1
  obtain ⟨hcut, c, d, ho, ra, rb⟩ := tree_path_edge_cut ht.2.1 hq hn hfm
  have subrest : ts.erase f ⊆ e :: ts.erase f := fun _ hm => List.mem_cons_of_mem e hm
  have hcd : Reach vs (e :: ts.erase f) c d :=
    Connected.trans (reach_symm (reach_mono subrest ra))
      (Connected.trans (reach_edge (by simp) hu hv) (reach_symm (reach_mono subrest rb)))
  have hnewf : Reach vs (e :: ts.erase f) (source f) (target f) := by
    rcases ho with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hcd
    · exact reach_symm hcd
  refine ⟨f, hft, hff, hfcross, ⟨ht.1, ?_, ?_⟩, ?_⟩
  · exact (forest_cons_iff _ _ _).mpr ⟨edgeForest_sublist List.erase_sublist ht.2.1, hu, hv, hcut⟩
  · intro u hum v hvm
    apply reach_replace_edges _ (ht.2.2 u hum v hvm)
    intro g hgm
    by_cases hgf : g = f
    · simpa [hgf] using hnewf
    · have hgr := (List.mem_erase_of_ne hgf).mpr hgm
      exact reach_edge (subrest hgr) (ht.2.1.2.1 g hgm).1 (ht.2.1.2.1 g hgm).2
  · intro g hgm
    have hgf : g ≠ f := fun h => hff (h ▸ hgm)
    exact (List.mem_erase_of_ne hgf).mpr (hsub hgm)

/-- The greedy law against every independent spanning-tree competitor. -/
theorem exchangeInv_cut_step {g : Graph} {us : List Vertex} {fs : List Edge} {e : Edge}
    (hin : EndpointsIn us fs) (hg : EndpointsIn (nodes g) (edges g))
    (he : e ∈ edges g) (hs : Safe us e)
    (hleast : ∀ f ∈ edges g, Safe us f → weight e ≤ weight f)
    (hprev : ExchangeInv g fs) : ExchangeInv g (e :: fs) := by
  intro t ht
  obtain ⟨replacement, hr, hfs, hcost⟩ := hprev t ht
  by_cases hem : e ∈ edges replacement
  · exact ⟨replacement, hr, List.cons_subset.mpr ⟨hem, hfs⟩, hcost⟩
  · obtain ⟨f, hft, _, hfcross, hnew, hrest⟩ :=
      visited_cut_exchange hr.2.2 hfs hin (hg e he).1 (hg e he).2 hs
    have hfinput := hr.2.1 hft
    refine ⟨(nodes g, e :: (edges replacement).erase f), ?_, ?_, ?_⟩
    · refine ⟨rfl, ?_, hnew⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact he
      · exact hr.2.1 (List.mem_of_mem_erase ha)
    · exact List.cons_subset.mpr ⟨by simp [edges], fun a ha => by
        exact List.mem_cons_of_mem _ (hrest ha)⟩
    · have hid := exchange_cost_identity (nodes g) (edges replacement) e f
        hft
      have hw := hleast f hfinput hfcross
      calc
        costMCST (nodes g, e :: (edges replacement).erase f) =
            costMCST (nodes g, edges replacement) + weight e - weight f := hid
        _ ≤ costMCST (nodes g, edges replacement) := by
          have hp := Int.sub_le_sub_right
            (Int.add_le_add_left hw (costMCST (nodes g, edges replacement))) (weight f)
          simpa only [Int.add_sub_cancel] using hp
        _ = costMCST replacement := rfl
        _ ≤ costMCST t := hcost


end Prim.Exchange
