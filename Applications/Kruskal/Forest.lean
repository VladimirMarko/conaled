import Applications.Kruskal.NestedPartition
import Applications.Kruskal.Correctness

set_option autoImplicit false
set_option warningAsError true

/-! Corrected all-edge Kruskal scan on disconnected graphs. Competitors are
independent acyclic edge lists with exactly the input graph's connectivity. -/
namespace MinimumSpanningForest
open Kruskal
open ForestPartition (Partition project chosen)
open ForestKruskalSource (Forest find merge scan)
open Connectivity.ListPartition (Connected)

def SpanningForest (g : Graph) (fs : List Edge) : Prop :=
  EdgeForest (nodes g) fs ∧ fs⊆edges g ∧
  ∀u v,Reach (nodes g) fs u v ↔ Reach (nodes g) (edges g) u v

def cost (fs : List Edge) : Int := (fs.map weight).sum

theorem cost_perm {fs gs : List Edge} (hp : fs.Perm gs) : cost fs=cost gs := (hp.map weight).sum_eq

theorem cost_chosen (ts : Forest) : cost (chosen ts)=(ts.map costMCST).sum := by
  simp only [cost, chosen, List.map_flatten, List.sum_flatten, List.map_map]
  rfl

def Minimum (g : Graph) (fs : List Edge) : Prop :=
  SpanningForest g fs ∧ ∀ts,SpanningForest g ts → cost fs≤cost ts

def Exchange (g : Graph) (fs : List Edge) : Prop :=
  ∀ts,SpanningForest g ts → ∃rs,SpanningForest g rs ∧ fs⊆rs ∧ cost rs≤cost ts

def Rep (vs : List Vertex) (ts : Forest) : Prop :=
  StateRep vs (project ts,chosen ts,[])

private theorem edge_reach {vs : List Vertex} {es : List Edge} {e : Edge}
    (he : e∈es) (hu : source e∈vs) (hv : target e∈vs) :
    Reach vs es (source e) (target e) :=
  reach_edge he hu hv

private theorem reach_perm {vs : List Vertex} {es fs : List Edge} (hp : es.Perm fs)
    (u v : Vertex) : Reach vs es u v ↔ Reach vs fs u v :=
  ⟨reach_mono hp.subset,reach_mono hp.symm.subset⟩

theorem spanningForest_of_all_edges {g : Graph} {fs : List Edge}
    (hf : EdgeForest (nodes g) fs) (hsub : fs⊆edges g)
    (hc : ∀e∈edges g,Reach (nodes g) fs (source e) (target e)) : SpanningForest g fs := by
  refine ⟨hf,hsub,?_⟩
  intro u v
  exact ⟨reach_mono hsub,reach_replace_edges hc⟩

theorem spanningForest_maximal {g : Graph} {fs : List Edge} (h : SpanningForest g fs)
    {e : Edge} (he : e∈edges g) (hend : EndpointsIn (nodes g) (edges g)) :
    ¬EdgeForest (nodes g) (e::fs) := by
  intro hf
  have hh := (forest_cons_iff _ _ _).mp hf
  exact hh.2.2.2 ((h.2.2 _ _).mpr (edge_reach he (hend e he).1 (hend e he).2))

theorem maximal_spanningForest {g : Graph} {fs : List Edge}
    (hf : EdgeForest (nodes g) fs) (hsub : fs⊆edges g)
    (hend : EndpointsIn (nodes g) (edges g))
    (hm : ∀e∈edges g,¬EdgeForest (nodes g) (e::fs)) : SpanningForest g fs := by
  classical
  apply spanningForest_of_all_edges hf hsub
  intro e he
  apply Classical.byContradiction
  intro hn
  exact hm e he ((forest_cons_iff _ _ _).mpr ⟨hf,(hend e he).1,(hend e he).2,hn⟩)

theorem connected_spanningForest {g : Graph} {fs : List Edge}
    (h : SpanningForest g fs) (hn : nodes g≠[]) (hc : ConnectedGraph g) :
    SpanningTree g (nodes g,fs) := by
  exact ⟨rfl,h.2.1,hn,h.1,fun u hu v hv => (h.2.2 u v).mpr (hc u hu v hv)⟩

theorem exchange_nil (g : Graph) : Exchange g [] := by
  intro ts ht
  exact ⟨ts,ht,by simp,Int.le_refl _⟩

theorem exchange_perm {g : Graph} {fs gs : List Edge} (hp : fs.Perm gs)
    (h : Exchange g gs) : Exchange g fs := by
  intro ts ht
  obtain ⟨rs,hr,hs,hc⟩ := h ts ht
  exact ⟨rs,hr,fun _ hm => hs (hp.subset hm),hc⟩

theorem exchange_take {g : Graph} {fs : List Edge} {e : Edge}
    (hf : EdgeForest (nodes g) fs) (he : e∈edges g)
    (hend : EndpointsIn (nodes g) (edges g))
    (hcross : ¬Reach (nodes g) fs (source e) (target e))
    (hle : ∀f∈edges g,¬Reach (nodes g) fs (source f) (target f) → weight e≤weight f)
    (hi : Exchange g fs) : Exchange g (e::fs) := by
  intro ts ht
  obtain ⟨rs,hr,hsub,hcost⟩ := hi ts ht
  by_cases hem : e∈rs
  · exact ⟨rs,hr,List.cons_subset.mpr ⟨hem,hsub⟩,hcost⟩
  · have hj := (hr.2.2 _ _).mpr (edge_reach he (hend e he).1 (hend e he).2)
    obtain ⟨f,hfr,hff,hfc,hnew,hconn,hrest⟩ := forest_exchange hf hr.1 hsub
      (hend e he).1 (hend e he).2 hcross hj
    have hfg := hr.2.1 hfr
    refine ⟨e::rs.erase f,⟨hnew,?_,?_⟩,List.cons_subset.mpr ⟨by simp,?_⟩,?_⟩
    · exact List.cons_subset.mpr ⟨he,fun _ hm => hr.2.1 (List.mem_of_mem_erase hm)⟩
    · intro u v
      exact (hconn u v).trans (hr.2.2 u v)
    · exact fun _ hm => List.mem_cons_of_mem e (hrest hm)
    · have hid := exchange_cost_identity (nodes g) rs e f hfr
      change cost (e::rs.erase f)=cost rs+weight e-weight f at hid
      have hw := hle f hfg hfc
      have hh := Int.sub_le_sub_right (Int.add_le_add_left hw (cost rs)) (weight f)
      have hb : cost (e::rs.erase f)≤cost rs := by
        rw [hid]
        simpa only [Int.add_sub_cancel] using hh
      exact Int.le_trans hb hcost

theorem exchange_minimum {g : Graph} {fs : List Edge}
    (hf : SpanningForest g fs) (hi : Exchange g fs) : Minimum g fs := by
  refine ⟨hf,?_⟩
  intro ts ht
  obtain ⟨rs,hr,hsub,hcost⟩ := hi ts ht
  have hp := same_components_subforest_eq_perm hf.1 hr.1 hsub (by
    intro e he
    exact (hf.2.2 _ _).mpr ((hr.2.2 _ _).mp
      (edge_reach he (hr.1.2.1 e he).1 (hr.1.2.1 e he).2)))
  rw [cost_perm hp]
  exact hcost

theorem rep_partition {vs : List Vertex} {ts : Forest} (h : Rep vs ts) : Partition vs ts :=
  (ForestPartition.partition_iff_project _ _).mpr h.1

theorem rep_find_connected {vs : List Vertex} {ts : Forest} (h : Rep vs ts)
    {u v : Vertex} (hu : u∈vs) (hv : v∈vs) :
    find ts u=find ts v ↔ Reach vs (chosen ts) u v := by
  have hp := rep_partition h
  obtain ⟨t,ht⟩ := (ForestPartition.find_defined hp u).mpr hu
  obtain ⟨w,hw⟩ := (ForestPartition.find_defined hp v).mpr hv
  have hf := state_find_iff_connected h hu hv
  simp only [components,ForestPartition.find_project,ht,hw,Option.map_some,Option.some.injEq] at hf
  rw [ht,hw,Option.some.injEq]
  exact ((ForestPartition.name_eq_iff hp (ForestKruskalSource.find_mem _ _ _ ht).1
    (ForestKruskalSource.find_mem _ _ _ hw).1).symm).trans hf

theorem rep_merge {vs : List Vertex} {ts : Forest} (h : Rep vs ts)
    {e : Edge} {t u : Tree} (ht : find ts (source e)=some t)
    (hu : find ts (target e)=some u) (hne : t≠u) : Rep vs (merge e ts t u) := by
  have hp := rep_partition h
  have htm := ForestKruskalSource.find_mem _ _ _ ht
  have hum := ForestKruskalSource.find_mem _ _ _ hu
  have hsource : source e∈vs := (ForestPartition.find_defined hp _).mp ⟨t,ht⟩
  have htarget : target e∈vs := (ForestPartition.find_defined hp _).mp ⟨u,hu⟩
  have hnt : Connectivity.ListPartition.findDS (project ts) (source e)=some (ForestPartition.name t) := by
    rw [ForestPartition.find_project,ht];rfl
  have hnu : Connectivity.ListPartition.findDS (project ts) (target e)=some (ForestPartition.name u) := by
    rw [ForestPartition.find_project,hu];rfl
  have hr : StateRep vs (project (merge e ts t u),e::chosen ts,[]) := merge_stateRep h
    hsource htarget hnt hnu (fun he => hne ((ForestPartition.name_eq_iff hp htm.1 hum.1).mp he))
    (ForestPartition.project_merge hp e htm.1 hum.1)
  have he := ForestPartition.merge_chosen_perm hp e htm.1 hum.1 hne
  refine ⟨hr.1,(forest_perm he).mpr hr.2.1,?_⟩
  intro a b
  exact (hr.2.2 a b).trans (reach_perm he a b).symm

theorem scan_correct {g : Graph} (hend : EndpointsIn (nodes g) (edges g))
    (es : List Edge) (ts : Forest) (hr : Rep (nodes g) ts)
    (hc : chosen ts⊆edges g) (he : es⊆edges g)
    (hs : es.Pairwise (fun e f => weight e≤weight f))
    (hprocessed : ∀e∈edges g,e∈es ∨ Reach (nodes g) (chosen ts) (source e) (target e))
    (hi : Exchange g (chosen ts)) :
    ∃out,scan ts es=some out ∧ Rep (nodes g) out ∧ Minimum g (chosen out) := by
  induction es generalizing ts with
  | nil =>
      have hf := spanningForest_of_all_edges (fs := chosen ts) hr.2.1 hc (by
        intro e he
        simpa using hprocessed e he)
      exact ⟨ts,rfl,hr,exchange_minimum hf hi⟩
  | cons e es ih =>
      have heg : e∈edges g := he (by simp)
      have huv := hend e heg
      have hp := rep_partition hr
      obtain ⟨t,ht⟩ := (ForestPartition.find_defined hp _).mpr huv.1
      obtain ⟨u,hu⟩ := (ForestPartition.find_defined hp _).mpr huv.2
      have htail : es⊆edges g := fun _ hm => he (List.mem_cons_of_mem e hm)
      have hsort := List.pairwise_cons.mp hs
      by_cases hne : t≠u
      · have htm := (ForestKruskalSource.find_mem _ _ _ ht).1
        have hum := (ForestKruskalSource.find_mem _ _ _ hu).1
        have hm := rep_merge hr ht hu hne
        have hperm := ForestPartition.merge_chosen_perm hp e htm hum hne
        have hcross : ¬Reach (nodes g) (chosen ts) (source e) (target e) := by
          intro hh
          have heq := (rep_find_connected hr huv.1 huv.2).mpr hh
          rw [ht,hu,Option.some.injEq] at heq
          exact hne heq
        have hleast : ∀f∈edges g,¬Reach (nodes g) (chosen ts) (source f) (target f) →
            weight e≤weight f := by
          intro f hfg hfc
          rcases hprocessed f hfg with hf | hf
          · rcases List.mem_cons.mp hf with rfl | hf
            · exact Int.le_refl _
            · exact hsort.1 f hf
          · exact False.elim (hfc hf)
        have hnexti := exchange_perm hperm (exchange_take hr.2.1 heg hend hcross hleast hi)
        have hold : chosen ts⊆chosen (merge e ts t u) :=
          fun _ hf => hperm.symm.subset (List.mem_cons_of_mem e hf)
        have hnewsub : chosen (merge e ts t u)⊆edges g := by
          intro f hf
          rcases List.mem_cons.mp (hperm.subset hf) with rfl | hf
          · exact heg
          · exact hc hf
        have hnewprocessed : ∀f∈edges g,f∈es ∨
            Reach (nodes g) (chosen (merge e ts t u)) (source f) (target f) := by
          intro f hfg
          rcases hprocessed f hfg with hf | hf
          · rcases List.mem_cons.mp hf with rfl | hf
            · exact Or.inr (edge_reach (hperm.symm.subset (by simp)) huv.1 huv.2)
            · exact Or.inl hf
          · exact Or.inr (reach_mono hold hf)
        obtain ⟨out,hout,hrep,hmin⟩ := ih (merge e ts t u) hm hnewsub htail hsort.2 hnewprocessed hnexti
        refine ⟨out,?_,hrep,hmin⟩
        simpa only [scan,ht,hu,ite_eq_left hne] using hout
      · have htu : t=u := by simpa using hne
        subst u
        have hconnected := (rep_find_connected hr huv.1 huv.2).mp (ht.trans hu.symm)
        have hnewprocessed : ∀f∈edges g,f∈es ∨ Reach (nodes g) (chosen ts) (source f) (target f) := by
          intro f hfg
          rcases hprocessed f hfg with hf | hf
          · rcases List.mem_cons.mp hf with rfl | hf
            · exact Or.inr hconnected
            · exact Or.inl hf
          · exact Or.inr hf
        obtain ⟨out,hout,hrep,hmin⟩ := ih ts hr hc htail hsort.2 hnewprocessed hi
        refine ⟨out,?_,hrep,hmin⟩
        simpa only [scan,ht,hu,ne_eq,not_true_eq_false,ite_false] using hout

theorem chosen_start (g : Graph) : chosen (ForestKruskalSource.start g).1=[] := by
  simp [chosen,ForestKruskalSource.start,List.map_map,Function.comp_def,edges]

theorem start_rep (g : Graph) (hn : (nodes g).Nodup) :
    Rep (nodes g) (ForestKruskalSource.start g).1 := by
  change StateRep (nodes g) (project (ForestKruskalSource.start g).1,
    chosen (ForestKruskalSource.start g).1,[])
  rw [ForestPartition.project_start,chosen_start]
  exact singleton_stateRep _ hn []

/-- Every valid finite graph has a corrected scan result globally minimal among
all independent spanning forests, including the empty and disconnected cases. -/
theorem mcsf_correct (g : Graph) (hn : (nodes g).Nodup)
    (hend : EndpointsIn (nodes g) (edges g)) :
    ∃out,ForestKruskalSource.mcsf g=some out ∧ Rep (nodes g) out ∧ Minimum g (chosen out) := by
  apply scan_correct hend (sortEdges (edges g)) (ForestKruskalSource.start g).1 (start_rep g hn)
  · rw [chosen_start];simp
  · exact (sortEdges_spec _).1.subset
  · exact (sortEdges_spec _).2.1
  · intro e he
    exact Or.inl ((sortEdges_spec _).1.symm.subset he)
  · rw [chosen_start];exact exchange_nil g

theorem mcsf_result_minimum {g : Graph} (hn : (nodes g).Nodup)
    (hend : EndpointsIn (nodes g) (edges g)) {out : Forest}
    (ho : ForestKruskalSource.mcsf g=some out) : Minimum g (chosen out) := by
  obtain ⟨result,hr,_,hm⟩ := mcsf_correct g hn hend
  exact Option.some.inj (hr.symm.trans ho) ▸ hm

theorem disconnected_boundary :
    ForestKruskalSource.kruskal0 ([1,2],[])=none ∧
    ForestKruskalSource.kruskal1 ([1,2],[])=none ∧
    ForestKruskalSource.mcsf ([1,2],[])=some [([1],[]),([2],[])] := by
  simp [ForestKruskalSource.kruskal0,ForestKruskalSource.kruskal1,
    ForestKruskalSource.untilRun,ForestKruskalSource.apply,ForestKruskalSource.gstep,
    ForestKruskalSource.startSorted,ForestKruskalSource.done,ForestKruskalSource.mcsf,
    ForestKruskalSource.start,scan,nodes,edges,sortEdges,Applications.Sorting.sortOn, Applications.Sorting.sortBy]

end MinimumSpanningForest
