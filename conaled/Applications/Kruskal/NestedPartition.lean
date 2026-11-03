import Applications.Kruskal.Nested

set_option autoImplicit false
set_option warningAsError true

/-! The literal nested forest represents exactly the first-name list partition.
Component order is preserved; component edge order is retained separately. -/
namespace ForestPartition
open Kruskal (Vertex Edge Graph Tree nodes edges source target)
open ForestKruskalSource (Forest find merge)

abbrev DS := Connectivity.ListPartition.DS

def carrier (ts : Forest) : List Vertex := (ts.map nodes).flatten

def chosen (ts : Forest) : List Edge := (ts.map edges).flatten

def name (t : Tree) : Vertex := (nodes t).headD 0

def project (ts : Forest) : DS := ts.map (fun t => (name t,nodes t))

def Partition (vs : List Vertex) (ts : Forest) : Prop :=
  vs.Nodup ∧ (carrier ts).Perm vs ∧ ∀t∈ts,nodes t≠[]

theorem mem_carrier (ts : Forest) (v : Vertex) :
    v∈carrier ts ↔ ∃t∈ts,v∈nodes t := by
  rw [carrier,List.mem_flatten]
  constructor
  · rintro ⟨xs,hxs,hv⟩
    obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hxs
    exact ⟨t,ht,hv⟩
  · rintro ⟨t,ht,hv⟩
    exact ⟨nodes t,List.mem_map.mpr ⟨t,ht,rfl⟩,hv⟩

theorem name_member {t : Tree} (h : nodes t≠[]) : name t∈nodes t := by
  cases hn : nodes t with
  | nil => exact False.elim (h hn)
  | cons v vs => simp [name,hn]

theorem partition_carrier_nodup {vs : List Vertex} {ts : Forest}
    (h : Partition vs ts) : (carrier ts).Nodup := h.2.1.symm.nodup h.1

theorem same_member_tree_eq {vs : List Vertex} {ts : Forest} (h : Partition vs ts)
    {t u : Tree} {v : Vertex} (ht : t∈ts) (hu : u∈ts)
    (hv : v∈nodes t) (hw : v∈nodes u) : t=u := by
  have hp : ts.Pairwise (fun a b => (nodes a).Disjoint (nodes b)) :=
    List.pairwise_map.mp (List.nodup_flatten.mp (partition_carrier_nodup h)).2
  have he : ts.Pairwise (fun a b => v ∈ nodes a → v ∈ nodes b → a = b) :=
    hp.imp (fun hd ha hb => False.elim (List.disjoint_left.mp hd ha hb))
  exact he.forall_of_forall_of_flip (fun _ _ _ _ => rfl)
    (hp.imp (fun hd hb ha => False.elim (List.disjoint_left.mp hd ha hb))) ht hu hv hw

theorem name_eq_iff {vs : List Vertex} {ts : Forest} (h : Partition vs ts)
    {t u : Tree} (ht : t∈ts) (hu : u∈ts) : name t=name u ↔ t=u := by
  refine ⟨?_,fun he => congrArg name he⟩
  intro he
  apply same_member_tree_eq h ht hu (name_member (h.2.2 t ht))
  rw [he]
  exact name_member (h.2.2 u hu)

/-- Answer9.8's head-name comparison agrees on valid component trees. -/
theorem notEqual_head {vs : List Vertex} {ts : Forest} (h : Partition vs ts)
    {t u : Tree} (ht : t∈ts) (hu : u∈ts) :
    decide (name t≠name u)=decide (t≠u) := by
  simp only [ne_eq,(name_eq_iff h ht hu)]

theorem project_carrier (ts : Forest) : Connectivity.ListPartition.carrier (project ts)=carrier ts := by
  simp [Connectivity.ListPartition.carrier,project,carrier,List.map_map,Function.comp_def]

theorem project_partition {vs : List Vertex} {ts : Forest} (h : Partition vs ts) :
    Connectivity.ListPartition.IsPartitionOf vs (project ts) := by
  refine ⟨h.1,?_,?_⟩
  · rw [project_carrier]; exact h.2.1
  · intro a xs hm
    obtain ⟨t,ht,he⟩ := List.mem_map.mp hm
    cases he
    have hn := h.2.2 t ht
    cases hx : nodes t with
    | nil => exact False.elim (hn hx)
    | cons v vs => simp [name,hx]

theorem project_length (ts : Forest) : (project ts).length=ts.length := by simp [project]

theorem find_project (ts : Forest) (v : Vertex) :
    Connectivity.ListPartition.findDS (project ts) v=(find ts v).map name := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      by_cases hv : v∈nodes t
      · simp [Connectivity.ListPartition.findDS,project,find,hv]
      · simpa [Connectivity.ListPartition.findDS,project,find,hv] using ih

theorem find_iff {vs : List Vertex} {ts : Forest} (h : Partition vs ts)
    (v : Vertex) (t : Tree) : find ts v=some t ↔ t∈ts ∧ v∈nodes t := by
  refine ⟨ForestKruskalSource.find_mem _ _ _,?_⟩
  rintro ⟨ht,hv⟩
  have hd := (Connectivity.ListPartition.findDS_partition_iff (project_partition h) v (name t)).mpr
    ⟨nodes t,List.mem_map.mpr ⟨t,ht,rfl⟩,hv⟩
  rw [find_project] at hd
  obtain ⟨u,hu,hn⟩ := Option.map_eq_some_iff.mp hd
  have hum := ForestKruskalSource.find_mem _ _ _ hu
  have he := same_member_tree_eq h ht hum.1 hv hum.2
  exact he ▸ hu

theorem find_defined {vs : List Vertex} {ts : Forest} (h : Partition vs ts)
    (v : Vertex) : (∃t,find ts v=some t) ↔ v∈vs := by
  constructor
  · rintro ⟨t,ht⟩
    have hm := (find_iff h v t).mp ht
    exact h.2.1.subset ((mem_carrier ts v).mpr ⟨t,hm.1,hm.2⟩)
  · intro hv
    obtain ⟨t,ht,hm⟩ := (mem_carrier ts v).mp (h.2.1.symm.subset hv)
    exact ⟨t,(find_iff h v t).mpr ⟨ht,hm⟩⟩

theorem project_start (g : Graph) :
    project (ForestKruskalSource.start g).1=(nodes g).map (fun v => (v,[v])) := by
  simp [project,ForestKruskalSource.start,name,List.map_map,Function.comp_def,nodes]

theorem start_partition (g : Graph) (h : (nodes g).Nodup) :
    Partition (nodes g) (ForestKruskalSource.start g).1 := by
  refine ⟨h,?_,?_⟩
  · simp [carrier, ForestKruskalSource.start, List.map_map, Function.comp_def, nodes, ← List.flatMap_def]
  · intro t ht
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp ht
    simp [nodes]

theorem lookup_project {vs : List Vertex} {ts : Forest} (h : Partition vs ts)
    {t : Tree} (ht : t ∈ ts) :
    Connectivity.ListPartition.lookupDS (project ts) (name t) = some (nodes t) :=
  Connectivity.ListPartition.lookupDS_of_member (project_partition h)
    (List.mem_map.mpr ⟨t, ht, rfl⟩)

theorem project_merge {vs : List Vertex} {ts : Forest} (h : Partition vs ts)
    (e : Edge) {t u : Tree} (ht : t∈ts) (hu : u∈ts) :
    Connectivity.ListPartition.unionDS (name t) (name u) (project ts)=
      some (project (merge e ts t u)) := by
  have hf : project (ts.filter (fun a => decide (a≠t ∧ a≠u)))=
      (project ts).filter (fun b => !([name t,name u].contains b.1)) := by
    rw [project,project,List.filter_map]
    congr 1
    apply List.filter_congr
    intro a ha
    simp [(name_eq_iff h ha ht),(name_eq_iff h ha hu)]
  have hn : name (nodes t++nodes u,e::edges t++edges u)=name t := by
    change (nodes t++nodes u).headD 0=(nodes t).headD 0
    have htne := h.2.2 t ht
    cases hx : nodes t with
    | nil => exact False.elim (htne hx)
    | cons v vs => simp
  simp only [Connectivity.ListPartition.unionDS,lookup_project h ht,lookup_project h hu]
  change some ((name t,nodes t++nodes u)::
    (project ts).filter (fun b => !([name t,name u].contains b.1)))=
    some ((name (nodes t++nodes u,e::edges t++edges u),nodes t++nodes u)::
      project (ts.filter (fun a => decide (a≠t ∧ a≠u))))
  rw [hn,hf]

theorem partition_iff_project (vs : List Vertex) (ts : Forest) :
    Partition vs ts ↔ Connectivity.ListPartition.IsPartitionOf vs (project ts) := by
  refine ⟨project_partition,?_⟩
  intro h
  refine ⟨h.1,?_,?_⟩
  · simpa only [project_carrier] using h.2.1
  · intro t ht
    exact Connectivity.ListPartition.partition_blocks_nonempty h (name t) (nodes t)
      (List.mem_map.mpr ⟨t,ht,rfl⟩)

theorem merge_partition {vs : List Vertex} {ts : Forest} (h : Partition vs ts)
    (e : Edge) {t u : Tree} (ht : t∈ts) (hu : u∈ts) (hne : t≠u) :
    Partition vs (merge e ts t u) := by
  apply (partition_iff_project _ _).mpr
  apply Connectivity.ListPartition.unionDS_partition (project_partition h)
    (List.mem_map.mpr ⟨(name t,nodes t),List.mem_map.mpr ⟨t,ht,rfl⟩,rfl⟩)
    (List.mem_map.mpr ⟨(name u,nodes u),List.mem_map.mpr ⟨u,hu,rfl⟩,rfl⟩)
    (fun he => hne ((name_eq_iff h ht hu).mp he)) (project_merge h e ht hu)

theorem merge_length {vs : List Vertex} {ts : Forest} (h : Partition vs ts)
    (e : Edge) {t u : Tree} (ht : t∈ts) (hu : u∈ts) (hne : t≠u) :
    (merge e ts t u).length+1=ts.length := by
  simpa only [project_length] using Connectivity.ListPartition.unionDS_block_count (project_partition h)
    (List.mem_map.mpr ⟨(name t,nodes t),List.mem_map.mpr ⟨t,ht,rfl⟩,rfl⟩)
    (List.mem_map.mpr ⟨(name u,nodes u),List.mem_map.mpr ⟨u,hu,rfl⟩,rfl⟩)
    (fun he => hne ((name_eq_iff h ht hu).mp he)) (project_merge h e ht hu)

theorem partition_nodup {vs : List Vertex} {ts : Forest} (h : Partition vs ts) : ts.Nodup := by
  have hn : (ts.map name).Nodup := by
    simpa [project,List.map_map,Function.comp_def] using
      Connectivity.ListPartition.partition_names_nodup (project_partition h)
  exact List.Pairwise.of_map name (fun _ _ hn he => hn (congrArg name he)) hn

theorem split_components_perm {vs : List Vertex} {ts : Forest} (h : Partition vs ts)
    {t u : Tree} (ht : t∈ts) (hu : u∈ts) (hne : t≠u) :
    (t::u::ts.filter (fun a => decide (a≠t ∧ a≠u))).Perm ts := by
  let p := fun a : Tree => decide (a=t ∨ a=u)
  have hp : (ts.filter p).Perm [t,u] := by
    apply (List.perm_ext_iff_of_nodup (List.Pairwise.filter p (partition_nodup h))
      (by simp [hne])).mpr
    intro a
    simp [p]
    rintro (rfl|rfl) <;> simp [ht,hu]
  have hh := (hp.append_right (ts.filter (fun a => !p a))).symm.trans
    (List.filter_append_perm p ts)
  simpa [p,not_or] using hh

theorem merge_chosen_perm {vs : List Vertex} {ts : Forest} (h : Partition vs ts)
    (e : Edge) {t u : Tree} (ht : t∈ts) (hu : u∈ts) (hne : t≠u) :
    (chosen (merge e ts t u)).Perm (e::chosen ts) := by
  have hp := ((split_components_perm h ht hu hne).map edges).flatten
  have hc := List.Perm.cons e hp
  simpa [chosen,merge,edges,List.append_assoc] using hc

end ForestPartition
