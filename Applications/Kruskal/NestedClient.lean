import Applications.Kruskal.Forest
import SquareKit.Iteration

/-! The actual nested forest client: exact component/residual projection,
first-hit iteration, arbitrary vertex labels, and independent global optimality.
Nested component edge order is retained and related by permutation, not silently
identified with the flat disjoint-set client's reverse acceptance list. -/
set_option autoImplicit false
set_option warningAsError true
namespace ForestKruskalClient
open Kruskal (Vertex Edge Graph Tree nodes edges source target)
open ForestKruskalSource (Forest State find merge gstep apply untilRun done extract startSorted)
open ForestPartition (Partition project chosen name)
open MinimumSpanningForest (Rep)

theorem gstep_projection {vs : List Vertex} {ts : Forest} (hp : Partition vs ts)
    (fs es : List Edge) :
    (gstep (ts,es)).map (fun s=>(project s.1,s.2))=
      (Kruskal.gstepK2 (project ts,fs,es)).map (fun s=>(s.1,s.2.2)) := by
  induction es with
  | nil=>simp [gstep,Kruskal.gstepK2]
  | cons e es ih=>
      cases ht:find ts (source e) with
      | none=>simp [gstep,Kruskal.gstepK2,ForestPartition.find_project,ht]
      | some t=>
          cases hu:find ts (target e) with
          | none=>simp [gstep,Kruskal.gstepK2,ForestPartition.find_project,ht,hu]
          | some u=>
              have htm:=(ForestKruskalSource.find_mem ts (source e) t ht).1
              have hum:=(ForestKruskalSource.find_mem ts (target e) u hu).1
              have hname:=ForestPartition.name_eq_iff hp htm hum
              by_cases he:t=u
              · subst u
                simpa [gstep,Kruskal.gstepK2,ForestPartition.find_project,ht,hu] using ih
              · simp [gstep,Kruskal.gstepK2,ForestPartition.find_project,ht,hu,he,
                  show name t≠name u from fun h=>he (hname.mp h),ForestPartition.project_merge hp e htm hum]

/-- Projection keeps the residual literally; nested and flat edge order need only permute. -/
theorem gstep_selected_projection {vs : List Vertex} {s out : State}
    (hp : Partition vs s.1) (hg : gstep s = some out) :
    ∃ flat, Kruskal.gstepK2 (project s.1, chosen s.1, s.2) = some flat ∧
      flat.1 = project out.1 ∧ flat.2.2 = out.2 ∧ (chosen out.1).Perm flat.2.1 := by
  have hstep := (ForestKruskalSource.gstep_source_iff s out).mp hg
  clear hg
  induction hstep with
  | @take ts e es t u ht hu hn =>
      have htm := (ForestKruskalSource.find_mem _ _ _ ht).1
      have hum := (ForestKruskalSource.find_mem _ _ _ hu).1
      have hname : name t ≠ name u := fun h => hn ((ForestPartition.name_eq_iff hp htm hum).mp h)
      refine ⟨(project (merge e ts t u), e :: chosen ts, es), ?_, rfl, rfl,
        ForestPartition.merge_chosen_perm hp e htm hum hn⟩
      simp [Kruskal.gstepK2, ForestPartition.find_project, ht, hu, hname,
        ForestPartition.project_merge hp e htm hum]
  | skip ht hu _ ih =>
      obtain ⟨flat, hf, hc, he, hp'⟩ := ih hp
      exact ⟨flat, by simpa [Kruskal.gstepK2, ForestPartition.find_project, ht, hu] using hf,
        hc, he, hp'⟩

theorem gstep_rep {vs : List Vertex} {s out : State} (hr : Rep vs s.1)
    (hg : gstep s=some out) : Rep vs out.1 ∧ out.1.length+1=s.1.length := by
  have hs:=(ForestKruskalSource.gstep_source_iff s out).mp hg
  clear hg
  induction hs with
  | @take ts e es t u ht hu hne=>
      have hp:=MinimumSpanningForest.rep_partition hr
      exact ⟨MinimumSpanningForest.rep_merge hr ht hu hne,
        ForestPartition.merge_length hp e (ForestKruskalSource.find_mem _ _ _ ht).1
          (ForestKruskalSource.find_mem _ _ _ hu).1 hne⟩
  | skip _ _ _ ih=>exact ih hr

theorem gstep_scan {s out : State} (hg : gstep s=some out) :
    ForestKruskalSource.scan s.1 s.2=ForestKruskalSource.scan out.1 out.2 := by
  have hs:=(ForestKruskalSource.gstep_source_iff s out).mp hg
  clear hg
  induction hs with
  | take ht hu hn=>simp [ForestKruskalSource.scan,ht,hu,hn]
  | skip ht hu _ ih=>simpa [ForestKruskalSource.scan,ht,hu] using ih

theorem apply_head (k : Nat) (s : State) : apply (k+1) s=(gstep s).bind (apply k) := by
  induction k generalizing s with
  | zero=>simp [apply]
  | succ k ih=>rw [apply,ih,Option.bind_assoc];rfl

theorem apply_rep {vs : List Vertex} {s out : State} (hr : Rep vs s.1) {k : Nat}
    (ha : apply k s=some out) : Rep vs out.1 ∧ out.1.length+k=s.1.length := by
  induction k generalizing out with
  | zero=>have he:s=out:=Option.some.inj ha;subst out;exact ⟨hr,by simp⟩
  | succ k ih=>
      rw [apply,Option.bind_eq_some_iff] at ha
      obtain ⟨mid,hm,hg⟩:=ha
      have hmid:=ih hm
      have hout:=gstep_rep hmid.1 hg
      exact ⟨hout.1,by omega⟩

theorem apply_scan {s out : State} {k : Nat} (ha : apply k s=some out) :
    ForestKruskalSource.scan s.1 s.2=ForestKruskalSource.scan out.1 out.2 := by
  induction k generalizing out with
  | zero=>have he:s=out:=Option.some.inj ha;subst out;rfl
  | succ k ih=>
      rw [apply,Option.bind_eq_some_iff] at ha
      obtain ⟨mid,hm,hg⟩:=ha
      exact (ih hm).trans (gstep_scan hg)

theorem singleton_scan_result {ts out : Forest} (hn : ts.length=1) {es : List Edge}
    (hs : ForestKruskalSource.scan ts es=some out) : out=ts := by
  obtain ⟨t,rfl⟩:=List.length_eq_one_iff.mp hn
  induction es with
  | nil=>exact (Option.some.inj hs).symm
  | cons e es ih=>
      cases ht:find [t] (source e) with
      | none=>simp [ForestKruskalSource.scan,ht] at hs
      | some u=>
          have he:u=t:=List.mem_singleton.mp (ForestKruskalSource.find_mem _ _ _ ht).1
          subst u
          cases hu:find [t] (target e) with
          | none=>simp [ForestKruskalSource.scan,ht,hu] at hs
          | some v=>
              have he:v=t:=List.mem_singleton.mp (ForestKruskalSource.find_mem _ _ _ hu).1
              subst v
              apply ih
              simpa [ForestKruskalSource.scan,ht,hu] using hs

theorem singleton_gstep_none (t : Tree) (es : List Edge) : gstep ([t],es)=none := by
  induction es with
  | nil=>simp [gstep]
  | cons e es ih=>
      cases ht:find [t] (source e) with
      | none=>simp [gstep,ht]
      | some u=>
          have he:u=t:=List.mem_singleton.mp (ForestKruskalSource.find_mem _ _ _ ht).1
          subst u
          cases hu:find [t] (target e) with
          | none=>simp [gstep,ht,hu]
          | some v=>
              have he:v=t:=List.mem_singleton.mp (ForestKruskalSource.find_mem _ _ _ hu).1
              subst v
              simpa [gstep,ht,hu] using ih

theorem scan_split {ts out : Forest} {es : List Edge}
    (hs : ForestKruskalSource.scan ts es=some out) (hne : out≠ts) :
    ∃mid,gstep (ts,es)=some mid ∧ ForestKruskalSource.scan mid.1 mid.2=some out := by
  induction es with
  | nil=>simp only [ForestKruskalSource.scan,Option.some.injEq] at hs;exact False.elim (hne hs.symm)
  | cons e es ih=>
      cases ht:find ts (source e) with
      | none=>simp [ForestKruskalSource.scan,ht] at hs
      | some t=>
          cases hu:find ts (target e) with
          | none=>simp [ForestKruskalSource.scan,ht,hu] at hs
          | some u=>
              by_cases he:t=u
              · subst u
                obtain ⟨mid,hm,ho⟩:=ih (by simpa [ForestKruskalSource.scan,ht,hu] using hs)
                exact ⟨mid,by simpa [gstep,ht,hu] using hm,ho⟩
              · exact ⟨(merge e ts t u,es),by simp [gstep,ht,hu,he],
                  by simpa [ForestKruskalSource.scan,ht,hu,he] using hs⟩

theorem apply_reaches_scan {vs : List Vertex} {ts final : Forest} {es : List Edge}
    (hr : Rep vs ts) (hs : ForestKruskalSource.scan ts es=some final) (hfinal : final.length=1)
    (k : Nat) (hlen : ts.length=k+1) :
    ∃rest,apply k (ts,es)=some (final,rest) := by
  induction k generalizing ts es with
  | zero=>
      have he:=singleton_scan_result (by simpa using hlen) hs
      subst final
      exact ⟨es,rfl⟩
  | succ k ih=>
      have hne:final≠ts:=by intro he;subst final;omega
      obtain ⟨mid,hm,ho⟩:=scan_split hs hne
      have hp:=gstep_rep hr hm
      have hcount : mid.1.length+1=ts.length:=hp.2
      obtain ⟨rest,ht⟩:=ih hp.1 ho (by omega)
      refine ⟨rest,?_⟩
      rw [apply_head,hm]
      exact ht

theorem until_eq_apply {vs : List Vertex} (k : Nat) (s : State) (hr : Rep vs s.1)
    (hlen : s.1.length=k+1) : untilRun k s=apply k s := by
  induction k generalizing s with
  | zero=>simp [untilRun,done,hlen,apply]
  | succ k ih=>
      have hd:done s=false:=by simp [done,hlen]
      rw [untilRun,hd,apply_head]
      cases hg:gstep s with
      | none=>rfl
      | some out=>
          have hp:=gstep_rep hr hg
          simp only [Option.bind_some]
          exact ih out hp.1 (by omega)

theorem until_first_hit {vs : List Vertex} {s out : State} (hr : Rep vs s.1)
    {k : Nat} (hlen : s.1.length=k+1) (ha : apply k s=some out) :
    Iteration.UntilSpec done
      (fun x=>(gstep x).getD x) s out := by
  induction k generalizing s with
  | zero=>
      have he:s=out:=Option.some.inj ha
      subst out
      exact .stop (by simp [done,hlen])
  | succ k ih=>
      rw [apply_head,Option.bind_eq_some_iff] at ha
      obtain ⟨mid,hm,ht⟩:=ha
      have hp:=gstep_rep hr hm
      have hs:done s=false:=by simp [done,hlen]
      have hi:=ih hp.1 (by omega) ht
      apply Iteration.UntilSpec.step hs
      simpa only [hm,Option.getD_some] using hi

theorem extract_iff (s : State) (t : Tree) : extract s=some t ↔ s.1=[t] := by
  rcases s with ⟨ts,es⟩
  cases ts with
  | nil=>simp [extract]
  | cons u ts=>cases ts <;> simp [extract]

theorem spanningTree_forest {g t : Graph} (hend : Kruskal.EndpointsIn (nodes g) (edges g))
    (ht : Kruskal.SpanningTree g t) : MinimumSpanningForest.SpanningForest g (edges t) := by
  refine ⟨ht.2.2.2.1,ht.2.1,?_⟩
  intro u v
  exact ⟨Kruskal.reach_mono ht.2.1,Kruskal.reach_replace_edges (fun e he=>
    ht.2.2.2.2 (source e) (hend e he).1 (target e) (hend e he).2)⟩

theorem singleton_minimum {g : Graph} {t : Tree} (hn : nodes g≠[])
    (hend : Kruskal.EndpointsIn (nodes g) (edges g)) (hr : Rep (nodes g) [t])
    (hm : MinimumSpanningForest.Minimum g (chosen [t])) :
    (nodes t).Perm (nodes g) ∧ Kruskal.MinimumSpanningTree g (nodes g,edges t) := by
  have hp:=MinimumSpanningForest.rep_partition hr
  have hv:(nodes t).Perm (nodes g):=by simpa [ForestPartition.carrier] using hp.2.1
  have hc:∀u∈nodes g,∀v∈nodes g,Kruskal.Reach (nodes g) (edges t) u v:=by
    intro u hu v hv'
    have hh:Connectivity.ListPartition.SameBlock (project [t]) u v:=
      ⟨name t,nodes t,by simp [project],hv.mem_iff.mpr hu,hv.mem_iff.mpr hv'⟩
    simpa [chosen,Kruskal.selected] using (hr.2.2 u v).mp hh
  refine ⟨hv,⟨rfl,?_,hn,?_,hc⟩,?_⟩
  · simpa [chosen,edges] using hm.1.2.1
  · simpa [chosen,edges] using hm.1.1
  · intro other ho
    have hh:=hm.2 (edges other) (spanningTree_forest hend ho)
    simpa [chosen,MinimumSpanningForest.cost,Kruskal.costMCST,edges] using hh

theorem startSorted_rep (g : Graph) (hn : (nodes g).Nodup) : Rep (nodes g) (startSorted g).1 :=
  MinimumSpanningForest.start_rep g hn

theorem kruskal_variants {g : Graph} (hn : (nodes g).Nodup) (hne : nodes g≠[]) :
    ForestKruskalSource.kruskal0 g=ForestKruskalSource.kruskal1 g := by
  have hp:0<(nodes g).length:=List.length_pos_iff.mpr hne
  have hlen:(startSorted g).1.length=(nodes g).length-1+1:=by simp [startSorted];omega
  rw [ForestKruskalSource.kruskal0,until_eq_apply _ _ (startSorted_rep g hn) hlen]
  rfl

/-- A successful tree wrapper returns exactly the singleton corrected forest. -/
theorem kruskal1_forest_result {g : Graph} (hn : (nodes g).Nodup)
    (hend : Kruskal.EndpointsIn (nodes g) (edges g)) {t : Tree}
    (ht : ForestKruskalSource.kruskal1 g = some t) :
    ForestKruskalSource.mcsf g = some [t] ∧ Rep (nodes g) [t] := by
  obtain ⟨s,hs,he⟩:=Option.bind_eq_some_iff.mp ht
  have hs':apply ((nodes g).length-1) (startSorted g)=some s:=hs
  have he':s.1=[t]:=(extract_iff s t).mp he
  have hr:=(apply_rep (startSorted_rep g hn) hs').1
  obtain ⟨final,hfinal,_,_⟩:=MinimumSpanningForest.mcsf_correct g hn hend
  have hscan:ForestKruskalSource.scan s.1 s.2=some final:=by
    rw [←apply_scan hs']
    exact hfinal
  have hsame:final=s.1:=singleton_scan_result (by rw [he'];rfl) hscan
  rw [he'] at hsame hr
  subst final
  exact ⟨hfinal, hr⟩

theorem kruskal1_result_minimum {g : Graph} (hn : (nodes g).Nodup) (hne : nodes g ≠ [])
    (hend : Kruskal.EndpointsIn (nodes g) (edges g)) {t : Tree}
    (ht : ForestKruskalSource.kruskal1 g = some t) :
    (nodes t).Perm (nodes g) ∧ Kruskal.MinimumSpanningTree g (nodes g, edges t) := by
  obtain ⟨hf, hr⟩ := kruskal1_forest_result hn hend ht
  exact singleton_minimum hne hend hr (MinimumSpanningForest.mcsf_result_minimum hn hend hf)

theorem kruskal1_exists {g : Graph} (hn : (nodes g).Nodup) (hne : nodes g≠[])
    (hend : Kruskal.EndpointsIn (nodes g) (edges g)) (hc : Kruskal.ConnectedGraph g) :
    ∃t,ForestKruskalSource.kruskal1 g=some t ∧
      (nodes t).Perm (nodes g) ∧ Kruskal.MinimumSpanningTree g (nodes g,edges t) := by
  obtain ⟨final,hfinal,hr,hmin⟩:=MinimumSpanningForest.mcsf_correct g hn hend
  have hall:∀u∈nodes g,∀v∈nodes g,Connectivity.ListPartition.SameBlock (project final) u v:=by
    intro u hu v hv
    exact (hr.2.2 u v).mpr ((hmin.1.2.2 u v).mpr (hc u hu v hv))
  have hlen:final.length=1:=by
    simpa only [Kruskal.components,ForestPartition.project_length] using (Kruskal.partition_singleton_iff hr.1 hne).mpr hall
  obtain ⟨t,rfl⟩:=List.length_eq_one_iff.mp hlen
  have hp:0<(nodes g).length:=List.length_pos_iff.mpr hne
  have hi:(startSorted g).1.length=(nodes g).length-1+1:=by simp [startSorted];omega
  obtain ⟨rest,hrest⟩:=apply_reaches_scan (startSorted_rep g hn)
    (show ForestKruskalSource.scan (startSorted g).1 (startSorted g).2=some [t] from hfinal)
    (by rfl) ((nodes g).length-1) hi
  refine ⟨t,?_,singleton_minimum hne hend hr hmin⟩
  simp [ForestKruskalSource.kruskal1,hrest,extract]

theorem kruskal1_defined_iff_connected {g : Graph} (hn : (nodes g).Nodup) (hne : nodes g≠[])
    (hend : Kruskal.EndpointsIn (nodes g) (edges g)) :
    (∃t,ForestKruskalSource.kruskal1 g=some t) ↔ Kruskal.ConnectedGraph g := by
  constructor
  · rintro ⟨t,ht⟩
    have hs:=(kruskal1_result_minimum hn hne hend ht).2.1
    intro u hu v hv
    exact Kruskal.reach_mono hs.2.1 (hs.2.2.2.2 u hu v hv)
  · intro hc
    obtain ⟨t,ht,_,_⟩:=kruskal1_exists hn hne hend hc
    exact ⟨t,ht⟩

theorem kruskal0_defined_iff_connected {g : Graph} (hn : (nodes g).Nodup)
    (hne : nodes g ≠ []) (hend : Kruskal.EndpointsIn (nodes g) (edges g)) :
    (∃ t, ForestKruskalSource.kruskal0 g = some t) ↔ Kruskal.ConnectedGraph g := by
  rw [kruskal_variants hn hne]
  exact kruskal1_defined_iff_connected hn hne hend

theorem kruskal0_result_minimum {g : Graph} (hn : (nodes g).Nodup) (hne : nodes g≠[])
    (hend : Kruskal.EndpointsIn (nodes g) (edges g)) {t : Tree}
    (ht : ForestKruskalSource.kruskal0 g=some t) :
    (nodes t).Perm (nodes g) ∧ Kruskal.MinimumSpanningTree g (nodes g,edges t) := by
  rw [kruskal_variants hn hne] at ht
  exact kruskal1_result_minimum hn hne hend ht

theorem kruskal0_first_hit {g : Graph} (hn : (nodes g).Nodup) (hne : nodes g≠[])
    {t : Tree} (ht : ForestKruskalSource.kruskal0 g=some t) :
    ∃s,Iteration.UntilSpec done (fun x=>(gstep x).getD x) (startSorted g) s ∧
      extract s=some t ∧ apply ((nodes g).length-1) (startSorted g)=some s := by
  rw [kruskal_variants hn hne] at ht
  obtain ⟨s,hs,he⟩:=Option.bind_eq_some_iff.mp ht
  have hp:0<(nodes g).length:=List.length_pos_iff.mpr hne
  have hlen:(startSorted g).1.length=(nodes g).length-1+1:=by simp [startSorted];omega
  exact ⟨s,until_first_hit (startSorted_rep g hn) hlen hs,he,hs⟩

end ForestKruskalClient
