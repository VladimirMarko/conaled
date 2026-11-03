import Applications.Prim.Array

set_option autoImplicit false
set_option warningAsError true

/-!
The link-array Prim invariant and independent all-competitor MST proof.  A
matrix representation states adjacency and symmetry, not an optimization law.
The proof follows the actual rank-tied selector and old-parent-tied update.
-/

namespace Prim.ArrayOptimality

open Kruskal Prim.Array
open Dijkstra.Store
open Prim.Exchange
open Connectivity.ListPartition (Connected)

variable {n : Nat}

structure MatrixRep (g : Graph) (wa : Weights n) : Prop where
  vertices : nodes g=labels n
  endpoints : EndpointsIn (nodes g) (edges g)
  cell : ∀ u v w, wa u v=some w ↔ (label u,label v,w)∈edges g
  symmetric : ∀ u v, wa u v=wa v u

structure Invariant (g : Graph) (wa : Weights n) (root : Fin n)
    (s : State n) (marked : List (Fin n)) : Prop where
  partition : (s.fresh++marked).Perm (List.finRange n)
  root_marked : root∈marked
  growing : Prim.Correctness.Growing (nodes g) (marked.map label,edgesFor root s marked)
  subgraph : edgesFor root s marked ⊆ edges g
  finite_marked : ∀ u∈marked,u≠root → ∃ w,distance s u=some w
  best : ∀ u∈s.fresh,
    (∀ v∈marked,DLE (distance s u) (wa u v)) ∧
    (∀ w,distance s u=some w → parent s u∈marked ∧ wa u (parent s u)=some w)
  exchange : ExchangeInv g (edgesFor root s marked)

theorem fresh_nodup {g : Graph} {wa : Weights n} {root : Fin n}
    {s : State n} {marked : List (Fin n)} (h : Invariant g wa root s marked) :
    s.fresh.Nodup := (List.nodup_append.mp (h.partition.nodup_iff.mpr (List.nodup_finRange n))).1

theorem marked_nodup {g : Graph} {wa : Weights n} {root : Fin n}
    {s : State n} {marked : List (Fin n)} (h : Invariant g wa root s marked) :
    marked.Nodup := (List.nodup_append.mp (h.partition.nodup_iff.mpr (List.nodup_finRange n))).2.1

theorem fresh_not_marked {g : Graph} {wa : Weights n} {root : Fin n}
    {s : State n} {marked : List (Fin n)} (h : Invariant g wa root s marked)
    {v : Fin n} (hv : v∈s.fresh) : v∉marked := by
  intro hm
  exact (List.nodup_append.mp (h.partition.nodup_iff.mpr
    (List.nodup_finRange n))).2.2 v hv v hm rfl

theorem not_marked_fresh {g : Graph} {wa : Weights n} {root : Fin n}
    {s : State n} {marked : List (Fin n)} (h : Invariant g wa root s marked)
    {v : Fin n} (hv : v∉marked) : v∈s.fresh := by
  have hm := h.partition.mem_iff.mpr (List.mem_finRange v)
  exact (List.mem_append.mp hm).resolve_right hv

private theorem shift_partition {s : State n} {marked : List (Fin n)} {v : Fin n}
    (hp : (s.fresh++marked).Perm (List.finRange n)) (hn : s.fresh.Nodup)
    (hv : v∈s.fresh) : (Prim.Array.remaining s v++v::marked).Perm (List.finRange n) := by
  have he : Prim.Array.remaining s v=s.fresh.erase v := by rw [Prim.Array.remaining,← hn.erase_eq_filter]
  have hc : (v::Prim.Array.remaining s v).Perm s.fresh := by
    rw [he]
    exact (List.perm_cons_erase hv).symm
  exact List.perm_middle.trans ((hc.append (List.Perm.refl marked)).trans hp)

theorem edgesFor_congr {root : Fin n} {s t : State n} {vs : List (Fin n)}
    (h : ∀ u∈vs,lookup s.links u=lookup t.links u) :
    edgesFor root s vs=edgesFor root t vs := by
  apply List.filterMap_congr
  intro v hv
  have he := h v hv
  have hf : edgeFor s v = edgeFor t v := by
    funext w
    simp only [edgeFor, parent, he]
  simp only [distance, he, hf]

theorem edgesFor_perm {root : Fin n} {s : State n} {xs ys : List (Fin n)}
    (h : xs.Perm ys) : (edgesFor root s xs).Perm (edgesFor root s ys) := by
  exact h.filterMap _

private theorem endpoints_rank {g : Graph} {wa : Weights n} (hg : MatrixRep g wa)
    {e : Edge} (he : e∈edges g) :
    ∃ u v : Fin n,e=(label u,label v,weight e) := by
  have hh := hg.endpoints e he
  rw [hg.vertices,labels] at hh
  obtain ⟨u,_,hu⟩ := List.mem_map.mp hh.1
  obtain ⟨v,_,hv⟩ := List.mem_map.mp hh.2
  exact ⟨u,v,by cases e with | mk a rest => cases rest with | mk b w =>
    simp only [source,target,label,weight] at hu hv ⊢
    exact Prod.ext hu.symm (Prod.ext hv.symm rfl)⟩

/-- Every crossing edge has an outside rank whose cached link is no heavier. -/
theorem crossing_cached {g : Graph} {wa : Weights n} {root : Fin n}
    {s : State n} {marked : List (Fin n)} (hg : MatrixRep g wa)
    (hi : Invariant g wa root s marked) {e : Edge} (he : e∈edges g)
    (hs : Prim.Core.Safe (marked.map label) e) :
    ∃ u∈s.fresh,DLE (distance s u) (some (weight e)) := by
  obtain ⟨u,v,hev⟩ := endpoints_rank hg he
  have hw : wa u v=some (weight e) := (hg.cell u v (weight e)).mpr (hev ▸ he)
  have hs' : (u∈marked ∧ v∉marked) ∨ (v∈marked ∧ u∉marked) := by
    rw [hev] at hs
    simpa only [Prim.Core.Safe,source,target,label_mem_map] using hs
  rcases hs' with ⟨hu,hv⟩ | ⟨hv,hu⟩
  · have hvf := not_marked_fresh hi hv
    refine ⟨v,hvf,?_⟩
    have hh := (hi.best v hvf).1 u hu
    rwa [hg.symmetric v u,hw] at hh
  · have huf := not_marked_fresh hi hu
    refine ⟨u,huf,?_⟩
    have hh := (hi.best u huf).1 v hv
    rwa [hw] at hh

/-- The selected cached edge is finite whenever the remaining cut is connected. -/
theorem choose_finite {g : Graph} {wa : Weights n} {root v : Fin n}
    {s : State n} {marked : List (Fin n)} (hg : MatrixRep g wa)
    (hi : Invariant g wa root s marked) (hc : ConnectedGraph g)
    (hchoose : choose s=some v) : ∃ w,distance s v=some w := by
  have hvfresh := (choose_spec hchoose).1
  have hvout := fresh_not_marked hi hvfresh
  have hroot : label root∈nodes g := by rw [hg.vertices]; exact mem_labels root
  have hv : label v∈nodes g := by rw [hg.vertices]; exact mem_labels v
  have hreach := hc (label root) hroot (label v) hv
  have hsafe : Prim.Core.Safe (marked.map label) (label root,label v,0) :=
    Or.inl ⟨(label_mem_map root marked).mpr hi.root_marked,
      fun hm => hvout ((label_mem_map v marked).mp hm)⟩
  obtain ⟨e,he,hes⟩ := reach_crossing (e := (label root,label v,0)) hreach hsafe
  obtain ⟨u,hu,hub⟩ := crossing_cached hg hi he hes
  have hbound := dle_trans ((choose_spec hchoose).2 u hu).1 hub
  obtain ⟨w,hw,_⟩ := dle_finite hbound
  exact ⟨w,hw⟩

theorem choose_cut_minimum {g : Graph} {wa : Weights n} {root v : Fin n}
    {s : State n} {marked : List (Fin n)} {w : Int} (hg : MatrixRep g wa)
    (hi : Invariant g wa root s marked) (hchoose : choose s=some v)
    (hw : distance s v=some w) :
    edgeFor s v w∈edges g ∧ Prim.Core.Safe (marked.map label) (edgeFor s v w) ∧
    (∀ e∈edges g,Prim.Core.Safe (marked.map label) e → w≤weight e) := by
  have hvm := (choose_spec hchoose).1
  have hparent := (hi.best v hvm).2 w hw
  have hcell : wa (parent s v) v=some w := by rw [hg.symmetric]; exact hparent.2
  refine ⟨(hg.cell _ _ _).mp hcell,Or.inl ⟨?_,?_⟩,?_⟩
  · exact (label_mem_map _ marked).mpr hparent.1
  · intro hv
    exact fresh_not_marked hi hvm ((label_mem_map _ marked).mp hv)
  · intro e he hsafe
    obtain ⟨u,hu,hbound⟩ := crossing_cached hg hi he hsafe
    have hh := dle_trans ((choose_spec hchoose).2 u hu).1 hbound
    simpa only [hw,DLE] using hh

private theorem update_marked_lookup {g : Graph} {wa : Weights n} {root v : Fin n}
    {s : State n} {marked : List (Fin n)} (hi : Invariant g wa root s marked)
    {u : Fin n} (hu : u∈marked) :
    lookup (update wa s v).links u=lookup s.links u := by
  apply update_unchanged wa s v u (fresh_nodup hi)
  intro hm
  exact fresh_not_marked hi ((mem_remaining _ _ _).mp hm).1 hu

private theorem update_chosen_lookup {g : Graph} {wa : Weights n} {root v : Fin n}
    {s : State n} {marked : List (Fin n)} (hi : Invariant g wa root s marked) :
    lookup (update wa s v).links v=lookup s.links v := by
  apply update_unchanged wa s v v (fresh_nodup hi)
  simp [mem_remaining]

theorem update_edges {g : Graph} {wa : Weights n} {root v : Fin n}
    {s : State n} {marked : List (Fin n)} {w : Int}
    (hi : Invariant g wa root s marked) (hv : v∈s.fresh)
    (hw : distance s v=some w) :
    edgesFor root (update wa s v) (v::marked)=edgeFor s v w::edgesFor root s marked := by
  have hne : v≠root := fun he => fresh_not_marked hi hv (he ▸ hi.root_marked)
  have hlookup := update_chosen_lookup hi (v := v)
  have htail : edgesFor root (update wa s v) marked=edgesFor root s marked :=
    edgesFor_congr (fun u hu => update_marked_lookup hi hu)
  have hd : distance (update wa s v) v=some w := by
    simpa only [distance,hlookup] using hw
  have he : edgeFor (update wa s v) v w=edgeFor s v w := by
    simp only [edgeFor,parent,hlookup]
  simp only [edgesFor,List.filterMap_cons,ite_eq_right hne,hd,Option.map_some]
  change edgeFor (update wa s v) v w :: edgesFor root (update wa s v) marked = _
  rw [he,htail]
  rfl

theorem update_invariant {g : Graph} {wa : Weights n} {root v : Fin n}
    {s : State n} {marked : List (Fin n)} {w : Int} (hg : MatrixRep g wa)
    (hi : Invariant g wa root s marked) (hchoose : choose s=some v)
    (hw : distance s v=some w) : Invariant g wa root (update wa s v) (v::marked) := by
  have hv := (choose_spec hchoose).1
  have hnd := fresh_nodup hi
  have hcut := choose_cut_minimum hg hi hchoose hw
  have hparent := (hi.best v hv).2 w hw
  have hedge := update_edges hi hv hw
  have hsource : source (edgeFor s v w)∈nodes (marked.map label,edgesFor root s marked) :=
    (label_mem_map _ marked).mpr hparent.1
  have htree : ((v::marked).map label,edgesFor root (update wa s v) (v::marked)) =
      Prim.Core.addP (edgeFor s v w) (marked.map label,edgesFor root s marked) := by
    rw [Prim.Core.addP,ite_eq_left hsource,hedge]
    rfl
  have hfinite : ∀ u∈v::marked,u≠root → ∃ w,distance (update wa s v) u=some w := by
    intro u hu hne
    rcases List.mem_cons.mp hu with hu | hu
    · subst u
      refine ⟨w,?_⟩
      simpa only [distance,update_chosen_lookup hi] using hw
    · obtain ⟨c,hc⟩ := hi.finite_marked u hu hne
      refine ⟨c,?_⟩
      simpa only [distance,update_marked_lookup hi hu] using hc
  refine ⟨shift_partition hi.partition hnd hv,List.mem_cons_of_mem _ hi.root_marked,
    ?_,?_,hfinite,?_,?_⟩
  · rw [htree]
    exact Prim.Correctness.growing_add hi.growing (hg.endpoints _ hcut.1).1
      (hg.endpoints _ hcut.1).2 hcut.2.1
  · rw [hedge]
    exact List.cons_subset.mpr ⟨hcut.1,hi.subgraph⟩
  · intro u hu
    change u∈Prim.Array.remaining s v at hu
    have hum := (mem_remaining s v u).mp hu
    have hlookup := update_lookup wa s v u hnd
    rw [ite_eq_left hu] at hlookup
    refine ⟨?_,?_⟩
    · intro a ha
      rcases List.mem_cons.mp ha with ha | ha
      · subst a
        exact update_relax_le wa s v u hnd hu
      · exact dle_trans (update_distance_le wa s v u hnd) ((hi.best u hum.1).1 a ha)
    · intro c hc
      by_cases hb : DLE (distance s u) (wa u v)
      · have hsame : lookup (update wa s v).links u=lookup s.links u := by
          rw [hlookup,better]
          exact ite_eq_left hb
        have hold : distance s u=some c := by
          simpa only [distance,hsame] using hc
        have hp := (hi.best u hum.1).2 c hold
        have heparent : parent (update wa s v) u=parent s u := congrArg Prod.fst hsame
        rw [heparent]
        exact ⟨List.mem_cons_of_mem _ hp.1,hp.2⟩
      · have hnew : lookup (update wa s v).links u=(v,wa u v) := by
          rw [hlookup,better]
          exact ite_eq_right hb
        have hcell : wa u v=some c := by simpa only [distance,hnew] using hc
        have heparent : parent (update wa s v) u=v := congrArg Prod.fst hnew
        rw [heparent]
        exact ⟨List.mem_cons_self,hcell⟩
  · rw [hedge]
    exact exchangeInv_cut_step hi.growing.inside hg.endpoints hcut.1 hcut.2.1
      hcut.2.2 hi.exchange

theorem after_root_invariant {g : Graph} {wa : Weights n} (hg : MatrixRep g wa)
    (root : Fin n) : Invariant g wa root (update wa (start root) root) [root] := by
  have hn : (start root).fresh.Nodup := List.nodup_finRange n
  have hpart : ((start root).fresh++[]).Perm (List.finRange n) := by
    simp only [start,List.append_nil]
    exact List.Perm.refl _
  have hzero : edgesFor root (update wa (start root) root) [root]=[] := by
    simp [edgesFor]
  have hroot : label root∈nodes g := by rw [hg.vertices]; exact mem_labels root
  have hnodes : (nodes g).Nodup := hg.vertices ▸ labels_nodup n
  refine ⟨shift_partition hpart hn (List.mem_finRange root),by simp,?_,?_,?_,?_,?_⟩
  · rw [hzero]
    refine ⟨by simp [nodes],by simp [nodes],?_,forest_nil hnodes,?_,?_⟩
    · simpa [nodes] using hroot
    · intro e he
      cases he
    · intro u hu v hv
      have hue : u=label root := by simpa [nodes] using hu
      have hve : v=label root := by simpa [nodes] using hv
      subst u
      subst v
      exact Connected.refl hroot
  · rw [hzero]
    simp
  · intro u hu hne
    have he : u=root := by simpa using hu
    exact False.elim (hne he)
  · intro u hu
    change u∈Prim.Array.remaining (start root) root at hu
    have hum := (mem_remaining (start root) root u).mp hu
    have hlookup := update_lookup wa (start root) root u hn
    rw [ite_eq_left hu] at hlookup
    have hd : distance (start root) u=none := by rw [start_distance,ite_eq_right hum.2]
    refine ⟨?_,?_⟩
    · intro v hv
      have he : v=root := by simpa using hv
      subst v
      exact update_relax_le wa (start root) root u hn hu
    · intro w hw
      cases hc : wa u root with
      | none =>
          have hout : distance (update wa (start root) root) u=none := by
            unfold distance
            rw [hlookup]
            simp only [better,show (lookup (start root).links u).2=none from hd,
              hc,DLE,ite_true]
          rw [hout] at hw
          cases hw
      | some c =>
          have hout : lookup (update wa (start root) root).links u=(root,some c) := by
            rw [hlookup]
            simp only [better,show (lookup (start root).links u).2=none from hd,
              hc,DLE,ite_false]
          have hew : c=w := by
            have hh : some c=some w := by simpa only [distance,hout] using hw
            exact Option.some.inj hh
          have hp : parent (update wa (start root) root) u=root := congrArg Prod.fst hout
          rw [hp]
          exact ⟨by simp,hew ▸ hc⟩
  · rw [hzero]
    exact exchangeInv_nil g

theorem run_fresh_counts {wa : Weights n} {s out : State n} {k : Nat}
    (hn : s.fresh.Nodup) (h : run wa k s=some out) :
    out.fresh.Nodup ∧ out.fresh.length+k=s.fresh.length := by
  induction k generalizing s with
  | zero =>
      cases Option.some.inj h
      exact ⟨hn,by simp⟩
  | succ k ih =>
      obtain ⟨middle,hm,ho⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨v,hv,hmid⟩ := Option.map_eq_some_iff.mp hm
      subst middle
      have hnd := remaining_nodup s v hn
      have hz := remaining_length s v hn (choose_spec hv).1
      have hh := ih hnd ho
      have hpos := List.length_pos_of_mem (choose_spec hv).1
      change out.fresh.Nodup ∧ out.fresh.length+(k+1)=s.fresh.length
      change (Prim.Array.remaining s v).length=s.fresh.length-1 at hz
      change out.fresh.Nodup ∧ out.fresh.length+k=(Prim.Array.remaining s v).length at hh
      exact ⟨hh.1,by omega⟩

theorem run_available_invariant {g : Graph} {wa : Weights n} {root : Fin n}
    {s : State n} {marked : List (Fin n)} {k : Nat} (hg : MatrixRep g wa)
    (hc : ConnectedGraph g) (hi : Invariant g wa root s marked)
    (hk : k≤s.fresh.length) :
    ∃ out marked',run wa k s=some out ∧ Invariant g wa root out marked' ∧
      out.fresh.length+k=s.fresh.length := by
  induction k generalizing s marked with
  | zero => exact ⟨s,marked,rfl,hi,by simp⟩
  | succ k ih =>
      have hne : s.fresh≠[] := by intro he; simp only [he,List.length_nil] at hk; omega
      have hchoose : ∃ v,choose s=some v := by
        cases hv : choose s with
        | none => exact False.elim (hne ((choose_none s).mp hv))
        | some v => exact ⟨v,rfl⟩
      obtain ⟨v,hv⟩ := hchoose
      obtain ⟨w,hw⟩ := choose_finite hg hi hc hv
      have hnext := update_invariant hg hi hv hw
      have hlen := remaining_length s v (fresh_nodup hi) (choose_spec hv).1
      obtain ⟨out,marked',hout,hiout,hsize⟩ := ih hnext (by
        change k≤(Prim.Array.remaining s v).length
        omega)
      refine ⟨out,marked',?_,hiout,?_⟩
      · simp only [run,step,hv,Option.map_some,Option.bind_some,hout]
      · change out.fresh.length+k=(Prim.Array.remaining s v).length at hsize
        omega

theorem finished_minimum {g : Graph} {wa : Weights n} {root : Fin n}
    {s : State n} {marked : List (Fin n)} (hg : MatrixRep g wa)
    (hi : Invariant g wa root s marked) (hf : s.fresh=[]) :
    extractP root s=some (labels n,edgesFor root s (List.finRange n)) ∧
      MinimumSpanningTree g (labels n,edgesFor root s (List.finRange n)) := by
  have hp : marked.Perm (List.finRange n) := by simpa only [hf,List.nil_append] using hi.partition
  have hlabel : (marked.map label).Perm (nodes g) := by rw [hg.vertices]; exact hp.map label
  have hedge := edgesFor_perm (root := root) (s := s) hp.symm
  have hspan : SpanningEdges (nodes g) (edgesFor root s marked) := by
    refine ⟨?_,hi.growing.forest,?_⟩
    · intro he
      have hm : label root∈nodes g := hlabel.subset ((label_mem_map root marked).mpr hi.root_marked)
      rw [he] at hm
      cases hm
    · intro u hu v hv
      exact hi.growing.connected u (hlabel.mem_iff.mpr hu) v (hlabel.mem_iff.mpr hv)
  refine ⟨?_,?_,?_⟩
  · have hex := extractOn_eq (root := root) (s := s) (vs := List.finRange n)
      (fun u hu hn => hi.finite_marked u (hp.mem_iff.mpr hu) hn)
    simp only [extractP,hex,Option.map_some]
  · refine ⟨hg.vertices.symm,?_,hspan.1,?_,?_⟩
    · exact fun e he => hi.subgraph (hedge.subset he)
    · exact (forest_perm hedge).mpr hi.growing.forest
    · intro u hu v hv
      exact reach_mono hedge.symm.subset (hspan.2.2 u hu v hv)
  · intro t ht
    obtain ⟨replacement,hr,hsub,hcost⟩ := hi.exchange t ht
    have hp := spanning_subforest_eq_perm hspan hr.2.2.2.1 hsub
    have hcosteq : costMCST (labels n,edgesFor root s (List.finRange n)) =
        costMCST replacement := ((hedge.trans hp).map weight).sum_eq
    rw [hcosteq]
    exact hcost

theorem full_run_minimum {g : Graph} {wa : Weights n} (hg : MatrixRep g wa)
    (hc : ConnectedGraph g) (root : Fin n) :
    ∃ out t,run wa n (start root)=some out ∧ out.fresh=[] ∧
      extractP root out=some t ∧ MinimumSpanningTree g t := by
  have hinit := after_root_invariant hg root
  have hlen : (update wa (start root) root).fresh.length=n-1 := by
    have hh := remaining_length (start root) root (List.nodup_finRange n) (List.mem_finRange root)
    change (Prim.Array.remaining (start root) root).length=n-1
    simpa only [start,List.length_finRange] using hh
  obtain ⟨out,marked,hout,hiout,hsize⟩ := run_available_invariant hg hc hinit
    (k := n-1) (by omega)
  have hf : out.fresh=[] := List.eq_nil_of_length_eq_zero (by omega)
  have hm := finished_minimum hg hiout hf
  refine ⟨out,_,?_,hf,hm.1,hm.2⟩
  have hn : 0<n := Nat.lt_of_le_of_lt (Nat.zero_le _) root.isLt
  have he : n=(n-1)+1 := by omega
  have hr := congrArg (fun k => run wa k (start root)) he
  rw [hr,run]
  simp only [step,choose_first_root,Option.map_some,Option.bind_some]
  exact hout

theorem extract_links_congr (root : Fin n) {s t : State n} (h : s.links=t.links) :
    extractP root s=extractP root t := by
  have he : ∀ vs,extractOn root s vs=extractOn root t vs := by
    intro vs
    induction vs with
    | nil => rfl
    | cons v vs ih =>
        simp only [extractOn,distance,parent,edgeFor,h,ih]
  simp only [extractP,he]

/-- The last selection changes no link: n-1 passes already determine every edge. -/
theorem final_pending_link {wa : Weights n} {root : Fin n} {out : State n}
    (h : run wa n (start root)=some out) :
    ∃ before,run wa (n-1) (start root)=some before ∧
      before.fresh.length=1 ∧ before.links=out.links := by
  have hn : 0<n := Nat.lt_of_le_of_lt (Nat.zero_le _) root.isLt
  have he : n=(n-1)+1 := by omega
  have hr := congrArg (fun k => run wa k (start root)) he
  rw [hr,run_add] at h
  obtain ⟨before,hbefore,hlast⟩ := Option.bind_eq_some_iff.mp h
  have hcounts := run_fresh_counts (List.nodup_finRange n) hbefore
  have hsize : before.fresh.length=1 := by
    change before.fresh.Nodup ∧ before.fresh.length+(n-1)=(List.finRange n).length at hcounts
    rw [List.length_finRange] at hcounts
    omega
  have hstep : step wa before=some out := by
    cases hs : step wa before <;> simpa only [run,hs,Option.bind_none,Option.bind_some] using hlast
  obtain ⟨v,hv,hout⟩ := Option.map_eq_some_iff.mp hstep
  have hmem := (choose_spec hv).1
  have hsingle : before.fresh=[v] := by
    obtain ⟨u,hu⟩ := List.length_eq_one_iff.mp hsize
    have hev : v=u := by simpa only [hu,List.mem_singleton] using hmem
    simpa only [hev] using hu
  refine ⟨before,hbefore,hsize,?_⟩
  rw [← hout]
  exact (last_update_links wa before v hsingle).symm

theorem prim2_exists_minimum {g : Graph} {wa : Weights n} (hg : MatrixRep g wa)
    (hc : ConnectedGraph g) (root : Fin n) :
    ∃ t,prim2 wa root=some t ∧ MinimumSpanningTree g t := by
  obtain ⟨out,t,hrun,_,hex,hm⟩ := full_run_minimum hg hc root
  obtain ⟨before,hbefore,_,hlinks⟩ := final_pending_link hrun
  have he := (extract_links_congr root hlinks).trans hex
  refine ⟨t,?_,hm⟩
  simp only [prim2,prim2State,hbefore,Option.bind_some,he]

theorem prim2_minimum {g t : Graph} {wa : Weights n} {root : Fin n}
    (hg : MatrixRep g wa) (hc : ConnectedGraph g) (h : prim2 wa root=some t) :
    MinimumSpanningTree g t := by
  obtain ⟨other,ho,hm⟩ := prim2_exists_minimum hg hc root
  have he : other=t := Option.some.inj (ho.symm.trans h)
  exact he ▸ hm

end Prim.ArrayOptimality
