import Applications.Dijkstra.Core

/-!
# Dijkstra's frontier invariant and independent global shortest paths

All comparisons are against the directed `Walk` relation, not an enumeration or
an objective computed from the executor. The literal start has n fresh vertices;
therefore n−1 updates leave one fresh vertex. The final-vertex argument below is
separate from the settled-vertex induction and proves that its distance is also
optimal. Genuine infinity gives an exact unreachable-vertex result as well.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Dijkstra.Optimality
open Dijkstra.Store
open Core
variable {n : Nat}

structure Invariant (wa : Weights n) (root : Fin n) (s : State n) : Prop where
  nodup : s.fresh.Nodup
  root_zero : distance s root=some 0
  realizes : ∀ v d,distance s v=some d → Walk wa root v d
  settled : ∀ v,v∉s.fresh → ∀ c,Walk wa root v c → DLE (distance s v) (some c)
  frontier : ∀ v,v∉s.fresh → ∀ u,u∈s.fresh →
    DLE (distance s u) (plus (distance s v) (wa v u))

theorem start_invariant (wa : Weights n) (root : Fin n) : Invariant wa root (start root) := by
  refine ⟨List.nodup_finRange _,?_,?_,?_,?_⟩
  · simp [start_distance]
  · intro v d hd
    rw [start_distance] at hd
    split at hd
    · subst v
      cases hd
      exact .nil
    · cases hd
  · intro v hv
    exact False.elim (hv (List.mem_finRange v))
  · intro v hv
    exact False.elim (hv (List.mem_finRange v))

/-- First-fresh-vertex proof, written as induction over arbitrary directed walks.
    Nonnegative edge weights justify every prefix-cost bound. -/
theorem frontier_min_bound (wa : Weights n) (root : Fin n) (s : State n)
    (inv : Invariant wa root s) (v : Fin n)
    (hm : ∀ u∈s.fresh,DLE (distance s v) (distance s u))
    (u : Fin n) (c : Nat) (hw : Walk wa root u c) (hu : u∈s.fresh) :
    DLE (distance s v) (some c) := by
  induction hw with
  | nil => simpa [inv.root_zero] using hm root hu
  | @snoc x y d w hp he ih =>
      by_cases hx : x∈s.fresh
      · exact dle_trans (ih hx) (by simp [DLE])
      · have hf := inv.frontier x hx y hu
        have hd := inv.settled x hx d hp
        have hs := plus_mono_left hd (wa x y)
        rw [he] at hf hs
        exact dle_trans (hm y hu) (dle_trans hf hs)

theorem selected_bound (wa : Weights n) (root : Fin n) (s : State n)
    (inv : Invariant wa root s) (v : Fin n) (hs : choose s=some v)
    (c : Nat) (hw : Walk wa root v c) : DLE (distance s v) (some c) := by
  have hc := choose_spec hs
  exact frontier_min_bound wa root s inv v (fun u hu => (hc.2 u hu).1) v c hw hc.1

theorem selected_shortest (wa : Weights n) (root : Fin n) (s : State n)
    (inv : Invariant wa root s) (v : Fin n) (hs : choose s=some v)
    (d : Nat) (hd : distance s v=some d) : Shortest wa root v d := by
  refine ⟨inv.realizes v d hd,fun c hw => ?_⟩
  simpa [hd,DLE] using selected_bound wa root s inv v hs c hw

theorem selected_finite (wa : Weights n) (root : Fin n) (s : State n)
    (inv : Invariant wa root s) (v : Fin n) (hs : choose s=some v)
    (hr : ∃ c,Walk wa root v c) : ∃ d,distance s v=some d ∧ Shortest wa root v d := by
  obtain ⟨c,hc⟩ := hr
  obtain ⟨d,hd,_⟩ := dle_finite (selected_bound wa root s inv v hs c hc)
  exact ⟨d,hd,selected_shortest wa root s inv v hs d hd⟩

theorem update_invariant (wa : Weights n) (root : Fin n) (s : State n)
    (inv : Invariant wa root s) (v : Fin n) (hs : choose s=some v) :
    Invariant wa root (update wa s v) := by
  have hc := choose_spec hs
  have hu (u : Fin n) (h : u∉remaining s v) :
      distance (update wa s v) u=distance s u :=
    congrArg Prod.snd (update_unchanged wa s v u inv.nodup h)
  have hv : v∉remaining s v := by simp [mem_remaining]
  refine ⟨remaining_nodup s v inv.nodup,?_,?_,?_,?_⟩
  · have hroot := update_distance_le wa s v root inv.nodup
    rw [inv.root_zero] at hroot
    obtain ⟨d,hd,hle⟩ := dle_finite hroot
    have he : d=0 := by omega
    simpa [he] using hd
  · intro u d hd
    unfold distance at hd
    rw [update_lookup wa s v u inv.nodup] at hd
    split at hd
    · unfold better at hd
      split at hd
      · exact inv.realizes u d hd
      · dsimp at hd
        cases hvd : distance s v with
        | none => simp [hvd,plus] at hd
        | some e =>
            cases he : wa v u with
            | none => simp [he,plus] at hd
            | some w =>
                simp only [hvd,he,plus,Option.some.injEq] at hd
                subst d
                exact .snoc (inv.realizes v e hvd) he
    · exact inv.realizes u d hd
  · intro u huf c hp
    change u∉remaining s v at huf
    rw [hu u huf]
    by_cases he : u=v
    · subst u
      exact selected_bound wa root s inv v hs c hp
    · have hnot : u∉s.fresh := by
        intro hf
        exact huf ((mem_remaining s v u).mpr ⟨hf,he⟩)
      exact inv.settled u hnot c hp
  · intro u huf z hz
    change u∉remaining s v at huf
    change z∈remaining s v at hz
    rw [hu u huf]
    by_cases he : u=v
    · subst u
      exact update_relax_le wa s v z inv.nodup hz
    · have hnot : u∉s.fresh := by
        intro hf
        exact huf ((mem_remaining s v u).mpr ⟨hf,he⟩)
      have hzold := ((mem_remaining s v z).mp hz).1
      exact dle_trans (update_distance_le wa s v z inv.nodup) (inv.frontier u hnot z hzold)

theorem step_invariant (wa : Weights n) (root : Fin n) (s out : State n)
    (inv : Invariant wa root s) (h : step wa s=some out) : Invariant wa root out := by
  unfold step at h
  cases hs : choose s with
  | none => simp [hs] at h
  | some v =>
      simp only [hs,Option.map_some,Option.some.injEq] at h
      subst out
      exact update_invariant wa root s inv v hs

theorem run_progress (wa : Weights n) (root : Fin n) (s : State n)
    (inv : Invariant wa root s) (k : Nat) (hk : k≤s.fresh.length) :
    ∃ out,run wa k s=some out ∧ Invariant wa root out ∧
      out.fresh.length=s.fresh.length-k := by
  induction k with
  | zero => exact ⟨s,rfl,inv,by omega⟩
  | succ k ih =>
      obtain ⟨mid,hr,hi,hlen⟩ := ih (by omega)
      have hn : mid.fresh≠[] := by intro he;simp [he] at hlen;omega
      obtain ⟨v,hv⟩ : ∃ v,choose mid=some v := by
        cases he : choose mid with
        | none => exact False.elim (hn ((choose_none mid).mp he))
        | some v => exact ⟨v,rfl⟩
      refine ⟨update wa mid v,?_,update_invariant wa root mid hi v hv,?_⟩
      · simp [run,hr,step,hv]
      · change (remaining mid v).length=s.fresh.length-(k+1)
        rw [remaining_length mid v hi.nodup (choose_spec hv).1,hlen]
        omega

theorem run_invariant (wa : Weights n) (root : Fin n) (s out : State n)
    (inv : Invariant wa root s) (k : Nat) (h : run wa k s=some out) :
    Invariant wa root out := by
  induction k generalizing out with
  | zero => cases h;exact inv
  | succ k ih =>
      simp only [run] at h
      cases hr : run wa k s with
      | none => simp [hr] at h
      | some mid =>
          simp only [hr,Option.bind_some] at h
          exact step_invariant wa root mid out (ih mid hr) h

private theorem only_fresh (vs : List (Fin n)) (h : vs.length≤1)
    (u v : Fin n) (hu : u∈vs) (hv : v∈vs) : u=v := by
  cases vs with
  | nil => simp at hu
  | cons a vs =>
      cases vs with
      | nil => simpa using (List.mem_singleton.mp hu).trans (List.mem_singleton.mp hv).symm
      | cons b bs => simp at h

/-- The one vertex left fresh after n−1 source steps is already optimal too. -/
theorem completed_bound (wa : Weights n) (root : Fin n) (s : State n)
    (inv : Invariant wa root s) (hlen : s.fresh.length≤1)
    (v : Fin n) (c : Nat) (hw : Walk wa root v c) : DLE (distance s v) (some c) := by
  by_cases hv : v∈s.fresh
  · apply frontier_min_bound wa root s inv v _ v c hw hv
    intro u hu
    have he := only_fresh s.fresh hlen u v hu hv
    subst u
    exact dle_refl _
  · exact inv.settled v hv c hw

/-- Exact optimum/unreachability statement, independent of reachability assumptions. -/
def Correct (wa : Weights n) (root : Fin n) (s : State n) : Prop :=
  (∀ v d,distance s v=some d → Shortest wa root v d) ∧
  (∀ v,distance s v=none ↔ ¬ ∃ d,Walk wa root v d)

theorem completed_correct (wa : Weights n) (root : Fin n) (s : State n)
    (inv : Invariant wa root s) (hlen : s.fresh.length≤1) : Correct wa root s := by
  constructor
  · intro v d hd
    refine ⟨inv.realizes v d hd,fun c hp => ?_⟩
    simpa [hd,DLE] using completed_bound wa root s inv hlen v c hp
  · intro v
    constructor
    · intro hd ⟨c,hp⟩
      have hh := completed_bound wa root s inv hlen v c hp
      simp [hd,DLE] at hh
    · intro hn
      cases hd : distance s v with
      | none => rfl
      | some d => exact False.elim (hn ⟨d,inv.realizes v d hd⟩)

theorem dijkstra_correct (wa : Weights n) (root : Fin n) :
    ∃ out,dijkstra wa root=some out ∧ Invariant wa root out ∧
      out.fresh.length=1 ∧ Correct wa root out := by
  obtain ⟨out,ho,hi,hlen⟩ := run_progress wa root (start root)
    (start_invariant wa root) (n-1) (by simp [start])
  have hn : 0<n := by have := root.isLt;omega
  have hl : out.fresh.length=1 := by simp only [start,List.length_finRange] at hlen;omega
  exact ⟨out,ho,hi,hl,completed_correct wa root out hi (by omega)⟩

theorem dijkstra_shortest (wa : Weights n) (root : Fin n) (hr : Reachable wa root) :
    ∃ out,dijkstra wa root=some out ∧ ∀ v,∃ d,
      distance out v=some d ∧ Shortest wa root v d := by
  obtain ⟨out,ho,_,_,hc⟩ := dijkstra_correct wa root
  refine ⟨out,ho,fun v => ?_⟩
  cases hd : distance out v with
  | none => exact False.elim ((hc.2 v).mp hd (hr v))
  | some d => exact ⟨d,rfl,hc.1 v d hd⟩

end Dijkstra.Optimality
