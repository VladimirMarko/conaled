import Applications.Dijkstra.Optimality
import Mathlib.Data.List.Basic

/-!
# Parent-array reconstruction and simple shortest paths

The source follows parent pointers backwards and reverses the result. A finite
fuel check totalizes malformed cyclic arrays. Reachable source states carry a
stronger constructive invariant: every finite label has a duplicate-free parent
chain to the root, so n cells of fuel always suffice. This evidence is separate
from scalar-distance optimality.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Dijkstra.Paths
open Dijkstra.Store
open List (Forall₂)
open Core Optimality
variable {n : Nat}

/-- A concrete directed vertex sequence, independent of parent pointers. -/
inductive Path (wa : Weights n) (root : Fin n) : List (Fin n) → Fin n → Nat → Prop
  | nil : Path wa root [root] root 0
  | snoc {ps : List (Fin n)} {v u : Fin n} {d w : Nat} :
      Path wa root ps v d → wa v u=some w → Path wa root (ps++[u]) u (d+w)

theorem Path.walk {wa : Weights n} {root v : Fin n} {ps : List (Fin n)} {d : Nat}
    (h : Path wa root ps v d) : Walk wa root v d := by
  induction h with
  | nil => exact .nil
  | snoc _ he ih => exact .snoc ih he

/-- Backwards source parent chain, including its exact directed edge cost. -/
inductive Chain (wa : Weights n) (root : Fin n) (s : State n) :
    Fin n → List (Fin n) → Nat → Prop
  | root : parent s root=root → Chain wa root s root [root] 0
  | cons {p u : Fin n} {ps : List (Fin n)} {d w : Nat} :
      Chain wa root s p ps d → u≠root → parent s u=p → wa p u=some w →
      Chain wa root s u (u::ps) (d+w)

theorem Chain.head_mem {wa : Weights n} {root : Fin n} {s : State n}
    {v : Fin n} {ps : List (Fin n)} {d : Nat} (h : Chain wa root s v ps d) : v∈ps := by
  cases h <;> simp

theorem Chain.path {wa : Weights n} {root : Fin n} {s : State n}
    {v : Fin n} {ps : List (Fin n)} {d : Nat} (h : Chain wa root s v ps d) :
    Path wa root ps.reverse v d := by
  induction h with
  | root => exact .nil
  | cons _ _ _ he ih => simpa using Path.snoc ih he

theorem Chain.transport {wa : Weights n} {root : Fin n} {s t : State n}
    {v : Fin n} {ps : List (Fin n)} {d : Nat} (h : Chain wa root s v ps d)
    (he : ∀ u∈ps,parent t u=parent s u) : Chain wa root t v ps d := by
  induction h with
  | root hr => exact .root ((he _ (by simp)).trans hr)
  | @cons p u ps d w hp hn hparent hw ih =>
      exact .cons (ih (fun x hx => he x (by simp [hx]))) hn
        ((he u (by simp)).trans hparent) hw

structure Parents (wa : Weights n) (root : Fin n) (s : State n) : Prop where
  root_parent : parent s root=root
  paths : ∀ v d,distance s v=some d → ∃ ps,
    Chain wa root s v ps d ∧ ps.Nodup ∧ ∀ u∈ps,u≠v → u∉s.fresh

theorem start_parents (wa : Weights n) (root : Fin n) : Parents wa root (start root) := by
  refine ⟨start_parent root root,?_⟩
  intro v d hd
  rw [start_distance] at hd
  split at hd
  · subst v
    cases hd
    refine ⟨[root],.root (start_parent root root),by simp,?_⟩
    intro u hu hn
    exact False.elim (hn (List.mem_singleton.mp hu))
  · cases hd

private theorem root_lookup_unchanged (wa : Weights n) (root : Fin n) (s : State n)
    (inv : Invariant wa root s) (v : Fin n) :
    lookup (update wa s v).links root=lookup s.links root := by
  rw [update_lookup wa s v root inv.nodup]
  split
  · apply ite_eq_left
    change DLE (distance s root) (plus (distance s v) (wa v root))
    rw [inv.root_zero]
    cases plus (distance s v) (wa v root) <;> simp [DLE]
  · rfl

theorem update_parents (wa : Weights n) (root : Fin n) (s : State n)
    (inv : Invariant wa root s) (par : Parents wa root s)
    (v : Fin n) (_hs : choose s=some v) : Parents wa root (update wa s v) := by
  have stay (u : Fin n) (hu : u∉remaining s v) :
      parent (update wa s v) u=parent s u :=
    congrArg Prod.fst (update_unchanged wa s v u inv.nodup hu)
  have liftChain (u : Fin n) (d : Nat) (ps : List (Fin n))
      (hc : Chain wa root s u ps d) (ha : ∀ x∈ps,x≠u → x∉s.fresh)
      (hu : parent (update wa s v) u=parent s u) :
      Chain wa root (update wa s v) u ps d := by
    apply hc.transport
    intro x hx
    by_cases he : x=u
    · simpa [he] using hu
    · apply stay x
      intro hnew
      exact ha x hx he ((mem_remaining s v x).mp hnew).1
  have oldAncestors (u : Fin n) (ps : List (Fin n))
      (ha : ∀ x∈ps,x≠u → x∉s.fresh) :
      ∀ x∈ps,x≠u → x∉(update wa s v).fresh := by
    intro x hx he hnew
    exact ha x hx he ((mem_remaining s v x).mp hnew).1
  refine ⟨(congrArg Prod.fst (root_lookup_unchanged wa root s inv v)).trans par.root_parent,?_⟩
  intro u d hd
  have heq := update_lookup wa s v u inv.nodup
  by_cases hrem : u∈remaining s v
  · rw [ite_eq_left hrem] at heq
    by_cases hb : DLE (lookup s.links u).2 (v,plus (distance s v) (wa v u)).2
    · rw [better,ite_eq_left hb] at heq
      have hold : distance s u=some d := by
        change (lookup s.links u).2=some d
        rw [← heq]
        exact hd
      obtain ⟨ps,hc,hn,ha⟩ := par.paths u d hold
      exact ⟨ps,liftChain u d ps hc ha (congrArg Prod.fst heq),hn,oldAncestors u ps ha⟩
    · rw [better,ite_eq_right hb] at heq
      have hnew : plus (distance s v) (wa v u)=some d := by
        rw [← show (lookup (update wa s v).links u).2=plus (distance s v) (wa v u)
          from congrArg Prod.snd heq]
        exact hd
      cases hvd : distance s v with
      | none => simp [hvd,plus] at hnew
      | some e =>
          cases hwu : wa v u with
          | none => simp [hwu,plus] at hnew
          | some w =>
              simp only [hvd,hwu,plus,Option.some.injEq] at hnew
              subst d
              obtain ⟨ps,hc,hn,ha⟩ := par.paths v e hvd
              have hvrem : v∉remaining s v := by simp [mem_remaining]
              have hc' := liftChain v e ps hc ha (stay v hvrem)
              have hune : u≠v := ((mem_remaining s v u).mp hrem).2
              have huold := ((mem_remaining s v u).mp hrem).1
              have hunot : u∉ps := by intro hup;exact ha u hup hune huold
              have huroot : u≠root := by
                intro hur
                subst u
                have hzero : distance s root=some 0 := inv.root_zero
                change ¬ DLE (distance s root) (plus (distance s v) (wa v root)) at hb
                rw [hzero] at hb
                simp [hvd,hwu,plus,DLE] at hb
              refine ⟨u::ps,.cons hc' huroot (congrArg Prod.fst heq) hwu,
                List.nodup_cons.mpr ⟨hunot,hn⟩,?_⟩
              intro x hx hxne hxnew
              rcases List.mem_cons.mp hx with he | hx
              · exact hxne he
              · by_cases hxv : x=v
                · subst x
                  exact hvrem hxnew
                · exact ha x hx hxv ((mem_remaining s v x).mp hxnew).1
  · rw [ite_eq_right hrem] at heq
    have hold : distance s u=some d := by
      change (lookup s.links u).2=some d
      rw [← heq]
      exact hd
    obtain ⟨ps,hc,hn,ha⟩ := par.paths u d hold
    exact ⟨ps,liftChain u d ps hc ha (congrArg Prod.fst heq),hn,oldAncestors u ps ha⟩

theorem run_parents (wa : Weights n) (root : Fin n) (s out : State n)
    (inv : Invariant wa root s) (par : Parents wa root s)
    (k : Nat) (h : run wa k s=some out) : Parents wa root out := by
  induction k generalizing out with
  | zero => cases h;exact par
  | succ k ih =>
      simp only [run] at h
      cases hr : run wa k s with
      | none => simp [hr] at h
      | some mid =>
          simp only [hr,Option.bind_some,step] at h
          cases hv : choose mid with
          | none => simp [hv] at h
          | some v =>
              simp only [hv,Option.map_some,Option.some.injEq] at h
              subst out
              exact update_parents wa root mid (run_invariant wa root s mid inv k hr)
                (ih mid hr) v hv

/-- Literal backwards parent chase, with explicit failure on insufficient fuel. -/
def getPathFuel (s : State n) : Nat → Fin n → Option (List (Fin n))
  | 0,_ => none
  | k+1,v =>
      let p := parent s v
      if p=v then some [v] else (getPathFuel s k p).map (v :: ·)

def getPath (s : State n) (v : Fin n) : Option (List (Fin n)) := getPathFuel s n v

theorem chain_getPathFuel {wa : Weights n} {root : Fin n} {s : State n}
    {v : Fin n} {ps : List (Fin n)} {d : Nat} (h : Chain wa root s v ps d)
    (hn : ps.Nodup) (k : Nat) (hk : ps.length≤k) : getPathFuel s k v=some ps := by
  induction h generalizing k with
  | root hp =>
      cases k with
      | zero => simp at hk
      | succ k => simp [getPathFuel,hp]
  | @cons p u ps d w hc hu hp hw ih =>
      have hn' := List.nodup_cons.mp hn
      have hpu : p≠u := by
        intro he
        exact hn'.1 (he ▸ hc.head_mem)
      cases k with
      | zero => simp at hk
      | succ k =>
          simp only [List.length_cons] at hk
          rw [getPathFuel,hp,ite_eq_right hpu,ih hn'.2 k (by omega)]
          rfl

theorem chain_getPath {wa : Weights n} {root : Fin n} {s : State n}
    {v : Fin n} {ps : List (Fin n)} {d : Nat} (h : Chain wa root s v ps d)
    (hn : ps.Nodup) : getPath s v=some ps := by
  apply chain_getPathFuel h hn n
  have hh := hn.length_le_of_subset (l₂ := List.finRange n) (fun x _ => List.mem_finRange x)
  simpa using hh

theorem reconstruct_finite (wa : Weights n) (root : Fin n) (s : State n)
    (par : Parents wa root s) (v : Fin n) (d : Nat) (hd : distance s v=some d) :
    ∃ ps,getPath s v=some ps ∧ ps.Nodup ∧ Path wa root ps.reverse v d := by
  obtain ⟨ps,hc,hn,_⟩ := par.paths v d hd
  exact ⟨ps,chain_getPath hc hn,hn,hc.path⟩

def pathTo (s : State n) (v : Fin n) : Option (List (Fin n) × Distance) :=
  (getPath s v).map (fun ps => (ps.reverse,distance s v))

def extractPaths (s : State n) : Option (List (List (Fin n) × Distance)) :=
  (List.finRange n).mapM (pathTo s)

theorem dijkstra_paths (wa : Weights n) (root : Fin n) (hr : Reachable wa root) :
    ∃ out,dijkstra wa root=some out ∧ ∀ v,∃ ps d,
      pathTo out v=some (ps,some d) ∧ ps.Nodup ∧
      Path wa root ps v d ∧ Shortest wa root v d := by
  obtain ⟨out,ho,hshort⟩ := dijkstra_shortest wa root hr
  have hp := run_parents wa root (start root) out (start_invariant wa root)
    (start_parents wa root) (n-1) ho
  refine ⟨out,ho,fun v => ?_⟩
  obtain ⟨d,hd,hm⟩ := hshort v
  obtain ⟨ps,hg,hn,hpath⟩ := reconstruct_finite wa root out hp v d hd
  exact ⟨ps.reverse,d,by simp [pathTo,hg,hd],
    List.pairwise_reverse.mpr (hn.imp (fun h => Ne.symm h)),hpath,hm⟩

/-- The whole extracted list is in source index order and contains a simple
    globally shortest path for every source-reachable vertex. -/
theorem dijkstra_extractPaths (wa : Weights n) (root : Fin n) (hr : Reachable wa root) :
    ∃ out ps,dijkstra wa root=some out ∧ extractPaths out=some ps ∧
      Forall₂ (fun v p => ∃ d,p.2=some d ∧ p.1.Nodup ∧
        Path wa root p.1 v d ∧ Shortest wa root v d) (List.finRange n) ps := by
  obtain ⟨out,ho,hp⟩ := dijkstra_paths wa root hr
  let value (v : Fin n) := (pathTo out v).getD ([], none)
  have hv (v : Fin n) : pathTo out v = some (value v) ∧
      ∃ d, (value v).2 = some d ∧ (value v).1.Nodup ∧
        Path wa root (value v).1 v d ∧ Shortest wa root v d := by
    obtain ⟨ps, d, hs, hn, hpath, hm⟩ := hp v
    simp only [value, hs, Option.getD_some]
    exact ⟨True.intro, d, rfl, hn, hpath, hm⟩
  refine ⟨out, (List.finRange n).map value, ho, ?_, ?_⟩
  · unfold extractPaths
    rw [show pathTo out = fun v => some (value v) from funext (fun v => (hv v).1)]
    exact List.mapM_pure (m := Option)
  · exact List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr (fun v _ => (hv v).2))

end Dijkstra.Paths
