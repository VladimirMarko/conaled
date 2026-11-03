import Applications.Dijkstra.Paths

/-!
# Whole dijkstraP output, including unreachable vertices

Literal source extraction returns the singleton [v] with an infinite label for
an unreachable vertex, because its parent remains itself. This invariant proves
that the full path-list pipeline is total on the mathematical-infinity extension.
It also proves the exact source filter-by-last lookup equals indexed extraction,
which is needed for the repeated-removal jogger baseline.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Dijkstra.AllPaths
open Dijkstra.Store
open Core Optimality Paths
variable {n : Nat}

def InfinitySelf (s : State n) : Prop := ∀ v,distance s v=none → parent s v=v

theorem start_infinitySelf (root : Fin n) : InfinitySelf (start root) := by
  intro v _
  exact start_parent root v

theorem update_infinitySelf (wa : Weights n) (s : State n) (v : Fin n)
    (hn : s.fresh.Nodup) (hi : InfinitySelf s) : InfinitySelf (update wa s v) := by
  intro u hd
  have hl:=update_lookup wa s v u hn
  by_cases hm : u∈remaining s v
  · rw [ite_eq_left hm] at hl
    by_cases hb : DLE (distance s u) (plus (distance s v) (wa v u))
    · have hold : lookup (update wa s v).links u=lookup s.links u := by
        simpa only [better,show (lookup s.links u).2=distance s u from rfl,ite_eq_left hb] using hl
      have hnone : distance s u=none := (congrArg Prod.snd hold).symm.trans hd
      exact (congrArg Prod.fst hold).trans (hi u hnone)
    · have hnew : lookup (update wa s v).links u=(v,plus (distance s v) (wa v u)) := by
        simpa only [better,show (lookup s.links u).2=distance s u from rfl,ite_eq_right hb] using hl
      have hnone : plus (distance s v) (wa v u)=none := (congrArg Prod.snd hnew).symm.trans hd
      exact False.elim (hb (by rw [hnone];cases distance s u <;> trivial))
  · rw [ite_eq_right hm] at hl
    exact (congrArg Prod.fst hl).trans (hi u ((congrArg Prod.snd hl).symm.trans hd))

theorem run_infinitySelf (wa : Weights n) (root : Fin n) (s out : State n)
    (inv : Invariant wa root s) (hi : InfinitySelf s) (k : Nat) (hr : run wa k s=some out) :
    InfinitySelf out := by
  induction k generalizing out with
  | zero => cases hr;exact hi
  | succ k ih =>
      simp only [run] at hr
      cases hm : run wa k s with
      | none => simp [hm] at hr
      | some t =>
          simp only [hm,Option.bind_some,step] at hr
          cases hv : choose t with
          | none => simp [hv] at hr
          | some v =>
              simp only [hv,Option.map_some,Option.some.injEq] at hr
              subst out
              exact update_infinitySelf wa t v (run_invariant wa root s t inv k hm).nodup (ih t hm)

theorem getPath_self (s : State n) (v : Fin n) (hp : parent s v=v) : getPath s v=some [v] := by
  have hn : 0<n := by have:=v.isLt;omega
  cases n with
  | zero => omega
  | succ k => simp [getPath,getPathFuel,hp]

theorem getPathFuel_head (s : State n) (k : Nat) (v : Fin n) (ps : List (Fin n))
    (h : getPathFuel s k v=some ps) : ps.head?=some v := by
  cases k with
  | zero => simp [getPathFuel] at h
  | succ k =>
      simp only [getPathFuel] at h
      split at h
      · cases h;rfl
      · cases he : getPathFuel s k (parent s v) with
        | none => simp [he] at h
        | some tail =>
            simp only [he,Option.map_some,Option.some.injEq] at h
            subst ps;rfl

theorem pathTo_endpoint (s : State n) (v : Fin n) (pd : List (Fin n) × Distance)
    (h : pathTo s v=some pd) : pd.1.getLast?=some v ∧ pd.2=distance s v := by
  unfold pathTo at h
  cases hg : getPath s v with
  | none => simp [hg] at h
  | some ps =>
      simp only [hg,Option.map_some,Option.some.injEq] at h
      subst pd
      exact ⟨by simpa using getPathFuel_head s n v ps hg,rfl⟩

theorem pathTo_total (wa : Weights n) (root : Fin n) (s : State n)
    (hp : Parents wa root s) (hi : InfinitySelf s) (v : Fin n) :
    ∃ pd,pathTo s v=some pd := by
  cases hd : distance s v with
  | none => exact ⟨([v],none),by simp [pathTo,getPath_self s v (hi v hd),hd]⟩
  | some d =>
      obtain ⟨ps,hg,_,_⟩:=reconstruct_finite wa root s hp v d hd
      exact ⟨(ps.reverse,some d),by simp [pathTo,hg,hd]⟩

def pathValue (s : State n) (v : Fin n) : List (Fin n) × Distance := (pathTo s v).getD ([],none)

theorem pathValue_exact (wa : Weights n) (root : Fin n) (s : State n)
    (hp : Parents wa root s) (hi : InfinitySelf s) (v : Fin n) :
    pathTo s v=some (pathValue s v) := by
  obtain ⟨pd,he⟩:=pathTo_total wa root s hp hi v
  simp [pathValue,he]

theorem extractPaths_exact (wa : Weights n) (root : Fin n) (s : State n)
    (hp : Parents wa root s) (hi : InfinitySelf s) :
    extractPaths s=some ((List.finRange n).map (pathValue s)) := by
  have he : pathTo s = fun v => some (pathValue s v) :=
    funext (pathValue_exact wa root s hp hi)
  unfold extractPaths
  rw [he]
  exact List.mapM_pure (m := Option)


/-- Literal head(filter((v==).last.fst)), with both partial observations checked. -/
def pathByLast (v : Fin n) (ps : List (List (Fin n) × Distance)) :
    Option (List (Fin n) × Distance) :=
  (ps.filter (fun pd => decide (pd.1.getLast?=some v))).head?


theorem pathByLast_exact (wa : Weights n) (root : Fin n) (s : State n)
    (hp : Parents wa root s) (hi : InfinitySelf s) (v : Fin n) :
    (extractPaths s).bind (pathByLast v)=pathTo s v := by
  rw [extractPaths_exact wa root s hp hi,Option.bind_some,pathByLast,List.head?_filter,List.find?_map]
  have he : (fun pd : List (Fin n) × Distance => decide (pd.1.getLast?=some v)) ∘ pathValue s=
      (fun u => decide (u=v)) := by
    funext u
    have hlast := (pathTo_endpoint s u (pathValue s u) (pathValue_exact wa root s hp hi u)).1
    simp [hlast]
  rw [he,pathValue_exact wa root s hp hi v]
  cases hf : (List.finRange n).find? (fun u => decide (u=v)) with
  | none =>
      have hn:=(List.find?_eq_none.mp hf) v (List.mem_finRange v)
      simp at hn
  | some u =>
      have hu : u=v := by simpa using List.find?_some hf
      subst u;rfl

theorem dijkstra_all_paths (wa : Weights n) (root : Fin n) :
    ∃ s,dijkstra wa root=some s ∧ Parents wa root s ∧ InfinitySelf s ∧ Correct wa root s ∧
      ∀ v,(extractPaths s).bind (pathByLast v)=pathTo s v := by
  obtain ⟨s,hs,_,_,hc⟩:=dijkstra_correct wa root
  have hp:=run_parents wa root (start root) s (start_invariant wa root) (start_parents wa root) (n-1) hs
  have hi:=run_infinitySelf wa root (start root) s (start_invariant wa root) (start_infinitySelf root) (n-1) hs
  exact ⟨s,hs,hp,hi,hc,pathByLast_exact wa root s hp hi⟩

end Dijkstra.AllPaths
