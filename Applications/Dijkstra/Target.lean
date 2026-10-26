import Applications.Dijkstra.AllPaths
import SquareKit.Iteration

/-!
# Exact first-hit Dijkstra termination at a requested destination

Exercise/Answer9.14 stops after the destination is removed from the fresh list.
The total executor below follows precisely that guard, with n as a proved fuel
bound. It is related to the existing independent UntilSpec, so a fuel limit does
not silently replace the source's first successful stopping state.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Dijkstra.Target
open Iteration
open Core Optimality Paths AllPaths
variable {n : Nat}

def done (target : Fin n) (s : State n) : Bool := decide (target∉s.fresh)

def stepTotal (wa : Weights n) (s : State n) : State n := (step wa s).getD s

def untilTarget (wa : Weights n) (target : Fin n) : Nat → State n → Option (State n)
  | fuel,s =>
      if done target s then some s else
      match fuel with
      | 0 => none
      | k+1 => (step wa s).bind (untilTarget wa target k)

theorem untilTarget_spec (wa : Weights n) (target : Fin n) (fuel : Nat) (s out : State n)
    (h : untilTarget wa target fuel s=some out) :
    UntilSpec (done target) (stepTotal wa) s out := by
  induction fuel generalizing s with
  | zero =>
      simp only [untilTarget] at h
      split at h
      · cases h
        exact .stop ‹_›
      · cases h
  | succ k ih =>
      simp only [untilTarget] at h
      split at h
      · cases h
        exact .stop ‹_›
      · have hd : done target s=false := by cases he : done target s <;> simp_all
        cases hs : step wa s with
        | none => simp [hs] at h
        | some mid =>
            simp only [hs,Option.bind_some] at h
            apply UntilSpec.step hd
            simpa [stepTotal,hs] using ih mid h

theorem untilTarget_progress (wa : Weights n) (root target : Fin n) (fuel : Nat)
    (s : State n) (inv : Invariant wa root s) (par : Parents wa root s)
    (hk : s.fresh.length≤fuel) :
    ∃ out,untilTarget wa target fuel s=some out ∧
      Invariant wa root out ∧ Parents wa root out ∧ target∉out.fresh := by
  induction fuel generalizing s with
  | zero =>
      have hn : s.fresh=[] := by simpa using Nat.eq_zero_of_le_zero hk
      exact ⟨s,by simp [untilTarget,done,hn],inv,par,by simp [hn]⟩
  | succ k ih =>
      by_cases hd : target∉s.fresh
      · exact ⟨s,by simp [untilTarget,done,hd],inv,par,hd⟩
      · have ht : target∈s.fresh := by simpa using hd
        have hn : s.fresh≠[] := by intro he;simp [he] at ht
        obtain ⟨v,hv⟩ : ∃ v,choose s=some v := by
          cases he : choose s with
          | none => exact False.elim (hn ((choose_none s).mp he))
          | some v => exact ⟨v,rfl⟩
        have hu : (update wa s v).fresh.length≤k := by
          change (remaining s v).length≤k
          rw [remaining_length s v inv.nodup (choose_spec hv).1]
          have hp : 0<s.fresh.length := by cases he : s.fresh <;> simp_all
          omega
        obtain ⟨out,ho,hi,hp,hstop⟩ := ih (update wa s v)
          (update_invariant wa root s inv v hv) (update_parents wa root s inv par v hv) hu
        exact ⟨out,by simp [untilTarget,done,ht,step,hv,ho],hi,hp,hstop⟩

/-- Infinity labels retain their literal singleton-path parent through first-hit execution. -/
theorem untilTarget_infinitySelf (wa : Weights n) (root target : Fin n) (fuel : Nat)
    (s out : State n) (inv : Invariant wa root s) (hi : InfinitySelf s)
    (hr : untilTarget wa target fuel s = some out) : InfinitySelf out := by
  induction fuel generalizing s with
  | zero =>
      simp only [untilTarget] at hr
      split at hr
      · cases hr; exact hi
      · cases hr
  | succ k ih =>
      simp only [untilTarget] at hr
      split at hr
      · cases hr; exact hi
      · simp only [step] at hr
        cases hv : choose s with
        | none => simp [hv] at hr
        | some v =>
            simp only [hv, Option.map_some, Option.bind_some] at hr
            exact ih (update wa s v) (update_invariant wa root s inv v hv)
              (update_infinitySelf wa s v inv.nodup hi) hr

def dijkstraZ (wa : Weights n) (root target : Fin n) : Option (List (Fin n) × Distance) :=
  (untilTarget wa target n (start root)).bind (fun s => pathTo s target)

theorem dijkstraZ_first_hit (wa : Weights n) (root target : Fin n) :
    ∃ out,untilTarget wa target n (start root)=some out ∧
      UntilSpec (done target) (stepTotal wa) (start root) out ∧
      Invariant wa root out ∧ Parents wa root out ∧ target∉out.fresh := by
  obtain ⟨out,ho,hi,hp,hd⟩ := untilTarget_progress wa root target n (start root)
    (start_invariant wa root) (start_parents wa root) (by simp [start])
  exact ⟨out,ho,untilTarget_spec wa target n (start root) out ho,hi,hp,hd⟩

/-- Only the requested destination needs to be reachable. -/
theorem dijkstraZ_shortest (wa : Weights n) (root target : Fin n)
    (hr : ∃ c,Walk wa root target c) :
    ∃ ps d,dijkstraZ wa root target=some (ps,some d) ∧ ps.Nodup ∧
      Path wa root ps target d ∧ Shortest wa root target d := by
  obtain ⟨out,ho,_,hi,hp,hdone⟩ := dijkstraZ_first_hit wa root target
  obtain ⟨c,hc⟩ := hr
  obtain ⟨d,hd,_⟩ := dle_finite (hi.settled target hdone c hc)
  have hm : Shortest wa root target d := by
    refine ⟨hi.realizes target d hd,fun e he => ?_⟩
    simpa [hd,DLE] using hi.settled target hdone e he
  obtain ⟨ps,hg,hn,hpath⟩ := reconstruct_finite wa root out hp target d hd
  refine ⟨ps.reverse,d,?_,?_,hpath,hm⟩
  · simp [dijkstraZ,ho,pathTo,hg,hd]
  · exact List.pairwise_reverse.mpr (hn.imp (fun h => Ne.symm h))

/-- The outer option succeeds even when the requested target has no path. -/
theorem dijkstraZ_unreachable (wa : Weights n) (root target : Fin n)
    (hn : ¬ ∃ c, Walk wa root target c) : dijkstraZ wa root target = some ([target], none) := by
  obtain ⟨out, ho, _, hi, _, _⟩ := dijkstraZ_first_hit wa root target
  have hs := untilTarget_infinitySelf wa root target n (start root) out
    (start_invariant wa root) (start_infinitySelf root) ho
  have hd : distance out target = none := by
    cases he : distance out target with
    | none => rfl
    | some d => exact False.elim (hn ⟨d, hi.realizes target d he⟩)
  simp [dijkstraZ, ho, pathTo, getPath_self out target (hs target hd), hd]

/-- A total first-hit result, with finite witnesses and unreachable placeholders separated. -/
theorem dijkstraZ_total (wa : Weights n) (root target : Fin n) :
    ∃ ps d, dijkstraZ wa root target = some (ps, d) ∧
      (match d with
       | some c => ps.Nodup ∧ Path wa root ps target c ∧ Shortest wa root target c
       | none => ps = [target] ∧ ¬ ∃ c, Walk wa root target c) := by
  by_cases hr : ∃ c, Walk wa root target c
  · obtain ⟨ps, d, he, hn, hp, hm⟩ := dijkstraZ_shortest wa root target hr
    exact ⟨ps, some d, he, hn, hp, hm⟩
  · exact ⟨[target], none, dijkstraZ_unreachable wa root target hr, rfl, hr⟩

end Dijkstra.Target
