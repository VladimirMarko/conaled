import Applications.Dijkstra.Core
import Applications.Resources.Dijkstra.StoreCosts
import Applications.Optimization.SelectionMap

set_option autoImplicit false
set_option warningAsError true

/-!
Full Dijkstra state-step work. The source whole (distance,vertex) comparator is
counted by scalar tests; scores are materialized once per fresh vertex. Filter,
optional-distance addition, ordered update association construction, one-copy
immutable accumulation, initialization and every fixed iteration are explicit.
Monolithic indexed cells and unit scalar arithmetic are the declared model.
-/
namespace Resources.DijkstraCosts
open Dijkstra.Core Dijkstra.Store Resources.DijkstraStore
open Optimization.Thinning
variable {n : Nat}

/-- The whole pair-order guard, with every scalar comparison charged. -/
def compareRun (a b : Score) : Bool × Nat :=
  if (ofLex a).1 ≤ (ofLex b).1 then
    if (ofLex a).1 = (ofLex b).1 then (decide ((ofLex a).2 ≤ (ofLex b).2),3) else (true,2)
  else (false,1)

theorem compareRun_value (a b : Score) : (compareRun a b).1=decide (a≤b) := by
  simp only [Prod.Lex.le_iff']
  by_cases hd : (ofLex a).1 ≤ (ofLex b).1 <;>
    by_cases he : (ofLex a).1 = (ofLex b).1 <;> simp [compareRun, hd, he]

theorem compareRun_bounds (a b : Score) : 1≤(compareRun a b).2 ∧ (compareRun a b).2≤3 := by
  unfold compareRun
  split <;> (try split) <;> simp

abbrev Candidate (n : Nat) := Score × Fin n

def smallerCandidate (a b : Candidate n) : Candidate n :=
  if a.1≤b.1 then a else b

def minimumRun : List (Candidate n) → Option (Candidate n) × Nat
  | [] => (none,1)
  | [a] => (some a,1)
  | a::b::xs =>
      let r := minimumRun (b::xs)
      match r.1 with
      | none => (none,r.2+1)
      | some c =>
          let cmp := compareRun a.1 c.1
          (some (if cmp.1 then a else c),r.2+cmp.2+1)

theorem minimumRun_value (xs : List (Candidate n)) :
    (minimumRun xs).1 = argmin Prod.fst xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b xs =>
      rw [minimumRun]
      conv_rhs => rw [argmin]
      rw [ih]
      cases h : argmin Prod.fst (b::xs) with
      | none =>
        have hh := (argmin_eq_none_iff Prod.fst (b::xs)).mp h
        contradiction
      | some c => simp only [compareRun_value,decide_eq_true_eq]

theorem minimumRun_work (xs : List (Candidate n)) : (minimumRun xs).2≤4*xs.length+1 := by
  induction xs with
  | nil => simp [minimumRun]
  | cons a xs ih =>
      cases xs with
      | nil => simp [minimumRun]
      | cons b xs =>
          simp only [minimumRun]
          cases hr : (minimumRun (b::xs)).1 with
          | none =>
              simp only [List.length_cons] at ih ⊢
              omega
          | some c =>
              have hc := (compareRun_bounds a.1 c.1).2
              simp only [List.length_cons] at ih ⊢
              omega

def candidates (key : Fin n → Score) (vs : List (Fin n)) : List (Candidate n) :=
  vs.map (fun v => (key v,v))

def chooseByRun (key : Fin n → Score) (vs : List (Fin n)) : Option (Fin n) × Nat :=
  let r := minimumRun (candidates key vs)
  (r.1.map Prod.snd,2*vs.length+r.2)

theorem chooseByRun_value (key : Fin n → Score) (vs : List (Fin n)) :
    (chooseByRun key vs).1 = argmin key vs := by
  simp only [chooseByRun,minimumRun_value,candidates,argmin_map,Option.map_map]
  change (argmin key vs).map id = argmin key vs
  simp only [Option.map_id, id_eq]

theorem chooseByRun_work (key : Fin n → Score) (vs : List (Fin n)) :
    (chooseByRun key vs).2≤6*vs.length+1 := by
  have hh := minimumRun_work (candidates key vs)
  have he : (candidates key vs).length=vs.length := by simp [candidates]
  rw [he] at hh
  simp only [chooseByRun]
  omega

def chooseRun (s : State n) : Option (Fin n) × Nat := chooseByRun (score s) s.fresh

theorem chooseRun_value (s : State n) : (chooseRun s).1=choose s := chooseByRun_value _ _
theorem chooseRun_work (s : State n) : (chooseRun s).2≤6*s.fresh.length+1 := chooseByRun_work _ _

def remainingRun (v : Fin n) : List (Fin n) → List (Fin n) × Nat
  | [] => ([],1)
  | u::us =>
      let r := remainingRun v us
      if u=v then (r.1,r.2+1) else (u::r.1,r.2+2)

theorem remainingRun_value (v : Fin n) (vs : List (Fin n)) :
    (remainingRun v vs).1=vs.filter (fun u => u != v) := by
  induction vs with
  | nil => rfl
  | cons u us ih => by_cases he : u=v <;> simp [remainingRun,he,ih]

theorem remainingRun_work (v : Fin n) (vs : List (Fin n)) :
    (remainingRun v vs).2≤2*vs.length+1 := by
  induction vs with
  | nil => simp [remainingRun]
  | cons u us ih => rw [remainingRun]; split <;> simp only [List.length_cons] <;> omega

def plusRun (a b : Distance) : Distance × Nat :=
  match b with
  | none => (none,1)
  | some w => match a with
      | none => (none,2)
      | some d => (some (d+w),3)

theorem plusRun_value (a b : Distance) : (plusRun a b).1=plus a b := by
  cases a <;> cases b <;> rfl

theorem plusRun_work (a b : Distance) : (plusRun a b).2≤3 := by
  cases a <;> cases b <;> simp [plusRun]

def updatesRun (wa : Weights n) (v : Fin n) (d : Distance) :
    List (Fin n) → List (Fin n × (Fin n × Distance)) × Nat
  | [] => ([],1)
  | u::us =>
      let one := plusRun d (wa v u)
      let rest := updatesRun wa v d us
      ((u,(v,one.1))::rest.1,rest.2+one.2+3)

theorem updatesRun_value (wa : Weights n) (v : Fin n) (d : Distance) (vs : List (Fin n)) :
    (updatesRun wa v d vs).1=vs.map (fun u => (u,(v,plus d (wa v u)))) := by
  induction vs with
  | nil => rfl
  | cons u us ih => simp only [updatesRun,plusRun_value,ih,List.map_cons]

theorem updatesRun_work (wa : Weights n) (v : Fin n) (d : Distance) (vs : List (Fin n)) :
    (updatesRun wa v d vs).2≤6*vs.length+1 := by
  induction vs with
  | nil => simp [updatesRun]
  | cons u us ih =>
      have hh := plusRun_work d (wa v u)
      simp only [updatesRun,List.length_cons]
      omega

def stepRun (wa : Weights n) (s : State n) : Option (State n) × Nat :=
  let c := chooseRun s
  match c.1 with
  | none => (none,c.2+1)
  | some v =>
      let vs := remainingRun v s.fresh
      let updates := updatesRun wa v (distance s v) vs.1
      let a := bulkRun better s.links updates.1
      (some ⟨a.1,vs.1⟩,c.2+vs.2+updates.2+a.2+2)

theorem stepRun_value (wa : Weights n) (s : State n) : (stepRun wa s).1=step wa s := by
  simp only [stepRun,chooseRun_value]
  cases hc : choose s with
  | none => simp only [step,hc,Option.map_none]
  | some v => simp only [bulkRun_exact,updatesRun_value,remainingRun_value,
      step,hc,Option.map_some,update,remaining]

theorem fresh_length_bound (s : State n) (h : s.fresh.Nodup) : s.fresh.length≤n := by
  have hh := h.length_le_of_subset (l₂ := List.finRange n) (fun _ _ => List.mem_finRange _)
  simpa only [List.length_finRange] using hh

theorem stepRun_work (wa : Weights n) (s : State n) (hn : s.fresh.Nodup) :
    (stepRun wa s).2≤18*n+5 := by
  have hc := chooseRun_work s
  have hsize := fresh_length_bound s hn
  simp only [stepRun,chooseRun_value]
  cases hs : choose s with
  | none => dsimp only; omega
  | some v =>
      have hf := remainingRun_work v s.fresh
      have hu := updatesRun_work wa v (distance s v) (remainingRun v s.fresh).1
      have hr : (remainingRun v s.fresh).1.length≤s.fresh.length := by
        rw [remainingRun_value]
        exact List.length_filter_le _ _
      have hz : (updatesRun wa v (distance s v) (remainingRun v s.fresh).1).1.length=
          (remainingRun v s.fresh).1.length := by rw [updatesRun_value,List.length_map]
      simp only [bulkRun_exact,hz]
      omega

theorem step_nodup {wa : Weights n} {s out : State n} (hn : s.fresh.Nodup)
    (h : step wa s=some out) : out.fresh.Nodup := by
  obtain ⟨v,_,he⟩ := Option.map_eq_some_iff.mp h
  subst out
  exact remaining_nodup s v hn

/-- Failed suffix iterations still cost one administrative unit. -/
def iteration (wa : Weights n) (_ : Unit) : Option (State n) → Measured (Option (State n)) Nat
  | none => (none,1)
  | some s => let one := stepRun wa s; (one.1,one.2+1)

/-- Shared execution with precisely the source's one-unit base charge. -/
def runCost (wa : Weights n) (k : Nat) (s : State n) : Measured (Option (State n)) Nat :=
  let r := Resources.run (iteration wa) (List.replicate k ()) (some s)
  (r.1,r.2+1)

theorem runCost_zero (wa : Weights n) (s : State n) : runCost wa 0 s = (some s,1) := rfl

theorem runCost_succ (wa : Weights n) (k : Nat) (s : State n) :
    runCost wa (k+1) s =
      let previous := runCost wa k s
      match previous.1 with
      | none => (none,previous.2+1)
      | some middle => let one := stepRun wa middle; (one.1,previous.2+one.2+1) := by
  simp only [runCost,List.replicate_succ',Resources.run_append,Resources.bind,
    Resources.run_cons,Resources.run_nil]
  cases h : (Resources.run (iteration wa) (List.replicate k ()) (some s)).1 <;>
    simp [iteration,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem runCost_value (wa : Weights n) (k : Nat) (s : State n) :
    (runCost wa k s).1=Dijkstra.Core.run wa k s := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [runCost_succ,ih,Dijkstra.Core.run]
      cases Dijkstra.Core.run wa k s with
      | none => rfl
      | some middle => exact stepRun_value wa middle

theorem run_nodup {wa : Weights n} {s out : State n} {k : Nat} (hn : s.fresh.Nodup)
    (h : Dijkstra.Core.run wa k s=some out) : out.fresh.Nodup := by
  let P : Option (State n) → Prop := fun t => ∀ x, t = some x → x.fresh.Nodup
  have closed : ∀ i t, P t → P (iteration wa i t).1 := by
    intro i t ht x hx
    cases t with
    | none => cases hx
    | some t =>
      exact step_nodup (ht t rfl) ((stepRun_value wa t).symm.trans hx)
  have hp := Resources.run_invariant (iteration wa) P closed (List.replicate k ())
    (some s) (by intro x hx; cases hx; exact hn)
  apply hp out
  exact (runCost_value wa k s).trans h

theorem runCost_work (wa : Weights n) (k : Nat) (s : State n) (hn : s.fresh.Nodup) :
    (runCost wa k s).2≤k*(18*n+6)+1 := by
  induction k with
  | zero => simp [runCost_zero]
  | succ k ih =>
      simp only [runCost_succ,runCost_value]
      cases hr : Dijkstra.Core.run wa k s with
      | none => dsimp only; rw [Nat.add_mul,Nat.one_mul]; omega
      | some middle =>
          have hs := stepRun_work wa middle (run_nodup hn hr)
          dsimp only
          rw [Nat.add_mul,Nat.one_mul]
          omega

def dijkstraRun (wa : Weights n) (root : Fin n) : Option (State n) × Nat :=
  let r := runCost wa (n-1) (start root)
  (r.1,2*n+r.2+2)

theorem dijkstraRun_value (wa : Weights n) (root : Fin n) :
    (dijkstraRun wa root).1=dijkstra wa root := runCost_value _ _ _

theorem dijkstraRun_work (wa : Weights n) (root : Fin n) :
    (dijkstraRun wa root).2≤(n-1)*(18*n+6)+2*n+3 := by
  have h := runCost_work wa (n-1) (start root) (List.nodup_finRange n)
  simp only [dijkstraRun]
  omega

theorem dijkstraRun_quadratic (wa : Weights n) (root : Fin n) :
    (dijkstraRun wa root).2≤29*(n*n) := by
  have hh := dijkstraRun_work wa root
  have hn : 1≤n := by have := root.isLt; omega
  have hm := Nat.mul_le_mul_right (18*n+6) (Nat.sub_le n 1)
  have hs : n≤n*n := Nat.le_mul_of_pos_right _ hn
  have hsq : 1≤n*n := by omega
  have heq : n*(18*n+6)=18*(n*n)+6*n := by
    rw [Nat.mul_add]
    congr 1 <;> ac_rfl
  rw [heq] at hm
  omega

end Resources.DijkstraCosts
