import Applications.Prim.Weights
import Applications.Prim.Correctness
import Applications.Optimization.SelectionTies
import Mathlib.Order.Prod.Lex.Basic

set_option autoImplicit false
set_option warningAsError true

/-!
The actual finite link-array Prim executor.  Fin ranks denote source labels 1..n.
Genuine infinity is distinct from any integer.  Finite-sentinel
specialization is outside this module.  The initial root is included in fresh;
the printed n-1 iterations intentionally leave the last vertex unprocessed.
-/

namespace Prim.Array
open Dijkstra.Store

abbrev Distance := Option Int
abbrev Weights (n : Nat) := Prim.Weights.WeightFunction n Int
abbrev Links (n : Nat) := Store n (Fin n × Distance)

def DLE : Distance → Distance → Prop
  | some a,some b => a ≤ b
  | _,none => True
  | none,some _ => False

instance (a b : Distance) : Decidable (DLE a b) := by
  cases a <;> cases b <;> simp only [DLE] <;> infer_instance

/-- Infinity is top; the underlying option is observed through the standard order. -/
def toTop (d : Distance) : WithTop Int := d

theorem dle_iff (a b : Distance) : DLE a b ↔ toTop a ≤ toTop b := by
  cases a with
  | none =>
      cases b with
      | none => exact iff_of_true trivial le_rfl
      | some b => exact iff_of_false id (WithTop.not_top_le_coe b)
  | some a =>
      cases b with
      | none => exact iff_of_true trivial le_top
      | some b => exact WithTop.coe_le_coe.symm

theorem dle_refl (a : Distance) : DLE a a := (dle_iff a a).mpr le_rfl

theorem dle_trans {a b c : Distance} (h : DLE a b) (k : DLE b c) : DLE a c :=
  (dle_iff a c).mpr (le_trans ((dle_iff a b).mp h) ((dle_iff b c).mp k))

theorem dle_antisymm {a b : Distance} (h : DLE a b) (k : DLE b a) : a = b :=
  show toTop a = toTop b from le_antisymm ((dle_iff a b).mp h) ((dle_iff b a).mp k)

theorem dle_total (a b : Distance) : DLE a b ∨ DLE b a := by
  simpa only [dle_iff] using le_total (toTop a) (toTop b)

theorem dle_finite {a : Distance} {b : Int} (h : DLE a (some b)) :
    ∃ c, a = some c ∧ c ≤ b := by cases a <;> simp_all [DLE]

abbrev Score := WithTop Int ×ₗ Nat

variable {n : Nat}

structure State (n : Nat) where
  links : Links n
  fresh : List (Fin n)
  deriving Repr

def parent (s : State n) (v : Fin n) : Fin n := (lookup s.links v).1
def distance (s : State n) (v : Fin n) : Distance := (lookup s.links v).2

def score (s : State n) (v : Fin n) : Score := toLex (toTop (distance s v), v.val)

theorem score_le_iff (s : State n) (u v : Fin n) :
    score s u ≤ score s v ↔ DLE (distance s u) (distance s v) ∧
      (distance s u = distance s v → u.val ≤ v.val) := by
  rw [Prod.Lex.le_iff']
  exact and_congr (dle_iff _ _).symm Iff.rfl

def choose (s : State n) : Option (Fin n) := Optimization.Thinning.argmin (score s) s.fresh

theorem choose_none (s : State n) : choose s = none ↔ s.fresh=[] :=
  Optimization.Thinning.argmin_eq_none_iff _ _

theorem choose_spec {s : State n} {v : Fin n} (h : choose s=some v) :
    v∈s.fresh ∧ ∀ u∈s.fresh,DLE (distance s v) (distance s u) ∧
      (distance s v=distance s u → v.val≤u.val) := by
  have hm := Optimization.Thinning.argmin_correct (score s) s.fresh v h
  exact ⟨hm.1, fun u hu => (score_le_iff s v u).mp (hm.2 hu)⟩

theorem choose_first (s : State n) (v : Fin n) : choose s = some v ↔
    Optimization.FirstMinimum (score s) s.fresh v :=
  Optimization.argmin_eq_some_iff_firstMinimum _ _ _

def better (old new : Fin n × Distance) : Fin n × Distance :=
  if DLE old.2 new.2 then old else new

theorem better_old_le (old new : Fin n × Distance) : DLE (better old new).2 old.2 := by
  unfold better
  split
  · exact dle_refl _
  · exact (dle_total _ _).resolve_left ‹_›

theorem better_new_le (old new : Fin n × Distance) : DLE (better old new).2 new.2 := by
  unfold better
  split
  · assumption
  · exact dle_refl _

theorem better_tie (old new : Fin n × Distance) (h : old.2=new.2) : better old new=old := by
  simp [better,h,dle_refl]

def remaining (s : State n) (v : Fin n) : List (Fin n) := s.fresh.filter (fun u => u != v)

def update (wa : Weights n) (s : State n) (v : Fin n) : State n :=
  let vs := remaining s v
  ⟨accum better s.links (vs.map (fun u => (u,(v,wa u v)))),vs⟩

def step (wa : Weights n) (s : State n) : Option (State n) :=
  (choose s).map (update wa s)

def run (wa : Weights n) : Nat → State n → Option (State n)
  | 0,s => some s
  | k+1,s => (step wa s).bind (run wa k)

def start (root : Fin n) : State n :=
  ⟨Vector.ofFn (fun v => (v,if v=root then some 0 else none)),List.finRange n⟩

def prim2State (wa : Weights n) (root : Fin n) : Option (State n) := run wa (n-1) (start root)

theorem start_distance (root v : Fin n) :
    distance (start root) v = if v=root then some 0 else none := by
  simp [distance,start,lookup]

theorem start_parent (root v : Fin n) : parent (start root) v=v := by
  simp [parent,start,lookup]

theorem mem_remaining (s : State n) (v u : Fin n) :
    u∈remaining s v ↔ u∈s.fresh ∧ u≠v := by simp [remaining]

theorem remaining_nodup (s : State n) (v : Fin n) (h : s.fresh.Nodup) :
    (remaining s v).Nodup := h.filter _

theorem remaining_length (s : State n) (v : Fin n) (h : s.fresh.Nodup) (hv : v∈s.fresh) :
    (remaining s v).length=s.fresh.length-1 := by
  rw [remaining,← h.erase_eq_filter]
  exact List.length_erase_of_mem hv

theorem update_lookup (wa : Weights n) (s : State n) (v u : Fin n) (h : s.fresh.Nodup) :
    lookup (update wa s v).links u =
      if u∈remaining s v then better (lookup s.links u) (v,wa u v)
      else lookup s.links u := by
  simp only [update,accum_lookup]
  rw [valuesAt_map_unique _ _ (remaining_nodup s v h)]
  split <;> rfl

theorem update_distance_le (wa : Weights n) (s : State n) (v u : Fin n) (h : s.fresh.Nodup) :
    DLE (distance (update wa s v) u) (distance s u) := by
  unfold distance
  rw [update_lookup wa s v u h]
  split
  · exact better_old_le _ _
  · exact dle_refl _

theorem update_relax_le (wa : Weights n) (s : State n) (v u : Fin n)
    (h : s.fresh.Nodup) (hu : u∈remaining s v) :
    DLE (distance (update wa s v) u) (wa u v) := by
  unfold distance
  rw [update_lookup wa s v u h,ite_eq_left hu]
  exact better_new_le _ _

theorem update_unchanged (wa : Weights n) (s : State n) (v u : Fin n)
    (h : s.fresh.Nodup) (hu : u∉remaining s v) :
    lookup (update wa s v).links u=lookup s.links u := by
  rw [update_lookup wa s v u h,ite_eq_right hu]


def label (v : Fin n) : Kruskal.Vertex := Int.ofNat (v.val+1)
def labels (n : Nat) : List Kruskal.Vertex := (List.finRange n).map label

def edgeFor (s : State n) (v : Fin n) (w : Int) : Kruskal.Edge :=
  (label (parent s v),label v,w)

def edgesFor (root : Fin n) (s : State n) (vs : List (Fin n)) : List Kruskal.Edge :=
  vs.filterMap (fun v => if v=root then none else (distance s v).map (edgeFor s v))

def extractOn (root : Fin n) (s : State n) : List (Fin n) → Option (List Kruskal.Edge)
  | [] => some []
  | v::vs => if v=root then extractOn root s vs else
      do let w ← distance s v
         let es ← extractOn root s vs
         pure (edgeFor s v w :: es)

def extractP (root : Fin n) (s : State n) : Option Kruskal.Tree :=
  (extractOn root s (List.finRange n)).map (fun es => (labels n,es))

def prim2 (wa : Weights n) (root : Fin n) : Option Kruskal.Tree :=
  (prim2State wa root).bind (extractP root)

theorem label_injective {u v : Fin n} (h : label u=label v) : u=v := by
  apply Fin.ext
  have hh : u.val+1=v.val+1 := Int.ofNat.inj h
  omega

theorem label_eq_iff (u v : Fin n) : label u=label v ↔ u=v :=
  ⟨label_injective,congrArg label⟩

theorem mem_labels (v : Fin n) : label v∈labels n := by
  simp [labels]

theorem labels_nodup (n : Nat) : (labels n).Nodup := by
  exact List.Pairwise.map label (fun _ _ hne he => hne (label_injective he))
    (List.nodup_finRange n)

theorem labels_length (n : Nat) : (labels n).length=n := by simp [labels]

theorem label_mem_map (v : Fin n) (vs : List (Fin n)) : label v∈vs.map label ↔ v∈vs := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨u,hu,he⟩
    exact label_injective he ▸ hu
  · intro hv
    exact ⟨v,hv,rfl⟩

theorem extractOn_eq {root : Fin n} {s : State n} {vs : List (Fin n)}
    (h : ∀ v∈vs,v≠root → ∃ w,distance s v=some w) :
    extractOn root s vs=some (edgesFor root s vs) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
      have ht : ∀ u∈vs,u≠root → ∃ w,distance s u=some w :=
        fun u hu hn => h u (List.mem_cons_of_mem _ hu) hn
      by_cases hv : v=root
      · simp only [extractOn,ite_eq_left hv,edgesFor,List.filterMap_cons]
        exact ih ht
      · obtain ⟨w,hw⟩ := h v List.mem_cons_self hv
        simp only [extractOn,ite_eq_right hv,hw,ih ht,
          edgesFor,List.filterMap_cons,Option.map_some]
        rfl

theorem choose_first_root (root : Fin n) : choose (start root)=some root := by
  cases hc : choose (start root) with
  | none =>
      have he := (choose_none (start root)).mp hc
      have hm : root∈(start root).fresh := List.mem_finRange root
      rw [he] at hm
      cases hm
  | some v =>
      have hh := (choose_spec hc).2 root (List.mem_finRange root)
      by_cases hv : v=root
      · exact congrArg some hv
      · rw [start_distance,start_distance] at hh
        simp [hv,DLE] at hh

theorem update_fresh (wa : Weights n) (s : State n) (v : Fin n) :
    (update wa s v).fresh=remaining s v := rfl

theorem run_zero (wa : Weights n) (s : State n) : run wa 0 s=some s := rfl

theorem run_succ (wa : Weights n) (k : Nat) (s : State n) :
    run wa (k+1) s=(step wa s).bind (run wa k) := rfl

theorem run_add (wa : Weights n) (k m : Nat) (s : State n) :
    run wa (k+m) s=(run wa k s).bind (run wa m) := by
  induction k generalizing s with
  | zero => simp [run]
  | succ k ih =>
      simp only [Nat.succ_add,run,Option.bind_assoc]
      congr 1
      funext next
      exact ih next

theorem last_update_links (wa : Weights n) (s : State n) (v : Fin n)
    (h : s.fresh=[v]) : (update wa s v).links=s.links := by
  have he : remaining s v=[] := by simp [remaining,h]
  simp [update,he,accum]

theorem singleton_result (w : Weights 1) :
    prim2 w ⟨0,by decide⟩=some ([1],[]) := by
  rfl

end Prim.Array
