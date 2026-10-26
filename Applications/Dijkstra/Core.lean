import Applications.Dijkstra.Store
import Applications.Optimization.SelectionTies
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Data.ENat.Basic

/-!
# Directed nonnegative paths and the literal finite link-array Dijkstra step

Ranks `Fin n` represent the source indices 1 through n. `none` represents genuine
infinity; its correspondence with the source's finite `maxInt` sentinel is a
separate range obligation. Links are finite immutable arrays, updates use the
already checked left-to-right `accum`, and ties retain the previous parent.
Selection compares the whole (distance,vertex) pair as in the extraction.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Dijkstra.Core
open Dijkstra.Store


abbrev Distance := Option Nat
abbrev Weights (n : Nat) := Fin n → Fin n → Option Nat
abbrev Links (n : Nat) := Store n (Fin n × Distance)

def DLE : Distance → Distance → Prop
  | some a,some b => a ≤ b
  | _,none => True
  | none,some _ => False

instance (a b : Distance) : Decidable (DLE a b) := by
  cases a <;> cases b <;> simp only [DLE] <;> infer_instance

/-- Explicit observation avoids Option's unrelated bottom order. -/
def toTop : Distance → WithTop Nat
  | none => ⊤
  | some d => WithTop.some d

theorem dle_iff (a b : Distance) : DLE a b ↔ toTop a ≤ toTop b := by
  cases a <;> cases b <;> simp only [DLE, toTop, WithTop.coe_le_coe, WithTop.not_top_le_coe, le_top]

theorem dle_refl (a : Distance) : DLE a a := (dle_iff a a).mpr le_rfl

theorem dle_trans {a b c : Distance} (h : DLE a b) (k : DLE b c) : DLE a c :=
  (dle_iff a c).mpr (le_trans ((dle_iff a b).mp h) ((dle_iff b c).mp k))

theorem toTop_injective : Function.Injective toTop := by
  intro a b h
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some b => exact False.elim (WithTop.top_ne_coe h)
  | some a =>
    cases b with
    | none => exact False.elim (WithTop.coe_ne_top h)
    | some b => exact congrArg some (WithTop.coe_eq_coe.mp h)

theorem dle_antisymm {a b : Distance} (h : DLE a b) (k : DLE b a) : a = b :=
  toTop_injective (le_antisymm ((dle_iff a b).mp h) ((dle_iff b a).mp k))

theorem dle_total (a b : Distance) : DLE a b ∨ DLE b a := by
  simpa only [dle_iff] using le_total (toTop a) (toTop b)

theorem dle_finite {a : Distance} {b : Nat} (h : DLE a (some b)) :
    ∃ c, a = some c ∧ c ≤ b := by cases a <;> simp_all [DLE]

def plus : Distance → Distance → Distance
  | some a, some b => some (a + b)
  | _, _ => none

theorem toTop_plus (a b : Distance) : toTop (plus a b) = toTop a + toTop b := by
  cases a with
  | none => cases b <;> simp only [plus, toTop, WithTop.top_add]
  | some a =>
    cases b with
    | none => simp only [plus, toTop, WithTop.add_top]
    | some b => exact WithTop.coe_add a b

theorem plus_mono_left {a b : Distance} (h : DLE a b) (w : Distance) :
    DLE (plus a w) (plus b w) := by
  rw [dle_iff, toTop_plus, toTop_plus]
  exact add_le_add_left ((dle_iff a b).mp h) _

abbrev Score := WithTop Nat ×ₗ Nat

variable {n : Nat}

structure State (n : Nat) where
  links : Links n
  fresh : List (Fin n)
  deriving Repr

def parent (s : State n) (v : Fin n) : Fin n := (lookup s.links v).1
def distance (s : State n) (v : Fin n) : Distance := (lookup s.links v).2

def score (s : State n) (v : Fin n) : Score := toLex (toTop (distance s v), v.val)
/-- Standard lexicographic comparison is exactly the source score relation. -/
theorem score_le_iff (s : State n) (u v : Fin n) :
    score s u ≤ score s v ↔ DLE (distance s u) (distance s v) ∧
      (distance s u = distance s v → u.val ≤ v.val) := by
  rw [Prod.Lex.le_iff']
  exact and_congr (dle_iff _ _).symm
    ⟨fun h he => h (congrArg toTop he), fun h he => h (toTop_injective he)⟩

def choose (s : State n) : Option (Fin n) := Optimization.Thinning.argmin (score s) s.fresh

theorem choose_none (s : State n) : choose s = none ↔ s.fresh=[] :=
  Optimization.Thinning.argmin_eq_none_iff _ _

theorem choose_spec {s : State n} {v : Fin n} (h : choose s=some v) :
    v∈s.fresh ∧ ∀ u∈s.fresh,DLE (distance s v) (distance s u) ∧
      (distance s v=distance s u → v.val≤u.val) := by
  have hm := Optimization.Thinning.argmin_correct (score s) s.fresh v h
  refine ⟨hm.1, fun u hu => ?_⟩
  exact (score_le_iff s v u).mp (hm.2 hu)

/-- Exact first occurrence under the distance/rank score, including arbitrary fresh lists. -/
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
  ⟨accum better s.links (vs.map (fun u => (u,(v,plus (distance s v) (wa v u))))),vs⟩

def step (wa : Weights n) (s : State n) : Option (State n) :=
  (choose s).map (update wa s)

def run (wa : Weights n) : Nat → State n → Option (State n)
  | 0,s => some s
  | k+1,s => (run wa k s).bind (step wa)

def start (root : Fin n) : State n :=
  ⟨Vector.ofFn (fun v => (v,if v=root then some 0 else none)),List.finRange n⟩

def dijkstra (wa : Weights n) (root : Fin n) : Option (State n) := run wa (n-1) (start root)

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

private theorem valuesAt_map_unique {β : Type} (vs : List (Fin n)) (f : Fin n → β)
    (h : vs.Nodup) (u : Fin n) :
    valuesAt u (vs.map (fun v => (v,f v))) = if u∈vs then [f u] else [] := by
  induction vs with
  | nil => simp [valuesAt]
  | cons v vs ih =>
      have hn := List.nodup_cons.mp h
      by_cases hv : v=u
      · subst v
        simp only [List.map_cons,valuesAt,List.filterMap_cons,
          List.mem_cons_self,ite_true]
        change f u :: valuesAt u (vs.map (fun v => (v,f v))) = [f u]
        rw [ih hn.2,ite_eq_right hn.1]
      · simpa only [List.map_cons,valuesAt,List.filterMap_cons,ite_eq_right hv,
          List.mem_cons,Ne.symm hv,false_or] using ih hn.2

theorem update_lookup (wa : Weights n) (s : State n) (v u : Fin n) (h : s.fresh.Nodup) :
    lookup (update wa s v).links u =
      if u∈remaining s v then better (lookup s.links u) (v,plus (distance s v) (wa v u))
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
    DLE (distance (update wa s v) u) (plus (distance s v) (wa v u)) := by
  unfold distance
  rw [update_lookup wa s v u h,ite_eq_left hu]
  exact better_new_le _ _

theorem update_unchanged (wa : Weights n) (s : State n) (v u : Fin n)
    (h : s.fresh.Nodup) (hu : u∉remaining s v) :
    lookup (update wa s v).links u=lookup s.links u := by
  rw [update_lookup wa s v u h,ite_eq_right hu]

/-- Independent directed walks, allowing repeated vertices and edges. -/
inductive Walk (wa : Weights n) (root : Fin n) : Fin n → Nat → Prop
  | nil : Walk wa root root 0
  | snoc {v u : Fin n} {d w : Nat} : Walk wa root v d → wa v u=some w →
      Walk wa root u (d+w)

/-- A finite result is realized by a directed walk and bounds every directed walk. -/
def Shortest (wa : Weights n) (root v : Fin n) (d : Nat) : Prop :=
  Walk wa root v d ∧ ∀ c,Walk wa root v c → d≤c

def Reachable (wa : Weights n) (root : Fin n) : Prop := ∀ v,∃ d,Walk wa root v d

end Dijkstra.Core
