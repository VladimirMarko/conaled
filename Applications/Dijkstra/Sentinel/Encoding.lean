import Applications.Dijkstra.Paths

/-!
# Literal finite-sentinel arithmetic and its explicit safe domain

The extracted Int program checks only the edge weight for maxInt before adding.
This module executes that exact rule over mathematical integers, and proves its
refinement of genuine infinity under a sufficient finite range condition. A
machine Int interpretation additionally needs its declared signed bound; the
proved operands/results then remain within it. No wraparound is assumed away.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Dijkstra.Sentinel
open Dijkstra.Store Dijkstra.Core Dijkstra.Optimality Dijkstra.Paths
variable {n : Nat}

abbrev RawScore := Int ×ₗ Nat

@[ext]
structure RawState (n : Nat) where
  links : Store n (Fin n × Int)
  fresh : List (Fin n)
  deriving Repr
abbrev RawWeights (n : Nat) := Fin n → Fin n → Int

def rawDistance (s : RawState n) (v : Fin n) : Int := (lookup s.links v).2
def rawParent (s : RawState n) (v : Fin n) : Fin n := (lookup s.links v).1
def rawScore (s : RawState n) (v : Fin n) : RawScore := toLex (rawDistance s v,v.val)
def rawChoose (s : RawState n) : Option (Fin n) := Optimization.Thinning.argmin (rawScore s) s.fresh

/-- The inherited decidable comparison executes exactly the source score guard. -/
theorem rawScore_decide (a b : RawScore) :
    decide (a ≤ b) = decide ((ofLex a).1 ≤ (ofLex b).1 ∧
      ((ofLex a).1 = (ofLex b).1 → (ofLex a).2 ≤ (ofLex b).2)) := by
  simp only [Prod.Lex.le_iff']

/-- The standard order has exactly the source distance/rank comparison. -/
theorem rawScore_le_iff (s : RawState n) (u v : Fin n) :
    rawScore s u ≤ rawScore s v ↔ rawDistance s u ≤ rawDistance s v ∧
      (rawDistance s u = rawDistance s v → u.val ≤ v.val) :=
  Prod.Lex.le_iff'

def rawSum (sentinel : Int) (d w : Int) : Int := if w=sentinel then sentinel else d+w
def rawBetter (old new : Fin n × Int) : Fin n × Int := if old.2≤new.2 then old else new

def rawUpdate (sentinel : Int) (wa : RawWeights n) (s : RawState n) (v : Fin n) : RawState n :=
  let vs := s.fresh.filter (fun u => u != v)
  ⟨accum rawBetter s.links (vs.map (fun u =>
    (u,(v,rawSum sentinel (rawDistance s v) (wa v u))))),vs⟩
def rawStep (sentinel : Int) (wa : RawWeights n) (s : RawState n) : Option (RawState n) :=
  (rawChoose s).map (rawUpdate sentinel wa s)
def rawRun (sentinel : Int) (wa : RawWeights n) : Nat → RawState n → Option (RawState n)
  | 0,s => some s
  | k+1,s => (rawRun sentinel wa k s).bind (rawStep sentinel wa)
def rawStart (sentinel : Int) (root : Fin n) : RawState n :=
  ⟨Vector.ofFn (fun v => (v,if v=root then 0 else sentinel)),List.finRange n⟩
def rawDijkstra (sentinel : Int) (wa : RawWeights n) (root : Fin n) : Option (RawState n) :=
  rawRun sentinel wa (n-1) (rawStart sentinel root)

def encode (sentinel : Nat) : Distance → Int
  | none => sentinel
  | some d => d

def Valid (sentinel : Nat) (d : Distance) : Prop := ∀ a,d=some a → a<sentinel

def encodeCell (sentinel : Nat) (c : Fin n × Distance) : Fin n × Int :=
  (c.1,encode sentinel c.2)
def encodeState (sentinel : Nat) (s : State n) : RawState n :=
  ⟨s.links.map (encodeCell sentinel),s.fresh⟩
def encodeWeights (sentinel : Nat) (wa : Weights n) : RawWeights n :=
  fun u v => encode sentinel (wa u v)

theorem encode_le (sentinel : Nat) (a b : Distance) (ha : Valid sentinel a) (hb : Valid sentinel b) :
    encode sentinel a≤encode sentinel b ↔ DLE a b := by
  cases a with
  | none =>
      cases b with
      | none => simp [encode,DLE]
      | some b => have h:=hb b rfl;simp [encode,DLE];omega
  | some a =>
      cases b with
      | none => have h:=ha a rfl;simp [encode,DLE];omega
      | some b => simp [encode,DLE]

theorem encode_eq (sentinel : Nat) (a b : Distance) (ha : Valid sentinel a) (hb : Valid sentinel b) :
    encode sentinel a=encode sentinel b ↔ a=b := by
  constructor
  · intro he
    exact dle_antisymm ((encode_le sentinel a b ha hb).mp (Int.le_of_eq he))
      ((encode_le sentinel b a hb ha).mp (Int.le_of_eq he.symm))
  · exact congrArg (encode sentinel)

theorem encode_lookup (sentinel : Nat) (s : State n) (v : Fin n) :
    lookup (encodeState sentinel s).links v=encodeCell sentinel (lookup s.links v) := by
  simp [encodeState,lookup]
theorem encode_distance (sentinel : Nat) (s : State n) (v : Fin n) :
    rawDistance (encodeState sentinel s) v=encode sentinel (distance s v) := by
  simp [rawDistance,encode_lookup,encodeCell,distance]
theorem encode_parent (sentinel : Nat) (s : State n) (v : Fin n) :
    rawParent (encodeState sentinel s) v=parent s v := by
  simp [rawParent,encode_lookup,encodeCell,parent]

theorem rawSum_encode (sentinel d : Nat) (w : Distance) (hw : Valid sentinel w) :
    rawSum sentinel d (encode sentinel w)=encode sentinel (plus (some d) w) := by
  cases w with
  | none => simp [rawSum,encode,plus]
  | some w =>
      have h:=hw w rfl
      have hn : (w : Int)≠sentinel := by omega
      simp [rawSum,encode,plus,hn]

theorem encode_choose (sentinel : Nat) (s : State n)
    (hs : ∀ v,Valid sentinel (distance s v)) :
    rawChoose (encodeState sentinel s)=choose s := by
  have hc (u v : Fin n) : rawScore (encodeState sentinel s) u ≤ rawScore (encodeState sentinel s) v ↔
      Dijkstra.Core.score s u ≤ Dijkstra.Core.score s v := by
    rw [rawScore_le_iff, Dijkstra.Core.score_le_iff, encode_distance, encode_distance,
      encode_le sentinel _ _ (hs u) (hs v), encode_eq sentinel _ _ (hs u) (hs v)]
  have he (xs : List (Fin n)) :
      Optimization.Thinning.argmin (rawScore (encodeState sentinel s)) xs =
        Optimization.Thinning.argmin (Dijkstra.Core.score s) xs := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      simp only [Optimization.Thinning.argmin, ih]
      split
      · rfl
      · simp only [hc]
  exact he s.fresh

theorem rawUpdate_lookup (sentinel : Int) (wa : RawWeights n) (s : RawState n) (v u : Fin n)
    (hn : s.fresh.Nodup) :
    lookup (rawUpdate sentinel wa s v).links u=
      if u∈s.fresh.filter (fun x => x != v) then
        rawBetter (lookup s.links u) (v,rawSum sentinel (rawDistance s v) (wa v u))
      else lookup s.links u := by
  simp only [rawUpdate,accum_lookup]
  rw [valuesAt_map_unique _ _ (hn.filter _) u]
  split <;> rfl

theorem encode_better (sentinel : Nat) (old new : Fin n × Distance)
    (ho : Valid sentinel old.2) (hn : Valid sentinel new.2) :
    encodeCell sentinel (better old new)=rawBetter (encodeCell sentinel old) (encodeCell sentinel new) := by
  unfold better rawBetter
  simp only [encodeCell,encode_le sentinel _ _ ho hn]
  split <;> rfl

theorem encode_update (sentinel : Nat) (wa : Weights n) (s : State n) (v : Fin n) (d : Nat)
    (hn : s.fresh.Nodup) (hd : distance s v=some d)
    (hs : ∀ u,Valid sentinel (distance s u))
    (hw : ∀ u,Valid sentinel (wa v u))
    (hsum : ∀ u,Valid sentinel (plus (some d) (wa v u))) :
    rawUpdate sentinel (encodeWeights sentinel wa) (encodeState sentinel s) v=
      encodeState sentinel (update wa s v) := by
  apply RawState.ext
  · apply Vector.ext
    intro i hi
    let u : Fin n := ⟨i,hi⟩
    change lookup (rawUpdate sentinel (encodeWeights sentinel wa) (encodeState sentinel s) v).links u=
      lookup (encodeState sentinel (update wa s v)).links u
    rw [rawUpdate_lookup _ _ _ _ _ hn,encode_lookup sentinel (update wa s v) u,
      update_lookup _ _ _ _ hn]
    change (if u∈remaining s v then
      rawBetter (lookup (encodeState sentinel s).links u)
        (v,rawSum sentinel (rawDistance (encodeState sentinel s) v) (encode sentinel (wa v u)))
      else lookup (encodeState sentinel s).links u)=_
    by_cases hm : u∈remaining s v
    · rw [ite_eq_left hm,ite_eq_left hm,encode_lookup,encode_distance,hd,encode,rawSum_encode sentinel d _ (hw u)]
      simpa only [hd,encodeCell] using (encode_better sentinel (lookup s.links u)
        (v,plus (some d) (wa v u)) (hs u) (hsum u)).symm
    · rw [ite_eq_right hm,ite_eq_right hm,encode_lookup]
  · rfl

end Dijkstra.Sentinel
