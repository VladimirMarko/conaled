import Applications.Dijkstra.Store
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.Induction

set_option autoImplicit false
set_option warningAsError true

/-!
Exercise/Answer 9.9: actual finite row-major weight matrices.  Source labels
1..n are ranks Fin n plus one.  Missing edges are genuine infinity (`none`).
The directed constructor writes forward associations.  The undirected source
writes every forward association, then every reverse association, in that order.
Repeated keys retain the Chapter3 last-write extension; graph correspondence
requires consistent weights for the same undirected pair.
-/

namespace Prim.Weights

open Dijkstra.Store

universe u
variable {α : Type u} {n : Nat}

abbrev FEdge (n : Nat) (α : Type u) := Fin n × Fin n × α
abbrev Matrix (n : Nat) (α : Type u) := Store (n*n) (Option α)
abbrev WeightFunction (n : Nat) (α : Type u) := Fin n → Fin n → Option α

def index (u v : Fin n) : Fin (n*n) := finProdFinEquiv (u, v)

theorem index_value (u v : Fin n) : (index u v).val = u.val * n + v.val := by
  change v.val + n * u.val = u.val * n + v.val
  ac_rfl

def view (a : Matrix n α) (u v : Fin n) : Option α := lookup a (index u v)

theorem index_injective (u v x y : Fin n) : index u v = index x y ↔ u=x ∧ v=y :=
  by simp only [index, EmbeddingLike.apply_eq_iff_eq, Prod.mk.injEq]

def forward (es : List (FEdge n α)) : List (Fin (n*n) × α) :=
  es.map (fun e => (index e.1 e.2.1,e.2.2))

def backward (es : List (FEdge n α)) : List (Fin (n*n) × α) :=
  es.map (fun e => (index e.2.1 e.1,e.2.2))

def weightsD (es : List (FEdge n α)) : Matrix n α := accum (fun _ x => some x) (Vector.replicate (n*n) none) (forward es)

def weightsP (es : List (FEdge n α)) : Matrix n α :=
  accum (fun _ x => some x) (Vector.replicate (n*n) none) (forward es ++ backward es)

def edgeValues (es : List (FEdge n α)) (u v : Fin n) : List α :=
  es.filterMap (fun e => if e.1=u ∧ e.2.1=v then some e.2.2 else none)

def lastWrite (xs : List α) : Option α := xs.getLast?

/-- The source overwrite fold is the standard last-element observation. -/
theorem overwrite_fold (xs : List α) (seed : Option α) :
    xs.foldl (fun _ x => some x) seed = xs.getLast?.or seed := by
  induction xs using List.reverseRecOn with
  | nil => rfl
  | append_singleton xs x ih => simp [List.foldl_append]

def Coherent (es : List (FEdge n α)) : Prop :=
  ∀ e ∈ es, ∀ f ∈ es,
    ((e.1=f.1 ∧ e.2.1=f.2.1) ∨ (e.1=f.2.1 ∧ e.2.1=f.1)) → e.2.2=f.2.2

theorem edgeValues_mem (es : List (FEdge n α)) (u v : Fin n) (w : α) :
    w ∈ edgeValues es u v ↔ (u,v,w) ∈ es := by
  simp only [edgeValues,List.mem_filterMap]
  constructor
  · rintro ⟨⟨a,b,c⟩,hm,hv⟩
    split at hv
    next h =>
      rcases h with ⟨rfl,rfl⟩
      have hc : c=w := Option.some.inj hv
      simpa only [hc] using hm
    next => simp at hv
  · intro hm
    exact ⟨(u,v,w),hm,by simp⟩

private theorem forward_values (es : List (FEdge n α)) (u v : Fin n) :
    valuesAt (index u v) (forward es) = edgeValues es u v := by
  simp only [valuesAt,forward,List.filterMap_map,edgeValues]
  congr 1
  funext e
  simp only [Function.comp_apply,index_injective]

private theorem backward_values (es : List (FEdge n α)) (u v : Fin n) :
    valuesAt (index u v) (backward es) = edgeValues es v u := by
  simp only [valuesAt,backward,List.filterMap_map,edgeValues]
  congr 1
  funext e
  simp only [Function.comp_apply,index_injective,and_comm]

theorem directed_lookup (es : List (FEdge n α)) (u v : Fin n) :
    view (weightsD es) u v = lastWrite (edgeValues es u v) := by
  simp only [view, weightsD, accum_lookup, forward_values, lastWrite]
  simp [lookup, overwrite_fold]

theorem undirected_lookup (es : List (FEdge n α)) (u v : Fin n) :
    view (weightsP es) u v = lastWrite (edgeValues es u v ++ edgeValues es v u) := by
  simp only [view, weightsP, accum_lookup, valuesAt, List.filterMap_append]
  rw [← valuesAt,← valuesAt,forward_values,backward_values]
  simp [lookup, overwrite_fold, lastWrite]

/-- Exactly the two source overwrite passes, including their relative order. -/
theorem undirected_two_passes (es : List (FEdge n α)) :
    weightsP es = accum (fun _ x => some x) (weightsD es) (backward es) := by
  simp only [weightsP, weightsD, accum, List.foldl_append]

theorem lastWrite_member {xs : List α} {w : α} (h : lastWrite xs=some w) : w∈xs :=
  List.mem_of_getLast? h

theorem lastWrite_none_iff (xs : List α) : lastWrite xs=none ↔ xs=[] :=
  List.getLast?_eq_none_iff

theorem lastWrite_constant {xs : List α} {w : α} (hne : xs≠[])
    (h : ∀ x∈xs,x=w) : lastWrite xs=some w := by
  cases he : lastWrite xs with
  | none => exact False.elim (hne ((lastWrite_none_iff xs).mp he))
  | some x => rw [h x (lastWrite_member he)]

theorem directed_sound {es : List (FEdge n α)} {u v : Fin n} {w : α}
    (h : view (weightsD es) u v=some w) : (u,v,w)∈es := by
  rw [directed_lookup] at h
  exact (edgeValues_mem es u v w).mp (lastWrite_member h)

theorem undirected_sound {es : List (FEdge n α)} {u v : Fin n} {w : α}
    (h : view (weightsP es) u v=some w) : (u,v,w)∈es ∨ (v,u,w)∈es := by
  rw [undirected_lookup] at h
  have hm := List.mem_append.mp (lastWrite_member h)
  exact hm.imp ((edgeValues_mem es u v w).mp) ((edgeValues_mem es v u w).mp)

theorem undirected_complete {es : List (FEdge n α)} (hc : Coherent es)
    {u v : Fin n} {w : α} (hm : (u,v,w)∈es ∨ (v,u,w)∈es) :
    view (weightsP es) u v=some w := by
  rw [undirected_lookup]
  have hw : w ∈ edgeValues es u v ++ edgeValues es v u := by
    exact List.mem_append.mpr (hm.imp ((edgeValues_mem es u v w).mpr) ((edgeValues_mem es v u w).mpr))
  apply lastWrite_constant (List.ne_nil_of_mem hw)
  intro x hx
  have hx' := (List.mem_append.mp hx).imp ((edgeValues_mem es u v x).mp) ((edgeValues_mem es v u x).mp)
  rcases hx' with hx | hx <;> rcases hm with hm | hm
  · exact hc _ hx _ hm (Or.inl ⟨rfl,rfl⟩)
  · exact hc _ hx _ hm (Or.inr ⟨rfl,rfl⟩)
  · exact hc _ hx _ hm (Or.inr ⟨rfl,rfl⟩)
  · exact hc _ hx _ hm (Or.inl ⟨rfl,rfl⟩)

theorem undirected_iff {es : List (FEdge n α)} (hc : Coherent es)
    (u v : Fin n) (w : α) :
    view (weightsP es) u v=some w ↔ (u,v,w)∈es ∨ (v,u,w)∈es :=
  ⟨undirected_sound,undirected_complete hc⟩

theorem undirected_symmetric {es : List (FEdge n α)} (hc : Coherent es)
    (u v : Fin n) : view (weightsP es) u v=view (weightsP es) v u := by
  cases hu : view (weightsP es) u v with
  | none =>
      cases hv : view (weightsP es) v u with
      | none => rfl
      | some w =>
          have hw := undirected_complete hc ((undirected_sound hv).symm)
          rw [hu] at hw
          cases hw
  | some w =>
      have hv := undirected_complete hc ((undirected_sound hu).symm)
      exact hv.symm

theorem directed_unique {es : List (FEdge n α)} {u v : Fin n} {w : α}
    (hm : (u,v,w)∈es) (hc : ∀ x, (u,v,x)∈es → x=w) :
    view (weightsD es) u v=some w := by
  rw [directed_lookup]
  apply lastWrite_constant (List.ne_nil_of_mem ((edgeValues_mem es u v w).mpr hm))
  intro x hx
  exact hc x ((edgeValues_mem es u v x).mp hx)

/-- Contradictory reverse declarations invalidate undirected matrix symmetry. -/
theorem reverse_conflict_counterexample :
    let es : List (FEdge 2 Nat) := [(⟨0,by decide⟩,⟨1,by decide⟩,3),
      (⟨1,by decide⟩,⟨0,by decide⟩,7)]
    view (weightsP es) ⟨0,by decide⟩ ⟨1,by decide⟩=some 7 ∧
    view (weightsP es) ⟨1,by decide⟩ ⟨0,by decide⟩=some 3 := by decide

end Prim.Weights
