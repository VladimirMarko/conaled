import Applications.Dijkstra.Store
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Fin

/-! Recompute row folds only where their actual input indices intersect an
ordered update. The frame law comes from the existing ADWH store accumulator. -/
set_option autoImplicit false
set_option warningAsError true
namespace Incremental.LocalRows
open Dijkstra.Store
variable {n m : Nat} {α β : Type}

def fold (combine : α → β → β) (seed : β) (indices : List (Fin n)) (values : Fin n → α) : β :=
  indices.foldr (fun i acc => combine (values i) acc) seed

theorem fold_congr (combine : α → β → β) (seed : β) (indices : List (Fin n))
    (f g : Fin n → α) (h : ∀ i ∈ indices, f i = g i) :
    fold combine seed indices f = fold combine seed indices g := by
  induction indices with
  | nil => rfl
  | cons i is ih =>
    change combine (f i) (fold combine seed is f) = combine (g i) (fold combine seed is g)
    rw [h i List.mem_cons_self, ih (fun j hj => h j (List.mem_cons_of_mem i hj))]

def affected (rows : Fin m → List (Fin n)) (changes : List (Fin n × α)) : Finset (Fin m) :=
  Finset.univ.filter fun v => ∃ i ∈ rows v, i ∈ changes.map Prod.fst

def evaluate (combine : Fin m → α → β → β) (seed : Fin m → β)
    (rows : Fin m → List (Fin n)) (values : Fin n → α) (v : Fin m) : β :=
  fold (combine v) (seed v) (rows v) values

def updateStore (a : Store n α) (changes : List (Fin n × α)) : Store n α :=
  accum (fun _ new => new) a changes

/-- Repeated assignments retain their original order through accum_lookup. -/
theorem updateStore_lookup (a : Store n α) (changes : List (Fin n × α)) (i : Fin n) :
    lookup (updateStore a changes) i = (valuesAt i changes).foldl (fun _ new => new) (lookup a i) :=
  accum_lookup _ _ _ _

theorem updateStore_frame (a : Store n α) (changes : List (Fin n × α)) (i : Fin n)
    (hi : i ∉ changes.map Prod.fst) : lookup (updateStore a changes) i = lookup a i := by
  rw [updateStore_lookup]
  have he : valuesAt i changes = [] := by
    unfold valuesAt
    apply List.filterMap_eq_nil_iff.mpr
    intro p hp
    have hn : p.1 ≠ i := by
      intro he
      exact hi (List.mem_map.mpr ⟨p, hp, he⟩)
    simp [hn]
  rw [he]
  rfl

def recompute (combine : Fin m → α → β → β) (seed : Fin m → β)
    (rows : Fin m → List (Fin n)) (a : Store n α) (cache : Fin m → β)
    (changes : List (Fin n × α)) (v : Fin m) : β :=
  if v ∈ affected rows changes then evaluate combine seed rows (lookup (updateStore a changes)) v
  else cache v

theorem recompute_correct (combine : Fin m → α → β → β) (seed : Fin m → β)
    (rows : Fin m → List (Fin n)) (a : Store n α) (cache : Fin m → β)
    (hc : ∀ v, cache v = evaluate combine seed rows (lookup a) v)
    (changes : List (Fin n × α)) (v : Fin m) :
    recompute combine seed rows a cache changes v = evaluate combine seed rows (lookup (updateStore a changes)) v := by
  unfold recompute
  split
  · rfl
  · rename_i hv
    rw [hc]
    apply fold_congr
    intro i hi
    apply (updateStore_frame a changes i _).symm
    intro hm
    apply hv
    simp only [affected, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨i, hi, hm⟩

theorem recompute_untouched (combine : Fin m → α → β → β) (seed : Fin m → β)
    (rows : Fin m → List (Fin n)) (a : Store n α) (cache : Fin m → β)
    (changes : List (Fin n × α)) (v : Fin m) (hv : v ∉ affected rows changes) :
    recompute combine seed rows a cache changes v = cache v := by simp [recompute, hv]

/-- The lattice specification and the literal row fold agree, including duplicates. -/
theorem inf_eq_fold {γ : Type} [LinearOrder γ] [OrderTop γ]
    (indices : List (Fin n)) (values : Fin n → γ) :
    indices.toFinset.inf values = fold min ⊤ indices values := by
  induction indices with
  | nil => simp [fold]
  | cons i is ih =>
    simp only [List.toFinset_cons, Finset.inf_insert]
    change min (values i) (is.toFinset.inf values) = min (values i) (fold min ⊤ is values)
    rw [ih]

end Incremental.LocalRows
