import Std

set_option autoImplicit false
set_option warningAsError true
namespace Dijkstra.Store
universe u v
variable {α : Type u} {β : Type v} {n : Nat}

abbrev Store (n : Nat) (α : Type u) := Vector α n

def lookup (a : Store n α) (i : Fin n) : α := a[i.val]

def write (a : Store n α) (i : Fin n) (x : α) : Store n α := a.set i.val x

theorem lookup_write (a : Store n α) (i j : Fin n) (x : α) :
    lookup (write a i x) j = if i = j then x else lookup a j := by
  simp [lookup, write, Vector.getElem_set, Fin.ext_iff]

def valuesAt (j : Fin n) (ivs : List (Fin n × β)) : List β :=
  ivs.filterMap (fun iv => if iv.1 = j then some iv.2 else none)

def accumStep (f : α → β → α) (a : Store n α) (iv : Fin n × β) : Store n α :=
  write a iv.1 (f (lookup a iv.1) iv.2)

def accum (f : α → β → α) (a : Store n α) (ivs : List (Fin n × β)) : Store n α :=
  ivs.foldl (accumStep f) a

theorem accum_lookup (f : α → β → α) (a : Store n α)
    (ivs : List (Fin n × β)) (j : Fin n) :
    lookup (accum f a ivs) j = (valuesAt j ivs).foldl f (lookup a j) := by
  induction ivs generalizing a with
  | nil => rfl
  | cons iv ivs ih =>
    simp only [accum, List.foldl_cons] at *
    rw [ih]
    by_cases h : iv.1 = j
    · simp [valuesAt, h, accumStep, lookup_write]
    · simp [valuesAt, h, accumStep, lookup_write]

theorem valuesAt_map_unique {β : Type v} (vs : List (Fin n)) (f : Fin n → β)
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

end Dijkstra.Store
