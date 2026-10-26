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

end Dijkstra.Store
