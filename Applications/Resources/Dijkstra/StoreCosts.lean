import Applications.Dijkstra.Store
import Applications.Resources.Workload

/-! Abstract monolithic-cell bulk accounting: one copy, then ordered read/combine/write.
These charges do not describe the physical allocation behavior of Lean's Vector.set. -/
namespace Resources.DijkstraStore
open Dijkstra.Store
universe u v
variable {α : Type u} {β : Type v} {n : Nat}

def copy (a : Store n α) : Store n α := Vector.ofFn (lookup a)

theorem copy_value (a : Store n α) : copy a = a := by
  apply Vector.ext
  intro i hi
  simp [copy,lookup]

def associationStep (f : α → β → α) (iv : Fin n × β) (a : Store n α) : Measured (Store n α) Nat :=
  (accumStep f a iv,3)

def accumRun (f : α → β → α) (ivs : List (Fin n × β)) (a : Store n α) : Measured (Store n α) Nat :=
  run (associationStep f) ivs a

/-- The source association recursion, specialized from the shared runner. -/
theorem accumRun_cons (f : α → β → α) (iv : Fin n × β)
    (ivs : List (Fin n × β)) (a : Store n α) :
    accumRun f (iv::ivs) a =
      let rest := accumRun f ivs (accumStep f a iv)
      (rest.1,3+rest.2) := rfl

theorem accumRun_value (f : α → β → α) (ivs : List (Fin n × β)) (a : Store n α) :
    (accumRun f ivs a).1 = accum f a ivs := by
  rw [accumRun,run_state]
  rfl

theorem accumRun_work (f : α → β → α) (ivs : List (Fin n × β)) (a : Store n α) :
    (accumRun f ivs a).2 = 3*ivs.length := by
  induction ivs generalizing a with
  | nil => rfl
  | cons iv ivs ih =>
    change 3 + (accumRun f ivs (accumStep f a iv)).2 = _
    rw [ih]
    simp [Nat.mul_add,Nat.add_comm]

def bulkRun (f : α → β → α) (a : Store n α) (ivs : List (Fin n × β)) : Measured (Store n α) Nat :=
  bind (copy a,n) (accumRun f ivs)

theorem bulkRun_exact (f : α → β → α) (a : Store n α) (ivs : List (Fin n × β)) :
    bulkRun f a ivs = (accum f a ivs,n+3*ivs.length) := by
  simp [bulkRun,bind,accumRun_value,accumRun_work,copy_value]

end Resources.DijkstraStore
