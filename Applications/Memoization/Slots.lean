import Applications.Memoization.Cache

namespace Applications.Memoization
namespace Slots

def Data : Nat → Type → Type
  | 0, _ => Unit
  | n + 1, V => V × Data n V

def read : {n : Nat} → Data n V → Fin n → Resources.Measured V Nat
  | 0, _, i => Fin.elim0 i
  | _ + 1, s, i => Fin.cases (s.1,1)
      (fun j => let r := read s.2 j; (r.1,r.2+1)) i

def tabulate : (n : Nat) → (Fin n → V) → Data n V
  | 0, _ => ()
  | n+1, f => (f 0, tabulate n (fun i => f i.succ))

@[simp] theorem read_tabulate (n : Nat) (f : Fin n → V) (k : Fin n) :
    (read (tabulate n f) k).1 = f k := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih => induction k using Fin.cases <;> simp [read, tabulate, ih]

@[simp] theorem tabulate_read (n : Nat) (s : Data n V) :
    tabulate n (fun i => (read s i).1) = s := by
  induction n with
  | zero => cases s; rfl
  | succ n ih => simp [tabulate, read, ih]; rfl

def representation (n : Nat) : Representation (Fin n) where
  Carrier := Data n
  meaning _ := {
    toFun := fun s i => (read s i).1
    invFun := tabulate n
    left_inv := tabulate_read n
    right_inv := fun f => funext (read_tabulate n f) }

def write : {n : Nat} → Data n V → Fin n → V → Resources.Measured (Data n V) Nat
  | 0, _, i, _ => Fin.elim0 i
  | _+1, s, i, v => Fin.cases ((v,s.2),1)
      (fun j => let w := write s.2 j v; ((s.1,w.1),w.2+1)) i

theorem read_write {n : Nat} (s : Data n V) (i : Fin n) (v : V) (j : Fin n) :
    (read (write s i v).1 j).1 = if j = i then v else (read s j).1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    induction i using Fin.cases <;> induction j using Fin.cases <;>
      simp [read, write, ih, eq_comm]

theorem read_cost {n : Nat} (s : Data n V) (i : Fin n) : (read s i).2 = i.val + 1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih => induction i using Fin.cases <;> simp [read, ih]

theorem write_cost {n : Nat} (s : Data n V) (i : Fin n) (v : V) :
    (write s i v).2 = i.val + 1 := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih => induction i using Fin.cases <;> simp [write, ih]

def storage (n : Nat) : Storage (Fin n) where
  representation := representation n
  read := read
  read_value := fun _ _ => rfl
  write := write
  write_lookup := read_write

@[simp] theorem storage_read_cost {n : Nat} (s : (storage n).representation.Carrier V)
    (i : Fin n) : ((storage n).read s i).2 = i.val + 1 := read_cost s i

/-- Empty retained slots are allocated eagerly, one cell per admitted key. -/
def setup : (n : Nat) → Resources.Measured ((storage n).State V) Nat
  | 0 => ((),0)
  | n+1 => let t := setup n; ((none,t.1),t.2+1)

theorem setup_cost (n : Nat) : (setup (V := V) n).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [setup, ih]

theorem setup_empty (n : Nat) : (setup (V := V) n).1 = (storage n).empty := by
  induction n with
  | zero => rfl
  | succ n ih => change (none,(setup n).1) = (none,tabulate n (fun _ => none)); rw [ih]; rfl

/-- Compositional correspondence to the sum of a singleton and the remaining keys. -/
def splitEquiv (n : Nat) : Unit ⊕ Fin n ≃ Fin (n+1) where
  toFun := Sum.elim (fun _ => 0) Fin.succ
  invFun := Fin.cases (.inl ()) (fun i => .inr i)
  left_inv := by intro k; cases k with
    | inl u => cases u; rfl
    | inr i => rfl
  right_inv := by intro i; induction i using Fin.cases <;> rfl

theorem sum_lookup (n : Nat) (s : Data (n+1) V) (i : Fin (n+1)) :
    ((Representation.sum .unit (representation n)).transport (splitEquiv n)).lookup s i =
      (representation (n+1)).lookup s i := by
  induction i using Fin.cases <;> rfl

end Slots
end Applications.Memoization
