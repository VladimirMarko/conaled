import SquareKit.DependentOperation.Syntax
import Mathlib.Data.Fin.Rev

/-! A selected position in an array of length n+1. Insertion changes both its
bound and its selected position. The machines use different state coordinates:
(total bound, position) and (distance from left, distance from right). -/
namespace SquareKit.DependentOperation.Selector
open DependentBranchTheoryMaps

abbrev Position (n : Nat) := Fin (n+1)

inductive Op : Signature where
  | reflect (n) : Op n n
  | insert (n) : Op n (n+1)
  | pad (n) : Op n (n+2)
  | reset (n) : Op n n

def operate : ∀ {n m}, Op n m → Position n → Position m
  | _, _, .reflect _, i => Fin.rev i
  | _, _, .insert _, i => ⟨i.val+1, by omega⟩
  | _, _, .pad _, i => ⟨i.val+1, by omega⟩
  | _, _, .reset _, _ => 0

inductive Low where | mirror | left | right | origin
  deriving DecidableEq, Repr

inductive Macro where | mirror | left | both | origin
  deriving DecidableEq, Repr

def instructions : ∀ {n m}, Op n m → List Macro
  | _, _, .reflect _ => [.mirror]
  | _, _, .insert _ => [.left]
  | _, _, .pad _ => [.both]
  | _, _, .reset _ => [.origin]

def lower : Macro → List Low
  | .mirror => [.mirror]
  | .left => [.left]
  | .both => [.left,.right]
  | .origin => [.origin]

/-- Native total-bound/position machine; no dependent proof is stored. -/
def runTotal : Low → Nat × Nat → Nat × Nat
  | .mirror, (n,i) => (n,n-i)
  | .left, (n,i) => (n+1,i+1)
  | .right, (n,i) => (n+1,i)
  | .origin, (n,_) => (n,0)

/-- Independent distance-coordinate machine. Reflection is a swap; resetting
moves all distance to the right. It does not call runTotal or decode a Fin. -/
def runDistances : Low → Nat × Nat → Nat × Nat
  | .mirror, (l,r) => (r,l)
  | .left, (l,r) => (l+1,r)
  | .right, (l,r) => (l,r+1)
  | .origin, (l,r) => (0,l+r)

def total (n) (i : Position n) : Nat × Nat := (n,i.val)
def distances (n) (i : Position n) : Nat × Nat := (i.val,n-i.val)

theorem total_injective (n) : Function.Injective (total n) := by
  intro x y h
  apply Fin.ext
  exact congrArg Prod.snd h

theorem distances_injective (n) : Function.Injective (distances n) := by
  intro x y h
  apply Fin.ext
  exact congrArg Prod.fst h

/-- The low-level primitive words realize the selected source operation,
including its output bound. These are the only machine-specific contracts. -/
theorem total_local {n m} (o : Op n m) (i : Position n) :
    ((instructions o).flatMap lower).foldl (fun s k => runTotal k s) (total n i) =
      total m (operate o i) := by
  cases o <;> simp [instructions, lower, runTotal, total, operate, Fin.rev]

theorem distances_local {n m} (o : Op n m) (i : Position n) :
    ((instructions o).flatMap lower).foldl (fun s k => runDistances k s) (distances n i) =
      distances m (operate o i) := by
  have hi := i.isLt
  cases o <;> simp [instructions, lower, runDistances, distances, operate, Fin.rev]
    <;> omega

/-- Native helpers are unrestricted and reusable. This proof is an independent
structural route, exposed to the native trial arm rather than artificially
requiring a proof for every concrete expression. -/
theorem native_distances {V : Nat → Type} (ρ : ∀ n, V n → Position n)
    {n} (t : Term Op V n) :
    (emit (fun o => (instructions o).flatMap lower) t).run runDistances
      (fun n v => distances n (ρ n v)) = distances n (eval @operate ρ t) := by
  induction t with
  | hyp v => rfl
  | rule r ts ih =>
    simp only [emit, Code.run, List.foldl_append]
    change ((instructions r.op).flatMap lower).foldl _
      ((emit (fun o => (instructions o).flatMap lower) (ts ())).run runDistances (fun k v => distances k (ρ k v))) = _
    rw [ih ()]
    exact distances_local r.op _

/-- Symmetric padding commutes with reflection. An arbitrary insertion does
not; this is an interaction obligation, not implied by the two local laws. -/
theorem reflect_pad (n) (i : Position n) :
    operate (.reflect (n+2)) (operate (.pad n) i) =
      operate (.pad n) (operate (.reflect n) i) := by
  apply Fin.ext
  simp [operate, Fin.rev]
  omega

theorem reflect_insert_fails :
    operate (.reflect 3) (operate (.insert 2) (0 : Position 2)) ≠
      operate (.insert 2) (operate (.reflect 2) (0 : Position 2)) := by decide

/-- The proposed maintenance change replaces symmetric padding by two left
insertions. Existing interaction proof is genuinely invalid after that edit. -/
theorem changed_padding_fails :
    operate (.reflect 4) (operate (.insert 3) (operate (.insert 2) (0 : Position 2))) ≠
      operate (.insert 3) (operate (.insert 2) (operate (.reflect 2) (0 : Position 2))) := by decide

end SquareKit.DependentOperation.Selector
