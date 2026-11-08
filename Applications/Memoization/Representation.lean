import Applications.Parallel.FFT
import Mathlib.Logic.Equiv.Defs

/-! Total key-shaped function representations. The equivalence is semantic;
it does not assert retained execution or a tariff for tabulation. -/
namespace Applications.Memoization

structure Representation (K : Type) where
  Carrier : Type → Type
  meaning : (V : Type) → Carrier V ≃ (K → V)

namespace Representation
variable {K L V W U : Type}
def lookup (R : Representation K) (r : R.Carrier V) : K → V := R.meaning V r
def tabulate (R : Representation K) (f : K → V) : R.Carrier V := (R.meaning V).symm f
@[simp] theorem lookup_tabulate (R : Representation K) (f : K → V) :
    R.lookup (R.tabulate f) = f := (R.meaning V).apply_symm_apply f
@[simp] theorem tabulate_lookup (R : Representation K) (r : R.Carrier V) :
    R.tabulate (R.lookup r) = r := (R.meaning V).symm_apply_apply r
theorem ext (R : Representation K) {r s : R.Carrier V}
    (h : ∀ k, R.lookup r k = R.lookup s k) : r = s :=
  (R.meaning V).injective (funext h)

def map (R : Representation K) (f : V → W) (r : R.Carrier V) : R.Carrier W :=
  R.tabulate (f ∘ R.lookup r)
@[simp] theorem lookup_map (R : Representation K) (f : V → W) (r : R.Carrier V) (k : K) :
    R.lookup (R.map f r) k = f (R.lookup r k) := congrFun (R.lookup_tabulate _) k
@[simp] theorem map_id (R : Representation K) (r : R.Carrier V) : R.map id r = r :=
  R.ext (fun _ => R.lookup_map _ _ _)
theorem map_comp (R : Representation K) (f : V → W) (g : W → U) (r : R.Carrier V) :
    R.map (g ∘ f) r = R.map g (R.map f r) := by
  apply R.ext
  intro k
  simp

/-- Transport the domain, keeping the represented carrier unchanged. -/
def transport (R : Representation K) (e : K ≃ L) : Representation L where
  Carrier := R.Carrier
  meaning V := (R.meaning V).trans {
    toFun := fun f => f ∘ e.symm
    invFun := fun f => f ∘ e
    left_inv := by intro f; funext k; simp
    right_inv := by intro f; funext k; simp }
@[simp] theorem transport_lookup (R : Representation K) (e : K ≃ L)
    (r : R.Carrier V) (l : L) : (R.transport e).lookup r l = R.lookup r (e.symm l) := rfl

theorem transport_map (R : Representation K) (e : K ≃ L)
    (f : V → W) (r : R.Carrier V) : (R.transport e).map f r = R.map f r := by
  apply (R.transport e).ext
  intro l
  exact ((R.transport e).lookup_map f r l).trans (R.lookup_map f r (e.symm l)).symm

/-- A local lookup square identifies an operation with the semantic map.
This proves no equality of execution costs. -/
theorem operation_eq_map (R : Representation K) (f : V → W)
    (op : R.Carrier V → R.Carrier W)
    (law : ∀ r k, R.lookup (op r) k = f (R.lookup r k)) (r : R.Carrier V) :
    op r = R.map f r := by
  apply R.ext
  intro k
  rw [law, R.lookup_map]

def empty : Representation Empty where
  Carrier _ := Unit
  meaning _ := {
    toFun := fun _ e => e.elim
    invFun := fun _ => ()
    left_inv := by intro r; cases r; rfl
    right_inv := by intro f; funext e; exact e.elim }

def unit : Representation Unit where
  Carrier V := V
  meaning _ := {
    toFun := fun v _ => v
    invFun := fun f => f ()
    left_inv := fun _ => rfl
    right_inv := by intro f; funext u; cases u; rfl }

/-- First component is false, second is true. -/
def bool : Representation Bool where
  Carrier V := V × V
  meaning _ := {
    toFun := fun p b => if b then p.2 else p.1
    invFun := fun f => (f false, f true)
    left_inv := by intro p; rfl
    right_inv := by intro f; funext b; cases b <;> rfl }

def sum (R : Representation K) (S : Representation L) : Representation (K ⊕ L) where
  Carrier V := R.Carrier V × S.Carrier V
  meaning _ := {
    toFun := fun p => Sum.elim (R.lookup p.1) (S.lookup p.2)
    invFun := fun f => (R.tabulate (f ∘ Sum.inl), S.tabulate (f ∘ Sum.inr))
    left_inv := by intro p; simp [lookup, tabulate]
    right_inv := by intro f; funext k; cases k <;> simp [lookup, tabulate] }

def prod (R : Representation K) (S : Representation L) : Representation (K × L) where
  Carrier V := R.Carrier (S.Carrier V)
  meaning _ := {
    toFun := fun r k => S.lookup (R.lookup r k.1) k.2
    invFun := fun f => R.tabulate (fun k => S.tabulate (fun l => f (k,l)))
    left_inv := by intro r; simp
    right_inv := by intro f; funext k; simp }

/-- Existing FFT nested products satisfy the same contract without changing FFT. -/
def factor (s : Applications.Parallel.Factor) : Representation s.Index where
  Carrier V := s.Data V
  meaning _ := {
    toFun := s.get
    invFun := s.tabulate
    left_inv := s.tabulate_get
    right_inv := fun f => funext (s.get_tabulate f) }

end Representation
end Applications.Memoization
