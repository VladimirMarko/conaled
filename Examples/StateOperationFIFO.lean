import Examples.StateOperationCombination
import Applications.ModelCombination.UnaryOperationTransport
import Applications.Sequences.AbstractFIFO

/-! Changed-arity reuse and an interleaved native FIFO consumer. -/
set_option autoImplicit false
namespace NativeModelCombination.StateOperations

def suppliedReverse (y : Y) : Y := (y.1.reverse, PUnit.unit)
theorem supplied_involution (y : Y) : suppliedReverse (suppliedReverse y) = y := by
  rcases y with ⟨ys,⟨⟩⟩; simp [suppliedReverse]
def directReverse (x : X) : X := overlap.symm (suppliedReverse (overlap x))
def helperReverse := OperationTransport.unary overlap suppliedReverse

def signatureReverse (x : X) : X :=
  let : SignatureTransport.extendedLanguage.Structure Y :=
    SignatureTransport.extendedStructure suppliedJoin suppliedUnit suppliedReverse
  let : SignatureTransport.extendedLanguage.Structure X := overlap.symm.inducedStructure
  FirstOrder.Language.Structure.funMap (L := SignatureTransport.extendedLanguage)
    (.inr SignatureTransport.UnarySymbol.reverse) (fun _ => x)

theorem direct_reverse_recovery (y : Y) : overlap (directReverse (overlap.symm y)) =
    suppliedReverse y := by simp [directReverse]
theorem direct_involution (x : X) : directReverse (directReverse x) = x := by
  simp [directReverse, supplied_involution]
theorem helper_involution (x : X) : helperReverse (helperReverse x) = x :=
  OperationTransport.involutive overlap suppliedReverse supplied_involution x
theorem signature_involution (x : X) : signatureReverse (signatureReverse x) = x :=
  SignatureTransport.involutive overlap suppliedJoin suppliedUnit suppliedReverse supplied_involution x
example : directReverse = helperReverse ∧ signatureReverse = helperReverse := ⟨rfl,rfl⟩
example : helperReverse [8,9,4] = [4,9,8] := rfl
example (y : Y) : overlap (helperReverse (overlap.symm y)) = suppliedReverse y :=
  OperationTransport.recover_unary overlap suppliedReverse y
example (x y : X) :
    letI : SignatureTransport.extendedLanguage.Structure Y :=
      SignatureTransport.extendedStructure suppliedJoin suppliedUnit suppliedReverse
    letI : SignatureTransport.extendedLanguage.Structure X := overlap.symm.inducedStructure
    FirstOrder.Language.Structure.funMap (L := SignatureTransport.extendedLanguage)
      (.inl SignatureTransport.Symbol.join) (fun i => if i = 0 then x else y) = helper x y :=
  SignatureTransport.extended_binary overlap suppliedJoin suppliedUnit suppliedReverse x y

open Sequences.AbstractFIFO
/-- Tail is supplied separately; no FIFO equation follows just from an equivalence. -/
def suppliedTail (y : Y) : Y := (y.1.tail, PUnit.unit)
def fifo : Ops Nat X where
  empty := overlap.symm suppliedUnit
  snoc x xs := helper xs [x]
  tail := OperationTransport.unary overlap suppliedTail
  head := List.head?

theorem fifo_eq_native : fifo = lists Nat := rfl

theorem all_runs (cs : List (Command Nat)) (xs : X) : run fifo cs xs = run (lists Nat) cs xs := by
  rw [fifo_eq_native]

def commands : List (Command Nat) := [.enqueue 8, .enqueue 9, .delete, .enqueue 4]
example : run fifo commands fifo.empty = [9,4] := rfl
example : client fifo commands fifo.empty = some 9 := rfl

/-- Retain the relational symmetric-list client under its original hypotheses. -/
theorem relational_client (cs : List (Command Nat)) :
    client (symmetric Nat) cs (symmetric Nat).empty = client fifo cs fifo.empty := by
  rw [fifo_eq_native]
  exact (symmetric_correct Nat).client_empty cs

/-- Exact recovery is strictly stronger than this existing relation-only interface. -/
example {Q R : Type} {a : Ops Nat Q} {b : Ops Nat R} {rel : Q → R → Prop}
    (h : Simulation a b rel) (cs : List (Command Nat)) {q r} (hr : rel q r) :
    client a cs q = client b cs r := h.client_eq cs hr
end NativeModelCombination.StateOperations
