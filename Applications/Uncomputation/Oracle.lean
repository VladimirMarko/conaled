import Applications.Uncomputation.Coordinates

namespace Uncomputation

abbrev functionOps := SquareKit.FunctionCategory.ops

abbrev functionLaws := SquareKit.FunctionCategory.laws

/-- The state order is (retained input, caller output), scratch. -/
def computeBit {X : Type} (f : X → Bool) : ((X × Bool) × Bool) ≃ ((X × Bool) × Bool) :=
  controlled (fun p => f p.1)

def useBit {X : Type} : ((X × Bool) × Bool) ≃ ((X × Bool) × Bool) where
  toFun p := ((p.1.1, xor p.1.2 p.2), p.2)
  invFun p := ((p.1.1, xor p.1.2 p.2), p.2)
  left_inv := by rintro ⟨⟨x, y⟩, t⟩; cases y <;> cases t <;> rfl
  right_inv := by rintro ⟨⟨x, y⟩, t⟩; cases y <;> cases t <;> rfl

def oracle {X : Type} (f : X → Bool) :=
  ((computeBit f).trans useBit).trans (computeBit f).symm

/-- A reusable specialization of the shared argument. The output specification
is controlled XOR of `f`, independent of the scratch implementation. -/
theorem oracle_clean {X : Type} (f : X → Bool) (p : X × Bool) :
    oracle f (p, false) = (controlled f p, false) := by
  have h := cleanup_correct functionOps functionLaws
    (fun p => computeBit f p) (fun p => useBit p) (fun p => (computeBit f).symm p)
    (fun p : X × Bool => (p, false)) (fun p => controlled f p)
    (by funext p; exact (computeBit f).symm_apply_apply _)
    (by
      funext ⟨x, y⟩
      change ((x, xor y (xor false (f x))), xor false (f x)) =
        ((x, xor y (f x)), xor false (f x))
      cases f x <;> rfl)
  exact congrFun h p

/-- AND oracle, including a caller output that need not be zero. -/
theorem and_oracle (a b y : Bool) :
    oracle (fun p : Bool × Bool => p.1 && p.2) (((a, b), y), false) =
      (((a, b), xor y (a && b)), false) := oracle_clean _ _

theorem oracle_reference {X R : Type} (f : X → Bool) (v : (X × Bool) × R → ℂ) :
    (fun p : (((X × Bool) × Bool) × R) =>
      if ((oracle f).symm p.1).2 = false then
        v (((oracle f).symm p.1).1, p.2) else 0) =
    (fun p => if p.1.2 = false then v ((controlled f).symm p.1.1, p.2) else 0) :=
  coherent_clean_reference false (oracle f) (controlled f) (oracle_clean f) v

/-- Dirty scratch corrupts the independently specified output. -/
theorem dirty_scratch : oracle (fun b : Bool => b) ((false, false), true) =
    ((false, true), true) := rfl

/-- Changing a dependency between compute and undo leaves scratch dirty. -/
theorem mutated_control : cnot.symm (true, (cnot (false, false)).2) = (true, true) := rfl

/-- Structural reassociation only changes wire grouping. Logical gate counts
charge CNOT/Toffoli; physical routing is outside this library. -/
def andCircuit : Circuit (((Bool × Bool) × Bool) × Bool) (((Bool × Bool) × Bool) × Bool) :=
  .seq (.tensor .toffoli (.ident Bool))
    (.seq (.assoc _ _ _)
      (.seq (.tensor (.ident (Bool × Bool)) .cnot)
        (.seq (.inverse (.assoc _ _ _)) (.inverse (.tensor .toffoli (.ident Bool))))))

def scratchOutputSwap {X : Type} : ((X × Bool) × Bool) ≃ ((X × Bool) × Bool) where
  toFun p := ((p.1.1,p.2),p.1.2)
  invFun p := ((p.1.1,p.2),p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

theorem andCircuit_connection (p : ((Bool × Bool) × Bool) × Bool) :
    andCircuit.perm p = scratchOutputSwap
      (oracle (fun p : Bool × Bool => p.1 && p.2) (scratchOutputSwap p)) := by
  rcases p with ⟨⟨⟨a,b⟩,t⟩,y⟩
  cases a <;> cases b <;> cases t <;> cases y <;> rfl

theorem andCircuit_clean (a b y : Bool) :
    andCircuit.perm (((a,b),false),y) = (((a,b),false),xor y (a && b)) := by
  rw [andCircuit_connection]
  change scratchOutputSwap (oracle _ (((a,b),y),false)) = _
  rw [and_oracle]
  rfl

end Uncomputation
