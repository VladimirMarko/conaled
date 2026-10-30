import Applications.Languages.Transposition

/-! Checked indexed constructor/observer transposition and witness-sensitive
parser recovery. The vector family is independent of language derivatives. -/
namespace Examples.EquationTranspose
open SquareKit.EquationTranspose

namespace Vectors
inductive Constructor : Nat → Type
  | nil : Constructor 0
  | cons (n : Nat) : Constructor (n+1)
  | repeat (n : Nat) : Constructor n

inductive Observer (n : Nat) : Type
  | at
  | size

def fields : Constructor n → Type
  | .nil => Unit
  | .cons n => Nat × (Fin n → Nat)
  | .repeat _ => Nat

def arguments : Observer n → Type
  | .at => Fin n
  | .size => Unit

abbrev signature : Signature Nat where
  Constructor := Constructor
  Observer := Observer
  fields := fields
  arguments := arguments
  result := fun _ => Nat

inductive Prim : Type → Type → Type 1
  | empty : Prim Unit (Fin 0 → Nat)
  | cons (n : Nat) : Prim (Nat × (Fin n → Nat)) (Fin (n+1) → Nat)
  | repeat (n : Nat) : Prim Nat (Fin n → Nat)
  | at (n : Nat) : Prim ((Fin n → Nat) × Fin n) Nat
  | size (n : Nat) : Prim Unit Nat

def meaning : Prim A B → A → B
  | .empty, _ => fun i => Fin.elim0 i
  | .cons _, (x,xs) => Fin.cases x xs
  | .repeat _, x => fun _ => x
  | .at _, (xs,i) => xs i
  | .size n, _ => n

def construction (c : Constructor n) : Expr Prim (Slot (fields c) A) (Fin n → Nat) :=
  match c with
  | .nil => .prim .empty (.var .first)
  | .cons n => .prim (.cons n) (.var .first)
  | .repeat n => .prim (.repeat n) (.var .first)

def equations : DataProgram signature Prim where
  body n d c := match d with
    | .at => .prim (.at n) (.pair (construction c) (.var .second))
    | .size => .prim (.size n) (.var .second)

/-- Both blocks move, even when their types happen to agree. -/
example : (transpose equations).body 2 (.cons 1) .at =
    .prim (.at 2) (.pair (.prim (.cons 1) (.var .second)) (.var .first)) := rfl

example : untranspose (transpose equations) = equations := untranspose_transpose _
example : transpose (untranspose (transpose equations)) = transpose equations :=
  transpose_untranspose _

/-- Head and tail order are independently expected to be 7 and 11. -/
example : (transpose equations).construct meaning (.cons 1) (7, fun _ => 11) .at ⟨0,by decide⟩ = 7 := by
  erw [transpose_preserves]
  rfl
example : (transpose equations).construct meaning (.cons 1) (7, fun _ => 11) .at ⟨1,by decide⟩ = 11 := by
  erw [transpose_preserves]
  rfl
example (n x : Nat) : (transpose equations).construct meaning (.repeat n) x .size () = n := by
  erw [transpose_preserves]
  rfl

/-- No well-typed lookup argument exists at the empty index. -/
theorem empty_lookup_impossible (i : arguments (Observer.at (n := 0))) : False :=
  Fin.elim0 i

/-- A constructor-only subset recovers its original equations after transposition. -/
def repeats := restrictConstructors equations (fun _ => Unit) (fun n _ => .repeat n)
example (n : Nat) (d : Observer n) :
    (transpose repeats).body n () d = (transpose equations).body n (.repeat n) d :=
  restrict_constructor_cell equations _ _ _ _ _

/-- Dropping size retains lookup; adding it requires a cell for every constructor. -/
def lookups := restrictObservers equations (fun _ => Unit) (fun _ _ => .at)
example (n : Nat) (c : Constructor n) :
    (transpose lookups).body n c () = (transpose equations).body n c .at :=
  restrict_observer_cell equations _ _ _ _ _
end Vectors

namespace Parsing
open LanguageWitnesses LanguageWitnesses.Transposition

example :
    untranspose (transpose (equations (α := Bool))) = equations := untranspose_transpose _

/-- Nullable star selects the empty list, without identifying it with a singleton parse. -/
example : (methods.construct (meaning (α := Bool)) (.star epsilon) Parser.epsilon .nullable PUnit.unit).down =
    Decision.yes ⟨[],rfl⟩ := recovered_nullable _ _

example : (nullableStarIso (epsilon (α := Bool))).forward
    (⟨[],rfl⟩ : Star epsilon []) ≠
    (nullableStarIso epsilon).forward (⟨[⟨[], ⟨rfl⟩⟩],rfl⟩ : Star epsilon []) := by
  intro h
  have bad := congrArg List.length h
  cases bad

example (p : Parser (α := Bool) P) (q : Parser Q) (n : Nat) (w : List Bool)
    (h : w.length ≤ n) :
    (methods.construct meaning (.concat P Q) (p,q) (.snapshot n) PUnit.unit).lookup w h =
      (Parser.concat p q).parse w := recovered_snapshot _ _ _ _ _

/-- This is the exact transformed syntax, including the retained right operand. -/
example (P Q : Language Bool) (a : Bool) :
    methods.body (Concat P Q) (.concat P Q) (.derive a) =
      .prim (.transport (fun w => (derivativeConcatIso P Q a w).symm))
        (.prim .union (.pair
          (.prim .scaleNullable (.pair (.fst (.var .second))
            (.prim (.derive a) (.snd (.var .second)))))
          (.prim .concat (.pair (.prim (.derive a) (.fst (.var .second)))
            (.snd (.var .second)))))) := rfl
end Parsing
end Examples.EquationTranspose
