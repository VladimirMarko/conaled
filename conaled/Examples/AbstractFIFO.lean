import Applications.Sequences.AbstractFIFOSyntax

/-! One operation-only word client, two representations, and a hidden-state
counterexample. No cost interface is needed to use the behavior theorem. -/
namespace Examples.AbstractFIFO
open Sequences.AbstractFIFO Sequences.Symmetric

def edits : List (Command Nat) := [.enqueue 1, .enqueue 2, .delete, .enqueue 3]

/-- The ordinary client has no decoder, invariant, or proof argument. -/
def ordinary (ops : Ops Nat Q) (q : Q) := client ops edits q

/-- This proof is authored once from public operation evidence. -/
theorem ordinary_correct (ops : Ops Nat Q) (rel : Q → List Nat → Prop)
    (h : Simulation ops (lists Nat) rel) : ordinary ops ops.empty = some 2 := by
  exact (h.client_empty edits).trans rfl

example : ordinary (lists Nat) [] = some 2 := ordinary_correct _ _ (lists_correct Nat)
example : ordinary (symmetric Nat) nilSL = some 2 := ordinary_correct _ _ (symmetric_correct Nat)
example : run (lists Nat) edits [] = [2,3] := rfl
example : fromSL (run (symmetric Nat) edits nilSL) = [2,3] :=
  ((symmetric_correct Nat).run_preserves edits ⟨inv_nilSL, rfl⟩).2

/-- Empty input and repeated deletion remain total. -/
example : client (symmetric Nat) [] nilSL = none :=
  (symmetric_correct Nat).client_empty []
example : client (symmetric Nat) [.delete,.delete] nilSL = none :=
  (symmetric_correct Nat).client_empty _

example (xs ys : List (Command Nat)) (s : SymList Nat) (valid : Inv s) :
    client (symmetric Nat) (xs ++ ys) s =
      client (lists Nat) ys (run (lists Nat) xs (fromSL s)) := by
  exact ((symmetric_correct Nat).client_eq (xs ++ ys) ⟨valid,rfl⟩).trans
    (congrArg (lists Nat).head (run_append _ xs ys _))

example (xs ys : List (Command Nat)) :
    (symmetric_correct Nat).runSquare (xs ++ ys) =
      Relational.compose ((symmetric_correct Nat).runSquare ys)
        ((symmetric_correct Nat).runSquare xs) := Simulation.runSquare_append _ _ _

/-- Word substitution expands each enqueue into enqueue twice. -/
def twice : Command Nat → List (Command Nat)
  | .enqueue x => [.enqueue x,.enqueue x]
  | .delete => [.delete]
example : run (lists Nat) ([Command.enqueue 4,.delete].flatMap twice) [] = [4] := by
  rw [run_flatMap]
  rfl

/-- Valid states with the same sequence have different private front lengths. -/
def leftLayout : SymList Nat := ([1],[3,2])
def rightLayout : SymList Nat := ([1,2],[3])
theorem left_related : (representation Nat).Rel leftLayout [1,2,3] := by
  exact ⟨by simp [leftLayout, Sequences.Symmetric.Inv], rfl⟩
theorem right_related : (representation Nat).Rel rightLayout [1,2,3] := by
  exact ⟨by simp [rightLayout, Sequences.Symmetric.Inv], rfl⟩

example (cs : List (Command Nat)) :
    client (symmetric Nat) cs leftLayout = client (symmetric Nat) cs rightLayout :=
  (symmetric_correct Nat).representation_independent cs left_related right_related

/-- A client outside the public operations can distinguish hidden representations. -/
theorem hidden_front_length : leftLayout.1.length ≠ rightLayout.1.length := by decide
example : ¬ ∃ f : List Nat → Nat,
    ∀ q xs, (representation Nat).Rel q xs → q.1.length = f xs := by
  rintro ⟨f,h⟩
  exact hidden_front_length ((h _ _ left_related).trans (h _ _ right_related).symm)

/-- The reversed relation is genuinely nonfunctional: both valid layouts are related
outputs for the same list. Simulation does not choose a decoder in this direction. -/
example : (fun xs q => (representation Nat).Rel q xs) [1,2,3] leftLayout ∧
    (fun xs q => (representation Nat).Rel q xs) [1,2,3] rightLayout ∧ leftLayout ≠ rightLayout := by
  refine ⟨left_related,right_related,?_⟩
  intro e
  exact hidden_front_length (congrArg (fun q : SymList Nat => q.1.length) e)

example (cs : List (Command Nat)) :
    client (lists Nat) cs [1,2,3] = client (symmetric Nat) cs rightLayout :=
  (symmetric_correct Nat).reverse.client_eq cs right_related

/-- Composed simulation relates the two layouts through their shared list. -/
example (cs : List (Command Nat)) :
    client (symmetric Nat) cs leftLayout = client (symmetric Nat) cs rightLayout :=
  ((symmetric_correct Nat).comp (symmetric_correct Nat).reverse).client_eq cs
    ⟨[1,2,3],left_related,right_related⟩

/-- The optional syntax and the ordinary client coexist; endpoint observation
stays outside the compiler's single-base state-transformer fragment. -/
example : (symmetric Nat).head
    ((CategoricalCompiler.compile
      (STLCRelations.target _ (Syntax.primitives (symmetric Nat) _ (symmetric_correct Nat)))
      (Syntax.program edits)).impl ((),nilSL)) = some 2 :=
  (Syntax.observe_program _ _ (symmetric_correct Nat) edits ⟨inv_nilSL,rfl⟩).trans rfl
example : (lists Nat).head
    ((CategoricalCompiler.compile
      (STLCRelations.target _ (Syntax.primitives (lists Nat) Eq (lists_correct Nat)))
      (Syntax.program edits)).impl ((),[])) = some 2 :=
  (Syntax.observe_program _ _ (lists_correct Nat) edits rfl).trans rfl

example (xs ys : List (Command Nat)) :
    Syntax.program (xs ++ ys) = Syntax.plug ys (Syntax.program xs) :=
  Syntax.plug_append xs ys _

end Examples.AbstractFIFO
