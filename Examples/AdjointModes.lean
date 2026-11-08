import SquareKit.AdjointModes.Evaluation
import SquareKit.AdjointModes.Category

/-! A selected unrestricted offset is transferred into a linear update. The
source `addDouble` primitive is expanded in two compiler passes, first into a U
doubling operation plus a linear update, then into U copying and addition. -/
namespace Examples.AdjointModes
open SquareKit.AdjointModes
set_option backward.isDefEq.respectTransparency false

abbrev U : Ty .unrestricted := .atom .unrestricted
abbrev L : Ty .linear := .atom .linear
abbrev Input : Ty .linear := .times (.down U) L

inductive Source : Signature
  | addDouble : Source Input L
  | finish : Source L L
inductive Middle : Signature
  | double : Middle U U
  | add : Middle Input L
  | finish : Middle L L
inductive Target : Signature
  | addU : Target (.times U U) U
  | addL : Target Input L
  | successor : Target L L

def sourceMeaning : PayloadMeaning tokenAtoms Source
  | _, _, _, .addDouble => fun ((n,x) : Nat × Nat) => (n+n)+x
  | _, _, _, .finish => fun (x : Nat) => x+1

def middleMeaning : PayloadMeaning tokenAtoms Middle
  | _, _, _, .double => fun (n : Nat) => n+n
  | _, _, _, .add => fun ((n,x) : Nat × Nat) => n+x
  | _, _, _, .finish => fun (x : Nat) => x+1

def targetMeaning : PayloadMeaning tokenAtoms Target
  | _, _, _, .addU => fun ((x,y) : Nat × Nat) => x+y
  | _, _, _, .addL => fun ((n,x) : Nat × Nat) => n+x
  | _, _, _, .successor => fun (x : Nat) => x+1

def firstPass : Translation Source Middle
  | _, _, _, .addDouble => .comp (.prim .add) (.times (.downMap (.prim .double)) .id)
  | _, _, _, .finish => .prim .finish

def secondPass : Translation Middle Target
  | _, _, _, .double => .comp (.prim .addU) .copy
  | _, _, _, .add => .prim .addL
  | _, _, _, .finish => .prim .successor

theorem first_local {m} {A B : Ty m} (a : Source A B) x :
    (firstPass a).denote tokenAtoms middleMeaning x = sourceMeaning a x := by cases a <;> rfl

theorem second_local {m} {A B : Ty m} (a : Middle A B) x :
    (secondPass a).denote tokenAtoms targetMeaning x = middleMeaning a x := by cases a <;> rfl

def targetResources : PrimitiveMeaning tokenAtoms Target
  | _, _, _, .addU => ⟨fun ((x,y) : Nat × Nat) => x+y, fun _ => rfl⟩
  | _, _, _, .addL => ⟨fun ((n,x) : Nat × Nat) => n+x, fun _ => rfl⟩
  | _, _, _, .successor => ⟨fun (x : Nat) => x+1, fun _ => rfl⟩

theorem target_local {m} {A B : Ty m} (a : Target A B) x :
    B.forget tokenAtoms ((targetResources a).run x) = targetMeaning a (A.forget tokenAtoms x) := by
  cases a <;> rfl

def client : Term Source Input L := .comp (.prim .finish) (.prim .addDouble)

def compiledClient : Term Target Input L := client.translate (secondPass.comp firstPass)

/-- Whole-program preservation is derived from the local primitive certificates,
including both nontrivial expansion passes and final resource interpretation. -/
theorem pipeline_preserves {m} {A B : Ty m} (t : Term Source A B) (x) :
    B.forget tokenAtoms (((t.translate (secondPass.comp firstPass)).compile tokenAtoms targetResources).run x)
      = t.denote tokenAtoms sourceMeaning (A.forget tokenAtoms x) := by
  rw [Term.compile_preserves tokenAtoms targetResources targetMeaning target_local]
  rw [Term.translate_comp, Term.translate_preserves tokenAtoms middleMeaning targetMeaning secondPass second_local,
    Term.translate_preserves tokenAtoms sourceMeaning middleMeaning firstPass first_local]

theorem selected_result : (compiledClient.compile tokenAtoms targetResources).run ((3 : Nat),(5 : Nat)) = (12 : Nat) := by
  have h := pipeline_preserves client ((3 : Nat),(5 : Nat))
  exact h

theorem selected_resources :
    (L.meaning tokenAtoms).degree ((compiledClient.compile tokenAtoms targetResources).run ((3 : Nat),(5 : Nat))) = 1 :=
  compiledClient.resource_sound tokenAtoms targetResources _

/-- The compiled syntax performs the linear update once and then its successor;
copying occurs solely within the unrestricted argument. -/
theorem expanded_client : compiledClient =
    Term.comp (.prim .successor)
      (.comp (.prim .addL) (.times (.downMap (.comp (.prim .addU) .copy)) .id)) := rfl

example : Nonempty (Term EmptySignature U (.times U U)) := ⟨.copy⟩
example : Nonempty (Term EmptySignature U (.one .unrestricted)) := ⟨.discard⟩
example : ¬Nonempty (Term EmptySignature L (.times L L)) := no_generic_linear_copy
example : ¬Nonempty (Term EmptySignature L (.one .linear)) := no_generic_linear_discard
example : ¬Above .linear .unrestricted := no_linear_dependency
example : ¬PolicyValid (fun _ _ => True) permits := reverse_order_invalid

/-- Both shifts are exercised, with selected U data retained through unit and counit. -/
def shiftedRoundTrip : Term EmptySignature (.down U) (.down U) :=
  .comp .counit (.downMap .unit)

example : (shiftedRoundTrip.compile tokenAtoms (emptyMeaning tokenAtoms)).run (7 : Nat) = (7 : Nat) := rfl
example : client.translate (Translation.identity Source) = client := client.translate_identity
example : client.translate (secondPass.comp firstPass) =
    (client.translate firstPass).translate secondPass := client.translate_comp firstPass secondPass

/-- A legal specialized linear type can still admit duplication and discard. -/
example : Nonempty (Map (down Nat) (tensor (down Nat) (down Nat))) := ⟨copyDown Nat⟩
example : Nonempty (Map (down Nat) one) := ⟨discardDown Nat⟩

/-- The scoped big-step semantics recovers the selected compiled result. -/
theorem selected_evaluation : Eval tokenAtoms targetMeaning compiledClient ((3 : Nat),(5 : Nat)) (12 : Nat) := by
  have h := compiledClient.compile_evaluates tokenAtoms targetResources targetMeaning target_local ((3 : Nat),(5 : Nat))
  rw [selected_result] at h
  exact h

/-- The direct resource-contract baseline for the same client. -/
def directClient : Map (Input.meaning tokenAtoms) (L.meaning tokenAtoms) :=
  ⟨fun ((n,x) : Nat × Nat) => (n+n)+x+1, fun _ => rfl⟩

theorem compiler_agrees_direct : compiledClient.compile tokenAtoms targetResources = directClient := by
  apply Map.ext
  intro x
  exact pipeline_preserves client x

end Examples.AdjointModes
