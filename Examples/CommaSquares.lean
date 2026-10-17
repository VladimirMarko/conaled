import SquareKit.CommaExact
import SquareKit.CommaLawful
import SquareKit.CodeCategory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Examples.CommaSquares
open SquareKit

/-- Decode adds one; neither of the horizontal arrows is an identity. -/
def shifted : Squares.Rep := ⟨Nat, Nat, fun n => n + 1⟩
def increment : Squares.Square shifted shifted where
  impl := fun (n : Nat) => n + 1
  spec := fun (n : Nat) => n + 1
  commutes _ := rfl

def double : Squares.Square shifted shifted where
  impl := fun (n : Nat) => 2 * n + 1
  spec := fun (n : Nat) => 2 * n
  commutes n := by dsimp [shifted]; omega

theorem ordered_composition :
    (Comma.Exact.toSquare (Comma.Exact.categoryOps.comp
      (Comma.Exact.ofSquare double) (Comma.Exact.ofSquare increment))).impl (3 : Nat) = (9 : Nat) := by
  rw [Comma.Exact.toSquare_compose, Comma.Exact.toSquare_ofSquare,
    Comma.Exact.toSquare_ofSquare]
  rfl

theorem semantic_composition :
    (Comma.Exact.categoryOps.comp (Comma.Exact.ofSquare double)
      (Comma.Exact.ofSquare increment)).right (4 : Nat) = (10 : Nat) := rfl

theorem increment_nonidentity :
    Comma.Exact.ofSquare increment ≠ Comma.Exact.categoryOps.ident := by
  intro h
  have bad := congrArg (fun f : Comma.Exact.Arrow (Comma.Exact.ofRep shifted)
    (Comma.Exact.ofRep shifted) => f.left (0 : Nat)) h
  cases bad

section Code
open CategoricalCompiler
variable {Prim : Ty → Ty → Type} {B : Type}
variable (meaning : {a b : Ty} → Prim a b → Val B a → Val B b)

/-- Distinct source families: raw typed syntax on the left, types and functions
on the right. The connector does not quotient or erase the syntax. -/
def codeObject (a : Ty) : Comma.Obj (CodeCategory.evaluation meaning)
    (RawMap.id FunctionCategory.ops) := ⟨a, Val B a, id⟩

def codeSquare {a b : Ty} (f : Code Prim a b) : Comma.Hom (equality FunctionCategory.ops)
    (codeObject meaning a) (codeObject meaning b) := ⟨f, run meaning f, rfl⟩

abbrev codeOps := Comma.ops (equalityCongr FunctionCategory.ops) FunctionCategory.laws
  (CodeCategory.evaluationLaws meaning) (RawMap.id_laws (equality FunctionCategory.ops))

/-- Every pair of raw programs composes through the comma public operations. -/
theorem code_composition {a b c : Ty} (g : Code Prim b c) (f : Code Prim a b) :
    (codeOps meaning).comp (codeSquare meaning g) (codeSquare meaning f) =
      codeSquare meaning (.comp g f) := rfl

theorem code_identity (a : Ty) :
    (codeOps meaning).ident (a := codeObject meaning a) = codeSquare meaning .ident := rfl

theorem code_association {a b c d : Ty}
    (h : Code Prim c d) (g : Code Prim b c) (f : Code Prim a b) :
    (Comma.equiv (equalityCongr FunctionCategory.ops) FunctionCategory.laws
      (CodeCategory.evaluationLaws meaning) (RawMap.id_laws (equality FunctionCategory.ops))).Rel
      ((codeOps meaning).comp ((codeOps meaning).comp (codeSquare meaning h)
        (codeSquare meaning g)) (codeSquare meaning f))
      ((codeOps meaning).comp (codeSquare meaning h)
        ((codeOps meaning).comp (codeSquare meaning g) (codeSquare meaning f))) :=
  (Comma.laws _ _ _ _ (CodeCategory.laws meaning) FunctionCategory.laws).assoc _ _ _

/-- Semantic associativity does not identify the stored raw syntax. -/
theorem code_association_raw_ne :
    codeSquare meaning (Code.comp (Code.comp .ident .ident) .ident : Code Prim .base .base) ≠
      codeSquare meaning (Code.comp .ident (Code.comp .ident .ident)) := by
  intro h
  exact CodeCategory.association_not_equal (Prim := Prim) (congrArg Comma.Hom.left h)

def codeQuotientMap := Comma.quotientMap
  (CodeCategory.congruence meaning) (CodeCategory.laws meaning)
  (equalityCongr FunctionCategory.ops) FunctionCategory.laws
  (equalityCongr FunctionCategory.ops) FunctionCategory.laws
  (CodeCategory.evaluationLaws meaning) (RawMap.id_laws (equality FunctionCategory.ops))

/-- The same unequal representatives become equal in Mathlib's comma of the
lawful quotients; the result is obtained from the shared square laws. -/
theorem code_quotient_association {a b c d : Ty}
    (h : Code Prim c d) (g : Code Prim b c) (f : Code Prim a b) :
    (codeQuotientMap meaning).map (codeSquare meaning (.comp (.comp h g) f)) =
      (codeQuotientMap meaning).map (codeSquare meaning (.comp h (.comp g f))) :=
  (Comma.quotientMap_laws (CodeCategory.congruence meaning) (CodeCategory.laws meaning)
    (equalityCongr FunctionCategory.ops) FunctionCategory.laws
    (equalityCongr FunctionCategory.ops) FunctionCategory.laws
    (CodeCategory.evaluationLaws meaning) (RawMap.id_laws (equality FunctionCategory.ops))).congr
      (code_association meaning h g f)

/-- Projection followed by evaluation reuses shared map composition proofs. -/
theorem semantic_projection_laws : MapLaws
    ((Comma.fst (equalityCongr FunctionCategory.ops) FunctionCategory.laws
      (CodeCategory.evaluationLaws meaning) (RawMap.id_laws (equality FunctionCategory.ops))).comp
      (CodeCategory.evaluation meaning))
    (Comma.equiv (equalityCongr FunctionCategory.ops) FunctionCategory.laws
      (CodeCategory.evaluationLaws meaning) (RawMap.id_laws (equality FunctionCategory.ops)))
    (equality FunctionCategory.ops) :=
  RawMap.comp_laws (Comma.fst_laws _ _ _ _) (CodeCategory.evaluationLaws meaning)
end Code
end Examples.CommaSquares
