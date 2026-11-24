module
public import Applications.ModelCombination.SignatureTransport

/-! A changed-arity extension of the frozen operation comparison. -/
@[expose] public section
set_option autoImplicit false
namespace NativeModelCombination
universe u v w
namespace OperationTransport
variable {X : Type u} {Y : Type v}

def unary (e : X ≃ Y) (op : Y → Y) (x : X) : X :=
  operation e (fun a : Unit → Y => op (a ())) (fun _ => x)

@[simp] theorem unary_def (e : X ≃ Y) (op : Y → Y) (x : X) :
    unary e op x = e.symm (op (e x)) := rfl

theorem recover_unary (e : X ≃ Y) (op : Y → Y) (y : Y) :
    e (unary e op (e.symm y)) = op y :=
  recover_operation e (fun a : Unit → Y => op (a ())) (fun _ => y)

theorem involutive (e : X ≃ Y) (op : Y → Y) (h : ∀ y, op (op y) = y) (x : X) :
    unary e op (unary e op x) = x := by simp [h]
end OperationTransport

namespace SignatureTransport
open FirstOrder FirstOrder.Language
variable {X : Type u} {Y : Type v}
inductive UnarySymbol : Nat → Type
  | reverse : UnarySymbol 1

def unaryLanguage : Language := ⟨UnarySymbol, fun _ => Empty⟩
def extendedLanguage : Language := language.sum unaryLanguage

@[instance_reducible] def extendedStructure (op : Y → Y → Y) (unit : Y) (rev : Y → Y) :
    extendedLanguage.Structure Y where
  funMap := fun {_n} f xs => match f with
    | .inl f => @Structure.funMap language Y (suppliedStructure op unit) _ f xs
    | .inr .reverse => rev (xs 0)
  RelMap := fun r => nomatch r

def reverseTerm {V : Type w} (t : extendedLanguage.Term V) : extendedLanguage.Term V :=
  .func (.inr UnarySymbol.reverse) (fun _ => t)

/-- The old binary operation has exactly the same interpretation in the disjoint extension. -/
theorem extended_binary (e : X ≃ Y) (op : Y → Y → Y) (unit : Y) (rev : Y → Y) (x y : X) :
    letI : extendedLanguage.Structure Y := extendedStructure op unit rev
    letI : extendedLanguage.Structure X := e.symm.inducedStructure
    Structure.funMap (L := extendedLanguage) (.inl Symbol.join) (fun i => if i = 0 then x else y) =
      OperationTransport.binary e op x y := rfl

theorem unary_recovery (e : X ≃ Y) (op : Y → Y → Y) (unit : Y) (rev : Y → Y) (x : X) :
    letI : extendedLanguage.Structure Y := extendedStructure op unit rev
    letI : extendedLanguage.Structure X := e.symm.inducedStructure
    Structure.funMap (L := extendedLanguage) (.inr UnarySymbol.reverse) (fun _ => x) =
      OperationTransport.unary e rev x := rfl

/-- The same open-equation theorem handles the new arity and its side law. -/
theorem involutive (e : X ≃ Y) (op : Y → Y → Y) (unit : Y) (rev : Y → Y)
    (h : ∀ y, rev (rev y) = y) (x : X) :
    OperationTransport.unary e rev (OperationTransport.unary e rev x) = x := by
  let instY : extendedLanguage.Structure Y := extendedStructure op unit rev
  let t : extendedLanguage.Term Unit := .var ()
  have hy : ∀ ys : Unit → Y, (reverseTerm (reverseTerm t)).realize ys = t.realize ys := by
    intro ys
    simpa [reverseTerm, t, Term.realize, Structure.funMap, instY, extendedStructure] using h (ys ())
  have hx := equation_transport e _ _ hy (fun _ => x)
  simpa [reverseTerm, t, Term.realize, Structure.funMap, instY, extendedStructure,
    Equiv.inducedStructure, OperationTransport.unary_def, Function.comp_def] using hx
end SignatureTransport
end NativeModelCombination
