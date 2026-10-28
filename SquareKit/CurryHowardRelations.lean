import SquareKit.CurryHoward
import SquareKit.STLCRelations

/-! A closed singleton-atom proof/program acts on related endofunction arguments. -/
namespace SquareKit.CurryHoward
open CategoricalCompiler

abbrev Endo : Formula := .implies .atom .atom

def twiceProof : Proof [] (.implies Endo Endo) :=
  Proof.impliesIntro (Proof.impliesIntro
    ((Proof.hyp (Γ := [.atom, Endo]) (a := Endo) (.there .here)).impliesElim
      ((Proof.hyp (Γ := [.atom, Endo]) (a := Endo) (.there .here)).impliesElim (Proof.hyp (Γ := [.atom, Endo]) (a := .atom) .here))))

def twice (f : X → X) (x : X) : X := f (f x)

def relationalPrimitives (R S : Type) (E : R → S → Prop) :
    STLCRelations.Primitives ⟨R,S,E⟩ NoPrim (meaning (B := S)) where
  impl p := nomatch p
  correct p := nomatch p

def compiledTwice {R S : Type} (E : R → S → Prop) (f : R → R) : R → R :=
  (compile (STLCRelations.target _ (relationalPrimitives R S E))
    (typedCompilation twiceProof)).impl () f

@[simp] theorem compiledTwice_eq {R S : Type} (E : R → S → Prop) (f : R → R) :
    compiledTwice E f = twice f := rfl

@[simp] theorem twice_meaning (f : S → S) :
    eval (meaning (B := S)) (typedCompilation twiceProof) () f = twice f := rfl

/-- Preservation follows from the shared compiler theorem at the full arrow type. -/
theorem twice_related {R S : Type} (E : R → S → Prop) (fR : R → R) (fS : S → S)
    (hf : ∀ x y, E x y → E (fR x) (fS y)) {x y} (hxy : E x y) :
    E (compiledTwice E fR x) (twice fS y) := by
  have h : (STLCRelations.encoding ⟨R,S,E⟩ (.arr (.arr .base .base) (.arr .base .base))).Rel
      ((compile (STLCRelations.target _ (relationalPrimitives R S E))
        (typedCompilation twiceProof)).impl ())
      (eval (meaning (B := S)) (typedCompilation twiceProof) ()) :=
    STLCRelations.compile_preserves ⟨R,S,E⟩ (relationalPrimitives R S E)
      (typedCompilation twiceProof) (r := ()) (s := ()) trivial
  exact h (r := fR) (s := fS) (fun {x y} => hf x y) hxy

end SquareKit.CurryHoward
