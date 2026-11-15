import Examples.CubicalGlue
import SquareKit.Internal.Cubical.UnivalenceTransport

/-! Discrete observations of transport along the constructed ua line. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalUnivalenceTransport
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalGlue

variable {S T : Type}

def constantSection (s : S) : Term (constantFamily terminal.{0} S) where
  val _ := s
  property _ := rfl

def codeIso (e : S ≃ T) :
    decode (constantLocal terminal S).code ≅ decode (constantLocal terminal T).code :=
  (constantLocal terminal S).decodeCodeIso ≪≫ constantIso e ≪≫
    (constantLocal terminal T).decodeCodeIso.symm

def input (s : S) : Term (decode (constantLocal terminal S).code) :=
  Term.map (constantLocal terminal S).decodeCodeIso.inv (constantSection s)

noncomputable def codeTransport (e : S ≃ T) :
    decode (constantLocal terminal S).code ⟶ decode (constantLocal terminal T).code :=
  Univalence.transport _ _ (codeIso e).hom (HomotopyEquivalence.ofIso (codeIso e))

noncomputable def observed (e : S ≃ T) (s : S) : Term (constantFamily terminal T) :=
  Term.map (constantLocal terminal T).decodeCodeIso.hom
    (Term.map (codeTransport e) (input s))

private theorem map_iso_action {Γ : Context.{0}} {A B C D : Family Γ}
    (i : A ≅ B) (j : C ≅ D) (k : B ≅ D) (x : Term B) :
    Term.map j.hom (Term.map (i ≪≫ k ≪≫ j.symm).hom (Term.map i.inv x)) = Term.map k.hom x :=
  (Term.map_iso_roundtrip j.symm (Term.map k.hom (Term.map i.hom (Term.map i.inv x)))).trans
    (congrArg (Term.map k.hom) (Term.map_iso_roundtrip i.symm x))

theorem codeIso_action (e : S ≃ T) (s : S) :
    Term.map (constantLocal terminal T).decodeCodeIso.hom
      (Term.map (codeIso e).hom (input s)) = constantSection (e s) :=
  map_iso_action (constantLocal terminal S).decodeCodeIso
    (constantLocal terminal T).decodeCodeIso (constantIso e) (constantSection s)

/-- This observes the actual ua transport, rather than reusing the supplied
bijection as the implementation of transport. -/
theorem observed_eq (e : S ≃ T) (s : S) : observed e s = constantSection (e s) :=
  (discretePath_endpoints (homogeneousPathMap (constantLocal terminal T).decodeCodeIso.hom
    (Univalence.comparison _ _ (codeIso e).hom (HomotopyEquivalence.ofIso (codeIso e))
      (input s)))).symm.trans (codeIso_action e s)

noncomputable def value (e : S ≃ T) (s : S) : T :=
  (observed e s).val (terminal.elementsMk (Opposite.op ⟨0⟩) PUnit.unit)

theorem value_eq (e : S ≃ T) (s : S) : value e s = e s :=
  congrArg (fun t => t.val (terminal.elementsMk (Opposite.op ⟨0⟩) PUnit.unit)) (observed_eq e s)

noncomputable def booleanUniverseLoop :=
  Univalence.ua _ _ (codeIso booleanTransposition).hom
    (HomotopyEquivalence.ofIso (codeIso booleanTransposition))

theorem boolean_true_to_false : value booleanTransposition true = false :=
  value_eq booleanTransposition true

theorem boolean_false_to_true : value booleanTransposition false = true :=
  value_eq booleanTransposition false

theorem successor_three_to_four : value CubicalStateTransport.successor 3 = 4 :=
  value_eq CubicalStateTransport.successor 3

theorem inverse_three_to_two : value CubicalStateTransport.successor.symm 3 = 2 :=
  value_eq CubicalStateTransport.successor.symm 3

end Examples.CubicalUnivalenceTransport
