import SquareKit.CategoryQuotient
import SquareKit.CartesianMapQuotient
import SquareKit.AssemblyLiftMonad
import Examples.ExceptionalInternalHom
import Examples.GroupoidTransport
import Mathlib.CategoryTheory.Monad.EquivMon
import Mathlib.CategoryTheory.Grothendieck

/-! Checked changes of ordinary categorical presentation. These conversions
retain morphisms and their laws, but do not recover erased raw data. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Examples.CategoryCharacterizations
open CategoryTheory CategoryTheory.Limits SquareKit

namespace Quotients

abbrev C := SingleObj (Nat × Nat)
def forgetSecond : C ⥤ SingleObj Nat := SingleObj.mapHom _ _ (MonoidHom.fst Nat Nat)
abbrev relation := forgetSecond.homRel
local instance : Category (HomQuotient (ofCategory C) (LawfulQuotient.equiv relation)) :=
  HomQuotient.category (LawfulQuotient.congruence relation) (LawfulQuotient.laws relation)

abbrev point : C := SingleObj.star _
def arrow (a b : Nat) : point ⟶ point := (a, b)
def cls (a b : Nat) := HomQuotient.classOf (E := LawfulQuotient.equiv relation) (arrow a b)

/-- The second coordinate is erased, while the first coordinate remains observable. -/
theorem erased : cls 2 3 = cls 2 7 := (HomQuotient.mk_eq_iff _ _).mpr rfl
theorem retained : cls 2 3 ≠ cls 5 3 := by
  intro h
  have : (2 : Nat) = 5 := (HomQuotient.mk_eq_iff _ _).mp h
  contradiction

theorem raw_distinct : arrow 2 3 ≠ arrow 2 7 := by
  change (2, 3) ≠ (2, 7)
  decide

theorem recovered (a b : Nat) :
    (LawfulQuotient.equivalence relation).inverse.map
      ((LawfulQuotient.equivalence relation).functor.map (cls a b)) = cls a b :=
  (LawfulQuotient.homEquiv relation _ _).symm_apply_apply _

/-- The equivalence transports a composite of nonidentity classes. -/
theorem mapped_composite :
    (LawfulQuotient.equivalence relation).functor.map (cls 2 3) ≫
      (LawfulQuotient.equivalence relation).functor.map (cls 5 7) =
      (LawfulQuotient.equivalence relation).functor.map (cls 10 21) := by
  rw [← Functor.map_comp]
  rfl

theorem mapped_erased :
    (LawfulQuotient.equivalence relation).functor.map (cls 2 3) =
      (LawfulQuotient.equivalence relation).functor.map (cls 2 7) :=
  congrArg _ erased
end Quotients

namespace Adjunctions
open ExceptionalHomFamilies Examples.ExceptionalInternalHom

def successor : Nat ⟶ Nat := ↾Nat.succ

/-- The unit reconstructed from the hom bijection inserts the selected index. -/
theorem unit_selected : (exceptional.unit.app coefficient true) true =
    (⟨true, true⟩ : Sigma coefficient) := rfl

theorem counit_selected : exceptional.counit.app Nat ⟨false, (31 : Nat)⟩ = (31 : Nat) := rfl

/-- This uses the recovered adjunction's naturality, not a separate evaluation. -/
theorem postcompose :
    exceptional.homEquiv coefficient Nat (observe ≫ successor) =
      exceptional.homEquiv coefficient Nat observe ≫ pull.map successor :=
  exceptional.homEquiv_naturality_right observe successor

theorem postcompose_value :
    (exceptional.homEquiv coefficient Nat (observe ≫ successor) true) true = (32 : Nat) := by
  rw [postcompose]
  rfl

theorem recover_observation :
    (exceptional.homEquiv coefficient Nat).symm
      (exceptional.homEquiv coefficient Nat observe) = observe :=
  (exceptional.homEquiv coefficient Nat).symm_apply_apply _
end Adjunctions

namespace Representability

/-- Bundled function arrows expose the same ordinary product operations. -/
def products : ProductOps (ofCategory (Type)) where
  prod := Prod
  fst := ↾Prod.fst
  snd := ↾Prod.snd
  pair f g := ↾fun x => ((show _ ⟶ _ from f) x, (show _ ⟶ _ from g) x)

theorem product_laws : ProductLaws (equality _) products where
  fst_pair _ _ := rfl
  snd_pair _ _ := rfl
  pair_eta _ := rfl

def productLimit := binaryFanIsLimit products product_laws Nat Nat
def input : BinaryFan Nat Nat := BinaryFan.mk (↾Nat.succ) (↾fun n : Nat => n * 2)
def recoveredLimit := IsLimit.ofRepresentableBy productLimit.representableBy

theorem lift_recovered : recoveredLimit.lift input = productLimit.lift input := rfl

theorem selected_pair : recoveredLimit.lift input (3 : Nat) = (4, 6) := by
  rw [lift_recovered]
  rfl

/-- Naturality of the representing hom equivalence retains precomposition. -/
theorem reindex :
    productLimit.representableBy.homEquiv.symm
      ((Functor.const _).map (↾Nat.succ) ≫ input.π) =
      (↾Nat.succ) ≫ productLimit.representableBy.homEquiv.symm input.π :=
  productLimit.homEquiv_symm_naturality input.π (↾Nat.succ)

theorem reindex_value :
    (productLimit.representableBy.homEquiv.symm
      ((Functor.const _).map (↾Nat.succ) ≫ input.π)) 3 = (5, 8) := by
  rw [reindex]
  rfl
end Representability

namespace Monads
open Realizability Realizability.Assembly
attribute [local instance] endofunctorMonoidalCategory

abbrev recovered := (Monad.monadMonEquiv Assembly).inverse.obj
  ((Monad.monadMonEquiv Assembly).functor.obj programLiftMonad)

theorem multiplication_recovered : recovered.μ = programLiftMonad.μ := rfl

theorem flatten_some : (recovered.μ.app (encoded Nat)).toFun (some (some (17 : Nat))) = some (17 : Nat) := rfl
theorem flatten_none : (recovered.μ.app (encoded Nat)).toFun (some none) = none := rfl

def successor := ofComputable Nat.succ Computable.succ

theorem mapped_successor : (recovered.map successor).toFun (some (17 : Nat)) = some (18 : Nat) := rfl

theorem multiplication_natural :
    recovered.map (recovered.map successor) ≫ recovered.μ.app (encoded Nat) =
      recovered.μ.app (encoded Nat) ≫ recovered.map successor :=
  Monad.mu_naturality Assembly recovered successor

/-- A nonidentity monad morphism inserts a defined computation. -/
def unitMorphism : Monad.id Assembly ⟶ programLiftMonad where
  app := programLiftUnit
  naturality := fun _ _ f => (programLiftUnit_natural f).symm
  app_η _ := rfl
  app_μ X := by
    apply Realizability.Assembly.Hom.ext
    intro x
    rfl

theorem monoid_morphism_value :
    (((Monad.monadMonEquiv Assembly).functor.map unitMorphism).hom.app
      (encoded Nat)).toFun (17 : Nat) = some (17 : Nat) := rfl

/-- Morphism recovery and composition use the categorical equivalence itself. -/
theorem morphism_recovered {A B : Monad Assembly} (f : A ⟶ B) :
    ((Monad.monadMonEquiv Assembly).inverse.map
      ((Monad.monadMonEquiv Assembly).functor.map f)).toNatTrans = f.toNatTrans := rfl

theorem map_comp {A B C : Monad Assembly} (f : A ⟶ B) (g : B ⟶ C) :
    (Monad.monadMonEquiv Assembly).functor.map (f ≫ g) =
      (Monad.monadMonEquiv Assembly).functor.map f ≫
        (Monad.monadMonEquiv Assembly).functor.map g := Functor.map_comp _ _ _
end Monads

namespace Elements
open GroupoidTransport

def moving (n : ZMod 4) : faithful.Elements := Functor.elementsMk faithful point n
def step (n : ZMod 4) : moving n ⟶ moving (1 + n) :=
  Functor.Elements.homMk (label 1) rfl

abbrev comparison := Grothendieck.grothendieckTypeToCat faithful

theorem step_base (n : ZMod 4) : (comparison.inverse.map (step n)).base = label 1 := rfl

theorem composite_base :
    (comparison.inverse.map (step 0 ≫ step (1 + 0))).base = label 1 ≫ label 1 := rfl

theorem arrow_recovered (n : ZMod 4) :
    comparison.functor.map (comparison.inverse.map (step n)) = step n := rfl

/-- An ineffective action retains nonidentity stabilizer arrows in both presentations. -/
def fixed : ineffective.Elements := Functor.elementsMk ineffective point (0 : Fin 2)
def stabilizer : fixed ⟶ fixed := Functor.Elements.homMk (label 1) rfl

theorem stabilizer_not_identity :
    (Grothendieck.grothendieckTypeToCat ineffective).inverse.map stabilizer ≠
      𝟙 ((Grothendieck.grothendieckTypeToCat ineffective).inverse.obj fixed) := by
  intro h
  have h' : (1 : ZMod 4) = 0 := congrArg (fun f => Multiplicative.toAdd f.base) h
  exact (by decide : (1 : ZMod 4) ≠ 0) h'
end Elements
end Examples.CategoryCharacterizations
