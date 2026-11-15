import SquareKit.AssemblyFunction
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-! The concrete product and function assemblies supply Mathlib's closed interface. -/
universe u
namespace Realizability.Assembly
open CategoryTheory Limits

/-- A terminal assembly in every carrier universe. -/
def terminal : Assembly.{u} where
  Carrier := PUnit
  realizes _ _ := True
  inhabited _ := ⟨0, trivial⟩

def terminalArrow (A : Assembly.{u}) : Hom A terminal where
  toFun _ := PUnit.unit
  tracked := ⟨fun _ => Part.some 0, Nat.Partrec.of_primrec (Nat.Primrec.const 0),
    fun _ _ _ => ⟨0, by simp, trivial⟩⟩

def terminalIsTerminal : IsTerminal terminal.{u} :=
  IsTerminal.ofUniqueHom terminalArrow (fun _ _ => Hom.ext fun _ => rfl)

def productIsLimit (A B : Assembly.{u}) : IsLimit (BinaryFan.mk (C := Assembly.{u}) (fst A B) (snd A B)) :=
  BinaryFan.IsLimit.mk _ (fun f g => pair f g) (fun _ _ => pair_fst _ _)
    (fun _ _ => pair_snd _ _) (fun f g h hf hg => by
      apply Hom.ext
      intro x
      exact Prod.ext (congrArg (fun k => k.toFun x) hf) (congrArg (fun k => k.toFun x) hg))

instance cartesianMonoidal : CartesianMonoidalCategory Assembly.{u} :=
  CartesianMonoidalCategory.ofChosenFiniteProducts
    ⟨asEmptyCone terminal, terminalIsTerminal⟩
    (fun A B => ⟨BinaryFan.mk (C := Assembly.{u}) (fst A B) (snd A B), productIsLimit A B⟩)

def swap (A B : Assembly.{u}) : Hom (prod A B) (prod B A) := pair (snd _ _) (fst _ _)

noncomputable def functionPostcompose {B C : Assembly.{u}} (f : Hom B C) (A : Assembly.{u}) :
    Hom (function A B) (function A C) := curry ((evaluation A B).comp f)

@[simp] theorem functionPostcompose_apply {A B C : Assembly.{u}} (f : Hom B C)
    (h : Hom A B) (a : A.Carrier) :
    ((functionPostcompose f A).toFun h).toFun a = f.toFun (h.toFun a) := curry_apply _ _ _

noncomputable def functionFunctor (A : Assembly.{u}) : Assembly.{u} ⥤ Assembly.{u} where
  obj := function A
  map f := functionPostcompose f A
  map_id _ := Hom.ext fun f => Hom.ext fun a => curry_apply _ _ _
  map_comp f g := by
    apply Hom.ext
    intro h
    apply Hom.ext
    intro a
    exact (functionPostcompose_apply (f.comp g) h a).trans
      ((congrArg g.toFun (functionPostcompose_apply f h a)).symm.trans
        (functionPostcompose_apply g ((functionPostcompose f A).toFun h) a).symm)

noncomputable def functionAdjunction (A : Assembly.{u}) :
    MonoidalCategory.tensorLeft A ⊣ functionFunctor A :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun Γ B => {
      toFun := fun h => curry ((swap Γ A).comp h)
      invFun := fun h => (swap A Γ).comp (uncurry h)
      left_inv := fun h => Hom.ext fun ⟨a,γ⟩ => curry_apply _ _ _
      right_inv := fun h => Hom.ext fun γ => Hom.ext fun a => curry_apply _ _ _ }
    homEquiv_naturality_left_symm := by
      intros
      apply Hom.ext
      rintro ⟨a,γ⟩
      rfl
    homEquiv_naturality_right := by
      intro Γ B C f g
      apply Hom.ext
      intro γ
      apply Hom.ext
      intro a
      exact (curry_apply _ _ _).trans
        ((congrArg g.toFun (curry_apply ((swap Γ A).comp f) γ a)).symm.trans
          (functionPostcompose_apply g _ a).symm) }

noncomputable instance monoidalClosed : MonoidalClosed Assembly.{u} where
  closed A := ⟨functionFunctor A, functionAdjunction A⟩

end Realizability.Assembly
