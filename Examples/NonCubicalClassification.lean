import SquareKit.Internal.PresheafFamilyClassification
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Data.Fintype.Card

/-! Dependent finite families over the one-object category of natural-number
multiplication. Restriction multiplies fiber values; context substitutions
change the finite fiber size. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.NonCubicalClassification
open CategoryTheory SquareKit.RepresentableClassification
abbrev Base := SingleObj ℕ
abbrev context : Context.{0} Base where
  obj _ := ℕ
  map _ := 𝟙 ℕ

def family : Family context where
  obj x := let n : ℕ := x.val; Fin (n + 1)
  map f := TypeCat.ofHom (fun z =>
    let k : ℕ := f.hom.unop
    cast (congrArg (fun n => Fin (n + 1)) f.map_val) (k • z))
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro z
    change (1 : ℕ) • z = z
    exact one_nsmul z
  map_comp := by
    intro x y z f g
    rcases x with @⟨I, n⟩
    rcases y with @⟨J, m⟩
    rcases z with @⟨K, k⟩
    have h : n = m := f.map_val
    have h' : m = k := g.map_val
    subst m
    subst k
    apply ConcreteCategory.hom_ext
    intro a
    let kf : ℕ := f.hom.unop
    let kg : ℕ := g.hom.unop
    change (kf * kg) • a = kg • (kf • a)
    rw [mul_nsmul]

def successor : context ⟶ context where
  app _ := TypeCat.ofHom Nat.succ

def double : context ⟶ context where
  app _ := TypeCat.ofHom (fun (n : ℕ) => 2 * n)

abbrev point (n : ℕ) : context.Elements := context.elementsMk (Opposite.op (SingleObj.star ℕ)) n

def restriction (n k : ℕ) : point n ⟶ point n :=
  Functor.Elements.homMk (Quiver.Hom.op k) rfl

example : family.map (restriction 2 2) (1 : Fin 3) = (2 : Fin 3) := rfl
example : family.map (restriction 2 2) (1 : Fin 3) ≠ (1 : Fin 3) := by
  change (2 : Fin 3) ≠ 1
  decide
example : restriction 2 2 ≠ 𝟙 (point 2) := by
  intro h
  have := congrArg (fun f => f.hom.unop) h
  change (2 : ℕ) = 1 at this
  contradiction

theorem different_fibers : ¬ Nonempty (family.obj (point 0) ≃ family.obj (point 1)) := by
  rintro ⟨e⟩
  change Fin 1 ≃ Fin 2 at e
  have h := Fintype.card_congr e
  change 1 = 2 at h
  contradiction

abbrev code := PresheafFamily.system.code family
abbrev decoded := PresheafFamily.system.decode PresheafFamily.universalDecode code

def recovery : decoded ≅ family := PresheafFamily.recovery family

theorem composed_substitution :
    PresheafFamily.system.code (double.mapElements ⋙ successor.mapElements ⋙ family) =
      raisedSub double ≫ raisedSub successor ≫ code :=
  PresheafFamily.system.code_reindex_comp family successor double

example : (successor.app (Opposite.op (SingleObj.star ℕ))) (2 : ℕ) = (3 : ℕ) := rfl
example : (double.app (Opposite.op (SingleObj.star ℕ))) (2 : ℕ) = (4 : ℕ) := rfl
example : ((double ≫ successor).app (Opposite.op (SingleObj.star ℕ))) (2 : ℕ) = (5 : ℕ) := rfl

/-- Recovery respects the nonidentity restriction action. -/
example : decoded.map (restriction 2 2) ≫ recovery.hom.app (point 2) =
    recovery.hom.app (point 2) ≫ family.map (restriction 2 2) :=
  recovery.hom.naturality (restriction 2 2)

end Examples.NonCubicalClassification
