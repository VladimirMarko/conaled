import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Data.ZMod.Basic

/-! The identity-span pushout control for #366. For a groupoid G, a cocone
from the terminal identity span consists of two objects and an arrow between
them. Its space of cocones is Arrow G, not a set of equalities of objects. -/
noncomputable section
namespace SquareKit.Internal.DesignatedMap.GroupoidControl
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v

variable (G : Type u) [Groupoid.{v} G]

def restriction : G ⥤ Arrow G where
  obj x := Arrow.mk (𝟙 x)
  map f := Arrow.homMk f f (by simp)

def sectionIso (c : Arrow G) : (restriction G).obj c.left ≅ c :=
  Arrow.isoMk (Iso.refl _) (asIso c.hom) (by simp [restriction])

/-- Actual restriction is an equivalence for every groupoid target; its
counit retains the chosen gluing arrow in the right component. -/
def universal : G ≌ Arrow G where
  functor := restriction G
  inverse := Arrow.leftFunc
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _)
  counitIso := NatIso.ofComponents (sectionIso G) (by
    intro c d f
    apply Arrow.hom_ext
    · simp [sectionIso, restriction]
    · simp [sectionIso, restriction])
  functor_unitIso_comp _ := by
    apply Arrow.hom_ext <;> simp [restriction, sectionIso]

@[simp] theorem section_right (c : Arrow G) : (sectionIso G c).hom.right = c.hom := rfl

/-- The identity law of F compares the two actual restriction objects. -/
def restrictionMapIso {H : Type*} [Groupoid H] (F : G ⥤ H) (x : G) :
    F.mapArrow.obj ((restriction G).obj x) ≅ (restriction H).obj (F.obj x) :=
  Arrow.isoMk (Iso.refl _) (Iso.refl _) (by simp [restriction])

/-- The entire comparison square survives postcomposition, after the actual
identity-map comparison. Its right component retains the gluing arrow. -/
theorem section_natural {H : Type*} [Groupoid H] (F : G ⥤ H) (c : Arrow G) :
    F.mapArrow.map (sectionIso G c).hom =
      (restrictionMapIso G F c.left).hom ≫ (sectionIso H (F.mapArrow.obj c)).hom := by
  apply Arrow.hom_ext <;> simp [sectionIso, restrictionMapIso]

abbrev C4 := SingleObj (Multiplicative (ZMod 4))
abbrev point : C4 := SingleObj.star _
def cocone (k : ZMod 4) : Arrow C4 := Arrow.mk (X := point) (Y := point) (Multiplicative.ofAdd k)

def multiply (n : ZMod 4) : C4 ⥤ C4 :=
  (show Multiplicative (ZMod 4) →* Multiplicative (ZMod 4) from
    { toFun := fun a => Multiplicative.ofAdd (n * a.toAdd)
      map_one' := by simp
      map_mul' := by intro a b; exact congrArg Multiplicative.ofAdd (mul_add n a.toAdd b.toAdd) }).toFunctor

/-- Postcomposition acts on the designated gluing, rather than replacing it. -/
theorem post_glue (n k : ZMod 4) :
    ((multiply n).mapArrow.obj (cocone k)).hom = Multiplicative.ofAdd (n * k) := rfl

/-- The actual comparison from a restricted gap to the selected cocone has
nontrivial gluing component, even though the object map sees a single point. -/
theorem selected_section : ((universal C4).counitIso.app (cocone 1)).hom.right =
    Multiplicative.ofAdd (1 : ZMod 4) := rfl

theorem selected_post : ((multiply 2).mapArrow.obj (cocone 1)).hom ≠
    ((multiply 2).mapArrow.obj (cocone 0)).hom := by
  change Multiplicative.ofAdd (2 * (1 : ZMod 4)) ≠ Multiplicative.ofAdd (2 * (0 : ZMod 4))
  decide

/-- No observation factored through native identity at the single object can
retain these two gluing labels. This refutes that attempted encoding only. -/
theorem no_native_glue_observation
    (encode : ZMod 4 → (point = point)) (observe : (point = point) → ZMod 4) :
    ¬ (∀ k, observe (encode k) = k) := by
  intro h
  have e : observe (encode 0) = observe (encode 1) := congrArg observe (Subsingleton.elim _ _)
  have bad : (0 : ZMod 4) = 1 := (h 0).symm.trans (e.trans (h 1))
  exact (by decide : (0 : ZMod 4) ≠ 1) bad

/-- An unrelated equivalence with the same endpoints can alter the required
observation. Multiplication by -1 is an actual automorphism of C4. -/
def reverse : C4 ≌ C4 :=
  (show Multiplicative (ZMod 4) ≃* Multiplicative (ZMod 4) from
    { toFun := fun a => Multiplicative.ofAdd (-a.toAdd)
      invFun := fun a => Multiplicative.ofAdd (-a.toAdd)
      left_inv := by intro a; simp
      right_inv := by intro a; simp
      map_mul' := by intro a b; exact congrArg Multiplicative.ofAdd (neg_add a.toAdd b.toAdd) }).toSingleObjEquiv

theorem unrelated_equivalence_changes_glue :
    (reverse.functor.mapArrow.obj (cocone 1)).hom ≠ (cocone 1).hom := by
  change Multiplicative.ofAdd (-(1 : ZMod 4)) ≠ Multiplicative.ofAdd (1 : ZMod 4)
  decide
end SquareKit.Internal.DesignatedMap.GroupoidControl
