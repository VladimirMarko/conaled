import SquareKit.Internal.PathTransport.CechMatchingContractible
import SquareKit.Internal.PathTransport.CechMatchingComprehensionIdentity
import SquareKit.Internal.PathTransport.CechMatchingConstant
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Algebra.Group.Int.Defs

noncomputable section
namespace Examples.CechMatchingIdentity
open CategoryTheory SquareKit.Internal.PathTransport
open CechMatching

abbrev Loops := SingleObj (Multiplicative ℤ)
abbrev star := SingleObj.star (Multiplicative ℤ)
abbrev loop : star ⟶ star := Multiplicative.ofAdd 1
abbrev C := Grpd.of Loops

def recoverPaths := Identity.restrictionIso (constantFunctor C) (𝟭 Loops) (𝟭 Loops)

/-- Identity matching retains a selected nonidentity loop, despite equal endpoints. -/
theorem selected_loop : (recoverPaths.hom.app star loop).val = loop := rfl

theorem selected_loop_ne_refl : recoverPaths.hom.app star loop ≠
    recoverPaths.hom.app star (𝟙 star) := by
  intro h
  have hh := congrArg Subtype.val h
  change (1 : ℤ) = 0 at hh
  exact (by decide : (1 : ℤ) ≠ 0) hh

/-- Recovery is defined for every supplied matching identity, not only a chosen image. -/
theorem arbitrary_local_recovery (p : Identity.Fiber
    ((constantFunctor C).obj star) ((constantFunctor C).obj star)) :
    recoverPaths.hom.app star (recoverPaths.inv.app star p) = p := by
  exact ConcreteCategory.congr_hom (recoverPaths.inv_hom_id_app star) p

/-- The general endpoint action retains conjugation by both selected arrows. -/
example {D : Diagram.{0,0}} {B : Type} [Category B]
    (X Y : B ⥤ Datum D) {b c : B} (f : b ⟶ c)
    (p : Identity.Fiber (X.obj b) (Y.obj b)) :
    ((Identity.family X Y).map f p).val =
      inv (X.map f).localArrow ≫ p.val ≫ (Y.map f).localArrow :=
  Identity.map_localArrow X Y f p

/-- In a relative fiber, recovery includes the supplied vertical matching arrow. -/
example {D : StrictDiagram.{0,0}} {A : Comprehension.FamilyData D} {h : A.Coherence}
    {d : Datum D.toDiagram} {x y : Comprehension.Fiber A h d}
    (p : Comprehension.Identity.Paths x y) :
    ((Comprehension.Identity.arrowEquiv x y) p).matchingArrow.localArrow = p.val.val := rfl

/-- The reconstructed arrow is vertical over the specified base datum. -/
example {D : StrictDiagram.{0,0}} {A : Comprehension.FamilyData D} {h : A.Coherence}
    {d : Datum D.toDiagram} {x y : Comprehension.Fiber A h d}
    (p : Comprehension.Identity.Paths x y) :
    ((Comprehension.Identity.arrowEquiv x y) p).matchingArrow.localArrow.base =
      𝟙 d.localObject := p.property

/-- Fully faithful relative restriction recovers every supplied vertical path. -/
example {D : StrictDiagram.{0,0}} {A : Comprehension.FamilyData D} {h : A.Coherence}
    {d : Datum D.toDiagram} {G B : Type} [Groupoid G] [Category B]
    (R : G ⥤ Comprehension.Fiber A h d) [R.Full] [R.Faithful]
    (X Y : B ⥤ G) (b : B)
    (p : Comprehension.Identity.Paths ((X ⋙ R).obj b) ((Y ⋙ R).obj b)) :
    (Comprehension.Identity.restrictionIso R X Y).hom.app b
      ((Comprehension.Identity.restrictionIso R X Y).inv.app b p) = p :=
  ConcreteCategory.congr_hom
    ((Comprehension.Identity.restrictionIso R X Y).inv_hom_id_app b) p

local instance : Groupoid (Discrete PUnit.{1}) := Groupoid.ofIsGroupoid

/-- Empty-context effectivity does not require unfolding the chosen functor. -/
example (R : Discrete PUnit.{1} ⥤ Datum (constant (Grpd.of (Discrete PUnit.{1})))) :
    R.IsEquivalence :=
  restriction_equivalence_of_contractible R (Discrete.mk PUnit.unit)
    (fun x y => eqToHom (Subsingleton.elim x y))
    (fun _ _ => inferInstance)
    (by
      intro x y
      change Discrete PUnit.{1} at x y
      exact eqToHom (Subsingleton.elim x y))
    (by
      intro x y
      change Discrete PUnit.{1} at x y
      change Subsingleton (x ⟶ y)
      infer_instance)
    (by
      intro x y
      change Discrete PUnit.{1} at x y
      change Subsingleton (x ⟶ y)
      infer_instance)

end Examples.CechMatchingIdentity
