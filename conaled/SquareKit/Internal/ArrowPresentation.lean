import SquareKit.Internal.SierpinskiGeneric
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic

/-! Every arrow has a canonical pushout presentation by constant arrows and
initial-domain arrows. The latter are products with the generic proposition. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.Internal.ArrowPresentation
open CategoryTheory CategoryTheory.Limits
universe v u
variable {C : Type u} [Category.{v} C] [HasInitial C]

/-- The initial-domain arrow includes into the constant arrow. -/
def boundary (X : C) : (ArrowGeometry.initialArrow C).obj X ⟶
    (ArrowGeometry.diagonal C).obj X := Arrow.homMk (initial.to X) (𝟙 X)

/-- The domain determines a map from its constant arrow. -/
def domain (a : Arrow C) : (ArrowGeometry.diagonal C).obj a.left ⟶ a :=
  Arrow.homMk (𝟙 _) a.hom

/-- The codomain determines a map from its initial-domain arrow. -/
def codomain (a : Arrow C) : (ArrowGeometry.initialArrow C).obj a.right ⟶ a :=
  Arrow.homMk (initial.to _) (𝟙 _)

theorem condition (a : Arrow C) :
    boundary a.left ≫ domain a = (ArrowGeometry.initialArrow C).map a.hom ≫ codomain a := by
  apply Arrow.hom_ext <;> simp [boundary, domain, codomain, ArrowGeometry.initialArrow]

/-- The defining presentation cocone for an arbitrary arrow. -/
def cocone (a : Arrow C) :
    PushoutCocone (boundary a.left) ((ArrowGeometry.initialArrow C).map a.hom) :=
  PushoutCocone.mk (domain a) (codomain a) (condition a)

/-- The canonical presentation is a pushout, with no restriction on the arrow. -/
def isColimit (a : Arrow C) : IsColimit (cocone a) :=
  PushoutCocone.IsColimit.mk (condition a)
    (fun s => Arrow.homMk s.inl.left s.inr.right (by
      have c := congrArg Arrow.Hom.right s.condition
      have w := Arrow.w s.inl
      dsimp [boundary, ArrowGeometry.initialArrow, ArrowGeometry.diagonal] at c w ⊢
      simpa using w.trans c))
    (fun s => by
      apply Arrow.hom_ext
      · simp [domain]
      · have c := congrArg Arrow.Hom.right s.condition
        simpa [boundary, domain, ArrowGeometry.initialArrow] using c.symm)
    (fun s => by apply Arrow.hom_ext; exact initial.hom_ext _ _; simp [codomain])
    (fun s m hl hr => by
      apply Arrow.hom_ext
      · simpa [domain] using congrArg Arrow.Hom.left hl
      · simpa [codomain] using congrArg Arrow.Hom.right hr)

omit [HasInitial C] in
@[reassoc] theorem domain_natural {a b : Arrow C} (f : a ⟶ b) :
    (ArrowGeometry.diagonal C).map f.left ≫ domain b = domain a ≫ f := by
  apply Arrow.hom_ext
  · simp [domain, ArrowGeometry.diagonal]
  · simp [domain, ArrowGeometry.diagonal]

@[reassoc] theorem codomain_natural {a b : Arrow C} (f : a ⟶ b) :
    (ArrowGeometry.initialArrow C).map f.right ≫ codomain b = codomain a ≫ f := by
  apply Arrow.hom_ext
  · exact initial.hom_ext _ _
  · simp [codomain, ArrowGeometry.initialArrow]

variable [HasTerminal C] [HasStrictInitialObjects C]

/-- The other projection of the initial-domain arrow is into the generic proposition. -/
def toGeneric (X : C) : (ArrowGeometry.initialArrow C).obj X ⟶ Sierpinski.generic C :=
  Arrow.homMk (𝟙 _) (terminal.from X)

/-- The initial-domain arrow is the product of the generic proposition and a constant arrow. -/
def boundaryIsProduct (X : C) : IsLimit (BinaryFan.mk (toGeneric X) (boundary X)) :=
  BinaryFan.isLimitMk
    (fun s => Arrow.homMk s.fst.left s.snd.right (by
      have hi : IsInitial s.pt.left := IsInitial.ofStrict s.fst.left initialIsInitial
      exact (hi.hom_ext _ s.snd.left).trans (by simpa [ArrowGeometry.diagonal] using Arrow.w s.snd)))
    (fun s => by
      apply Arrow.hom_ext
      · simp [toGeneric]
      · exact terminal.hom_ext _ _)
    (fun s => by
      apply Arrow.hom_ext
      · have hi : IsInitial s.pt.left := IsInitial.ofStrict s.fst.left initialIsInitial
        exact hi.hom_ext _ _
      · simp [boundary])
    (fun s m hf hg => by
      apply Arrow.hom_ext
      · simpa [toGeneric] using congrArg Arrow.Hom.left hf
      · simpa [boundary] using congrArg Arrow.Hom.right hg)

end SquareKit.Internal.ArrowPresentation
