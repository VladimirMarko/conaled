import SquareKit.Internal.PathTransport.SectionDescent
import Examples.DescentClosure

/-! Complete sections retain their arrow actions and selected transformations. -/
noncomputable section
namespace Examples.SectionDescent
open CategoryTheory SquareKit.Internal.PathTransport.GroupoidModel
open Examples.DescentClosure
set_option backward.isDefEq.respectTransparency false

abbrev loopFamily := constant (Γ := Loops) Loops

theorem loopEquivalences : ∀ x : Loops, Functor.IsEquivalence ((𝟙 loopFamily : loopFamily ⟶ loopFamily).app x) :=
  fun _ => inferInstanceAs (𝟭 Loops).IsEquivalence

def moving : Section loopFamily := constantSection (𝟭 Loops)
def stationary : Section loopFamily :=
  constantSection ((Functor.const Loops).obj (SingleObj.star (Multiplicative ℤ)))

/-- Equal object assignments can carry different actions on context loops. -/
theorem same_objects (x : Loops) : moving.obj x = stationary.obj x := by
  cases x
  rfl

theorem different_arrow_actions : moving ≠ stationary := by
  intro h
  have hm := congrArg (fun s : Section loopFamily =>
    (baseFunctor s).map oneLoop) h
  change (1 : ℤ) = 0 at hm
  exact (by decide : (1 : ℤ) ≠ 0) hm

/-- A selected vertical loop transformation of the stationary section. -/
def turn : stationary.lift ⟶ stationary.lift where
  app x := ⟨𝟙 x, oneLoop⟩
  naturality {x y} f := by
    fapply Grothendieck.ext
    · change f ≫ 𝟙 y = 𝟙 x ≫ f
      simp
    · change (0 : ℤ) + 1 = 1 + 0
      decide

def selectedTurn : {η : stationary.lift ⟶ stationary.lift //
    ∀ x, (η.app x).base = 𝟙 x} := ⟨turn, fun _ => rfl⟩
def selectedIdentity : {η : stationary.lift ⟶ stationary.lift //
    ∀ x, (η.app x).base = 𝟙 x} := ⟨𝟙 stationary.lift, fun _ => rfl⟩

theorem selectedTurn_ne_identity : selectedTurn ≠ selectedIdentity := by
  intro h
  have hh := congrArg (fun η =>
    ((η : stationary.lift ⟶ stationary.lift).app (SingleObj.star (Multiplicative ℤ))).fiber)
    (congrArg Subtype.val h)
  change (1 : ℤ) = 0 at hh
  exact (by decide : (1 : ℤ) ≠ 0) hh

/-- The inverse transport retains the chosen nonidentity loop, not just its
endpoints or existence of a transformation. -/
example :
    (SectionDescent.sectionVerticalEquiv (hβ := loopEquivalences) (CategoryTheory.Equivalence.refl (C := Loops))
      stationary (𝟙 loopFamily) stationary).symm selectedTurn ≠
    (SectionDescent.sectionVerticalEquiv (hβ := loopEquivalences) (CategoryTheory.Equivalence.refl (C := Loops))
      stationary (𝟙 loopFamily) stationary).symm selectedIdentity :=
  fun h => selectedTurn_ne_identity
    ((SectionDescent.sectionVerticalEquiv (hβ := loopEquivalences) (CategoryTheory.Equivalence.refl (C := Loops))
      stationary (𝟙 loopFamily) stationary).symm.injective h)

/-- The identity comparison still reconstructs the complete section, with
vertical recovery. It never replaces the supplied loop action by a constant. -/
example (s : Section loopFamily) (x : Loops) :
    ((SectionDescent.recoverFibers (hβ := loopEquivalences) (CategoryTheory.Equivalence.refl (C := Loops)) s (𝟙 loopFamily)).hom.app x).base =
      𝟙 x :=
  SectionDescent.recoverFibers_base (hβ := loopEquivalences) (CategoryTheory.Equivalence.refl (C := Loops)) s (𝟙 loopFamily) x

/-- Selected vertical transformations survive transport injectively. -/
example (s t : Section loopFamily)
    (η θ : {η : (SectionDescent.descendFibers (hβ := loopEquivalences) (CategoryTheory.Equivalence.refl (C := Loops)) s
        (𝟙 loopFamily)).lift ⟶
      (SectionDescent.descendFibers (hβ := loopEquivalences) (CategoryTheory.Equivalence.refl (C := Loops)) t (𝟙 loopFamily)).lift //
        ∀ x, (η.app x).base = 𝟙 x})
    (h : SectionDescent.sectionVerticalEquiv (hβ := loopEquivalences) (CategoryTheory.Equivalence.refl (C := Loops)) s (𝟙 loopFamily) t η =
      SectionDescent.sectionVerticalEquiv (hβ := loopEquivalences) (CategoryTheory.Equivalence.refl (C := Loops)) s (𝟙 loopFamily) t θ) :
    η = θ :=
  (SectionDescent.sectionVerticalEquiv (hβ := loopEquivalences) (CategoryTheory.Equivalence.refl (C := Loops)) s (𝟙 loopFamily) t).injective h

/-- Section transport also admits a base equivalence that collapses distinct
object representatives. The loop-valued fiber still carries its whole groupoid. -/
def baseCollapseComparison : constant (Γ := Two) Loops ⟶
    collapse.{0,0} ⋙ constant (Γ := Discrete PUnit.{1}) Loops where
  app _ := 𝟭 Loops
  naturality {_ _} _ := rfl

theorem baseCollapseFibers : ∀ x : Two,
    Functor.IsEquivalence (baseCollapseComparison.app x) :=
  fun _ => inferInstanceAs (𝟭 Loops).IsEquivalence

example (s : Section (constant (Γ := Discrete PUnit.{1}) Loops)) (x : Two) :
    ((SectionDescent.recoverFibers (hβ := baseCollapseFibers)
      collapse.{0,0}.asEquivalence s baseCollapseComparison).hom.app x).base =
      𝟙 (collapse.{0,0}.obj x) :=
  SectionDescent.recoverFibers_base (hβ := baseCollapseFibers)
    collapse.{0,0}.asEquivalence s baseCollapseComparison x

end Examples.SectionDescent
