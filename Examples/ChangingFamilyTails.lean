import SquareKit.Internal.PathTransport.ChangingTailComparison
import Examples.FamilyMapElimination

/-! Noninvertible path and changing-tail comparisons retain actual C4 arrows. -/
noncomputable section
namespace Examples.ChangingFamilyTails
open CategoryTheory CategoryTheory.Functor
open SquareKit.Internal.PathTransport.GroupoidModel
open ContextualElimination FamilyMapElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev Γ := Discrete PUnit
local instance : Groupoid Γ := Groupoid.ofIsGroupoid
local instance : IsGroupoid (Cat.of Γ) := inferInstanceAs (IsGroupoid Γ)
abbrev γ : Γ := Discrete.mk PUnit.unit
abbrev A := before (Cat.of Γ)
abbrev B := after (Cat.of Γ)
abbrev α := familyMap (Cat.of Γ)
abbrev x := inhabitBefore (Cat.of Γ)
abbrev y := x.familyImage α
abbrev R := PathComparison.familyMap α x

def chosen (g : p ⟶ p) : PathComparison.PathCtx A x :=
  ⟨x.lift.obj γ,Discrete.mk (selected false g)⟩

/-- The actual path map sends each chosen source loop to the identical C4
label, even though its family map is not full. -/
example (g : p ⟶ p) : (R.obj (chosen g)).fiber.as = g := rfl
example (g h : p ⟶ p) (hne : g ≠ h) : (R.obj (chosen g)).fiber.as ≠ (R.obj (chosen h)).fiber.as := hne
example : ¬ collapse.Full := collapse_not_full

/-- The general base/family theorem constructs the root square; it is not
supplied as an assumption by this example. -/
example : EquivalenceSquare.Square (PathComparison.pathEquivalence B y)
    (PathComparison.pathEquivalence A x)
    (PathComparison.familyMapTo α x (y.reindex (𝟭 Γ)) rfl ⋙
      PathComparison.substitution B y (𝟭 Γ)) (𝟭 Γ) :=
  PathComparison.baseFamilySquare B A (𝟭 Γ) α y x rfl

/-- The same noninvertible comparison is available over independently
specified contexts and their map. -/
def declarationMap {C C' : Cat.{0,0}} (K : C' ⥤ C) :
    before C' ⋙ Grpd.forgetToCat ⟶ K ⋙ after C ⋙ Grpd.forgetToCat where
  app _ := collapse.toCatHom
  naturality {_ _} _ := rfl

abbrev targetContext := Cat.of (PathComparison.PathCtx B y)
abbrev sourceContext := Cat.of (PathComparison.PathCtx A x)
abbrev firstTarget := after targetContext ⋙ Grpd.forgetToCat
abbrev firstSource := before sourceContext ⋙ Grpd.forgetToCat
abbrev firstMap := Grothendieck.map (declarationMap (C := targetContext) (C' := sourceContext) R) ⋙ Grothendieck.pre firstTarget R
abbrev secondTarget := after (Cat.of (Grothendieck firstTarget)) ⋙ Grpd.forgetToCat
abbrev secondSource := before (Cat.of (Grothendieck firstSource)) ⋙ Grpd.forgetToCat
abbrev finalMap := Grothendieck.map (declarationMap (C := Cat.of (Grothendieck firstTarget))
    (C' := Cat.of (Grothendieck firstSource)) firstMap) ⋙ Grothendieck.pre secondTarget firstMap

/-- Two successive changing declarations; the second is over the whole
extended context, rather than over the original root. -/
def twoStep : ChangingTail (C := targetContext) (C' := sourceContext) R
    (E := Cat.of (Grothendieck secondTarget)) (E' := Cat.of (Grothendieck secondSource)) finalMap :=
  .extend (.extend .empty firstTarget firstSource (declarationMap (C := targetContext) (C' := sourceContext) R))
    secondTarget secondSource (declarationMap (C := Cat.of (Grothendieck firstTarget))
    (C' := Cat.of (Grothendieck firstSource)) firstMap)

/-- Finite propagation constructs all branch coherence from the actual root. -/
example : EquivalenceSquare.Square
    (twoStep.target.reindex (PathComparison.normalized B y)).2.2.equiv
    (twoStep.source.reindex (PathComparison.normalized A x)).2.2.equiv finalMap
    (twoStep.propagate (PathComparison.normalized B y) (PathComparison.normalized A x)
      (𝟭 Γ) (PathComparison.familyMapSquare α x)).val :=
  (twoStep.propagate (PathComparison.normalized B y) (PathComparison.normalized A x)
    (𝟭 Γ) (PathComparison.familyMapSquare α x)).property


def unitFamily (C : Cat.{0,0}) : C ⥤ Cat.{0,0} :=
  (CategoryTheory.Functor.const C).obj (Cat.of (Discrete PUnit))

def unitBranch {D C : Cat.{0,0}} (e : NormalizedEquivalence D C) :
    D ⥤ Grothendieck (unitFamily C) where
  obj d := ⟨e.equiv.functor.obj d, Discrete.mk PUnit.unit⟩
  map f := ⟨e.equiv.functor.map f, 𝟙 _⟩
  map_id d := by
    fapply Grothendieck.ext
    · exact e.equiv.functor.map_id d
    · exact congrArg Discrete.Hom.mk rfl
  map_comp f g := by
    fapply Grothendieck.ext
    · exact e.equiv.functor.map_comp f g
    · exact congrArg Discrete.Hom.mk rfl

def unitMap {C C' : Cat.{0,0}} (K : C' ⥤ C) : unitFamily C' ⟶ K ⋙ unitFamily C where
  app _ := 𝟙 _
  naturality {_ _} _ := rfl

theorem unitBranch_square {D C D' C' : Cat.{0,0}}
    (e : NormalizedEquivalence D C) (e' : NormalizedEquivalence D' C')
    (K : C' ⥤ C) (L : D' ⥤ D) (sq : EquivalenceSquare.Square e.equiv e'.equiv K L) :
    unitBranch e' ⋙ Grothendieck.map (unitMap K) ⋙ Grothendieck.pre (unitFamily C) K =
      L ⋙ unitBranch e := by
  fapply CategoryTheory.Functor.ext
  · intro a
    exact congrArg (fun c => (⟨c,Discrete.mk PUnit.unit⟩ : Grothendieck (unitFamily C)))
      (CategoryTheory.Functor.congr_obj sq.forward a)
  · intro a b f
    fapply Grothendieck.ext
    · simpa [unitBranch, Grothendieck.map, Grothendieck.pre, Grothendieck.comp_base,
        Grothendieck.base_eqToHom] using CategoryTheory.Functor.congr_hom sq.forward f
    · exact congrArg Discrete.Hom.mk rfl

/-- The changing-tail comparison is consumed by elimination with constructed,
inhabited branches. The branch equation follows from the generated square. -/
example :
    (twoStep.source.reindex (PathComparison.normalized A x)).2.2.eliminate
        (unitBranch (twoStep.source.reindex (PathComparison.normalized A x)).2.2) rfl ⋙
      Grothendieck.map (unitMap (C := Cat.of (Grothendieck secondTarget))
        (C' := Cat.of (Grothendieck secondSource)) finalMap) ⋙
      Grothendieck.pre (unitFamily (Cat.of (Grothendieck secondTarget))) finalMap =
    finalMap ⋙ (twoStep.target.reindex (PathComparison.normalized B y)).2.2.eliminate
      (unitBranch (twoStep.target.reindex (PathComparison.normalized B y)).2.2) rfl := by
  exact twoStep.eliminate (PathComparison.normalized B y) (PathComparison.normalized A x)
    (𝟭 Γ) (PathComparison.familyMapSquare α x) _ _ (unitMap (C := Cat.of (Grothendieck secondTarget))
        (C' := Cat.of (Grothendieck secondSource)) finalMap) _ rfl _ rfl
    (unitBranch_square (twoStep.target.reindex (PathComparison.normalized B y)).2.2
      (twoStep.source.reindex (PathComparison.normalized A x)).2.2 finalMap _
      (twoStep.propagate (PathComparison.normalized B y) (PathComparison.normalized A x)
        (𝟭 Γ) (PathComparison.familyMapSquare α x)).property)

end Examples.ChangingFamilyTails
