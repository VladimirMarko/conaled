import SquareKit.SheafActionQuotientDescentCategory

/-! Arbitrary parameter covers have an equivalent split-display presentation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SheafActionQuotient.Descent
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M X Y : Sheaf J (Type (max u v))}
variable (a : Action G M) (f : Y ⟶ X)

instance splitCover_locallySurjective [Presheaf.IsLocallySurjective J f.hom] :
    Presheaf.IsLocallySurjective J (SplitSheaf.p (SplitSheaf.ofDisplay f)).hom := by
  rw [← SplitSheaf.displayIso_projection f]
  change Presheaf.IsLocallySurjective J ((SplitSheaf.displayIso f).hom.hom ≫ f.hom)
  infer_instance

/-- The arbitrary sheaf cover is represented by its actual fibers. The cover
isomorphism remains explicit; this does not select a section of the cover. -/
def displayDescentEquivalence [Presheaf.IsLocallySurjective J f.hom] :
    Datum (a := a) (SplitSheaf.ofDisplay f) ≌ Object a X :=
  quotientDescentEquivalence a (SplitSheaf.ofDisplay f)

/-- Changing a parameter by an isomorphism changes the full quotient groupoid
by an equivalence, including all torsors and arrows. -/
def parameterIsoEquivalence {Z : Sheaf J (Type (max u v))} (e : Y ≅ Z) :
    Object a Z ≌ Object a Y :=
  CategoryTheory.Equivalence.mk (restriction e.hom) (restriction e.inv)
    (eqToIso (by rw [restriction_comp, e.inv_hom_id, restriction_id]))
    (eqToIso (by rw [restriction_comp, e.hom_inv_id, restriction_id]))

/-- Local quotient data on the original cover can be moved to its split
presentation without choosing local or global torsor trivializations. -/
def coverParameterEquivalence :
    Object a Y ≌ Object a (SplitSheaf.Ext (SplitSheaf.ofDisplay f)) :=
  parameterIsoEquivalence a (SplitSheaf.displayIso f)

end SquareKit.SheafActionQuotient.Descent
