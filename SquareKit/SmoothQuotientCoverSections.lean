import SquareKit.SmoothQuotientParameterSections
import SquareKit.SheafActionQuotientDescentDisplay

/-! Parameter-local deformation sections on an arbitrary sheaf display.
The split presentation is used for gluing, not in the supplied local data. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SmoothQuotientDeformations
open CategoryTheory SheafActionQuotient SmoothOpenSite
open Internal.PathTransport.GroupoidModel
variable {H : Type} [Group H] {M X Y : Sheaf topology Type}
variable {a : Action (locallyConstantGroup H) M}

/-- Full sections at every parameter into the original cover, with its actual
overlap condition. No global quotient object or global section is supplied. -/
structure CoverSectionFamily (f : Y ⟶ X) where
  sections : ∀ {Z : Sheaf topology Type}, (Z ⟶ Y) →
    Section (setFamily (family a Z))
  natural {Z W : Sheaf topology Type} (g : Z ⟶ Y) (u : W ⟶ Z)
    (P : Object a Z) :
    restrict u ((sections g).obj P).as = ((sections (u ≫ g)).obj (reindex P u)).as
  matching {Z : Sheaf topology Type} (g h : Z ⟶ Y)
    (he : g ≫ f = h ≫ f) (P : Object a Z) :
    ((sections g).obj P).as = ((sections h).obj P).as

namespace CoverSectionFamily
variable {f : Y ⟶ X}

/-- Move supplied sections along an isomorphism of covers. This preserves
their values and their entire context-arrow maps. -/
def alongIso {Z : Sheaf topology Type} (s : CoverSectionFamily (a := a) f)
    (e : Z ≅ Y) : CoverSectionFamily (a := a) (e.hom ≫ f) where
  sections g := s.sections (g ≫ e.hom)
  natural g u P := by simpa only [Category.assoc] using s.natural (g ≫ e.hom) u P
  matching g h he P := s.matching (g ≫ e.hom) (h ≫ e.hom)
    (by simpa only [Category.assoc] using he) P

/-- Construct the split-display input from the original cover data. -/
def toSplit (s : CoverSectionFamily (a := a) f) :
    LocalSection.ParameterFamily (a := a) (SplitSheaf.ofDisplay f) where
  sections g := s.sections (g ≫ (SplitSheaf.displayIso f).hom)
  natural g u P := by
    simpa only [Category.assoc] using s.natural (g ≫ (SplitSheaf.displayIso f).hom) u P
  matching g h he P := s.matching _ _ (by
    simpa only [Category.assoc, SplitSheaf.displayIso_projection] using he) P

/-- Return split-display sections to the actual original cover. -/
def fromSplit (s : LocalSection.ParameterFamily (a := a) (SplitSheaf.ofDisplay f)) :
    CoverSectionFamily (a := a) f where
  sections g := s.sections (g ≫ (SplitSheaf.displayIso f).inv)
  natural g u P := by
    simpa only [Category.assoc] using s.natural (g ≫ (SplitSheaf.displayIso f).inv) u P
  matching g h he P := s.matching _ _ (by
    rw [← SplitSheaf.displayIso_projection f]
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using he) P

/-- Recovery is of full sections, not only their values at global objects. -/
theorem fromSplit_toSplit_sections (s : CoverSectionFamily (a := a) f)
    {Z : Sheaf topology Type} (g : Z ⟶ Y) :
    (fromSplit s.toSplit).sections g = s.sections g := by
  change s.sections ((g ≫ (SplitSheaf.displayIso f).inv) ≫
    (SplitSheaf.displayIso f).hom) = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

theorem toSplit_fromSplit_sections
    (s : LocalSection.ParameterFamily (a := a) (SplitSheaf.ofDisplay f))
    {Z : Sheaf topology Type} (g : Z ⟶ SplitSheaf.Ext (SplitSheaf.ofDisplay f)) :
    (fromSplit s).toSplit.sections g = s.sections g := by
  change s.sections ((g ≫ (SplitSheaf.displayIso f).hom) ≫
    (SplitSheaf.displayIso f).inv) = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable [Presheaf.IsLocallySurjective topology f.hom]

/-- Glue independently supplied parameter-local sections using the constructed
split-display presentation of an arbitrary locally surjective map. -/
def glue (s : CoverSectionFamily (a := a) f) : Section (setFamily (family a X)) :=
  s.toSplit.glue

/-- Recover every local section at its own parameter, including objects that
were not supplied as restrictions from the original base. -/
theorem recover_local_section (s : CoverSectionFamily (a := a) f)
    {Z : Sheaf topology Type} (g : Z ⟶ Y) :
    (s.toSplit.baseChange (g ≫ f)).glue = s.sections g := by
  have h := s.toSplit.recover_local_section (g ≫ (SplitSheaf.displayIso f).inv)
  have hp : (g ≫ (SplitSheaf.displayIso f).inv) ≫
      SplitSheaf.p (SplitSheaf.ofDisplay f) = g ≫ f := by
    rw [← SplitSheaf.displayIso_projection f]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [hp] at h
  exact h.trans (fromSplit_toSplit_sections s g)

/-- The actual original cover recovers the supplied section, with its arrow
maps. The comparison is obtained through parameter naturality, not an assumed
equivalence of section spaces. -/
theorem glue_restrict_section (s : CoverSectionFamily (a := a) f) :
    restrictSection f s.glue = (s.sections (𝟙 Y)).reindex
      (SheafActionQuotient.restriction f) := by
  have h : (s.toSplit.baseChange f).glue = s.sections (𝟙 Y) := by
    convert s.recover_local_section (𝟙 Y) using 1
    congr 2
  exact (s.toSplit.glue_natural_section f).trans
    (congrArg (fun t => t.reindex (SheafActionQuotient.restriction f)) h)

/-- The underlying deformation also restricts along the original map. -/
theorem glue_restrict (s : CoverSectionFamily (a := a) f) (P : Object a X) :
    restrict f ((s.glue.obj P).as) =
      ((s.sections (𝟙 Y)).obj (reindex P f)).as :=
  congrArg (fun t => (t.obj P).as) s.glue_restrict_section

/-- Restriction at any parameter agrees with the glued split pullback. -/
theorem glue_natural_section (s : CoverSectionFamily (a := a) f)
    {Z : Sheaf topology Type} (u : Z ⟶ X) :
    restrictSection u s.glue = (s.toSplit.baseChange u).glue.reindex
      (SheafActionQuotient.restriction u) :=
  s.toSplit.glue_natural_section u

end CoverSectionFamily
end SquareKit.SmoothQuotientDeformations
