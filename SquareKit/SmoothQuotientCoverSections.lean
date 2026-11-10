import SquareKit.SmoothQuotientParameterSections
import SquareKit.SheafActionQuotientDescentDisplay

/-! Parameter-local deformation sections on an arbitrary sheaf display.
The split presentation is used for gluing, not in the supplied local data. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
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

/-- Proof fields add no data beyond the complete supplied sections. -/
@[ext] theorem ext {s t : CoverSectionFamily (a := a) f}
    (h : ∀ {Z : Sheaf topology Type} (g : Z ⟶ Y), s.sections g = t.sections g) : s = t := by
  cases s with
  | mk ss sn sm =>
    cases t with
    | mk ts tn tm =>
      have hs : @ss = @ts := funext fun Z => funext fun g => h g
      cases hs
      rfl

/-- Move supplied sections along an isomorphism of covers. This preserves
their values and their entire context-arrow maps. -/
def alongIso {Z : Sheaf topology Type} (s : CoverSectionFamily (a := a) f)
    (e : Z ≅ Y) : CoverSectionFamily (a := a) (e.hom ≫ f) where
  sections g := s.sections (g ≫ e.hom)
  natural g u P := by simpa only [Category.assoc] using s.natural (g ≫ e.hom) u P
  matching g h he P := s.matching (g ≫ e.hom) (h ≫ e.hom)
    (by simpa only [Category.assoc] using he) P

/-- Transfer supplied sections along a commuting square of covers. Neither
parameter map needs to be invertible; this also permits cover refinements. -/
def alongSquare {X' Y' : Sheaf topology Type} {k : Y' ⟶ X'}
    (s : CoverSectionFamily (a := a) f) (u : X' ⟶ X) (v : Y' ⟶ Y)
    (square : v ≫ f = k ≫ u) : CoverSectionFamily (a := a) k where
  sections g := s.sections (g ≫ v)
  natural g w P := by simpa only [Category.assoc] using s.natural (g ≫ v) w P
  matching g h he P := s.matching (g ≫ v) (h ≫ v) (by
    simpa only [Category.assoc, square] using congrArg (fun j => j ≫ u) he) P

/-- The identity square recovers each full supplied section. -/
theorem alongSquare_id_sections (s : CoverSectionFamily (a := a) f)
    {Z : Sheaf topology Type} (g : Z ⟶ Y) :
    (s.alongSquare (k := f) (𝟙 X) (𝟙 Y) (by simp)).sections g = s.sections g := by
  simp only [alongSquare, Category.comp_id]

theorem alongSquare_id (s : CoverSectionFamily (a := a) f) :
    s.alongSquare (k := f) (𝟙 X) (𝟙 Y) (by simp) = s :=
  ext (s.alongSquare_id_sections)

/-- Composition is coherent on complete sections, including their arrow maps. -/
theorem alongSquare_comp_sections {X' Y' X'' Y'' : Sheaf topology Type}
    {k : Y' ⟶ X'} {l : Y'' ⟶ X''}
    (s : CoverSectionFamily (a := a) f) (u : X' ⟶ X) (v : Y' ⟶ Y)
    (square : v ≫ f = k ≫ u) (u' : X'' ⟶ X') (v' : Y'' ⟶ Y')
    (square' : v' ≫ k = l ≫ u') {Z : Sheaf topology Type} (g : Z ⟶ Y'') :
    ((s.alongSquare u v square).alongSquare u' v' square').sections g =
      (s.alongSquare (u' ≫ u) (v' ≫ v) (by
        rw [Category.assoc, square, ← Category.assoc v', square', Category.assoc])).sections g := by
  simp only [alongSquare, Category.assoc]

theorem alongSquare_comp {X' Y' X'' Y'' : Sheaf topology Type}
    {k : Y' ⟶ X'} {l : Y'' ⟶ X''}
    (s : CoverSectionFamily (a := a) f) (u : X' ⟶ X) (v : Y' ⟶ Y)
    (square : v ≫ f = k ≫ u) (u' : X'' ⟶ X') (v' : Y'' ⟶ Y')
    (square' : v' ≫ k = l ≫ u') :
    (s.alongSquare u v square).alongSquare u' v' square' =
      s.alongSquare (u' ≫ u) (v' ≫ v) (by
        rw [Category.assoc, square, ← Category.assoc v', square', Category.assoc]) :=
  ext (s.alongSquare_comp_sections u v square u' v' square')

/-- Restriction to the categorical pullback of the original cover. -/
def baseChange (s : CoverSectionFamily (a := a) f)
    {Z : Sheaf topology Type} (u : Z ⟶ X) :
    CoverSectionFamily (a := a) (Limits.pullback.snd f u) :=
  s.alongSquare u (Limits.pullback.fst f u) Limits.pullback.condition

/-- Construct the split-display input from the original cover data. -/
def toSplit (s : CoverSectionFamily (a := a) f) :
    LocalSection.ParameterFamily (a := a) (SplitSheaf.ofDisplay f) where
  sections g := s.sections (g ≫ (SplitSheaf.displayIso f).hom)
  natural g u P := by
    simpa only [Category.assoc] using s.natural (g ≫ (SplitSheaf.displayIso f).hom) u P
  matching g h he P := s.matching _ _ (by
    simpa only [Category.assoc, SplitSheaf.displayIso_projection] using he) P

/-- The selected map between split presentations retains the original map. -/
def splitSquareMap {X' Y' : Sheaf topology Type} {k : Y' ⟶ X'} (v : Y' ⟶ Y) :
    SplitSheaf.Ext (SplitSheaf.ofDisplay k) ⟶ SplitSheaf.Ext (SplitSheaf.ofDisplay f) :=
  (SplitSheaf.displayIso k).hom ≫ v ≫ (SplitSheaf.displayIso f).inv

theorem splitSquareMap_projection {X' Y' : Sheaf topology Type} {k : Y' ⟶ X'}
    (u : X' ⟶ X) (v : Y' ⟶ Y) (square : v ≫ f = k ≫ u) :
    splitSquareMap (f := f) (k := k) v ≫ SplitSheaf.p (SplitSheaf.ofDisplay f) =
      SplitSheaf.p (SplitSheaf.ofDisplay k) ≫ u := by
  rw [← SplitSheaf.displayIso_projection f, ← SplitSheaf.displayIso_projection k]
  simp only [splitSquareMap, Category.assoc, Iso.inv_hom_id_assoc, square]

/-- Transferring to split presentations commutes with the chosen square map
on complete sections, rather than only on their object values. -/
theorem toSplit_alongSquare_sections {X' Y' : Sheaf topology Type} {k : Y' ⟶ X'}
    (s : CoverSectionFamily (a := a) f) (u : X' ⟶ X) (v : Y' ⟶ Y)
    (square : v ≫ f = k ≫ u) {Z : Sheaf topology Type}
    (g : Z ⟶ SplitSheaf.Ext (SplitSheaf.ofDisplay k)) :
    (s.alongSquare u v square).toSplit.sections g =
      s.toSplit.sections (g ≫ splitSquareMap (f := f) (k := k) v) := by
  simp only [toSplit, alongSquare, splitSquareMap, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

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

theorem fromSplit_toSplit (s : CoverSectionFamily (a := a) f) :
    fromSplit s.toSplit = s := ext (s.fromSplit_toSplit_sections)

theorem toSplit_fromSplit_sections
    (s : LocalSection.ParameterFamily (a := a) (SplitSheaf.ofDisplay f))
    {Z : Sheaf topology Type} (g : Z ⟶ SplitSheaf.Ext (SplitSheaf.ofDisplay f)) :
    (fromSplit s).toSplit.sections g = s.sections g := by
  change s.sections ((g ≫ (SplitSheaf.displayIso f).hom) ≫
    (SplitSheaf.displayIso f).inv) = _
  rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The split pullback maps to the ordinary pullback over the original cover. -/
def pullbackComparison {Z : Sheaf topology Type} (u : Z ⟶ X) :
    SplitSheaf.Ext (SplitSheaf.tySub (SplitSheaf.ofDisplay f) u) ⟶ Limits.pullback f u :=
  Limits.pullback.lift
    (SplitSheaf.lift (SplitSheaf.ofDisplay f) u ≫ (SplitSheaf.displayIso f).hom)
    (SplitSheaf.p (SplitSheaf.tySub (SplitSheaf.ofDisplay f) u)) (by
      rw [Category.assoc, SplitSheaf.displayIso_projection, SplitSheaf.lift_p])

/-- The same comparison is an isomorphism, with both projections retained. -/
theorem originalPullbackSquare {Z : Sheaf topology Type} (u : Z ⟶ X) :
    IsPullback
      (SplitSheaf.lift (SplitSheaf.ofDisplay f) u ≫ (SplitSheaf.displayIso f).hom)
      (SplitSheaf.p (SplitSheaf.tySub (SplitSheaf.ofDisplay f) u)) f u := by
  apply (SplitSheaf.extension_pullback (SplitSheaf.ofDisplay f) u).of_iso
    (Iso.refl _) (SplitSheaf.displayIso f) (Iso.refl _) (Iso.refl _)
  · simp
  · simp
  · simpa using (SplitSheaf.displayIso_projection f).symm
  · simp

def originalPullbackIso {Z : Sheaf topology Type} (u : Z ⟶ X) :
    SplitSheaf.Ext (SplitSheaf.tySub (SplitSheaf.ofDisplay f) u) ≅ Limits.pullback f u :=
  (originalPullbackSquare (f := f) u).isoPullback

theorem originalPullbackIso_hom {Z : Sheaf topology Type} (u : Z ⟶ X) :
    (originalPullbackIso (f := f) u).hom = pullbackComparison (f := f) u := by
  apply Limits.pullback.hom_ext
  · simpa only [originalPullbackIso, pullbackComparison, Limits.pullback.lift_fst] using
      (originalPullbackSquare (f := f) u).isoPullback_hom_fst
  · simpa only [originalPullbackIso, pullbackComparison, Limits.pullback.lift_snd] using
      (originalPullbackSquare (f := f) u).isoPullback_hom_snd

variable [Presheaf.IsLocallySurjective topology f.hom]

/-- Arbitrary parameter pullbacks of the original cover are again covers. -/
instance pullback_locallySurjective {Z : Sheaf topology Type} (u : Z ⟶ X) :
    Presheaf.IsLocallySurjective topology (Limits.pullback.snd f u).hom := by
  apply Presheaf.isLocallySurjective_of_isLocallySurjective_fac (J := topology)
    (f₁ := (pullbackComparison (f := f) u).hom)
    (f₃ := (SplitSheaf.p (SplitSheaf.tySub (SplitSheaf.ofDisplay f) u)).hom)
  have h : pullbackComparison (f := f) u ≫ Limits.pullback.snd f u =
      SplitSheaf.p (SplitSheaf.tySub (SplitSheaf.ofDisplay f) u) :=
    Limits.pullback.lift_snd _ _ _
  exact congrArg (fun k : SplitSheaf.Ext (SplitSheaf.tySub (SplitSheaf.ofDisplay f) u) ⟶ Z =>
    k.hom) h

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

/-- Gluing commutes with any square whose two vertical maps are covers.
In particular it applies to arbitrary pullbacks and covering refinements. -/
theorem glue_alongSquare {X' Y' : Sheaf topology Type} {k : Y' ⟶ X'}
    [Presheaf.IsLocallySurjective topology k.hom]
    (s : CoverSectionFamily (a := a) f) (u : X' ⟶ X) (v : Y' ⟶ Y)
    (square : v ≫ f = k ≫ u) (P : Object a X) :
    restrict u ((s.glue.obj P).as) =
      (((s.alongSquare u v square).glue.obj (reindex P u)).as) := by
  apply restrict_injective k
  have hn := s.natural (𝟙 Y) v (reindex P f)
  have he := (congrArg (restrict v) (s.glue_restrict P)).trans hn
  simp only [restrict_comp, Category.comp_id] at he
  change restrict (v ≫ f) ((s.glue.obj P).as) =
    (((s.sections v).obj (reindex P (v ≫ f))).as) at he
  rw [square] at he
  rw [restrict_comp]
  exact he.trans (by
    simpa only [alongSquare, Category.id_comp, reindex_comp] using
      ((s.alongSquare u v square).glue_restrict (reindex P u)).symm)

/-- The commuting-square comparison retains complete sections and their
selected context-arrow maps. Discrete fibers justify equality here. -/
theorem glue_alongSquare_section {X' Y' : Sheaf topology Type} {k : Y' ⟶ X'}
    [Presheaf.IsLocallySurjective topology k.hom]
    (s : CoverSectionFamily (a := a) f) (u : X' ⟶ X) (v : Y' ⟶ Y)
    (square : v ≫ f = k ≫ u) :
    restrictSection u s.glue = (s.alongSquare u v square).glue.reindex
      (SheafActionQuotient.restriction u) :=
  LocalSection.ParameterFamily.setSection_ext _ (s.glue_alongSquare u v square)

/-- Naturality uses the actual categorical pullback of the original cover. -/
theorem glue_baseChange_section (s : CoverSectionFamily (a := a) f)
    {Z : Sheaf topology Type} (u : Z ⟶ X) :
    restrictSection u s.glue = (s.baseChange u).glue.reindex
      (SheafActionQuotient.restriction u) :=
  s.glue_alongSquare_section u (Limits.pullback.fst f u) Limits.pullback.condition

/-- The original covering values uniquely determine the complete glued section. -/
theorem glue_unique (s : CoverSectionFamily (a := a) f)
    (t : Section (setFamily (family a X)))
    (h : ∀ P, restrict f ((t.obj P).as) =
      (((s.sections (𝟙 Y)).obj (reindex P f)).as)) : t = s.glue := by
  apply s.toSplit.glue_unique t
  intro P
  have ht := congrArg (restrict (SplitSheaf.displayIso f).hom) (h P)
  have hn := s.natural (𝟙 Y) (SplitSheaf.displayIso f).hom (reindex P f)
  have he := ht.trans hn
  simp only [restrict_comp, Category.comp_id] at he
  change restrict ((SplitSheaf.displayIso f).hom ≫ f) ((t.obj P).as) =
    (((s.sections (SplitSheaf.displayIso f).hom).obj
      (reindex P ((SplitSheaf.displayIso f).hom ≫ f))).as) at he
  rw [SplitSheaf.displayIso_projection] at he
  simpa only [toSplit, Category.id_comp] using he

end CoverSectionFamily
end SquareKit.SmoothQuotientDeformations
