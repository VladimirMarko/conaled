import SquareKit.SheafActionQuotientDescentOverlap
import SquareKit.SmoothQuotientLocalSections

/-! Parameter-compatible deformation sections supply local cocycle matching. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SmoothQuotientDeformations
open CategoryTheory SheafActionQuotient SmoothOpenSite
open Internal.PathTransport.GroupoidModel
variable {H : Type} [Group H] {M X : Sheaf topology Type}
variable {a : Action (locallyConstantGroup H) M} {A : SplitSheaf.Ty X}

/-- Deformation equality is reflected by restriction along a cover. -/
theorem restrict_injective {Y : Sheaf topology Type} (f : Y ⟶ X)
    [Presheaf.IsLocallySurjective topology f.hom] {P : Object a X}
    {h k : Deformation P} (he : restrict f h = restrict f k) : h = k := by
  apply Deformation.ext
  apply (cancel_epi (cover P f)).mp
  exact congrArg Deformation.map he

/-- Restrict every deformation in a full section along a parameter map,
retaining the selected quotient arrow in its reindexed context. -/
def restrictSection {Y : Sheaf topology Type} (f : Y ⟶ X)
    (t : Section (setFamily (family a X))) :
    Section (setFamily (SheafActionQuotient.restriction f ⋙ family a Y)) where
  obj P := Discrete.mk (restrict f (t.obj P).as)
  map {P _Q} c := eqToHom (congrArg Discrete.mk
    ((transport_restrict f c (t.obj P).as).symm.trans
      (congrArg (restrict f) (Discrete.eq_of_hom (t.map c)))))
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- A section at every parameter into the cover, with parameter naturality and
matching over the base. The fibers here are discrete deformations; context
sections retain all selected quotient arrows. No global section is supplied. -/
structure LocalSection.ParameterFamily (A : SplitSheaf.Ty X) where
  sections : ∀ {Y : Sheaf topology Type}, (Y ⟶ SplitSheaf.Ext A) →
    Section (setFamily (family a Y))
  natural {Y Z : Sheaf topology Type} (g : Y ⟶ SplitSheaf.Ext A) (u : Z ⟶ Y)
    (P : Object a Y) :
    restrict u ((sections g).obj P).as = ((sections (u ≫ g)).obj (reindex P u)).as
  matching {Y : Sheaf topology Type} (g h : Y ⟶ SplitSheaf.Ext A)
    (he : g ≫ SplitSheaf.p A = h ≫ SplitSheaf.p A) (P : Object a Y) :
    ((sections g).obj P).as = ((sections h).obj P).as

namespace LocalSection.ParameterFamily
variable (s : LocalSection.ParameterFamily (a := a) A)

/-- The two restricted deformation values agree through the actual cocycle
arrow. Parameter naturality and overlap matching produce this equation. -/
theorem overlap (d : Descent.Datum (a := a) A) :
    transport d.overlapArrow
      (restrict (SplitSheaf.p (SplitSheaf.tySub A (SplitSheaf.p A)))
        ((s.sections (𝟙 (SplitSheaf.Ext A))).obj d.localObject).as) =
    restrict (SplitSheaf.lift A (SplitSheaf.p A))
      ((s.sections (𝟙 (SplitSheaf.Ext A))).obj d.localObject).as := by
  let q := SplitSheaf.p (SplitSheaf.tySub A (SplitSheaf.p A))
  let r := SplitSheaf.lift A (SplitSheaf.p A)
  have hq := s.natural (𝟙 (SplitSheaf.Ext A)) q d.localObject
  have hr := s.natural (𝟙 (SplitSheaf.Ext A)) r d.localObject
  have hm := s.matching (q ≫ 𝟙 (SplitSheaf.Ext A))
    (r ≫ 𝟙 (SplitSheaf.Ext A)) rfl (reindex d.localObject q)
  have ha : transport d.overlapArrow
      (((s.sections (r ≫ 𝟙 (SplitSheaf.Ext A))).obj (reindex d.localObject q)).as) =
      (((s.sections (r ≫ 𝟙 (SplitSheaf.Ext A))).obj (reindex d.localObject r)).as) :=
    Discrete.eq_of_hom ((s.sections (r ≫ 𝟙 (SplitSheaf.Ext A))).map d.overlapArrow)
  exact (congrArg (transport d.overlapArrow) (hq.trans hm)).trans (ha.trans hr.symm)

/-- Parameter-compatible overlap matching implies the actual local cocycle
matching equation needed by the section assembly theorem. -/
theorem cocycleMatching :
    LocalSection.Matching (s.sections (𝟙 (SplitSheaf.Ext A))) := by
  intro d x b c t p
  have h := congrArg (fun k : Deformation
      (reindex d.localObject (SplitSheaf.lift A (SplitSheaf.p A))) =>
    k.map.hom.app x.obj (t, ⟨⟨⟨x.val,b⟩,c⟩,d.torsorDatum.transport x b c p⟩))
    (s.overlap d)
  change ((s.sections (𝟙 (SplitSheaf.Ext A))).obj d.localObject).as.map.hom.app x.obj
    (t, ⟨⟨x.val,b⟩,d.torsorDatum.transport x c b (d.torsorDatum.transport x b c p)⟩) =
    ((s.sections (𝟙 (SplitSheaf.Ext A))).obj d.localObject).as.map.hom.app x.obj
      (t, ⟨⟨x.val,c⟩,d.torsorDatum.transport x b c p⟩) at h
  rw [d.torsorDatum.cocycle, d.torsorDatum.identity] at h
  exact h.symm

/-- The supplied parameter family restricts to the pulled-back cover, using
composition of the actual parameter maps. -/
def baseChange {Y : Sheaf topology Type} (f : Y ⟶ X) :
    LocalSection.ParameterFamily (a := a) (SplitSheaf.tySub A f) where
  sections g := s.sections (g ≫ SplitSheaf.lift A f)
  natural g u P := s.natural (g ≫ SplitSheaf.lift A f) u P
  matching g h he P := s.matching (g ≫ SplitSheaf.lift A f)
    (h ≫ SplitSheaf.lift A f) (congrArg (fun k => k ≫ f) he) P

/-- Identity parameter change leaves the full supplied family unchanged. -/
theorem baseChange_id : s.baseChange (𝟙 X) = s := by
  cases s
  rfl

/-- Parameter change is coherent under composition on the full supplied family. -/
theorem baseChange_comp {Y Z : Sheaf topology Type} (f : Y ⟶ X) (g : Z ⟶ Y) :
    (s.baseChange f).baseChange g = s.baseChange (g ≫ f) := rfl

variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

/-- Assemble the global section from the supplied parameter-local sections;
cocycle matching is proved from their local overlap contract. -/
def glue : Section (setFamily (family a X)) :=
  LocalSection.glue (s.sections (𝟙 (SplitSheaf.Ext A))) s.cocycleMatching

/-- The resulting section recovers the supplied local value at each cocycle. -/
theorem recover (d : Descent.Datum (a := a) A) :
    transport d.comparison (restrict (SplitSheaf.p A) ((s.glue.obj d.object).as)) =
      ((s.sections (𝟙 (SplitSheaf.Ext A))).obj d.localObject).as :=
  LocalSection.glue_recover _ _ d

/-- Restriction of the glued value recovers the supplied covering section at
all global quotient objects. -/
theorem glue_restrict (P : Object a X) :
    restrict (SplitSheaf.p A) ((s.glue.obj P).as) =
      ((s.sections (𝟙 (SplitSheaf.Ext A))).obj (reindex P (SplitSheaf.p A))).as :=
  LocalSection.glue_restrict _ _ P

/-- Gluing is natural under arbitrary parameter change, on all quotient
objects. Each component belongs to a full section on context arrows. -/
theorem glue_natural {Y : Sheaf topology Type} (f : Y ⟶ X) (P : Object a X) :
    restrict f ((s.glue.obj P).as) =
      (((s.baseChange f).glue.obj (reindex P f)).as) := by
  apply SmoothQuotientDeformations.restrict_injective
    (SplitSheaf.p (SplitSheaf.tySub A f))
  calc
    restrict (SplitSheaf.p (SplitSheaf.tySub A f)) (restrict f ((s.glue.obj P).as)) =
        restrict (SplitSheaf.lift A f) (restrict (SplitSheaf.p A) ((s.glue.obj P).as)) := by
      apply Deformation.ext
      rfl
    _ = restrict (SplitSheaf.lift A f)
        (((s.sections (𝟙 (SplitSheaf.Ext A))).obj (reindex P (SplitSheaf.p A))).as) :=
      congrArg (restrict (SplitSheaf.lift A f)) (s.glue_restrict P)
    _ = (((s.sections (SplitSheaf.lift A f ≫ 𝟙 (SplitSheaf.Ext A))).obj
        (reindex (reindex P (SplitSheaf.p A)) (SplitSheaf.lift A f))).as) :=
      s.natural _ _ _
    _ = restrict (SplitSheaf.p (SplitSheaf.tySub A f))
        (((s.baseChange f).glue.obj (reindex P f)).as) :=
      ((s.baseChange f).glue_restrict (reindex P f)).symm

/-- Every original local quotient object is recovered after gluing at its
parameter, without requiring it to extend to the original base. -/
theorem recover_local {Y : Sheaf topology Type} (g : Y ⟶ SplitSheaf.Ext A)
    (P : Object a Y) :
    (((s.baseChange (g ≫ SplitSheaf.p A)).glue.obj P).as) =
      ((s.sections g).obj P).as := by
  let f := g ≫ SplitSheaf.p A
  let q := SplitSheaf.p (SplitSheaf.tySub A f)
  apply SmoothQuotientDeformations.restrict_injective q
  calc
    restrict q (((s.baseChange f).glue.obj P).as) =
        (((s.sections (𝟙 _ ≫ SplitSheaf.lift A f)).obj (reindex P q)).as) :=
      (s.baseChange f).glue_restrict P
    _ = (((s.sections (q ≫ g)).obj (reindex P q)).as) :=
      s.matching (𝟙 _ ≫ SplitSheaf.lift A f) (q ≫ g) rfl (reindex P q)
    _ = restrict q (((s.sections g).obj P).as) := (s.natural g q P).symm

/-- Sections of a discrete family are determined by their object values. -/
theorem setSection_ext {Γ : Type*} [Category* Γ] (F : Γ ⥤ Type*)
    {s t : Section (setFamily F)} (h : ∀ γ, (s.obj γ).as = (t.obj γ).as) : s = t := by
  cases s with
  | mk so sm si sc =>
    cases t with
    | mk tob tm ti tc =>
      have ho : so = tob := funext fun γ => Discrete.ext (h γ)
      cases ho
      have hm : @sm = @tm := by
        funext γ δ f
        exact Subsingleton.elim _ _
      cases hm
      rfl

/-- Parameter compatibility holds for the complete sections, including their
arrow maps. No groupoid-context arrows are replaced by mere endpoints. -/
theorem glue_natural_section {Y : Sheaf topology Type} (f : Y ⟶ X) :
    restrictSection f s.glue = (s.baseChange f).glue.reindex
      (SheafActionQuotient.restriction f) :=
  setSection_ext _ (s.glue_natural f)

/-- Recovery is equality of the complete local section, so its entire selected
context-arrow action is retained. Discrete fibers justify this stronger form. -/
theorem recover_local_section {Y : Sheaf topology Type} (g : Y ⟶ SplitSheaf.Ext A) :
    (s.baseChange (g ≫ SplitSheaf.p A)).glue = s.sections g :=
  setSection_ext _ (s.recover_local g)

/-- The glued value is uniquely determined by the local covering values. -/
theorem glue_unique (t : Section (setFamily (family a X)))
    (h : ∀ P, restrict (SplitSheaf.p A) ((t.obj P).as) =
      (((s.sections (𝟙 (SplitSheaf.Ext A))).obj (reindex P (SplitSheaf.p A))).as)) :
    t = s.glue := by
  apply setSection_ext
  intro P
  apply SmoothQuotientDeformations.restrict_injective (SplitSheaf.p A)
  exact (h P).trans (s.glue_restrict P).symm

end LocalSection.ParameterFamily
end SquareKit.SmoothQuotientDeformations
