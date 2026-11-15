import SquareKit.SplitSheafCech

/-! The actual double and triple pullbacks of an arbitrary sheaf cover, with
explicit comparisons to its split-display overlaps. -/
noncomputable section
namespace SquareKit.SheafCoverCech
open CategoryTheory CategoryTheory.Limits
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {X Y : Sheaf J (Type w)} (f : Y ⟶ X)

abbrev double := pullback f f
abbrev first : double f ⟶ Y := pullback.fst f f
abbrev second : double f ⟶ Y := pullback.snd f f

def diagonal : Y ⟶ double f := pullback.lift (𝟙 Y) (𝟙 Y) rfl

abbrev triple := pullback (first f ≫ f) f
abbrev firstSecond : triple f ⟶ double f := pullback.fst (first f ≫ f) f
abbrev third : triple f ⟶ Y := pullback.snd (first f ≫ f) f

def firstThird : triple f ⟶ double f :=
  pullback.lift (firstSecond f ≫ first f) (third f)
    (by simpa only [Category.assoc] using (pullback.condition (f := first f ≫ f) (g := f)))

def secondThird : triple f ⟶ double f :=
  pullback.lift (firstSecond f ≫ second f) (third f) (by
    rw [Category.assoc, ← (pullback.condition (f := f) (g := f))]
    exact (pullback.condition (f := first f ≫ f) (g := f)))

@[simp] theorem diagonal_first : diagonal f ≫ first f = 𝟙 Y := pullback.lift_fst _ _ _
@[simp] theorem diagonal_second : diagonal f ≫ second f = 𝟙 Y := pullback.lift_snd _ _ _
@[simp] theorem firstThird_first : firstThird f ≫ first f = firstSecond f ≫ first f :=
  pullback.lift_fst _ _ _
@[simp] theorem firstThird_second : firstThird f ≫ second f = third f :=
  pullback.lift_snd _ _ _
@[simp] theorem secondThird_first : secondThird f ≫ first f = firstSecond f ≫ second f :=
  pullback.lift_fst _ _ _
@[simp] theorem secondThird_second : secondThird f ≫ second f = third f :=
  pullback.lift_snd _ _ _

/-- The first two split overlap projections form the actual pullback of f. -/
theorem splitDoubleSquare :
    IsPullback
      (SplitSheaf.Cech.first (SplitSheaf.ofDisplay f) ≫ (SplitSheaf.displayIso f).hom)
      (SplitSheaf.Cech.second (SplitSheaf.ofDisplay f) ≫ (SplitSheaf.displayIso f).hom) f f := by
  apply (SplitSheaf.extension_pullback (SplitSheaf.ofDisplay f)
    (SplitSheaf.p (SplitSheaf.ofDisplay f))).flip.of_iso
      (Iso.refl _) (SplitSheaf.displayIso f) (SplitSheaf.displayIso f) (Iso.refl _)
  · simp
  · simp
  · simpa using (SplitSheaf.displayIso_projection f).symm
  · simpa using (SplitSheaf.displayIso_projection f).symm

def splitDoubleIso : SplitSheaf.Cech.double (SplitSheaf.ofDisplay f) ≅ double f :=
  (splitDoubleSquare f).isoPullback

@[simp, reassoc] theorem splitDouble_first :
    (splitDoubleIso f).hom ≫ first f =
      SplitSheaf.Cech.first (SplitSheaf.ofDisplay f) ≫ (SplitSheaf.displayIso f).hom :=
  (splitDoubleSquare f).isoPullback_hom_fst

@[simp, reassoc] theorem splitDouble_second :
    (splitDoubleIso f).hom ≫ second f =
      SplitSheaf.Cech.second (SplitSheaf.ofDisplay f) ≫ (SplitSheaf.displayIso f).hom :=
  (splitDoubleSquare f).isoPullback_hom_snd

/-- The chosen diagonal is preserved as a map, not merely on sections. -/
theorem splitDouble_diagonal :
    SplitSheaf.Cech.diagonal (SplitSheaf.ofDisplay f) ≫ (splitDoubleIso f).hom =
      (SplitSheaf.displayIso f).hom ≫ diagonal f := by
  apply pullback.hom_ext <;> simp [Category.assoc, ← Category.assoc
    (SplitSheaf.Cech.diagonal (SplitSheaf.ofDisplay f))]

abbrev splitThird : SplitSheaf.Cech.triple (SplitSheaf.ofDisplay f) ⟶
    SplitSheaf.Ext (SplitSheaf.ofDisplay f) :=
  SplitSheaf.lift (SplitSheaf.ofDisplay f)
    (SplitSheaf.Cech.first (SplitSheaf.ofDisplay f) ≫ SplitSheaf.p (SplitSheaf.ofDisplay f))

theorem splitTripleSquare :
    IsPullback
      (SplitSheaf.Cech.firstSecond (SplitSheaf.ofDisplay f) ≫ (splitDoubleIso f).hom)
      (splitThird f ≫ (SplitSheaf.displayIso f).hom) (first f ≫ f) f := by
  apply (SplitSheaf.extension_pullback (SplitSheaf.ofDisplay f)
    (SplitSheaf.Cech.first (SplitSheaf.ofDisplay f) ≫
      SplitSheaf.p (SplitSheaf.ofDisplay f))).flip.of_iso
        (Iso.refl _) (splitDoubleIso f) (SplitSheaf.displayIso f) (Iso.refl _)
  · simp
  · simp
  · simp only [Iso.refl_hom, Category.comp_id, splitDouble_first_assoc,
      SplitSheaf.displayIso_projection]
  · simpa using (SplitSheaf.displayIso_projection f).symm

def splitTripleIso : SplitSheaf.Cech.triple (SplitSheaf.ofDisplay f) ≅ triple f :=
  (splitTripleSquare f).isoPullback

@[simp, reassoc] theorem splitTriple_firstSecond :
    (splitTripleIso f).hom ≫ firstSecond f =
      SplitSheaf.Cech.firstSecond (SplitSheaf.ofDisplay f) ≫ (splitDoubleIso f).hom :=
  (splitTripleSquare f).isoPullback_hom_fst

@[simp, reassoc] theorem splitTriple_third :
    (splitTripleIso f).hom ≫ third f = splitThird f ≫ (SplitSheaf.displayIso f).hom :=
  (splitTripleSquare f).isoPullback_hom_snd

/-- Both selected pair projections are preserved through the triple overlap. -/
theorem splitTriple_firstThird :
    (splitTripleIso f).hom ≫ firstThird f =
      SplitSheaf.Cech.firstThird (SplitSheaf.ofDisplay f) ≫ (splitDoubleIso f).hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, firstThird_first, splitTriple_firstSecond_assoc,
      Category.assoc, splitDouble_first]
    rfl
  · simp only [Category.assoc, firstThird_second, splitTriple_third, splitDouble_second]
    rfl

theorem splitTriple_secondThird :
    (splitTripleIso f).hom ≫ secondThird f =
      SplitSheaf.Cech.secondThird (SplitSheaf.ofDisplay f) ≫ (splitDoubleIso f).hom := by
  apply pullback.hom_ext
  · simp only [Category.assoc, secondThird_first, splitTriple_firstSecond_assoc,
      Category.assoc, splitDouble_second, splitDouble_first]
    rfl
  · simp only [Category.assoc, secondThird_second, splitTriple_third, splitDouble_second]
    rfl

end SquareKit.SheafCoverCech
