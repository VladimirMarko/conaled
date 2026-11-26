import SquareKit.SheafTorsorCocycleClassification
import SquareKit.SheafCoverCech
import SquareKit.SheafFamilyCover

/-! Cocycles as sheaf morphisms on double overlaps, with equations on triple overlaps. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafTorsor.Cocycle
open CategoryTheory Opposite
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{w}} {X : Sheaf J (Type w)} {A : SplitSheaf.Ty X}

/-- The stage labels form a morphism on the actual split double overlap. -/
def Datum.splitLabel (c : Datum G A) : SplitSheaf.Cech.double A ⟶ groupSheaf G := ⟨{
  app U := ↾fun z => c.label (X.obj.elementsMk U z.1.1) z.1.2 z.2
  naturality {U V} f := by
    ext z
    exact (c.natural (ElementFamilies.along X.obj f z.1.1) z.1.2 z.2).symm }⟩

@[simp] theorem Datum.splitLabel_diagonal (c : Datum G A) :
    SplitSheaf.Cech.diagonal A ≫ c.splitLabel = labelOne _ := by
  ext U z
  exact c.identity _ _

theorem Datum.splitLabel_cocycle (c : Datum G A) :
    labelMul (SplitSheaf.Cech.firstSecond A ≫ c.splitLabel)
      (SplitSheaf.Cech.secondThird A ≫ c.splitLabel) =
        SplitSheaf.Cech.firstThird A ≫ c.splitLabel := by
  ext U z
  exact c.cocycle _ _ _ _

/-- An alternative independent presentation uses only overlap morphisms and equations. -/
structure SplitOverlapDatum (G : Sheaf J GrpCat.{w}) (A : SplitSheaf.Ty X) where
  label : SplitSheaf.Cech.double A ⟶ groupSheaf G
  diagonal : SplitSheaf.Cech.diagonal A ≫ label = labelOne _
  cocycle : labelMul (SplitSheaf.Cech.firstSecond A ≫ label)
      (SplitSheaf.Cech.secondThird A ≫ label) = SplitSheaf.Cech.firstThird A ≫ label

@[ext] theorem SplitOverlapDatum.ext (c d : SplitOverlapDatum G A)
    (h : c.label = d.label) : c = d := by
  cases c; cases d; cases h; rfl

def Datum.toSplitOverlap (c : Datum G A) : SplitOverlapDatum G A :=
  ⟨c.splitLabel, c.splitLabel_diagonal, c.splitLabel_cocycle⟩

def SplitOverlapDatum.toDatum (c : SplitOverlapDatum G A) : Datum G A where
  label x a b := c.label.hom.app x.obj ⟨⟨x.val, a⟩, b⟩
  identity x a := congrArg (fun k => k.hom.app x.obj ⟨x.val, a⟩) c.diagonal
  cocycle x a b k := congrArg (fun f => f.hom.app x.obj ⟨⟨⟨x.val, a⟩, b⟩, k⟩) c.cocycle
  natural f a b := labelValue_natural c.label (coverArrow f a) b

def splitOverlapEquiv : Datum G A ≃ SplitOverlapDatum G A where
  toFun := Datum.toSplitOverlap
  invFun := SplitOverlapDatum.toDatum
  left_inv _ := Datum.ext _ _ fun _ _ _ => rfl
  right_inv _ := SplitOverlapDatum.ext _ _ rfl

/-- Gauge compatibility is the usual square on the double overlap. -/
theorem Gauge.overlap_compatible {c d : Datum G A} (g : Gauge c d) :
    labelMul c.splitLabel (SplitSheaf.Cech.second A ≫ g.label) =
      labelMul (SplitSheaf.Cech.first A ≫ g.label) d.splitLabel := by
  ext U z
  exact g.compatible _ _ _

variable {Y : Sheaf J (Type w)} (f : Y ⟶ X)

/-- Cech labels on actual pullbacks. The input contains no descended torsor. -/
structure OverlapDatum where
  label : SheafCoverCech.double f ⟶ groupSheaf G
  diagonal : SheafCoverCech.diagonal f ≫ label = labelOne _
  cocycle : labelMul (SheafCoverCech.firstSecond f ≫ label)
      (SheafCoverCech.secondThird f ≫ label) = SheafCoverCech.firstThird f ≫ label

@[ext] theorem OverlapDatum.ext (c d : OverlapDatum (G := G) f)
    (h : c.label = d.label) : c = d := by
  cases c; cases d; cases h; rfl

namespace OverlapDatum

def toSplit (c : OverlapDatum (G := G) f) : SplitOverlapDatum G (SplitSheaf.ofDisplay f) where
  label := (SheafCoverCech.splitDoubleIso f).hom ≫ c.label
  diagonal := by
    rw [← Category.assoc, SheafCoverCech.splitDoubleIso_diagonal, Category.assoc, c.diagonal]
    rfl
  cocycle := by
    have h := congrArg (fun k => (SheafCoverCech.splitTripleIso f).hom ≫ k) c.cocycle
    simp only [labelMul_precomp, ← Category.assoc] at h
    rw [SheafCoverCech.splitTripleIso_firstSecond, SheafCoverCech.splitTripleIso_secondThird,
      SheafCoverCech.splitTripleIso_firstThird] at h
    simpa only [Category.assoc] using h

def ofSplit (c : SplitOverlapDatum G (SplitSheaf.ofDisplay f)) : OverlapDatum (G := G) f where
  label := (SheafCoverCech.splitDoubleIso f).inv ≫ c.label
  diagonal := by
    apply (cancel_epi (SplitSheaf.displayIso f).hom).mp
    rw [← Category.assoc, ← SheafCoverCech.splitDoubleIso_diagonal, Category.assoc,
      Iso.hom_inv_id_assoc, c.diagonal]
    rfl
  cocycle := by
    apply (cancel_epi (SheafCoverCech.splitTripleIso f).hom).mp
    simp only [labelMul_precomp, ← Category.assoc]
    rw [SheafCoverCech.splitTripleIso_firstSecond, SheafCoverCech.splitTripleIso_secondThird,
      SheafCoverCech.splitTripleIso_firstThird]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using c.cocycle

end OverlapDatum

/-- The stage and actual-pullback presentations recover each other's labels exactly. -/
def overlapEquiv : Datum G (SplitSheaf.ofDisplay f) ≃ OverlapDatum (G := G) f :=
  splitOverlapEquiv.trans {
    toFun := OverlapDatum.ofSplit f
    invFun := OverlapDatum.toSplit f
    left_inv c := by apply SplitOverlapDatum.ext; simp [OverlapDatum.toSplit, OverlapDatum.ofSplit]
    right_inv c := by apply OverlapDatum.ext; simp [OverlapDatum.toSplit, OverlapDatum.ofSplit] }

/-- Admission on an ordinary sheaf map is a property, not a chosen trivialization. -/
def AdmitsCover (P : Torsor G X) : Prop :=
  Nonempty (Arrow (SheafTorsor.trivial G Y) (reindex P f))

theorem admitsCover_iff_split (P : Torsor G X) :
    AdmitsCover f P ↔ Nonempty (Arrow (SheafTorsor.trivial G (SplitSheaf.extension (SplitSheaf.ofDisplay f)))
      (reindex P (SplitSheaf.p (SplitSheaf.ofDisplay f)))) := by
  constructor
  · rintro ⟨e⟩
    have h := e.reindex (SplitSheaf.displayIso f).hom
    change Arrow (SheafTorsor.trivial G _) (reindex P ((SplitSheaf.displayIso f).hom ≫ f)) at h
    rw [SplitSheaf.displayIso_projection] at h
    exact ⟨h⟩
  · rintro ⟨e⟩
    have h := e.reindex (SplitSheaf.displayIso f).inv
    change Arrow (SheafTorsor.trivial G Y)
      (reindex P ((SplitSheaf.displayIso f).inv ≫ SplitSheaf.p (SplitSheaf.ofDisplay f))) at h
    rw [← SplitSheaf.displayIso_projection, Iso.inv_hom_id_assoc] at h
    exact ⟨h⟩

section Family
open CategoryTheory.Limits
variable {G : Sheaf J GrpCat.{max u v}} {X : Sheaf J (Type (max u v))}
variable {I : Type (max u v)} {Y : I → Sheaf J (Type (max u v))}
variable (f : ∀ i, Y i ⟶ X)

/-- Componentwise admission is exactly admission on the categorical coproduct cover.
This also covers an empty index type. -/
theorem admitsCover_family (P : Torsor G X) :
    AdmitsCover (Sigma.desc f) P ↔ ∀ i, AdmitsCover (f i) P := by
  constructor
  · rintro ⟨e⟩ i
    have h := e.reindex (Sigma.ι Y i)
    change Arrow (SheafTorsor.trivial G (Y i)) (reindex P (Sigma.ι Y i ≫ Sigma.desc f)) at h
    rw [Sigma.ι_comp_desc] at h
    exact ⟨h⟩
  · intro h
    let t (i : I) := sectionOfArrow (h i).some
    let k : (∐ Y) ⟶ SplitSheaf.extension P.family := Sigma.desc (fun i => SplitSheaf.pair P.family (f i) (t i))
    have hk : k ≫ SplitSheaf.p P.family = Sigma.desc f := by
      apply Sigma.hom_ext
      intro i
      simp only [k, ← Category.assoc, Sigma.ι_comp_desc, SplitSheaf.pair_p]
    exact ⟨ofSection (reindex P (Sigma.desc f)) (SplitSheaf.readTerm P.family k hk)⟩

end Family
end SquareKit.SheafTorsor.Cocycle
