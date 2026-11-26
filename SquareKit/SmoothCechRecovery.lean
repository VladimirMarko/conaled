import SquareKit.SmoothCechExtraction
import SquareKit.SheafTorsorLocalIso
import Mathlib.CategoryTheory.HomCongr

/-! Recover actual quotient objects from represented local trivializations. -/
noncomputable section
open scoped Manifold ContDiff
namespace SquareKit.SmoothCech
open CategoryTheory CategoryTheory.Limits Opposite EuclideanOpen SmoothOpenSite
open SmoothRepresentedCover SmoothManifoldAction ManifoldRealization SheafActionQuotient
variable {X : Sheaf topology Type} {I : Type} (A : Atlas X I)
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))

/-- Admission asks for equivariant chart trivializations of the actual torsor.
No global section or quotient comparison is an input. -/
structure TrivializedOn (P : Object (representation smoothAction).action X) where
  trivialization : ∀ i, SheafTorsor.Arrow
    (SheafTorsor.trivial (locallyConstantGroup G) (embedding.obj (A.domain i)))
    (SheafTorsor.reindex P.torsor (A.chart i))

/-- Conjugate canonical descent through an actual local quotient isomorphism.
The cocycle is derived from cancellation of that isomorphism. -/
def descentOfLocalIso {B : SplitSheaf.Ty X}
    (P : Object (representation smoothAction).action X)
    (Q : Object (representation smoothAction).action (SplitSheaf.extension B))
    (e : SheafActionQuotient.Arrow Q (reindex P (SplitSheaf.p B))) :
    Descent.Datum (a := (representation smoothAction).action) B :=
  Descent.ofLocalIso P Q e

def descentOfLocalIsoMap {B : SplitSheaf.Ty X}
    (P : Object (representation smoothAction).action X)
    (Q : Object (representation smoothAction).action (SplitSheaf.extension B))
    (e : SheafActionQuotient.Arrow Q (reindex P (SplitSheaf.p B))) :
    Descent.Map (descentOfLocalIso smoothAction P Q e) (Descent.canonicalDatum B P) :=
  Descent.ofLocalIsoMap P Q e

/-- A selected global recovery isomorphism, constructed through effective descent. -/
def descentOfLocalIsoRecovery {B : SplitSheaf.Ty X}
    [Presheaf.IsLocallySurjective topology (SplitSheaf.p B).hom]
    (P : Object (representation smoothAction).action X)
    (Q : Object (representation smoothAction).action (SplitSheaf.extension B))
    (e : SheafActionQuotient.Arrow Q (reindex P (SplitSheaf.p B))) :
    SheafActionQuotient.Arrow (descentOfLocalIso smoothAction P Q e).object P :=
  Descent.ofLocalIsoRecovery P Q e

namespace TrivializedOn
variable {A smoothAction} {P : Object (representation smoothAction).action X}
variable (t : TrivializedOn A smoothAction P)

def sectionMap : A.total ⟶ SplitSheaf.extension P.torsor.family :=
  SheafCoproductLocal.desc A.family (fun i => SplitSheaf.pair P.torsor.family (A.chart i)
    (SheafTorsor.sectionOfArrow (t.trivialization i)))

theorem sectionMap_projection : t.sectionMap ≫ SplitSheaf.p P.torsor.family = A.cover := by
  apply colimit.hom_ext
  intro ⟨i⟩
  change A.inclusion i ≫ _ = A.inclusion i ≫ _
  rw [← Category.assoc, sectionMap, SheafCoproductLocal.inclusion_desc]
  erw [SplitSheaf.pair_p]
  exact (A.inclusion_cover i).symm

/-- The section is on the coproduct cover, not on the original parameter. -/
def localSection : SplitSheaf.Tm (SheafTorsor.reindex P.torsor A.cover).family :=
  SplitSheaf.readTerm P.torsor.family t.sectionMap t.sectionMap_projection

def regularization : SheafActionQuotient.Arrow
    (chart (representation smoothAction).action ((reindex P A.cover).sectionMap t.localSection))
    (reindex P A.cover) where
  torsorArrow := SheafTorsor.ofSection (SheafTorsor.reindex P.torsor A.cover) t.localSection
  preserves x g := (reindex P A.cover).equivariant x g (t.localSection.val x)


/-- The actual local value map reconstructs a smooth map by full faithfulness. -/
def localMap (i : I) : External.SmoothMap (A.domain i) d M :=
  ⟨ManifoldRealization.reconstruct ((principalIso (A.domain i)).hom ≫
    (reindex P (A.chart i)).sectionMap (SheafTorsor.sectionOfArrow (t.trivialization i))),
    ManifoldRealization.reconstruct_smooth _⟩

theorem localMap_hat (i : I) : hat (t.localMap i).val (t.localMap i).property =
    (reindex P (A.chart i)).sectionMap (SheafTorsor.sectionOfArrow (t.trivialization i)) := by
  unfold localMap hat
  rw [ManifoldRealization.map_reconstruct, Iso.inv_hom_id_assoc]

theorem localValue_factorization :
    (reindex P A.cover).sectionMap t.localSection = t.sectionMap ≫ P.totalMap := by
  change SplitSheaf.pair P.torsor.family A.cover t.localSection ≫ P.totalMap = _
  rw [localSection, SplitSheaf.pair_read]

theorem localValue_chart (i : I) :
    A.inclusion i ≫ (reindex P A.cover).sectionMap t.localSection =
      hat (t.localMap i).val (t.localMap i).property := by
  rw [localValue_factorization, ← Category.assoc, sectionMap,
    SheafCoproductLocal.inclusion_desc, localMap_hat]
  rfl

/-- All reconstructed smooth maps assemble to the actual chosen local value map. -/
theorem localValue_assembled :
    SheafCoproductLocal.desc A.family (fun i => hat (t.localMap i).val (t.localMap i).property) =
      (reindex P A.cover).sectionMap t.localSection := by
  apply colimit.hom_ext
  intro ⟨i⟩
  change A.inclusion i ≫ _ = A.inclusion i ≫ _
  rw [SheafCoproductLocal.inclusion_desc, localValue_chart]

def splitRegularization : SheafActionQuotient.Arrow
    (chart (representation smoothAction).action
      ((SplitSheaf.displayIso A.cover).hom ≫ (reindex P A.cover).sectionMap t.localSection))
    (reindex P (SplitSheaf.p (SplitSheaf.ofDisplay A.cover))) :=
  (t.regularization.reindex (SplitSheaf.displayIso A.cover).hom).comp
    (eqToHom (congrArg (reindex P) (SplitSheaf.displayIso_projection A.cover)))

/-- Canonical descent expressed through the actually chosen cover trivialization. -/
def regularDescent : Descent.Datum (a := (representation smoothAction).action)
    (SplitSheaf.ofDisplay A.cover) :=
  descentOfLocalIso smoothAction P _ t.splitRegularization

/-- Recovery includes the chosen equivariant value map, not only the torsor. -/
def recovery : SheafActionQuotient.Arrow t.regularDescent.object P :=
  descentOfLocalIsoRecovery smoothAction P _ t.splitRegularization

/-- The regularized local object is the realization of the extracted smooth maps. -/
theorem regularDescent_localObject : (Cech.ofDescent t.regularDescent).localObject =
    chart (representation smoothAction).action
      ((SplitSheaf.displayIso A.cover).hom ≫ assembledMap t.localMap) := by
  change chart _ (_ ≫ (reindex P A.cover).sectionMap t.localSection) = _
  rw [← t.localValue_assembled]

/-- Extract independent ordinary maps and transitions from the admitted object. -/
def extractedDatum : Datum (d := d) (G := G) (M := M) A :=
  (RegularLabels.fromCech smoothAction (Cech.ofDescent t.regularDescent)
    t.regularDescent_localObject).datum smoothAction

theorem extractedDatum_cech : t.extractedDatum.cech smoothAction =
    Cech.ofDescent t.regularDescent :=
  RegularLabels.fromCech_roundtrip smoothAction _ _

theorem extractedDatum_descent : (t.extractedDatum.cech smoothAction).toDescent =
    t.regularDescent := by
  rw [t.extractedDatum_cech, Cech.toDescent_ofDescent]

/-- Selected recovery of the interpreted external datum, including its value map. -/
def extractedRecovery : SheafActionQuotient.Arrow
    (t.extractedDatum.interpreted smoothAction) P :=
  (eqToHom (congrArg (fun z =>
    (Descent.displayDescentEquivalence (representation smoothAction).action A.cover).functor.obj z)
    t.extractedDatum_descent)).comp t.recovery

variable {Q : Object (representation smoothAction).action X}

/-- All arrows between the admitted objects correspond to full external families. -/
def arrowEquiv (u : TrivializedOn A smoothAction Q) :
    Hom t.extractedDatum u.extractedDatum ≃ SheafActionQuotient.Arrow P Q :=
  (interpretedHomEquiv smoothAction _ _).trans
    (CategoryTheory.Iso.homCongr t.extractedRecovery.toIso u.extractedRecovery.toIso)

def extractArrow (u : TrivializedOn A smoothAction Q) (f : SheafActionQuotient.Arrow P Q) :
    Hom t.extractedDatum u.extractedDatum := (t.arrowEquiv u).symm f

theorem arrow_roundtrip (u : TrivializedOn A smoothAction Q)
    (f : SheafActionQuotient.Arrow P Q) : t.arrowEquiv u (t.extractArrow u f) = f :=
  (t.arrowEquiv u).apply_symm_apply f

theorem external_arrow_roundtrip (u : TrivializedOn A smoothAction Q)
    (f : Hom t.extractedDatum u.extractedDatum) :
    t.extractArrow u (t.arrowEquiv u f) = f := (t.arrowEquiv u).symm_apply_apply f

/-- The chosen recovery commutes with the actual input arrow. -/
theorem recovery_naturality (u : TrivializedOn A smoothAction Q)
    (f : SheafActionQuotient.Arrow P Q) :
    (interpretedHomEquiv smoothAction _ _ (t.extractArrow u f)).comp u.extractedRecovery =
      t.extractedRecovery.comp f := by
  have h := t.arrow_roundtrip u f
  change t.extractedRecovery.toIso.inv ≫
    (interpretedHomEquiv smoothAction _ _ (t.extractArrow u f)) ≫
      u.extractedRecovery.toIso.hom = f at h
  have hh := congrArg (fun z => t.extractedRecovery.toIso.hom ≫ z) h
  rw [Iso.hom_inv_id_assoc] at hh
  exact hh

theorem arrowEquiv_ident : t.arrowEquiv t (Hom.ident t.extractedDatum) =
    SheafActionQuotient.Arrow.ident P := by
  have hi : CategoryTheory.Iso.homCongr t.extractedRecovery.toIso
      t.extractedRecovery.toIso (𝟙 _) = 𝟙 P := by simp
  exact (congrArg (CategoryTheory.Iso.homCongr t.extractedRecovery.toIso
    t.extractedRecovery.toIso) ((interpretation smoothAction).map_id t.extractedDatum)).trans hi

theorem arrowEquiv_comp {R : Object (representation smoothAction).action X}
    (u : TrivializedOn A smoothAction Q) (v : TrivializedOn A smoothAction R)
    (f : Hom t.extractedDatum u.extractedDatum) (g : Hom u.extractedDatum v.extractedDatum) :
    t.arrowEquiv v (f.comp g) = (t.arrowEquiv u f).comp (u.arrowEquiv v g) := by
  exact (congrArg (CategoryTheory.Iso.homCongr t.extractedRecovery.toIso
    v.extractedRecovery.toIso) ((interpretation smoothAction).map_comp f g)).trans
      (CategoryTheory.Iso.homCongr_comp t.extractedRecovery.toIso u.extractedRecovery.toIso
        v.extractedRecovery.toIso ((interpretation smoothAction).map f)
        ((interpretation smoothAction).map g))

theorem extractArrow_ident : t.extractArrow t (SheafActionQuotient.Arrow.ident P) =
    Hom.ident t.extractedDatum := by
  apply (t.arrowEquiv t).injective
  rw [t.arrow_roundtrip, t.arrowEquiv_ident]

theorem extractArrow_comp {R : Object (representation smoothAction).action X}
    (u : TrivializedOn A smoothAction Q) (v : TrivializedOn A smoothAction R)
    (f : SheafActionQuotient.Arrow P Q) (g : SheafActionQuotient.Arrow Q R) :
    t.extractArrow v (f.comp g) = (t.extractArrow u f).comp (u.extractArrow v g) := by
  apply (t.arrowEquiv v).injective
  rw [t.arrow_roundtrip, t.arrowEquiv_comp, t.arrow_roundtrip, u.arrow_roundtrip]

end TrivializedOn
end SquareKit.SmoothCech

open scoped Manifold ContDiff
namespace SquareKit.SmoothCech
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothManifoldAction SheafActionQuotient ManifoldRealization
variable {X : Sheaf topology Type} {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))

/-- Restricting the chosen global recovery gives precisely the local isomorphism
following the effective-descent comparison. -/
theorem descentOfLocalIsoRecovery_reindex {B : SplitSheaf.Ty X}
    [Presheaf.IsLocallySurjective topology (SplitSheaf.p B).hom]
    (P : Object (representation smoothAction).action X)
    (Q : Object (representation smoothAction).action (SplitSheaf.extension B))
    (e : Arrow Q (reindex P (SplitSheaf.p B))) :
    (descentOfLocalIsoRecovery smoothAction P Q e).reindex (SplitSheaf.p B) =
      (descentOfLocalIso smoothAction P Q e).comparison.comp e :=
  Descent.ofLocalIsoRecovery_reindex P Q e
namespace TrivializedOn
variable {I : Type} {A : SmoothRepresentedCover.Atlas X I}
variable {smoothAction} {P : Object (representation smoothAction).action X}
variable (t : TrivializedOn A smoothAction P)

/-- The extracted descent comparison recovers the chosen local regularization,
including the value map. The equality arrow records the checked extraction
round trip. -/
theorem extractedRecovery_reindex :
    t.extractedRecovery.reindex (SplitSheaf.p (SplitSheaf.ofDisplay A.cover)) =
      (t.extractedDatum.cech smoothAction).toDescent.comparison.comp
        ((eqToHom (congrArg (fun z : Descent.Datum (a := (representation smoothAction).action) (SplitSheaf.ofDisplay A.cover) => z.localObject) t.extractedDatum_descent)).comp
          t.splitRegularization) := by
  have ht {c e : Descent.Datum (a := (representation smoothAction).action)
      (SplitSheaf.ofDisplay A.cover)} (h : c = e) :
      ((eqToHom (congrArg (fun z : Descent.Datum (a := (representation smoothAction).action) (SplitSheaf.ofDisplay A.cover) => z.object) h)).reindex
        (SplitSheaf.p (SplitSheaf.ofDisplay A.cover))).comp e.comparison =
      c.comparison.comp (eqToHom (congrArg (fun z : Descent.Datum (a := (representation smoothAction).action) (SplitSheaf.ofDisplay A.cover) => z.localObject) h)) := by
    cases h
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    rfl
  change ((eqToHom (congrArg (fun z : Descent.Datum (a := (representation smoothAction).action) (SplitSheaf.ofDisplay A.cover) => z.object) t.extractedDatum_descent)).reindex
    (SplitSheaf.p (SplitSheaf.ofDisplay A.cover))).comp
      (t.recovery.reindex (SplitSheaf.p (SplitSheaf.ofDisplay A.cover))) = _
  rw [show t.recovery.reindex (SplitSheaf.p (SplitSheaf.ofDisplay A.cover)) =
      t.regularDescent.comparison.comp t.splitRegularization from
    descentOfLocalIsoRecovery_reindex smoothAction P _ t.splitRegularization]
  have hh := congrArg (fun z => z.comp t.splitRegularization) (ht t.extractedDatum_descent)
  exact hh
/-- Extraction preserves the actual conjugated overlap arrow; value-map
reconstruction introduces no new transition choices. -/
theorem extractedDatum_overlapLabel :
    t.extractedDatum.overlapLabel smoothAction =
      (SheafCoverCech.splitDoubleIso A.cover).inv ≫
        arrowLabel (a := (representation smoothAction).action)
          (m := SplitSheaf.Cech.first _ ≫ ((SplitSheaf.displayIso A.cover).hom ≫ (reindex P A.cover).sectionMap t.localSection))
          (n := SplitSheaf.Cech.second _ ≫ ((SplitSheaf.displayIso A.cover).hom ≫ (reindex P A.cover).sectionMap t.localSection))
          (Cech.ofDescent t.regularDescent).overlap.hom := by
  have aux (v : SplitSheaf.extension (SplitSheaf.ofDisplay A.cover) ⟶
      ManifoldRealization.object d M)
      (e : Arrow (chart (representation smoothAction).action v)
        (reindex P (SplitSheaf.p (SplitSheaf.ofDisplay A.cover))))
      (h : v = (SplitSheaf.displayIso A.cover).hom ≫ assembledMap t.localMap) :
      (RegularLabels.fromCech smoothAction
        (Cech.ofDescent (descentOfLocalIso smoothAction P _ e))
        (congrArg (chart (representation smoothAction).action) h)).label =
      (SheafCoverCech.splitDoubleIso A.cover).inv ≫
        arrowLabel (a := (representation smoothAction).action)
          (m := SplitSheaf.Cech.first _ ≫ v) (n := SplitSheaf.Cech.second _ ≫ v)
          (Cech.ofDescent (descentOfLocalIso smoothAction P _ e)).overlap.hom := by
    cases h
    rfl
  rw [extractedDatum, RegularLabels.datum_label]
  exact aux _ t.splitRegularization (congrArg
    (fun v => (SplitSheaf.displayIso A.cover).hom ≫ v) t.localValue_assembled.symm)

/-- A forward ordinary transition is the inverse of the actual regular-torsor
transport label. -/
theorem extractedDatum_transition_apply (i j : I) (x : Points (A.pair i j)) :
    (t.extractedDatum.transition i j).val x =
      (ordinaryHomLabelEquiv G (A.pair i j)
        (A.pairMap i j ≫ ((SheafCoverCech.splitDoubleIso A.cover).inv ≫
          arrowLabel (a := (representation smoothAction).action)
            (m := SplitSheaf.Cech.first _ ≫ ((SplitSheaf.displayIso A.cover).hom ≫
              (reindex P A.cover).sectionMap t.localSection))
            (n := SplitSheaf.Cech.second _ ≫ ((SplitSheaf.displayIso A.cover).hom ≫
              (reindex P A.cover).sectionMap t.localSection))
            (Cech.ofDescent t.regularDescent).overlap.hom)) x)⁻¹ := by
  let k := RegularLabels.fromCech smoothAction (Cech.ofDescent t.regularDescent)
    t.regularDescent_localObject
  change (k.transition smoothAction i j).val x = _
  rw [RegularLabels.transition_apply]
  have h := (k.datum_label smoothAction).symm.trans t.extractedDatum_overlapLabel
  rw [h]

/-- The selected section restricts to the section of the supplied chart
trivialization, as an equality in the actual total sheaf. -/
theorem localSection_chart (i : I) :
    A.inclusion i ≫ SplitSheaf.pair P.torsor.family A.cover t.localSection =
      SplitSheaf.pair P.torsor.family (A.chart i)
        (SheafTorsor.sectionOfArrow (t.trivialization i)) := by
  rw [localSection, SplitSheaf.pair_read, sectionMap, SheafCoproductLocal.inclusion_desc]

/-- The regularization on every chart is the supplied trivialization at every
group element, expressed in the total sheaf to retain the actual base point. -/
theorem regularization_chart_apply (i : I) (U : SmoothPresentationSite.Siteᵒᵖ)
    (x : (embedding.obj (A.domain i)).obj.obj U)
    (g : (locallyConstantGroup G).obj.obj U) :
    (⟨A.cover.hom.app U ((A.inclusion i).hom.app U x),
      t.regularization.torsorArrow.iso.hom.app
        (A.total.obj.elementsMk U ((A.inclusion i).hom.app U x)) g⟩ :
      (SplitSheaf.extension P.torsor.family).obj.obj U) =
    ⟨(A.chart i).hom.app U x,
      (t.trivialization i).iso.hom.app ((embedding.obj (A.domain i)).obj.elementsMk U x) g⟩ := by
  have h := congrArg (fun k => k.hom.app U x) (t.localSection_chart i)
  have hh := congrArg (fun z : (SplitSheaf.extension P.torsor.family).obj.obj U =>
    (⟨z.1, P.torsor.act (X.obj.elementsMk U z.1) g z.2⟩ :
      (SplitSheaf.extension P.torsor.family).obj.obj U)) h
  change (⟨_, _⟩ : (SplitSheaf.extension P.torsor.family).obj.obj U) =
    ⟨_, P.torsor.act _ g ((t.trivialization i).iso.hom.app ((embedding.obj (A.domain i)).obj.elementsMk U x) (1 : (locallyConstantGroup G).obj.obj U))⟩ at hh
  have he := (t.trivialization i).equivariant
    ((embedding.obj (A.domain i)).obj.elementsMk U x) g (1 : (locallyConstantGroup G).obj.obj U)
  change (t.trivialization i).iso.hom.app ((embedding.obj (A.domain i)).obj.elementsMk U x) (g * (1 : (locallyConstantGroup G).obj.obj U)) = _ at he
  rw [mul_one] at he
  exact hh.trans (congrArg (fun z =>
    (⟨(A.chart i).hom.app U x, z⟩ : (SplitSheaf.extension P.torsor.family).obj.obj U)) he.symm)

/-- Passing from the coproduct cover to its split display changes only its
presentation; the selected regularization has the same actual total value. -/
theorem splitRegularization_apply (U : SmoothPresentationSite.Siteᵒᵖ)
    (z : (SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.obj U)
    (g : (locallyConstantGroup G).obj.obj U) :
    (⟨(SplitSheaf.p (SplitSheaf.ofDisplay A.cover)).hom.app U z,
      t.splitRegularization.torsorArrow.iso.hom.app
        ((SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U z) g⟩ :
      (SplitSheaf.extension P.torsor.family).obj.obj U) =
    ⟨A.cover.hom.app U ((SplitSheaf.displayIso A.cover).hom.hom.app U z),
      t.regularization.torsorArrow.iso.hom.app
        (A.total.obj.elementsMk U ((SplitSheaf.displayIso A.cover).hom.hom.app U z)) g⟩ := by
  have aux {Y : Sheaf topology Type} (f k : Y ⟶ X) (h : f = k)
      (z : Y.obj.obj U)
      (q : (reindex P f).torsor.family.family.obj (Y.obj.elementsMk U z)) :
      (⟨k.hom.app U z,
        (eqToHom (congrArg (reindex P) h)).torsorArrow.iso.hom.app
          (Y.obj.elementsMk U z) q⟩ : (SplitSheaf.extension P.torsor.family).obj.obj U) =
        ⟨f.hom.app U z, q⟩ := by
    cases h
    rfl
  exact aux _ _ (SplitSheaf.displayIso_projection A.cover) z
    (t.regularization.torsorArrow.iso.hom.app
      (A.total.obj.elementsMk U ((SplitSheaf.displayIso A.cover).hom.hom.app U z)) g)

/-- The extraction round-trip equality has no effect on regular-torsor
coordinates. -/
theorem extractedLocalRegularization_apply (U : SmoothPresentationSite.Siteᵒᵖ)
    (z : (SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.obj U)
    (g : (locallyConstantGroup G).obj.obj U) :
    ((eqToHom (congrArg
      (fun c : Descent.Datum (a := (representation smoothAction).action)
        (SplitSheaf.ofDisplay A.cover) => c.localObject)
      t.extractedDatum_descent)).comp t.splitRegularization).torsorArrow.iso.hom.app
        ((SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U z) g =
      t.splitRegularization.torsorArrow.iso.hom.app
        ((SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U z) g := by
  have aux (v w : SplitSheaf.extension (SplitSheaf.ofDisplay A.cover) ⟶
      ManifoldRealization.object d M) (h : v = w)
      (e : Arrow (chart (representation smoothAction).action w)
        (reindex P (SplitSheaf.p (SplitSheaf.ofDisplay A.cover)))) :
      ((eqToHom (congrArg (chart (representation smoothAction).action) h)).comp e).torsorArrow.iso.hom.app
        ((SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U z) g =
      e.torsorArrow.iso.hom.app
        ((SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U z) g := by
    cases h
    rfl
  exact aux _ _ (congrArg (fun v => (SplitSheaf.displayIso A.cover).hom ≫ v)
    t.localValue_assembled) t.splitRegularization

/-- Recovering an extracted object after the inverse local descent comparison
returns exactly the chosen split-cover trivialization. -/
theorem extractedRecovery_comparison_apply (U : SmoothPresentationSite.Siteᵒᵖ)
    (z : (SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.obj U)
    (g : (locallyConstantGroup G).obj.obj U) :
    t.extractedRecovery.torsorArrow.iso.hom.app
      (X.obj.elementsMk U ((SplitSheaf.p (SplitSheaf.ofDisplay A.cover)).hom.app U z))
      ((t.extractedDatum.cech smoothAction).toDescent.comparison.torsorArrow.iso.inv.app
        ((SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U z) g) =
      t.splitRegularization.torsorArrow.iso.hom.app
        ((SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U z) g := by
  let c := (t.extractedDatum.cech smoothAction).toDescent.comparison
  let y := (SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U z
  have h := congrArg (fun e => e.torsorArrow.iso.hom.app y (c.torsorArrow.iso.inv.app y g))
    t.extractedRecovery_reindex
  have hc := congrArg (fun k => k.app y g) c.torsorArrow.iso.inv_hom_id
  change c.torsorArrow.iso.hom.app y (c.torsorArrow.iso.inv.app y g) = g at hc
  change _ = ((eqToHom (congrArg
      (fun q : Descent.Datum (a := (representation smoothAction).action)
        (SplitSheaf.ofDisplay A.cover) => q.localObject)
      t.extractedDatum_descent)).comp t.splitRegularization).torsorArrow.iso.hom.app y
      (c.torsorArrow.iso.hom.app y (c.torsorArrow.iso.inv.app y g)) at h
  rw [hc] at h
  exact h.trans (t.extractedLocalRegularization_apply U z g)

/-- On each represented chart, descent followed by the selected recovery is
exactly the supplied trivialization, at every stage and every group element. -/
theorem extractedRecovery_chart_apply (i : I) (U : SmoothPresentationSite.Siteᵒᵖ)
    (x : (embedding.obj (A.domain i)).obj.obj U)
    (g : (locallyConstantGroup G).obj.obj U) :
    let z := (SplitSheaf.displayIso A.cover).inv.hom.app U ((A.inclusion i).hom.app U x)
    (⟨(SplitSheaf.p (SplitSheaf.ofDisplay A.cover)).hom.app U z,
      t.extractedRecovery.torsorArrow.iso.hom.app
        (X.obj.elementsMk U ((SplitSheaf.p (SplitSheaf.ofDisplay A.cover)).hom.app U z))
        ((t.extractedDatum.cech smoothAction).toDescent.comparison.torsorArrow.iso.inv.app
          ((SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U z) g)⟩ :
      (SplitSheaf.extension P.torsor.family).obj.obj U) =
    ⟨(A.chart i).hom.app U x,
      (t.trivialization i).iso.hom.app ((embedding.obj (A.domain i)).obj.elementsMk U x) g⟩ := by
  dsimp only
  let z := (SplitSheaf.displayIso A.cover).inv.hom.app U ((A.inclusion i).hom.app U x)
  have hr := congrArg (fun q =>
    (⟨(SplitSheaf.p (SplitSheaf.ofDisplay A.cover)).hom.app U z, q⟩ :
      (SplitSheaf.extension P.torsor.family).obj.obj U)) (t.extractedRecovery_comparison_apply U z g)
  have hs := t.splitRegularization_apply U z g
  have hi := congrArg (fun k => k.hom.app U ((A.inclusion i).hom.app U x))
    (SplitSheaf.displayIso A.cover).inv_hom_id
  change (SplitSheaf.displayIso A.cover).hom.hom.app U z = (A.inclusion i).hom.app U x at hi
  rw [hi] at hs
  exact hr.trans (hs.trans (t.regularization_chart_apply i U x g))

/-- Extraction preserves the selected inverse arrow as a complete family. -/
theorem extractArrow_inverse {Q : Object (representation smoothAction).action X}
    (u : TrivializedOn A smoothAction Q) (f : SheafActionQuotient.Arrow P Q) :
    u.extractArrow t f.inverse = (t.extractArrow u f).inverse := by
  have h : f.comp f.inverse = SheafActionQuotient.Arrow.ident P := by
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    exact f.torsorArrow.iso.hom_inv_id
  have he : (t.extractArrow u f).comp (u.extractArrow t f.inverse) =
      Hom.ident t.extractedDatum := by
    rw [← t.extractArrow_comp u t, h, t.extractArrow_ident]
  have hh := congrArg (fun z => (t.extractArrow u f).inverse.comp z) he
  rw [← Hom.comp_assoc, Hom.inverse_comp, Hom.ident_comp, Hom.comp_ident] at hh
  exact hh


end TrivializedOn
end SquareKit.SmoothCech

noncomputable section
open scoped Manifold ContDiff
namespace SquareKit.SmoothCech
open CategoryTheory CategoryTheory.Limits Opposite EuclideanOpen SmoothOpenSite
open SmoothRepresentedCover SmoothManifoldAction ManifoldRealization SheafActionQuotient
variable {X : Sheaf topology Type} {I : Type} {A : Atlas X I}
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
variable {smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x)}
private theorem descentArrow_inverse
    {q r : Descent.Datum (a := (representation smoothAction).action) (SplitSheaf.ofDisplay A.cover)}
    (h : Descent.Map q r) :
    (Descent.Map.arrow (inv (C := Descent.Datum (a := (representation smoothAction).action)
      (SplitSheaf.ofDisplay A.cover)) h)) = h.arrow.inverse := by
  have hi := (Descent.descentFunctor (representation smoothAction).action
    (SplitSheaf.ofDisplay A.cover)).map_inv h
  exact hi.trans (Groupoid.inv_eq_inv (C := Object (representation smoothAction).action X) h.arrow).symm

private theorem inverse_comp_arrow {P Q R : Object (representation smoothAction).action X}
    (f : Arrow P Q) (g : Arrow Q R) : (f.comp g).inverse = g.inverse.comp f.inverse := by
  change Groupoid.inv (obj := Object (representation smoothAction).action X) (f ≫ g) =
    Groupoid.inv (obj := Object (representation smoothAction).action X) g ≫
      Groupoid.inv (obj := Object (representation smoothAction).action X) f
  simp only [Groupoid.inv_eq_inv, IsIso.inv_comp]

private theorem comp_assoc_arrow {P Q R S : Object (representation smoothAction).action X}
    (f : Arrow P Q) (g : Arrow Q R) (h : Arrow R S) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  Category.assoc (obj := Object (representation smoothAction).action X) f g h

namespace TrivializedOn
variable {P : Object (representation smoothAction).action X}
variable (t : TrivializedOn A smoothAction P)
/-- The extracted local datum maps to canonical descent through its actual
regularization, before either datum is descended. -/
def canonicalDescentMap : Descent.Map
    (t.extractedDatum.cech smoothAction).toDescent
    (Descent.canonicalDatum (SplitSheaf.ofDisplay A.cover) P) :=
  eqToHom t.extractedDatum_descent ≫
    descentOfLocalIsoMap smoothAction P _ t.splitRegularization

/-- The existing selected canonical recovery gives exactly extractedRecovery
through the constructed local comparison. -/
theorem canonicalDescentMap_recovery :
    t.canonicalDescentMap.arrow.comp
      (Descent.canonicalRecovery (SplitSheaf.ofDisplay A.cover) P) = t.extractedRecovery := by
  change (Descent.descentFunctor (representation smoothAction).action
    (SplitSheaf.ofDisplay A.cover)).map
      (eqToHom t.extractedDatum_descent ≫
        descentOfLocalIsoMap smoothAction P _ t.splitRegularization) ≫ _ = _
  erw [Functor.map_comp, eqToHom_map]
  rfl

/-- Compare an external arrow with canonical descent by composing actual local
maps; no global recovered arrow is an input to this construction. -/
def canonicalArrowMap {Q : Object (representation smoothAction).action X}
    (u : TrivializedOn A smoothAction Q) (f : Hom t.extractedDatum u.extractedDatum) :
    Descent.Map (Descent.canonicalDatum (SplitSheaf.ofDisplay A.cover) P)
      (Descent.canonicalDatum (SplitSheaf.ofDisplay A.cover) Q) :=
  Descent.Map.comp (Descent.Map.comp
    (inv (C := Descent.Datum (a := (representation smoothAction).action)
      (SplitSheaf.ofDisplay A.cover)) t.canonicalDescentMap)
    (f.cechMap smoothAction).toDescent) u.canonicalDescentMap

theorem canonicalArrowMap_agreement {Q : Object (representation smoothAction).action X}
    (u : TrivializedOn A smoothAction Q) (f : Hom t.extractedDatum u.extractedDatum) :
    Descent.canonicalArrowEquiv (SplitSheaf.ofDisplay A.cover) P Q
      (t.canonicalArrowMap u f) = t.arrowEquiv u f := by
  simp only [Descent.canonicalArrowEquiv, Equiv.trans_apply,
    Descent.arrowEquiv, Equiv.coe_fn_mk, canonicalArrowMap, Descent.Map.arrow_comp,
    arrowEquiv]
  have ht := t.canonicalDescentMap_recovery
  have hu := u.canonicalDescentMap_recovery
  dsimp only [Iso.homCongr, Equiv.coe_fn_mk]
  have hi : (Descent.Map.arrow (inv (C := Descent.Datum (a := (representation smoothAction).action)
      (SplitSheaf.ofDisplay A.cover)) t.canonicalDescentMap)) =
      t.canonicalDescentMap.arrow.inverse := by
    exact descentArrow_inverse t.canonicalDescentMap
  have hf : interpretedHomEquiv smoothAction _ _ f = (f.cechMap smoothAction).toDescent.arrow := rfl
  rw [hi, hf, ← ht, ← hu]
  dsimp only [Arrow.toIso]
  erw [inverse_comp_arrow]
  change (Descent.canonicalRecovery (SplitSheaf.ofDisplay A.cover) P).inverse.comp
    (((t.canonicalDescentMap.arrow.inverse.comp (f.cechMap smoothAction).toDescent.arrow).comp
      u.canonicalDescentMap.arrow).comp (Descent.canonicalRecovery (SplitSheaf.ofDisplay A.cover) Q)) =
    ((Descent.canonicalRecovery (SplitSheaf.ofDisplay A.cover) P).inverse.comp
      t.canonicalDescentMap.arrow.inverse).comp ((f.cechMap smoothAction).toDescent.arrow.comp
      (u.canonicalDescentMap.arrow.comp (Descent.canonicalRecovery (SplitSheaf.ofDisplay A.cover) Q)))
  simp only [comp_assoc_arrow]

end TrivializedOn
end SquareKit.SmoothCech

noncomputable section
open scoped Manifold ContDiff
namespace SquareKit.SmoothCech
open CategoryTheory CategoryTheory.Limits Opposite EuclideanOpen SmoothOpenSite
open SmoothRepresentedCover SmoothManifoldAction ManifoldRealization SheafActionQuotient
variable {X : Sheaf topology Type} {I : Type} {A : Atlas X I}
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]
variable {smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x)}
private theorem comparison_inverse_apply
    {q r : Descent.Datum (a := (representation smoothAction).action) (SplitSheaf.ofDisplay A.cover)}
    (h : Descent.Map q r) (U : SmoothPresentationSite.Siteᵒᵖ)
    (z : (SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.obj U)
    (g : q.localObject.torsor.family.family.obj
      ((SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U z)) :
    h.arrow.torsorArrow.iso.hom.app
      (X.obj.elementsMk U ((SplitSheaf.p (SplitSheaf.ofDisplay A.cover)).hom.app U z))
      (q.comparison.torsorArrow.iso.inv.app
        ((SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U z) g) =
    r.comparison.torsorArrow.iso.inv.app
      ((SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U z)
      (h.localArrow.torsorArrow.iso.hom.app
        ((SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U z) g) := by
  let y := (SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U z
  let x := X.obj.elementsMk U ((SplitSheaf.p (SplitSheaf.ofDisplay A.cover)).hom.app U z)
  let v := q.comparison.torsorArrow.iso.inv.app y g
  have hn := Descent.Map.comparison_naturality (representation smoothAction).action
    (SplitSheaf.ofDisplay A.cover) h
  have hv := congrArg (fun e => e.torsorArrow.iso.hom.app y v) hn
  have hc := congrArg (fun k => k.app y g) q.comparison.torsorArrow.iso.inv_hom_id
  change q.comparison.torsorArrow.iso.hom.app y v = g at hc
  change r.comparison.torsorArrow.iso.hom.app y (h.arrow.torsorArrow.iso.hom.app x v) =
    h.localArrow.torsorArrow.iso.hom.app y (q.comparison.torsorArrow.iso.hom.app y v) at hv
  have hv2 := hv.trans (congrArg (h.localArrow.torsorArrow.iso.hom.app y) hc)
  have hh := congrArg (r.comparison.torsorArrow.iso.inv.app y) hv2
  have hcancel := congrArg (fun k => k.app y (h.arrow.torsorArrow.iso.hom.app x v))
    r.comparison.torsorArrow.iso.hom_inv_id
  change r.comparison.torsorArrow.iso.inv.app y
    (r.comparison.torsorArrow.iso.hom.app y (h.arrow.torsorArrow.iso.hom.app x v)) =
      h.arrow.torsorArrow.iso.hom.app x v at hcancel
  exact hcancel.symm.trans hh

private theorem conjugate_apply
    {P Q P' Q' : Object (representation smoothAction).action X}
    (t : Arrow P P') (u : Arrow Q Q') (h : Arrow P Q)
    (x : X.obj.Elements) (v : P.torsor.family.family.obj x) :
    ((t.toIso.homCongr u.toIso) h).torsorArrow.iso.hom.app x
      (t.torsorArrow.iso.hom.app x v) =
    u.torsorArrow.iso.hom.app x (h.torsorArrow.iso.hom.app x v) := by
  have ht := congrArg (fun k => k.app x v) t.torsorArrow.iso.hom_inv_id
  change t.torsorArrow.iso.inv.app x (t.torsorArrow.iso.hom.app x v) = v at ht
  exact congrArg (fun q => u.torsorArrow.iso.hom.app x (h.torsorArrow.iso.hom.app x q)) ht

namespace TrivializedOn
variable {P Q : Object (representation smoothAction).action X}
variable (t : TrivializedOn A smoothAction P) (u : TrivializedOn A smoothAction Q)

/-- Recovering an external arrow on a chosen split-cover coordinate gives the
actual local arrow between the supplied regularizations. -/
theorem arrowEquiv_split_apply (f : Hom t.extractedDatum u.extractedDatum)
    (U : SmoothPresentationSite.Siteᵒᵖ)
    (z : (SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.obj U)
    (g : (locallyConstantGroup G).obj.obj U) :
    (t.arrowEquiv u f).torsorArrow.iso.hom.app
      (X.obj.elementsMk U ((SplitSheaf.p (SplitSheaf.ofDisplay A.cover)).hom.app U z))
      (t.splitRegularization.torsorArrow.iso.hom.app
        ((SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U z) g) =
    u.splitRegularization.torsorArrow.iso.hom.app
      ((SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U z)
      ((f.localArrow smoothAction).torsorArrow.iso.hom.app
        ((SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U z) g) := by
  let cp := (t.extractedDatum.cech smoothAction).toDescent.comparison
  let cq := (u.extractedDatum.cech smoothAction).toDescent.comparison
  let y := (SplitSheaf.extension (SplitSheaf.ofDisplay A.cover)).obj.elementsMk U z
  let x := X.obj.elementsMk U ((SplitSheaf.p (SplitSheaf.ofDisplay A.cover)).hom.app U z)
  let v := cp.torsorArrow.iso.inv.app y g
  have htransport := comparison_inverse_apply (f.cechMap smoothAction).toDescent U z g
  have hrval := conjugate_apply t.extractedRecovery u.extractedRecovery
    (interpretedHomEquiv smoothAction _ _ f) x v
  exact (congrArg ((t.arrowEquiv u f).torsorArrow.iso.hom.app x)
      (t.extractedRecovery_comparison_apply U z g).symm).trans
    (hrval.trans ((congrArg (u.extractedRecovery.torsorArrow.iso.hom.app x)
      htransport).trans (u.extractedRecovery_comparison_apply U z
        ((f.localArrow smoothAction).torsorArrow.iso.hom.app y g))))

end TrivializedOn
end SquareKit.SmoothCech
