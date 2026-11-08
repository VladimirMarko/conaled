import SquareKit.SmoothConstantComparison
import SquareKit.SheafActionQuotientDescent
import Mathlib.CategoryTheory.Sites.EpiMono

/-! Actual cover displays and canonical descent recovery for ordinary principal
covers. These comparisons are between the chosen recovery maps. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace SquareKit.EuclideanOpen
open SmoothAlgebra SmoothOpenSite
variable (U : Domain) {ι : Type} (g : ι → Free U.dimension)

def ordinaryCoverMap : (∐ fun i => embedding.obj (subdomain U (g i))) ⟶ embedding.obj U :=
  Sigma.desc (fun i => embedding.map (subInclusion U (g i)))

include g in
theorem ordinaryCoverMap_epi (hc : Covers U g) : Epi (ordinaryCoverMap U g) where
  left_cancellation a b h := by
    apply cover_jointly_epic U g hc _ a b
    intro i
    have hi := congrArg (fun k => Sigma.ι (fun i => embedding.obj (subdomain U (g i))) i ≫ k) h
    simpa only [← Category.assoc, ordinaryCoverMap, Sigma.ι_comp_desc] using hi

def ordinaryCoverFamily : SplitSheaf.Ty (embedding.obj U) := SplitSheaf.ofDisplay (ordinaryCoverMap U g)

theorem ordinaryCoverFamily_locallySurjective (hc : Covers U g) :
    Presheaf.IsLocallySurjective topology (SplitSheaf.p (ordinaryCoverFamily U g)).hom := by
  let := ordinaryCoverMap_epi U g hc
  have : Sheaf.IsLocallySurjective (ordinaryCoverMap U g) :=
    (Sheaf.isLocallySurjective_iff_epi _).mpr inferInstance
  change Presheaf.IsLocallySurjective topology (SplitSheaf.p (SplitSheaf.ofDisplay (ordinaryCoverMap U g))).hom
  rw [← SplitSheaf.displayIso_projection]
  change Presheaf.IsLocallySurjective topology
    ((SplitSheaf.displayIso (ordinaryCoverMap U g)).hom.hom ≫ (ordinaryCoverMap U g).hom)
  infer_instance

end SquareKit.EuclideanOpen
namespace SquareKit.SheafActionQuotient.Descent
open SmoothOpenSite EuclideanOpen
variable {G : Sheaf topology GrpCat} {M X : Sheaf topology Type} {a : Action G M}
variable (A B : SplitSheaf.Ty X)
variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]
variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p B).hom]

/-- Compare canonical descents through their actual recovery arrows. -/
def recoveryComparison (P : Object a X) :
    Arrow (canonicalDatum A P).object (canonicalDatum B P).object :=
  (canonicalRecovery A P).comp (canonicalRecovery B P).inverse

theorem recoveryComparison_commutes (P : Object a X) :
    (recoveryComparison A B P).comp (canonicalRecovery B P) = canonicalRecovery A P := by
  change (canonicalRecovery A P) ≫ (canonicalRecovery B P).toIso.inv ≫
    (canonicalRecovery B P).toIso.hom = _
  simp

/-- The selected arrow transport is the one recovered from the same global arrow. -/
def recoveryArrowComparison (P Q : Object a X) :
    Map (canonicalDatum A P) (canonicalDatum A Q) ≃ Map (canonicalDatum B P) (canonicalDatum B Q) :=
  (canonicalArrowEquiv A P Q).trans (canonicalArrowEquiv B P Q).symm

theorem recoveryArrowComparison_commutes (P Q : Object a X)
    (f : Map (canonicalDatum A P) (canonicalDatum A Q)) :
    canonicalArrowEquiv B P Q (recoveryArrowComparison A B P Q f) = canonicalArrowEquiv A P Q f :=
  (canonicalArrowEquiv B P Q).apply_symm_apply _

/-- The recovered arrow commutes with the selected object comparison, before
forgetting to the globally recovered objects. -/
theorem recoveryComparison_natural (P Q : Object a X)
    (f : Map (canonicalDatum A P) (canonicalDatum A Q)) :
    (recoveryComparison A B P).comp (recoveryArrowComparison A B P Q f).arrow =
      f.arrow.comp (recoveryComparison A B Q) := by
  have h := recoveryArrowComparison_commutes A B P Q f
  change (canonicalRecovery B P).toIso.inv ≫ (recoveryArrowComparison A B P Q f).arrow ≫
      (canonicalRecovery B Q).toIso.hom =
    (canonicalRecovery A P).toIso.inv ≫ f.arrow ≫ (canonicalRecovery A Q).toIso.hom at h
  have hh := congrArg (fun z => (canonicalRecovery A P).toIso.hom ≫ z ≫
    (canonicalRecovery B Q).toIso.inv) h
  change ((canonicalRecovery A P).toIso.hom ≫ (canonicalRecovery B P).toIso.inv) ≫
      (recoveryArrowComparison A B P Q f).arrow =
    f.arrow ≫ (canonicalRecovery A Q).toIso.hom ≫ (canonicalRecovery B Q).toIso.inv
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id] using hh

end SquareKit.SheafActionQuotient.Descent
