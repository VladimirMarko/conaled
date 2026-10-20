import SquareKit.SmoothOpenEmbedding
import Mathlib.CategoryTheory.Sites.Point.Presheaf
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-! Covering sieves lift ordinary real points. This concerns points of the site,
and does not assert that points detect arbitrary infinitesimal sections. -/
noncomputable section
open CategoryTheory Opposite
namespace SquareKit.SmoothOpenSite
open SmoothAlgebra SmoothPresentationSite PresentedLocalization

def realEvaluation : Hom (Carrier (free 0)) ℝ :=
  Hom.comp (evaluate (Fin.elim0 : Fin 0 → ℝ)) (freeValue 0)

theorem realEvaluation_inverse :
    Hom.comp (DualExtension.realHom : Hom ℝ (Carrier (free 0))) realEvaluation =
      Hom.ident := by
  apply (freeHomEquiv 0 (free 0)).injective
  exact funext (fun i => i.elim0)

theorem realEvaluation_isUnit (a : Carrier (free 0)) (ha : realEvaluation a ≠ 0) :
    IsUnit a := by
  have h := (isUnit_iff_ne_zero.mpr ha).map
    (DualExtension.realHom : Hom ℝ (Carrier (free 0))).toAlgHom
  change IsUnit ((Hom.comp DualExtension.realHom realEvaluation) a) at h
  rw [realEvaluation_inverse] at h
  exact h

/-- Every covering sieve admits a lift of each real point. The induction uses
the actual generated topology, including arbitrary and iterated covers. -/
theorem realPoint_lift {X : Site} (S : Sieve X) (hS : S ∈ topology X)
    (x : op (free 0) ⟶ X) :
    ∃ (Y : Site) (f : Y ⟶ X), S f ∧
      ∃ y : op (free 0) ⟶ Y, y ≫ f = x := by
  induction hS with
  | of X R hR =>
    obtain ⟨ι, s, hs, rfl⟩ := hR
    obtain ⟨i, hi⟩ := hs (Hom.comp realEvaluation x.unop)
    have hu : IsUnit ((smoothMap x.unop) (s i)) := realEvaluation_isUnit _ hi
    let y : localization X.unop (s i) ⟶ free 0 :=
      PresentedLocalization.lift X.unop.equations
        (PresentedLocalization.representative X.unop.equations (s i)) x.unop
        (by simpa only [PresentedLocalization.representative_eq] using hu)
    refine ⟨op (localization X.unop (s i)), (localizationBase X.unop (s i)).op,
      Sieve.le_generate _ _ _ ⟨i⟩, y.op, ?_⟩
    exact congrArg Quiver.Hom.op
      (PresentedLocalization.lift_base X.unop.equations
        (PresentedLocalization.representative X.unop.equations (s i)) x.unop
        (by simpa only [PresentedLocalization.representative_eq] using hu))
  | top X =>
    exact ⟨X, 𝟙 X, trivial, x, Category.comp_id x⟩
  | transitive X R S hR hS ihR ihS =>
    obtain ⟨Y, f, hf, y, hy⟩ := ihR x
    obtain ⟨Z, g, hg, z, hz⟩ := ihS hf y
    exact ⟨Z, g ≫ f, hg, z, by rw [← Category.assoc, hz, hy]⟩

/-- The real stage defines a point of the actual open-cover site. -/
def realPoint : topology.Point where
  fiber := (GrothendieckTopology.pointBot (op (free 0))).fiber
  jointly_surjective S hS x := by
    obtain ⟨x, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective x
    obtain ⟨Y, f, hf, y, hy⟩ := realPoint_lift S hS x
    refine ⟨Y, f, hf, shrinkYonedaObjObjEquiv.symm y, ?_⟩
    change (shrinkYoneda.map f).app _ (shrinkYonedaObjObjEquiv.symm y) = _
    rw [shrinkYoneda_map_app_shrinkYonedaObjObjEquiv_symm, hy]

/-- Evaluation of a sheaf at the real stage. -/
def realSections : Sheaf topology Type ⥤ Type :=
  sheafToPresheaf topology Type ⋙ (evaluation Siteᵒᵖ Type).obj (op (op (free 0)))

def realSectionsIso : realPoint.sheafFiber ≅ realSections :=
  Functor.isoWhiskerLeft (sheafToPresheaf topology Type)
    (GrothendieckTopology.pointBotPresheafFiberIso (op (free 0)) Type)

/-- Real sections commute with sheaf colimits because every cover lifts real
points. Evaluation at a general infinitesimal stage is not asserted to do so. -/
instance : Limits.PreservesColimits realSections :=
  Limits.preservesColimits_of_natIso realSectionsIso

end SquareKit.SmoothOpenSite
