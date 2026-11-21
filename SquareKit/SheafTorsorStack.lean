import SquareKit.SheafTorsorStackDescent
import SquareKit.SheafContextTopology
import SquareKit.Internal.TorsorClassifierDescent

/-! The torsor stack on sheaf contexts with locally surjective covers. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.SheafTorsor.Stack
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

export SheafCover (cover_pullback topology overCoverage over_topology_le)

variable (G : Sheaf J GrpCat.{max u v})

instance isPrestack : (pseudofunctor G).IsPrestack (topology (J := J)) where
  isSheaf {S} M N := by
    apply Presheaf.IsSheaf.of_le (over_topology_le S)
    rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_coverage]
    rintro X R ⟨Y, f, rfl, hf⟩
    rw [Presieve.isSheafFor_iff_generate]
    apply Pseudofunctor.IsPrestackFor.isSheafFor'
    rw [Sieve.overEquiv_generate, ← Sieve.arrows_generate_map_eq_functorPushforward,
      Sieve.generate_sieve]
    simp only [Presieve.map_singleton]
    rw [← Presieve.ofArrows_pUnit.{0}]
    apply (Pseudofunctor.IsPrestackFor_generate_iff _ _).mpr
    exact (isStackFor_cover (G := G) f.left).isPrestackFor

instance isStack : (pseudofunctor G).IsStack (topology (J := J)) := by
  apply Pseudofunctor.IsStack.of_isStackFor
  rintro X R ⟨Y, f, hf, hR⟩
  apply Pseudofunctor.IsStackFor.of_le (pseudofunctor G) (isStackFor_cover (G := G) f) (J := topology (J := J))
  · exact ⟨Y, f, hf, Sieve.ofArrows_mk _ _ ()⟩
  · intro Z g hg
    cases hg
    exact hR

variable {G} {X : Sheaf J (Type (max u v))} {A : SplitSheaf.Ty X}
variable [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]

/-- The chosen effective object is exactly the existing constructive glued torsor. -/
abbrev glue (D : Data (G := G) A) : Torsor G X := Descent.torsor (datum D)

/-- Classifier recovery compares its decoded result to the stack's effective object. -/
def classifierComparison (D : Data (G := G) A) :
    RepresentableClassification.TorsorDescent.glue (datum D) ≅ glue D :=
  (RepresentableClassification.TorsorDescent.comparison (glue D)).toIso

theorem classifier_localComparison (D : Data (G := G) A) :
    ((classifierComparison D).hom.reindex (SplitSheaf.p A)).comp
        ((localComparison D).hom.hom ()) =
      RepresentableClassification.TorsorDescent.localComparison (datum D) := rfl

/-- Every Mathlib compatible map survives constructive descent and classification. -/
def classifiedMapEquiv (D E : Data (G := G) A) :
    (D ⟶ E) ≃ SheafTorsor.Arrow
      (RepresentableClassification.TorsorDescent.glue (datum D))
      (RepresentableClassification.TorsorDescent.glue (datum E)) :=
  (datumMapEquiv D E).trans (RepresentableClassification.TorsorDescent.mapEquiv (datum D) (datum E))

theorem classifier_map_comparison {D E : Data (G := G) A} (h : D ⟶ E) :
    (classifiedMapEquiv D E h).comp (classifierComparison E).hom =
      (classifierComparison D).hom.comp (datumMap h).arrow :=
  RepresentableClassification.TorsorDescent.map_comparison _ _ _

/-- The comparison retains the actual display over the original context. -/
theorem classifier_projection (D : Data (G := G) A) :
    (RepresentableClassification.PresheafFamily.decodeSheafIso (glue D).family).hom ≫
      SplitSheaf.p (glue D).family =
        SplitSheaf.p (RepresentableClassification.TorsorDescent.glue (datum D)).family :=
  RepresentableClassification.TorsorDescent.projection _

/-- Arbitrary substitution preserves the comparison square, using strict restriction. -/
theorem classifier_map_reindex {D E : Data (G := G) A} (h : D ⟶ E)
    {Y : Sheaf J (Type (max u v))} (f : Y ⟶ X) :
    ((classifiedMapEquiv D E h).reindex f).comp ((classifierComparison E).hom.reindex f) =
      ((classifierComparison D).hom.reindex f).comp ((datumMap h).arrow.reindex f) :=
  congrArg (fun k => SheafTorsor.Arrow.reindex k f) (classifier_map_comparison h)

end SquareKit.SheafTorsor.Stack
