import SquareKit.SheafTorsorStackDescent
import SquareKit.SheafActionQuotientDescentBaseChange
import SquareKit.Internal.TorsorClassifierDescent

/-! The torsor stack on sheaf contexts with locally surjective covers. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.SheafTorsor.Stack
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Locally surjective maps have locally surjective refinements after any base change. -/
theorem cover_pullback {X Y Z : Sheaf J (Type (max u v))} (f : Y ⟶ X) (g : Z ⟶ X)
    [Presheaf.IsLocallySurjective J f.hom] :
    ∃ (W : Sheaf J (Type (max u v))) (p : W ⟶ Z) (q : W ⟶ Y),
      Presheaf.IsLocallySurjective J p.hom ∧ q ≫ f = p ≫ g := by
  let A := SplitSheaf.ofDisplay f
  refine ⟨SplitSheaf.Ext (SplitSheaf.tySub A g), SplitSheaf.p _,
    SplitSheaf.lift A g ≫ (SplitSheaf.displayIso f).hom, inferInstance, ?_⟩
  rw [Category.assoc, SplitSheaf.displayIso_projection, SplitSheaf.lift_p]

/-- The topology on sheaf contexts in which a covering sieve contains a locally
surjective map. This is distinct from the original site topology `J`. -/
def topology : GrothendieckTopology (Sheaf J (Type (max u v))) where
  sieves X := {R | ∃ (Y : Sheaf J (Type (max u v))) (f : Y ⟶ X),
    Presheaf.IsLocallySurjective J f.hom ∧ R f}
  top_mem' X := ⟨X, 𝟙 X, inferInstance, by trivial⟩
  pullback_stable' {_ _ R} g := by
    rintro ⟨Y, f, hf, hR⟩
    obtain ⟨W, p, q, hp, eq⟩ := cover_pullback f g
    refine ⟨W, p, hp, ?_⟩
    change R (p ≫ g)
    rw [← eq]
    exact Sieve.downward_closed _ hR q
  transitive' := by
    rintro X S ⟨Y, f, hf, hS⟩ R hR
    obtain ⟨Z, g, hg, h⟩ := hR hS
    refine ⟨Z, g ≫ f, ?_, h⟩
    change Presheaf.IsLocallySurjective J (g.hom ≫ f.hom)
    infer_instance

/-- Singleton locally surjective covers in a slice of sheaf contexts. -/
def overCoverage (S : Sheaf J (Type (max u v))) : Coverage (Over S) where
  coverings X := {R | ∃ (Y : Over S) (f : Y ⟶ X),
    R = Presieve.singleton f ∧ Presheaf.IsLocallySurjective J f.left.hom}
  pullback := by
    rintro X Y g R ⟨Z, f, rfl, hf⟩
    obtain ⟨W, p, q, hp, eq⟩ := cover_pullback f.left g.left
    let W' : Over S := Over.mk (p ≫ Y.hom)
    let p' : W' ⟶ Y := Over.homMk p
    let q' : W' ⟶ Z := Over.homMk q (by
      dsimp [W']; rw [← Over.w f, ← Category.assoc, eq, Category.assoc, Over.w g])
    refine ⟨Presieve.singleton p', ⟨W', p', rfl, hp⟩, ?_⟩
    intro V a ha
    cases ha
    exact ⟨Z, q', f, Presieve.singleton_self _, by apply Over.OverMorphism.ext; exact eq⟩

lemma over_topology_le (S : Sheaf J (Type (max u v))) :
    (topology (J := J)).over S ≤ (overCoverage S).toGrothendieck := by
  intro X R hR
  obtain ⟨Y, f, hf, h⟩ := hR
  let Y' : Over S := Over.mk (f ≫ X.hom)
  let f' : Y' ⟶ X := Over.homMk f
  apply Coverage.mem_toGrothendieck_sieves_of_superset (overCoverage S)
    (R := Presieve.singleton f')
  · intro Z g hg
    cases hg
    exact (Sieve.overEquiv_iff _ _).mp h
  · exact ⟨Y', f', rfl, hf⟩

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
