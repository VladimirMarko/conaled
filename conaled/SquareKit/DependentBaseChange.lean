import SquareKit.ExponentiablePullback
import Mathlib.CategoryTheory.Adjunction.Mates

/-! Experimental canonical Beck–Chevalley for the constructed dependent
products. Both mates use actual slice pullbacks and the existing adjunctions. -/
noncomputable section
namespace SquareKit.DependentBaseChange
open CategoryTheory Limits
universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {A B A' B' : C} {f : A ⟶ B} {g : B' ⟶ B} {f' : A' ⟶ B'} {g' : A' ⟶ A}
variable (h : IsPullback f' g' g f)

include h in
/-- Pasting the square with the ordinary pullback of X. -/
theorem outer (X : Over B') : IsPullback (pullback.fst X.hom f')
    (pullback.snd X.hom f' ≫ g') (X.hom ≫ g) f :=
  ((IsPullback.of_hasPullback X.hom f').flip.paste_horiz h.flip).flip

/-- The sum/pullback comparison for an actual pullback square. -/
def leftComparison : Over.pullback f' ⋙ Over.map g' ≅ Over.map g ⋙ Over.pullback f :=
  NatIso.ofComponents (fun X => Over.isoMk (outer h X).isoPullback
    (outer h X).isoPullback_hom_snd) (by
      intro X Y k
      apply Over.OverMorphism.ext
      apply pullback.hom_ext <;>
        simp [Over.pullback, Over.map, Category.assoc])

@[reassoc (attr := simp)] theorem leftComparison_fst (X : Over B') :
    ((leftComparison h).hom.app X).left ≫ pullback.fst (X.hom ≫ g) f =
      pullback.fst X.hom f' := (outer h X).isoPullback_hom_fst

@[reassoc (attr := simp)] theorem leftComparison_snd (X : Over B') :
    ((leftComparison h).hom.app X).left ≫ pullback.snd (X.hom ≫ g) f =
      pullback.snd X.hom f' ≫ g' := (outer h X).isoPullback_hom_snd

/-- The commuting pullback comparison is the first canonical mate. -/
def pullbackComparison : Over.pullback g ⋙ Over.pullback f' ⟶ Over.pullback f ⋙ Over.pullback g' :=
  mateEquiv (Over.mapPullbackAdj g) (Over.mapPullbackAdj g') (leftComparison h).hom

@[reassoc (attr := simp)] theorem comparison_base (X : Over B) :
    ((pullbackComparison h).app X).left ≫ pullback.snd (pullback.snd X.hom f) g' =
      pullback.snd (pullback.snd X.hom g) f' := Over.w _

@[reassoc (attr := simp)] theorem comparison_value (X : Over B) :
    ((pullbackComparison h).app X).left ≫
      pullback.fst (pullback.snd X.hom f) g' ≫ pullback.fst X.hom f =
    pullback.fst (pullback.snd X.hom g) f' ≫ pullback.fst X.hom g := by
  have e := mateEquiv_counit (Over.mapPullbackAdj g) (Over.mapPullbackAdj g')
    (leftComparison h).hom X
  have ee := congrArg (fun k => k.left ≫ pullback.fst X.hom f) e
  change (((pullbackComparison h).app X).left ≫
    (𝟙 _ ≫ pullback.fst (pullback.snd X.hom f) g')) ≫ pullback.fst X.hom f =
    (((leftComparison h).hom.app ((Over.pullback g).obj X)).left ≫
      ((Over.pullback f).map ((Over.mapPullbackAdj g).counit.app X)).left) ≫
        pullback.fst X.hom f at ee
  simp [Category.assoc, Over.pullback, Over.mapPullbackAdj_counit_app] at ee
  exact ee.trans ((Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ pullback.fst X.hom g)
      (leftComparison_fst h ((Over.pullback g).obj X))))

@[reassoc (attr := simp)] theorem comparison_argument (X : Over B) :
    ((pullbackComparison h).app X).left ≫
      pullback.fst (pullback.snd X.hom f) g' ≫ pullback.snd X.hom f =
    pullback.snd (pullback.snd X.hom g) f' ≫ g' := by
  rw [pullback.condition, comparison_base_assoc]

/-- Inverse of the commuting pullback map, built from the two universal pairs. -/
def pullbackInverse (X : Over B) :
    (Over.pullback f ⋙ Over.pullback g').obj X ⟶ (Over.pullback g ⋙ Over.pullback f').obj X :=
  Over.homMk (pullback.lift
    (pullback.lift
      (pullback.fst (pullback.snd X.hom f) g' ≫ pullback.fst X.hom f)
      (pullback.snd (pullback.snd X.hom f) g' ≫ f') (by
        rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition]
        rw [Category.assoc, ← h.w, Category.assoc]))
    (pullback.snd (pullback.snd X.hom f) g') (by simp)) (by simp)

instance comparison_isIso (X : Over B) : IsIso ((pullbackComparison h).app X) := by
  refine ⟨⟨pullbackInverse h X, ?_, ?_⟩⟩
  · apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · apply pullback.hom_ext <;>
        simp [pullbackInverse, Category.assoc, ← pullback.condition]
    · simp [pullbackInverse, Category.assoc]
  · apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · apply pullback.hom_ext <;>
        simp [pullbackInverse, Category.assoc, ← pullback.condition]
    · simp [pullbackInverse, Category.assoc]

/-- Commutation of the actual pullback functors, with the mate as forward map. -/
def pullbackIso : Over.pullback g ⋙ Over.pullback f' ≅ Over.pullback f ⋙ Over.pullback g' :=
  NatIso.ofComponents (fun X => asIso ((pullbackComparison h).app X))
    (by intro X Y k; exact (pullbackComparison h).naturality k)

variable {R : Over A ⥤ Over B} (adj : Over.pullback f ⊣ R)

namespace WithAdjunction
variable {R' : Over A' ⥤ Over B'} (adj' : Over.pullback f' ⊣ R')

/-- The mate of the actual pullback comparison under two specified adjunctions. -/
def mate : R ⋙ Over.pullback g ⟶
    Over.pullback g' ⋙ R' :=
  mateEquiv adj adj' (pullbackComparison h)

/-- Iterating mates identifies this map with conjugation of the proven left iso. -/
theorem mate_conjugate : mate h adj adj' =
    conjugateEquiv ((Over.mapPullbackAdj g).comp adj)
      (adj'.comp (Over.mapPullbackAdj g'))
        (leftComparison h).hom :=
  iterated_mateEquiv_conjugateEquiv (Over.mapPullbackAdj g) (Over.mapPullbackAdj g')
    adj' adj (leftComparison h).hom

instance mate_isIso : IsIso (mate h adj adj') := by
  rw [mate_conjugate]
  infer_instance

/-- The forward map is the canonical mate; invertibility is proved above. -/
def iso : R ⋙ Over.pullback g ≅
    Over.pullback g' ⋙ R' := asIso (mate h adj adj')

/-- Transposing the mate gives comparison followed by base-changed evaluation. -/
theorem evaluation (Y : Over A) :
    (Over.pullback f').map ((mate h adj adj').app Y) ≫
      adj'.counit.app ((Over.pullback g').obj Y) =
    (pullbackComparison h).app (R.obj Y) ≫ (Over.pullback g').map (adj.counit.app Y) :=
  mateEquiv_counit adj adj' (pullbackComparison h) Y

/-- Underlying evaluation equation for callers composing actual family maps. -/
theorem evaluation_left (Y : Over A) :
    ((Over.pullback f').map ((mate h adj adj').app Y)).left ≫
      (adj'.counit.app ((Over.pullback g').obj Y)).left =
    ((pullbackComparison h).app (R.obj Y)).left ≫
      ((Over.pullback g').map (adj.counit.app Y)).left :=
  congrArg (fun k => k.left) (evaluation h adj adj' Y)

/-- Evaluation remains compatible after explicit parameter and value maps. -/
theorem evaluation_comp (Y : Over A) {X Z : C}
    (l : X ⟶ ((Over.pullback f').obj ((Over.pullback g).obj (R.obj Y))).left)
    (r : ((Over.pullback g').obj Y).left ⟶ Z) :
    l ≫ ((Over.pullback f').map ((mate h adj adj').app Y)).left ≫
      (adj'.counit.app ((Over.pullback g').obj Y)).left ≫ r =
    l ≫ ((pullbackComparison h).app (R.obj Y)).left ≫
      ((Over.pullback g').map (adj.counit.app Y)).left ≫ r := by
  have he := congrArg (fun k => l ≫ k ≫ r) (evaluation_left h adj adj' Y)
  simpa only [Category.assoc] using he

/-- Discharge evaluation through the base-changed old counit. -/
theorem evaluation_of (Y : Over A) {X Z : C}
    (l : X ⟶ ((Over.pullback f').obj ((Over.pullback g).obj (R.obj Y))).left)
    (r : ((Over.pullback g').obj Y).left ⟶ Z) (k : X ⟶ Z)
    (hk : l ≫ ((pullbackComparison h).app (R.obj Y)).left ≫
      ((Over.pullback g').map (adj.counit.app Y)).left ≫ r = k) :
    l ≫ ((Over.pullback f').map ((mate h adj adj').app Y)).left ≫
      (adj'.counit.app ((Over.pullback g').obj Y)).left ≫ r = k :=
  (evaluation_comp h adj adj' Y l r).trans hk

theorem transpose (Y : Over A) :
    (mate h adj adj').app Y = adj'.homEquiv _ _
      ((pullbackComparison h).app (R.obj Y) ≫ (Over.pullback g').map (adj.counit.app Y)) := by
  apply adj'.homEquiv _ _ |>.symm.injective
  erw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, evaluation]

/-- Transpose after a map of the base-changed input family. -/
theorem transpose_map (Y : Over A) (Z : Over A') (j : (Over.pullback g').obj Y ⟶ Z) :
    adj'.homEquiv ((Over.pullback g).obj (R.obj Y)) Z
      ((pullbackComparison h).app (R.obj Y) ≫ (Over.pullback g').map (adj.counit.app Y) ≫ j) =
    (mate h adj adj').app Y ≫ R'.map j := by
  rw [← Category.assoc, adj'.homEquiv_naturality_right, ← transpose]

/-- Transport any transposed family map; the inverse law recovers its evaluation. -/
theorem curry_baseChange (X : Over B) (Y : Over A) (k : (Over.pullback f).obj X ⟶ Y) :
    (Over.pullback g).map (adj.homEquiv X Y k) ≫ (mate h adj adj').app Y =
      adj'.homEquiv _ _
        ((pullbackComparison h).app X ≫ (Over.pullback g').map k) := by
  apply adj'.homEquiv _ _ |>.symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc, evaluation]
  erw [(pullbackComparison h).naturality_assoc]
  simp only [Functor.comp_map, ← Functor.map_comp]
  erw [← adj.homEquiv_counit, Equiv.symm_apply_apply]

end WithAdjunction

/-- Canonical mate for the exact right adjoint constructed by pullback stability. -/
abbrev mate := WithAdjunction.mate h adj (ExponentiablePullback.squareAdjunction f g adj h)
abbrev mate_conjugate := WithAdjunction.mate_conjugate h adj (ExponentiablePullback.squareAdjunction f g adj h)
abbrev iso := WithAdjunction.iso h adj (ExponentiablePullback.squareAdjunction f g adj h)
abbrev evaluation := WithAdjunction.evaluation h adj (ExponentiablePullback.squareAdjunction f g adj h)
abbrev transpose := WithAdjunction.transpose h adj (ExponentiablePullback.squareAdjunction f g adj h)
abbrev curry_baseChange := WithAdjunction.curry_baseChange h adj (ExponentiablePullback.squareAdjunction f g adj h)

end SquareKit.DependentBaseChange
