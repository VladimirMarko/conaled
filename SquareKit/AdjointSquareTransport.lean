import SquareKit.DependentBaseChange
import SquareKit.AdjointComparison

/-! Transport of curried arrows through adjoint squares. No invertibility is
assumed: the comparison itself is enough to transport a supplied arrow. -/
namespace SquareKit.AdjointSquareTransport
open CategoryTheory
open scoped CategoryTheory.TwoSquare
universe u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆
variable {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
variable [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
variable {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
variable (a : L ⊣ R) (a' : L' ⊣ R') {G : C ⥤ C'} {H : D ⥤ D'}
variable (s : TwoSquare G L L' H)

/-- A curried arrow transports through the exact mate of the supplied square. -/
theorem curry {X : C} {Y : D} (k : L.obj X ⟶ Y) :
    G.map (a.homEquiv X Y k) ≫ (mateEquiv a a' s).app Y =
      a'.homEquiv _ _ (s.app X ≫ H.map k) := by
  apply (a'.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc, mateEquiv_counit]
  erw [s.naturality_assoc]
  simp only [Functor.comp_map, ← Functor.map_comp]
  erw [← a.homEquiv_counit, Equiv.symm_apply_apply]

variable {C'' : Type u₅} {D'' : Type u₆}
variable [Category.{v₅} C''] [Category.{v₆} D'']
variable {L'' : C'' ⥤ D''} {R'' : D'' ⥤ C''} (a'' : L'' ⊣ R'')
variable {G' : C' ⥤ C''} {H' : D' ⥤ D''} (t : TwoSquare G' L' L'' H')

/-- Two transported curried arrows equal the transpose of the pasted input square. -/
theorem curry_paste {X : C} {Y : D} (k : L.obj X ⟶ Y) :
    G'.map (G.map (a.homEquiv X Y k) ≫ (mateEquiv a a' s).app Y) ≫
      (mateEquiv a' a'' t).app (H.obj Y) =
    a''.homEquiv _ _ ((s ≫ₕ t).app X ≫ (H ⋙ H').map k) := by
  rw [curry a a' s, curry a' a'' t]
  congr 1
  simp [TwoSquare.hComp, Functor.map_comp, Category.assoc]

/-- Uncurrying a transported selected arrow recovers the pasted input map. -/
theorem uncurry_paste {X : C} {Y : D} (q : X ⟶ R.obj Y) :
    (a''.homEquiv _ _).symm
      (G'.map (G.map q ≫ (mateEquiv a a' s).app Y) ≫
        (mateEquiv a' a'' t).app (H.obj Y)) =
    (s ≫ₕ t).app X ≫ (H ⋙ H').map ((a.homEquiv X Y).symm q) := by
  have e := curry_paste a a' s a'' t ((a.homEquiv X Y).symm q)
  rw [Equiv.apply_symm_apply] at e
  exact (congrArg (a''.homEquiv _ _).symm e).trans
    ((a''.homEquiv _ _).symm_apply_apply _)

/-- The comparison used above is itself the mate of the pasted square, as a
whole natural transformation, not only after evaluating a chosen arrow. -/
theorem mate_paste : mateEquiv a a'' (s ≫ₕ t) =
    (mateEquiv a a' s) ≫ᵥ (mateEquiv a' a'' t) :=
  mateEquiv_vcomp a a' a'' s t

end SquareKit.AdjointSquareTransport

namespace SquareKit.DependentBaseChange
open CategoryTheory Limits
open scoped CategoryTheory.TwoSquare
universe u v
variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable {A B A' B' A'' B'' : C}
variable {f : A ⟶ B} {g : B' ⟶ B} {f' : A' ⟶ B'} {g' : A' ⟶ A}
variable {j : B'' ⟶ B'} {f'' : A'' ⟶ B''} {j' : A'' ⟶ A'}
variable (h : IsPullback f' g' g f) (k : IsPullback f'' j' j f')
variable {R : Over A ⥤ Over B} {R' : Over A' ⥤ Over B'} {R'' : Over A'' ⥤ Over B''}
variable (a : Over.pullback f ⊣ R) (a' : Over.pullback f' ⊣ R')
variable (a'' : Over.pullback f'' ⊣ R'')

/-- The existing one-square curry contract follows from the general square law. -/
theorem curry_recovery (X : Over B) (Y : Over A) (q : (Over.pullback f).obj X ⟶ Y) :
    (Over.pullback g).map (a.homEquiv X Y q) ≫
      (WithAdjunction.mate h a a').app Y =
    a'.homEquiv _ _ ((pullbackComparison h).app X ≫ (Over.pullback g').map q) :=
  AdjointSquareTransport.curry a a' (pullbackComparison h) q

/-- Canonical dependent-product mates transport an actual family map through
both squares. No replacement of its value by mere existence is made. -/
theorem curry_paste (X : Over B) (Y : Over A) (q : (Over.pullback f).obj X ⟶ Y) :
    (Over.pullback j).map ((Over.pullback g).map (a.homEquiv X Y q) ≫
      (WithAdjunction.mate h a a').app Y) ≫
      (WithAdjunction.mate k a' a'').app ((Over.pullback g').obj Y) =
    a''.homEquiv _ _
      ((pullbackComparison h ≫ₕ pullbackComparison k).app X ≫
        (Over.pullback g' ⋙ Over.pullback j').map q) :=
  AdjointSquareTransport.curry_paste a a' (pullbackComparison h) a'' (pullbackComparison k) q

/-- Equality with the canonical mate of the pasted pullback comparisons. -/
theorem mate_paste : mateEquiv a a'' (pullbackComparison h ≫ₕ pullbackComparison k) =
    (WithAdjunction.mate h a a') ≫ᵥ (WithAdjunction.mate k a' a'') :=
  AdjointSquareTransport.mate_paste a a' (pullbackComparison h) a'' (pullbackComparison k)
end SquareKit.DependentBaseChange
