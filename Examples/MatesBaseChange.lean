import SquareKit.MixedBaseChange
import SquareKit.Internal.GeometricMixedChange
import SquareKit.AdjointSquareTransport
import Examples.IndexedWitnessAdjunctions
import Examples.TerminalProducts

/-! Recovery of the geometric client, a change from slice settings to their base,
and two actual dependent-product transports of a selected varying finite value. -/
noncomputable section
namespace Examples.MatesBaseChange
open CategoryTheory Limits
open scoped CategoryTheory.TwoSquare

section Recovery
universe u v w x
variable {C : Type u} {D : Type v} [Category.{w} C] [Category.{x} D]
variable [HasPullbacks C] [HasPullbacks D]
variable (h : SquareKit.Internal.GeometricMorphism D C)
variable {A X Y Z : C} (p : A ⟶ Y) (σ : X ⟶ Y) (τ : Z ⟶ X)

/-- Recovery is equality of the whole natural transformation, hence of every witness map. -/
theorem geometric_recovery (h : SquareKit.Internal.GeometricMorphism D C) {X Y : C} (σ : X ⟶ Y) :
    SquareKit.MixedBaseChange.comparison h.inverseImage σ = (h.pullbackPost σ).hom := rfl

theorem geometric_iso_recovery (h : SquareKit.Internal.GeometricMorphism D C) {X Y : C} (σ : X ⟶ Y) :
    SquareKit.MixedBaseChange.iso h.inverseImage σ = h.pullbackPost σ := by
  apply Iso.ext
  apply NatTrans.ext
  funext Z
  apply Over.OverMorphism.ext
  rfl

theorem geometric_context_recovery (h : SquareKit.Internal.GeometricMorphism D C)
    {A X Y Z : C} (p : A ⟶ Y) (σ : X ⟶ Y) (τ : Z ⟶ X) :
    SquareKit.MixedBaseChange.contextPaste h.inverseImage p σ τ = h.mixedContextPaste p σ τ := rfl

/-- The native first projection follows from the general comparison. -/
theorem recover_fst (W : Over Y) :
    ((h.pullbackPost σ).hom.app W).left ≫
      pullback.fst (h.inverseImage.map W.hom) (h.inverseImage.map σ) =
    h.inverseImage.map (pullback.fst W.hom σ) :=
  SquareKit.MixedBaseChange.comparison_fst h.inverseImage σ W

theorem recover_snd (W : Over Y) :
    ((h.pullbackPost σ).hom.app W).left ≫
      pullback.snd (h.inverseImage.map W.hom) (h.inverseImage.map σ) =
    h.inverseImage.map (pullback.snd W.hom σ) :=
  SquareKit.MixedBaseChange.comparison_snd h.inverseImage σ W

theorem recover_identity (W : Over Y) :
    ((SquareKit.Internal.GeometricMorphism.pullbackPost
      (SquareKit.Internal.GeometricMorphism.identity C) σ).hom.app W).left =
      𝟙 (pullback W.hom σ) :=
  SquareKit.MixedBaseChange.identity σ W

theorem recover_context_composition :
    h.inverseImage.map (SquareKit.Family.compositionIso p σ τ).hom ≫
      pullbackComparison h.inverseImage p (τ ≫ σ) = h.mixedContextPaste p σ τ :=
  SquareKit.MixedBaseChange.context_composition h.inverseImage p σ τ

variable {E : Type*} [Category E] [HasPullbacks E]
/-- Ambient composition has exactly the original component map and order. -/
theorem recover_ambient_composition (k : SquareKit.Internal.GeometricMorphism E D) (W : Over Y) :
    (((k.comp h).pullbackPost σ).hom.app W).left =
      k.inverseImage.map ((h.pullbackPost σ).hom.app W).left ≫
        ((k.pullbackPost (h.inverseImage.map σ)).hom.app ((Over.post h.inverseImage).obj W)).left :=
  SquareKit.MixedBaseChange.composition h.inverseImage k.inverseImage σ W
end Recovery

/-- Forgetting a display over Bool is a genuine change of category. The pasted
comparison retains the full underlying value map, with no geometric adjunction supplied. -/
theorem forget_context_paste {A X Y Z : Over Bool}
    (p : A ⟶ Y) (σ : X ⟶ Y) (τ : Z ⟶ X) :
    (Over.forget Bool).map (SquareKit.Family.compositionIso p σ τ).hom ≫
      pullbackComparison (Over.forget Bool) p (τ ≫ σ) =
    SquareKit.MixedBaseChange.contextPaste (Over.forget Bool) p σ τ :=
  SquareKit.MixedBaseChange.context_composition (Over.forget Bool) p σ τ

/-- Pullback preservation makes the slice-forgetting comparison invertible. -/
def forgetComparisonIso {X Y : Over Bool} (σ : X ⟶ Y) :=
  SquareKit.MixedBaseChange.iso (Over.forget Bool) σ

/-- The new client cannot be packaged with this inverse image as a geometric
morphism: forgetting the terminal display over Bool leaves a nonterminal type. -/
theorem forget_not_leftExact : ¬ PreservesFiniteLimits (Over.forget Bool) := by
  intro h
  let := h
  have ht := Limits.IsTerminal.isTerminalObj (Over.forget Bool) _ (Over.mkIdTerminal (X := Bool))
  have e := ht.hom_ext (↾fun _ : Unit => false) (↾fun _ : Unit => true)
  exact Bool.false_ne_true (congrArg (fun k : Unit ⟶ Bool => k ()) e)

namespace FiniteProducts
open SquareKit
open CategoryTheory.CartesianMonoidalCategory
abbrev Values := Examples.TerminalProducts.Native.Values
abbrev point := TypeTerminalProduct.pointEquiv Values Examples.TerminalProducts.Native.last
abbrev oldAdj := TerminalProduct.adjunction Nat
abbrev oldInput := (toOverUnit (Type)).obj TypeTerminalProduct.unit
abbrev oldOutput := TypeTerminalProduct.family Values
abbrev oldBody := (oldAdj.homEquiv oldInput oldOutput).symm point
abbrev f : Nat ⟶ PUnit := toUnit Nat
abbrev sigma : Nat ⟶ PUnit := toUnit Nat
def tau : Nat ⟶ Nat := ↾fun n => n + 1
abbrev f₁ := pullback.snd f sigma
abbrev g₁ := pullback.fst f sigma
abbrev first_isPullback := (IsPullback.of_hasPullback f sigma).flip
abbrev second_isPullback := (IsPullback.of_hasPullback f₁ tau).flip
def firstPi := ExponentiablePullback.squareRightAdjoint f sigma oldAdj first_isPullback
def firstAdj : Over.pullback f₁ ⊣ firstPi := ExponentiablePullback.squareAdjunction f sigma oldAdj first_isPullback
def secondPi := ExponentiablePullback.squareRightAdjoint f₁ tau firstAdj second_isPullback
def secondAdj : Over.pullback (pullback.snd f₁ tau) ⊣ secondPi := ExponentiablePullback.squareAdjunction f₁ tau firstAdj second_isPullback
abbrev firstMate := DependentBaseChange.WithAdjunction.mate first_isPullback oldAdj firstAdj
abbrev secondMate := DependentBaseChange.WithAdjunction.mate second_isPullback firstAdj secondAdj

/-- The starting product contains an actual choice in each different Fin(n+1). -/
theorem selected_value (n : Nat) :
    (TypeTerminalProduct.evaluate Values Examples.TerminalProducts.Native.last n).val = n :=
  Examples.TerminalProducts.Native.last_component n

/-- The value fibers really differ, independently of the categorical encoding. -/
theorem different_fibers : ¬ Nonempty (Values 0 ≃ Values 1) := by
  change ¬ Nonempty (Fin 1 ≃ Fin 2)
  rintro ⟨e⟩
  have h : (0 : Fin 2) = 1 := e.symm.injective (Subsingleton.elim _ _)
  exact (by decide : (0 : Fin 2) ≠ 1) h

/-- The first change collapses distinct parameters. -/
theorem sigma_not_injective : ¬ Function.Injective sigma := by
  intro h
  have bad : 0 = 1 := h (by rfl)
  exact Nat.noConfusion bad

/-- Apply both canonical mates to that selected dependent function. -/
def twice := (Over.pullback tau).map
  ((Over.pullback sigma).map point ≫ firstMate.app oldOutput) ≫
    secondMate.app ((Over.pullback g₁).obj oldOutput)

/-- Evaluation of the twice-transported chosen function is exactly the twice
base-changed original body, with both pullback comparison witnesses retained. -/
abbrev twice_evaluation :=
  AdjointSquareTransport.uncurry_paste oldAdj firstAdj
    (DependentBaseChange.pullbackComparison first_isPullback) secondAdj
    (DependentBaseChange.pullbackComparison second_isPullback) point

/-- The two canonical transformations equal the mate of the pasted input square. -/
theorem pasted_mate : mateEquiv oldAdj secondAdj
    (DependentBaseChange.pullbackComparison first_isPullback ≫ₕ
      DependentBaseChange.pullbackComparison second_isPullback) = firstMate ≫ᵥ secondMate :=
  DependentBaseChange.mate_paste first_isPullback second_isPullback oldAdj firstAdj secondAdj

theorem tau_not_identity : tau ≠ 𝟙 Nat := by
  intro h
  have bad := congrArg (fun k : Nat ⟶ Nat => k 0) h
  exact Nat.noConfusion bad
end FiniteProducts

/-- A reused mathematical rejection: an invertible mate can have a noninvertible
inverse mate. The actual domain is empty while the codomain is inhabited. -/
theorem noninvertible_inverse_mate :
    ¬ IsIso (((mateEquiv
      (Over.mapPullbackAdj IndexedWitnessAdjunctions.NonPullback.unitMap)
      (Over.mapPullbackAdj IndexedWitnessAdjunctions.NonPullback.emptyMap)).symm
      IndexedWitnessAdjunctions.NonPullback.invertibleMate).app
      IndexedWitnessAdjunctions.NonPullback.X) :=
  IndexedWitnessAdjunctions.NonPullback.inverse_mate_not_invertible

end Examples.MatesBaseChange
