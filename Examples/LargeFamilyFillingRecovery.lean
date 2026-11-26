import Examples.CubicalConstructorRecomputation
import SquareKit.Internal.Cubical.LargeFamilyFillingRecovery
import SquareKit.Internal.Cubical.CartesianLargeFamilyFillingRecovery
import SquareKit.Internal.Cubical.LargeFamilyClassification
import SquareKit.Internal.Cubical.UniverseDecode
import SquareKit.Internal.Cubical.CartesianRealization
import SquareKit.Internal.Cubical.CartesianLargeFamilyClassification
import SquareKit.Internal.Cubical.CartesianUniverseComposition
import Examples.CartesianHigherSeparation

/-! Controls for recovery of complete selected filling operations. -/
set_option autoImplicit false
set_option warningAsError true

namespace Examples.LargeFamilyFillingRecovery
open CategoryTheory
universe u

namespace Original
open SquareKit.Cubical.Presheaf SmallUniverse

/-- Subsingleton fibers determine the whole operation, even without filling laws. -/
theorem subsingleton_filling_unique {Γ : Context.{u}} {A : Family Γ}
    (h : ∀ x, Subsingleton (A.obj x)) (F G : Filling A) : F = G := by
  cases F with | mk ff =>
    cases G with | mk gg =>
      congr
      funext Δ p φ b
      apply Term.ext
      intro x
      exact @Subsingleton.elim _ (h _) _ _

/-- A presentation of a discrete family recovers every box and the whole filler section. -/
theorem presented_recovery {Ξ : Context.{u+1}} {A : Family Ξ}
    (P : SmallPresentation.Data.{u} A) {S : Type (u+1)}
    (e : A ≅ constantFamily Ξ S) (F : Filling A) (hF : F.Lawful) :
    (NativeDecode.filling (P.code F hF)).transport (P.nativeIso F hF) = F :=
  presented_filling_unique e _ F
    (Filling.transport_lawful _ _ (NativeDecode.filling_lawful _)) hF


/-- The chart uses Boolean negation before lifting; it is not the identity presentation. -/
def negatedPresentation (Ξ : Context.{1}) :
    SmallPresentation.Data.{0} (constantFamily Ξ (ULift.{1} Bool)) where
  Fiber _ := Bool
  equiv _ := {
    toFun := fun b => ⟨!b⟩
    invFun := fun b => !(b.down)
    left_inv := fun b => Bool.not_not b
    right_inv := fun b => ULift.ext (Bool.not_not b.down) }

theorem negatedPresentation_true (Ξ : Context.{1}) (x : Ξ.Elements) :
    ((negatedPresentation Ξ).equiv x true).down = false := rfl

theorem negated_bool_recovery (Ξ : Context.{1}) :
    (NativeDecode.filling ((negatedPresentation Ξ).code
      (presentedConstantFilling Ξ (ULift Bool)) (presentedConstantFilling_lawful Ξ (ULift Bool)))).transport
        ((negatedPresentation Ξ).nativeIso (presentedConstantFilling Ξ (ULift Bool)) (presentedConstantFilling_lawful Ξ (ULift Bool))) =
      presentedConstantFilling Ξ (ULift Bool) :=
  (negatedPresentation Ξ).native_filling_recovery _ (presentedConstantFilling_lawful Ξ (ULift Bool))


open CubicalLargeConstructors CubicalConstructorRecomputation

/-- Varying dependent products preserve the canonical operation under every substitution. -/
example (σ : context ⟶ context) :
    (NativeDecode.filling (σ ≫ (LargeConstructors.pi naturalsCode varyingCode).code)).transport
      (LargeConstructors.piSubstitution naturalsCode varyingCode σ) =
    NativeDecode.filling (LargeConstructors.pi (σ ≫ naturalsCode)
      (liftSub (liftedDecode naturalsCode) σ ≫ varyingCode)).code :=
  LargeConstructors.piSubstitution_native_filling _ _ _

/-- The fixed nonreflexive state-line Sigma consumer now preserves the full operation. -/
example :
    (NativeDecode.filling (liftSub (interval context) (twiceSub ≫ successorSub) ≫
      (LargeConstructors.sigma stateLine stateField).code)).transport
      (LargeConstructors.sigmaSubstitution stateLine stateField
        (liftSub (interval context) (twiceSub ≫ successorSub))) =
    NativeDecode.filling (LargeConstructors.sigma
      (liftSub (interval context) (twiceSub ≫ successorSub) ≫ stateLine)
      (liftSub (liftedDecode stateLine) (liftSub (interval context) (twiceSub ≫ successorSub)) ≫
        stateField)).code :=
  LargeConstructors.sigmaSubstitution_native_filling _ _ _

/-- The corresponding Pi equation retains the independently rebuilt decoder adapter. -/
example :
    (NativeDecode.filling (liftSub (interval context) (twiceSub ≫ successorSub) ≫
      (LargeConstructors.pi stateLine stateField).code)).transport
      (LargeConstructors.piSubstitution stateLine stateField
        (liftSub (interval context) (twiceSub ≫ successorSub))) =
    NativeDecode.filling (LargeConstructors.pi
      (liftSub (interval context) (twiceSub ≫ successorSub) ≫ stateLine)
      (liftSub (liftedDecode stateLine) (liftSub (interval context) (twiceSub ≫ successorSub)) ≫
        stateField)).code :=
  LargeConstructors.piSubstitution_native_filling _ _ _

end Original

namespace Cartesian
open SquareKit.Cubical.Cartesian SmallUniverse

/-- Subsingleton recovery includes every variable cap and every face subcontext. -/
theorem subsingleton_filling_unique {Γ : Context.{u}} {A : Family Γ}
    (h : ∀ x, Subsingleton (A.obj x)) (F G : Filling A) : F = G := by
  cases F with | mk ff =>
    cases G with | mk gg =>
      congr
      funext Δ p φ r b
      apply Term.ext
      intro x
      exact @Subsingleton.elim _ (h _) _ _

/-- The source graph determines each section in a presented discrete family. -/
theorem presented_filling_unique {Γ : Context.{u}} {A : Family Γ} {S : Type u}
    (e : A ≅ constantFamily Γ S) (F G : Filling A)
    (hF : F.Lawful) (hG : G.Lawful) : F = G := by
  cases F with | mk ff =>
    cases G with | mk gg =>
      congr
      funext Δ p φ r b
      exact (b.presentedFill_unique (Functor.isoWhiskerLeft p.mapElements e) _
        (hF.fills p φ r b).1).trans
          (b.presentedFill_unique (Functor.isoWhiskerLeft p.mapElements e) _
            (hG.fills p φ r b).1).symm

theorem presented_recovery {Ξ : Context.{u+1}} {A : Family Ξ}
    (P : SmallPresentation.Data.{u} A) {S : Type (u+1)}
    (e : A ≅ constantFamily Ξ S) (F : Filling A) (hF : F.Lawful) :
    (NativeDecode.filling (P.code F hF)).transport (P.nativeIso F hF) = F :=
  presented_filling_unique e _ F
    (Filling.transport_lawful _ _ (NativeDecode.filling_lawful _)) hF


/-- The chart uses Boolean negation before lifting; it is not the identity presentation. -/
def negatedPresentation (Ξ : Context.{1}) :
    SmallPresentation.Data.{0} (constantFamily Ξ (ULift.{1} Bool)) where
  Fiber _ := Bool
  equiv _ := {
    toFun := fun b => ⟨!b⟩
    invFun := fun b => !(b.down)
    left_inv := fun b => Bool.not_not b
    right_inv := fun b => ULift.ext (Bool.not_not b.down) }

theorem negatedPresentation_true (Ξ : Context.{1}) (x : Ξ.Elements) :
    ((negatedPresentation Ξ).equiv x true).down = false := rfl

theorem negated_bool_recovery (Ξ : Context.{1}) :
    (NativeDecode.filling ((negatedPresentation Ξ).code
      (presentedFilling (Iso.refl _)) (presentedFilling_lawful (Iso.refl _)))).transport
        ((negatedPresentation Ξ).nativeIso (presentedFilling (Iso.refl _)) (presentedFilling_lawful (Iso.refl _))) =
      presentedFilling (Iso.refl _) :=
  (negatedPresentation Ξ).native_filling_recovery _ (presentedFilling_lawful (Iso.refl _))


/-- Lift group arrows without discarding any nontrivial loop. -/
def groupSystemLift (V : Type) : GroupSystem CartesianHigherSeparation.Two V ≃
    GroupSystem (ULift.{1} CartesianHigherSeparation.Two) V where
  toFun T := {
    arrow := fun v w => ⟨T.arrow v w⟩
    identity := fun v => congrArg ULift.up (T.identity v)
    composition := fun v w z => congrArg ULift.up (T.composition v w z) }
  invFun T := {
    arrow := fun v w => (T.arrow v w).down
    identity := fun v => congrArg ULift.down (T.identity v)
    composition := fun v w z => congrArg ULift.down (T.composition v w z) }
  left_inv _ := rfl
  right_inv _ := rfl

def groupPresentation (Ξ : Context.{1}) : SmallPresentation.Data.{0}
    (GroupNerve.family (ULift.{1} CartesianHigherSeparation.Two) Ξ) where
  Fiber x := GroupSystem CartesianHigherSeparation.Two (Vertex x.obj.unop.dimension)
  equiv x := groupSystemLift (Vertex x.obj.unop.dimension)

/-- General recovery applies to each non-discrete group-nerve filler selection. -/
theorem group_filling_recovery (Ξ : Context.{1})
    (g : ULift.{1} CartesianHigherSeparation.Two) :
    (NativeDecode.filling ((groupPresentation Ξ).code (GroupNerve.chosenFilling g Ξ)
      (GroupNerve.chosenFilling_lawful g Ξ))).transport
      ((groupPresentation Ξ).nativeIso (GroupNerve.chosenFilling g Ξ)
        (GroupNerve.chosenFilling_lawful g Ξ)) = GroupNerve.chosenFilling g Ξ :=
  (groupPresentation Ξ).native_filling_recovery _ (GroupNerve.chosenFilling_lawful g Ξ)


namespace LargeGroup
abbrev point : Context.{1} := representable ⟨0⟩
abbrev G := ULift.{1} CartesianHigherSeparation.Two

def zero : Term (interval point) where
  val x := ⟨Cube.endpoint x.obj.unop false⟩
  property _ := rfl

def trivial : Term (GroupNerve.family G point) where
  val _ := GroupSystem.ofPotential (fun _ => 1)
  property _ := rfl

def emptyBox : OpenBox (GroupNerve.family G (total (interval point))) Subcontext.bot zero where
  tube := ⟨fun _ h => h.elim, fun _ h => h.elim⟩
  base := trivial
  boundary _ h := h.elim

def genericPoint : point.Elements := point.elementsMk (.op ⟨0⟩) ⟨𝟙 _⟩

theorem selected_arrow (g : G) :
    (((GroupNerve.chosenFilling g point).fill (projection (interval point))
      Subcontext.bot zero emptyBox).val (freshExtension genericPoint)).arrow
        (fun _ => false) (fun _ => true) = g := by
  simp only [GroupNerve.chosenFilling, GroupNerve.Fill.fillSection,
    GroupNerve.Fill.value, GroupNerve.Fill.system, GroupSystem.reindex, GroupSystem.conjugate]
  simp [GroupNerve.Fill.vertical, emptyBox, trivial, GroupSystem.ofPotential, zero, Subcontext.bot,
    genericPoint, freshExtension, freshBase, extendObj, projection, Cube.fresh, Cube.endpoint, Dim.eval]

/-- The large-context consumer really has distinct lawful selected operations. -/
theorem choices_distinct : GroupNerve.chosenFilling (1 : G) point ≠
    GroupNerve.chosenFilling (⟨CartesianHigherSeparation.nontrivial⟩ : G) point := by
  intro h
  have hh := congrArg (fun F : Filling (GroupNerve.family G point) =>
    ((F.fill (projection (interval point)) Subcontext.bot zero emptyBox).val
      (freshExtension genericPoint)).arrow (fun _ => false) (fun _ => true)) h
  rw [selected_arrow, selected_arrow] at hh
  exact CartesianHigherSeparation.nontrivial_ne_one (congrArg ULift.down hh).symm

end LargeGroup

/-- Recovery of selected records coexists with two lawful choices on one carrier.
Thus the discrete uniqueness proof does not extend to all Cartesian families. -/
theorem nonunique_selected_records :
    (∀ g : CartesianHigherSeparation.Two,
      (GroupNerve.chosenFilling g CartesianHigherSeparation.point).Lawful ∧
      decodedLocalFamily (CartesianHigherSeparation.classified g).code =
        CartesianHigherSeparation.classified g ∧
      (CartesianHigherSeparation.classified g).toFilling =
        GroupNerve.chosenFilling g CartesianHigherSeparation.point) ∧
    GroupNerve.chosenFilling (1 : CartesianHigherSeparation.Two)
        CartesianHigherSeparation.point ≠
      GroupNerve.chosenFilling CartesianHigherSeparation.nontrivial
        CartesianHigherSeparation.point :=
  ⟨fun g => ⟨CartesianHigherSeparation.both_lawful g,
    CartesianHigherSeparation.decode_classified g,
    CartesianHigherSeparation.classified_filling g⟩,
    CartesianHigherSeparation.selected_fillings_distinct⟩

end Cartesian
end Examples.LargeFamilyFillingRecovery
