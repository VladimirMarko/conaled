import SquareKit.Internal.PathTransport.GeneratedCylinderPrimitive
import SquareKit.Internal.PathTransport.UniversalTransferComparison
import Examples.ComparisonModification
import Examples.SignatureInterpretationMaps

/-! Selected C4 components, a genuinely dependent caller, and rejection of
incoherent objectwise choices. -/
noncomputable section
namespace Examples.GeneratedSelectedComparison
open CategoryTheory SquareKit.Internal.PathTransport
open GroupoidModel Comparison SignatureCylinder
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

local instance : Groupoid GroupoidTransport.C4 := Groupoid.ofIsGroupoid
abbrev C := Grpd.of GroupoidTransport.C4

def selected : (𝟭 C) ≅ 𝟭 C := NatIso.ofComponents
  (fun _ => asIso (show GroupoidTransport.point ⟶ GroupoidTransport.point from
    Multiplicative.ofAdd (1 : ZMod 4))) (by
      intro x y f
      change Multiplicative (ZMod 4) at f
      change Multiplicative.ofAdd (1 : ZMod 4) * f = f * Multiplicative.ofAdd (1 : ZMod 4)
      exact mul_comm _ _)

def before : C ⥤ Type := GroupoidTransport.ineffective
def alpha : before ⟶ (𝟭 C) ⋙ before := 𝟙 _

theorem square : alpha ≫ Functor.whiskerRight selected.hom before = alpha := rfl

/-- The actual generated component recovers the chosen nonidentity C4 label,
even though its action on the primitive fibers is trivial. -/
theorem chosen_quarter_turn :
    ((normalizedPrimitiveComparison (𝟭 C) before selected before alpha alpha square).hom.app
      ⟨⟨PUnit.unit⟩, GroupoidTransport.point⟩).fiber = Multiplicative.ofAdd (1 : ZMod 4) :=
  normalizedPrimitiveComparison_fiber _ _ _ _ _ _ _ _

theorem chosen_ne_identity :
    ((normalizedPrimitiveComparison (𝟭 C) before selected before alpha alpha square).hom.app
      ⟨⟨PUnit.unit⟩, GroupoidTransport.point⟩).fiber ≠ 𝟙 GroupoidTransport.point := by
  rw [chosen_quarter_turn]
  exact (by decide : Multiplicative.ofAdd (1 : ZMod 4) ≠ Multiplicative.ofAdd 0)

/-- The original source proof participates with the selected C4 component. -/
example : SectionCoherence (𝟭 C) before selected before alpha alpha square
    Typed.Authoring.UniversalTransfer.context Typed.Authoring.UniversalTransfer.type
    Typed.Authoring.UniversalTransfer.proof :=
  universalTransferComparison _ _ _ _ _ _ _

/-- A nonfaithful C4 base map and a noninjective fiber map still support the
same dependent J caller and its two-binder tail. -/
example : SectionCoherence ComparisonModification.left ComparisonModification.before
    ComparisonModification.comparison ComparisonModification.after
    ComparisonModification.alpha ComparisonModification.beta ComparisonModification.primitive_square
    SignatureInterpretationMaps.DependentTail.withFiber
    SignatureInterpretationMaps.DependentTail.command.motive.typing
    SignatureInterpretationMaps.DependentTail.generic :=
  sectionCoherence _ _ _ _ _ _ _ _ _ _

/-- Strict equality of the generated base-family maps would identify the
fixture's unequal primitive base functors. -/
theorem strict_family_rejected :
    generatedFamilyMap (Signature.mk
      (Context.mk ComparisonModification.C ComparisonModification.D ComparisonModification.left)
      ComparisonModification.before ComparisonModification.after ComparisonModification.alpha)
      (.empty : Typed.CtxDeriv [] Typed.emptyCode.{1}) (.base .empty) ≠
    generatedFamilyMap (Signature.mk
      (Context.mk ComparisonModification.C ComparisonModification.D ComparisonModification.right)
      ComparisonModification.before ComparisonModification.after ComparisonModification.beta)
      (.empty : Typed.CtxDeriv [] Typed.emptyCode.{1}) (.base .empty) := by
  intro h
  apply ComparisonModification.functors_unequal
  have he := congrArg (fun m => m.app (Discrete.mk PUnit.unit)) h
  simpa only [generatedFamilyMap_base] using he

example := contextComparison_trans selected selected before before alpha alpha alpha
  square square (by rfl) SignatureInterpretationMaps.DependentTail.withFiber

open SignatureInterpretationMaps.DependentTail in
example := contextComparison_substitution (𝟭 C) before selected before alpha alpha square
  (.telescope paths tail)
  (.telescope (.path (.ext context (.fiber point.deriv))
      (.sub (.base context) weakening) (.sub point.deriv weakening))
    (.pathReindex context (.base context) point.deriv tail weakening)) tailMap

namespace Incoherent

def constant : Codiscrete Bool ⥤ C := (Functor.const _).obj GroupoidTransport.point

def choices (x : Codiscrete Bool) : constant.obj x ≅ constant.obj x :=
  asIso (Multiplicative.ofAdd (if x.as then (1 : ZMod 4) else 0))

/-- Every proposed component is an isomorphism, but the bridge arrow prevents
these choices from defining a natural isomorphism. -/
theorem rejected : ¬ ∃ η : constant ≅ constant, ∀ x, η.app x = choices x := by
  rintro ⟨η, hη⟩
  have hn := η.hom.naturality (show (⟨false⟩ : Codiscrete Bool) ⟶ ⟨true⟩ from ())
  have hfalse := congrArg Iso.hom (hη ⟨false⟩)
  have htrue := congrArg Iso.hom (hη ⟨true⟩)
  change (𝟙 _) ≫ η.hom.app ⟨true⟩ = η.hom.app ⟨false⟩ ≫ (𝟙 _) at hn
  change η.hom.app ⟨false⟩ = _ at hfalse
  change η.hom.app ⟨true⟩ = _ at htrue
  rw [hfalse, htrue] at hn
  simp only [Category.id_comp, Category.comp_id] at hn
  have he : (1 : ZMod 4) = 0 := congrArg Multiplicative.toAdd hn
  exact (by decide : (1 : ZMod 4) ≠ 0) he

end Incoherent
end Examples.GeneratedSelectedComparison
