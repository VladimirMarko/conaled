import SquareKit.Internal.DependentJudgments.CoherentGroupoidMaps
import Examples.GroupoidRoutes
import Examples.GroupoidComprehensionBoundary

/-! The selected C₄ generator acts on the binary family, while the kernel
loop remains observable separately from the resulting binary value. -/
noncomputable section
namespace Examples.CoherentGroupoidPresentations
open CategoryTheory CategoryTheory.Functor
open SquareKit.Internal.PathTransport.GroupoidModel
open SquareKit.Internal.DependentJudgments.CoherentGroupoidMaps
open Examples.GroupoidTransport
open Examples.GroupoidRoutes
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev UnitContext := @Grpd.of (Discrete PUnit.{1}) (Groupoid.ofIsGroupoid (C := Discrete PUnit.{1}))
abbrev LoopContext := Grpd.of C4

def pointSub : UnitContext ⥤ LoopContext := (Functor.const _).obj point

def generatorComparison : pointSub ≅ pointSub :=
  NatIso.ofComponents (fun _ => asIso (label 1)) (by intros; simp [pointSub])

abbrev binaryGroupoid : LoopContext ⥤ Grpd := setFamily binary
abbrev pulledBinary : UnitContext ⥤ Grpd := pointSub ⋙ binaryGroupoid

def zeroSection : Section pulledBinary where
  obj _ := ⟨0⟩
  map _ := eqToHom (by rfl)
  map_id _ := rfl
  map_comp _ _ := by simp

def generatorTransport : DisplayMap pulledBinary pulledBinary :=
  DisplayMap.substitution pointSub pointSub generatorComparison

/-- The comparison path changes the selected value; replacing it by reflexivity
would incorrectly leave zero fixed. -/
theorem generatorTransport_zero :
    ((generatorTransport.term zeroSection).obj ⟨PUnit.unit⟩).as = (1 : ZMod 2) := by
  have h := Functor.congr_obj
    (DisplayMap.ofNatural_term_lift (whiskerRight generatorComparison.hom binaryGroupoid)
      zeroSection) (Discrete.mk PUnit.unit)
  have hh := congrArg (fun x : Extend pulledBinary => x.fiber.as) h
  exact hh

theorem generatorComparison_ne_refl : generatorComparison ≠ Iso.refl pointSub := by
  intro h
  have hh := congrArg (fun e : pointSub ≅ pointSub => e.hom.app ⟨PUnit.unit⟩) h
  have hn : (1 : ZMod 4) = 0 := labels_injective hh
  exact (by decide : (1 : ZMod 4) ≠ 0) hn

def wrappedBinary : C4 ⥤ Type where
  obj _ := ULift.{0} (ZMod 2)
  map p := ↾fun b => ⟨parity (Multiplicative.toAdd p) + b.down⟩
  map_id _ := by ext b; exact zero_add b.down
  map_comp p q := by
    ext b
    change parity (Multiplicative.toAdd q + Multiplicative.toAdd p) + b.down = _
    rw [map_add, add_assoc]
    rfl

def fiberEquiv : ZMod 2 ≃ ULift.{0} (ZMod 2) where
  toFun b := ⟨b + 1⟩
  invFun b := b.down + 1
  left_inv := by decide
  right_inv := by decide

def familyComparison : binary ≅ wrappedBinary :=
  NatIso.ofComponents (fun _ => fiberEquiv.toIso) (by
    intro x y p
    ext b
    change ULift.up ((parity (Multiplicative.toAdd p) + b) + 1) =
      ULift.up (parity (Multiplicative.toAdd p) + (b + 1))
    rw [add_assoc])

abbrev wrappedGroupoid : LoopContext ⥤ Grpd := setFamily wrappedBinary

def wrappedDisplay : DisplayMap pulledBinary (pointSub ⋙ wrappedGroupoid) :=
  DisplayMap.reindex (whiskerRight familyComparison.hom discrete) pointSub

/-- Actual unequal fiber carriers, with the selected coordinate change. -/
theorem wrapped_zero :
    ((wrappedDisplay.term zeroSection).obj ⟨PUnit.unit⟩).as.down = (1 : ZMod 2) := by
  have h := Functor.congr_obj (DisplayMap.ofNatural_term_lift
    (whiskerLeft pointSub (whiskerRight familyComparison.hom discrete)) zeroSection)
    (Discrete.mk PUnit.unit)
  exact congrArg (fun x : Extend (pointSub ⋙ wrappedGroupoid) => x.fiber.as.down) h

/-- Ordinary contextual J transport retains the selected path's action after
changing the fiber presentation. Naturality supplies the conclusion. -/
theorem source_transport (p q : point ⟶ point) (b : ZMod 2) :
    fiberEquiv (sourceTransport binary p q b) =
      sourceTransport wrappedBinary p q (fiberEquiv b) := by
  rw [sourceTransport_eq, sourceTransport_eq]
  exact ConcreteCategory.congr_hom (familyComparison.hom.naturality p) b

/-- The ineffective kernel action does not erase the selected identity witness. -/
example : label (2 : ZMod 4) ≠ label 0 := by
  intro h
  exact (by decide : (2 : ZMod 4) ≠ 0) (labels_injective h)

example : sourceTransport wrappedBinary (label 2) (label 0) (fiberEquiv 0) = fiberEquiv 0 := by
  rw [← source_transport, sourceTransport_eq, kernel_two]

namespace LoopFibers
attribute [local instance] uliftCategory
local instance : CategoryTheory.Groupoid (ULift.{0} C4) where
  __ := uliftCategory C4
  inv {X Y} f := @CategoryTheory.Groupoid.inv C4 inferInstance X.down Y.down f
  inv_comp {X Y} f := @CategoryTheory.Groupoid.inv_comp C4 inferInstance X.down Y.down f
  comp_inv {X Y} f := @CategoryTheory.Groupoid.comp_inv C4 inferInstance X.down Y.down f

abbrev A : LoopContext ⥤ Grpd := constant C4
abbrev B : LoopContext ⥤ Grpd := constant (ULift.{0} C4)

def wrap : A ⟶ B where
  app _ := (show C4 ⥤ ULift.{0} C4 from CategoryTheory.ULift.upFunctor)
  naturality := by intros; rfl

/-- The projection comparison carries the nonzero central base loop. -/
def coherentWrap : DisplayMap A B where
  context := CategoryTheory.Equivalence.refl
  total := (DisplayMap.ofNatural wrap).total
  over := NatIso.ofComponents (fun x => asIso
    (show x.base ⟶ x.base from Multiplicative.ofAdd (1 : ZMod 4))) (by
      intro x y f
      change Multiplicative.ofAdd (1 : ZMod 4) * (show Multiplicative (ZMod 4) from f.base) =
        (show Multiplicative (ZMod 4) from f.base) * Multiplicative.ofAdd (1 : ZMod 4)
      exact mul_comm _ _)

def diagonal : Section A where
  obj _ := point
  map f := f
  map_id _ := rfl
  map_comp f g := by simp [constant, Grpd.id_eq_id]

/-- The ordinary groupoid fibers retain their nontrivial arrows. -/
theorem selected_loop (n : ZMod 4) :
    (coherentWrap.term diagonal).map (label n) = Multiplicative.ofAdd n := by
  simp [DisplayMap.term, Section.ofOver, Section.lift,
    ContextualElimination.normalize, ContextualElimination.normalizeIso,
    ContextualElimination.normalizeObj, Grothendieck.transportIso, Grothendieck.isoMk,
    coherentWrap, DisplayMap.image, DisplayMap.imageOver, DisplayMap.ofNatural,
    diagonal, wrap, constant, Grpd.forgetToCat, Grpd.id_eq_id, label]
  rfl

example : (coherentWrap.term diagonal).map (label 2) ≠
    (coherentWrap.term diagonal).map (label 0) := by
  rw [selected_loop, selected_loop]
  intro h
  exact (by decide : (2 : ZMod 4) ≠ 0) (congrArg Multiplicative.toAdd h)
theorem selected_source_loop (n : ZMod 4) :
    (coherentWrap.term diagonal).map
      (Examples.AgdaTransferModels.sourceLabel binary 0 n) = Multiplicative.ofAdd n := by
  rw [Examples.AgdaTransferModels.sourceLabel_eq, selected_loop]

/-- The projection coherence cannot be replaced by the identity comparison. -/
theorem projection_nontrivial :
    coherentWrap.over.hom.app (diagonal.lift.obj point) ≠ 𝟙 point := by
  intro h
  have hh : (1 : ZMod 4) = 0 := congrArg Multiplicative.toAdd h
  exact (by decide : (1 : ZMod 4) ≠ 0) hh

abbrev WrappedContext := Grpd.of (ULift.{0} C4)
abbrev wrappedContextFamily : WrappedContext ⥤ Grpd := constant (ULift.{0} C4)

def contextChange : DisplayMap B wrappedContextFamily :=
  DisplayMap.changeBase CategoryTheory.ULift.equivalence wrappedContextFamily

def completeComparison : DisplayMap A wrappedContextFamily := coherentWrap.compose contextChange

def sequentialComparison := coherentWrap.termCompose contextChange diagonal

/-- Both context and fiber carriers change; the selected loop remains nonzero. -/
theorem different_context_loop (n : ZMod 4) :
    (completeComparison.term diagonal).map
      (show ULift.up point ⟶ ULift.up point from label n) = Multiplicative.ofAdd n := by
  simp [completeComparison, DisplayMap.compose, DisplayMap.changeBase, DisplayMap.term,
    Section.ofOver, Section.lift, ContextualElimination.normalize,
    ContextualElimination.normalizeIso, ContextualElimination.normalizeObj,
    Grothendieck.transportIso, Grothendieck.isoMk, coherentWrap, contextChange,
    DisplayMap.image, DisplayMap.imageOver, DisplayMap.ofNatural, diagonal, wrap,
    constant, Grpd.forgetToCat, Grpd.id_eq_id, label]
  rfl

/-- Sequential and composed transport compare along the retained normalization
arrows, including after an arbitrary substitution. -/
example {Ξ : Grpd} (σ : Ξ ⥤ WrappedContext) :
    isoWhiskerLeft σ sequentialComparison ≪≫ completeComparison.termSubstitution diagonal σ =
      isoWhiskerLeft σ (contextChange.termComparison (coherentWrap.term diagonal) ≪≫
        isoWhiskerLeft contextChange.context.inverse
          (isoWhiskerRight (coherentWrap.termComparison diagonal) contextChange.total)) :=
  DisplayMap.termCompose_substitution coherentWrap contextChange diagonal σ

def contextBack : DisplayMap wrappedContextFamily B :=
  DisplayMap.changeBase CategoryTheory.ULift.equivalence.symm B

/-- Three actual maps, changing carriers twice, satisfy the selected associativity law. -/
example :
    contextBack.mapComparison (coherentWrap.termCompose contextChange diagonal) ≪≫
      (coherentWrap.compose contextChange).termCompose contextBack diagonal ≪≫
        DisplayMap.termAssociator coherentWrap contextChange contextBack diagonal =
    contextChange.termCompose contextBack (coherentWrap.term diagonal) ≪≫
      coherentWrap.termCompose (contextChange.compose contextBack) diagonal :=
  DisplayMap.termCompose_assoc coherentWrap contextChange contextBack diagonal

example :
    (DisplayMap.identity A).termCompose coherentWrap diagonal ≪≫
      DisplayMap.termLeftUnit coherentWrap diagonal =
    coherentWrap.mapComparison (DisplayMap.termIdentity diagonal) :=
  DisplayMap.termCompose_leftUnit coherentWrap diagonal

example :
    coherentWrap.termCompose (DisplayMap.identity B) diagonal ≪≫
      DisplayMap.termRightUnit coherentWrap diagonal =
    DisplayMap.termIdentity (coherentWrap.term diagonal) :=
  DisplayMap.termCompose_rightUnit coherentWrap diagonal

abbrev PathBase := @Grpd.of (PathComparison.PathCtx A diagonal) Groupoid.ofIsGroupoid

def root : ContextualElimination.NormalizedEquivalence (Cat.of LoopContext)
    (Cat.of PathBase) where
  equiv := PathComparison.pathEquivalence A diagonal
  unit_obj _ := rfl
  unit_hom _ := rfl

abbrev motive : PathBase ⥤ Grpd := constant C4
abbrev wrappedMotive : PathBase ⥤ Grpd := constant (ULift.{0} C4)

def motiveMap : motive ⟶ wrappedMotive where
  app _ := (show C4 ⥤ ULift.{0} C4 from CategoryTheory.ULift.upFunctor)
  naturality := by intros; rfl

def branch : Section (root.equiv.functor ⋙ motive) where
  obj _ := point
  map f := f
  map_id _ := rfl
  map_comp f g := by simp [constant, Grpd.id_eq_id]

/-- The branch comparison constructs the chosen contextual J comparison over
an actual path context with non-discrete motive fibers. -/
def chosenJComparison := DisplayMap.naturalEliminationComparison root motiveMap branch

def mappedJ := (DisplayMap.ofNatural motiveMap).term (eliminateSection root motive branch)
def targetJ := eliminateSection root wrappedMotive
  ((DisplayMap.reindex motiveMap root.equiv.functor).term branch)

theorem mappedJ_branch : mappedJ.reindex root.equiv.functor =
    (DisplayMap.reindex motiveMap root.equiv.functor).term branch := by
  rw [mappedJ, ← DisplayMap.reindex_term]
  exact congrArg ((DisplayMap.reindex motiveMap root.equiv.functor).term)
    (eliminateSection_beta root motive branch)

theorem targetJ_branch : targetJ.reindex root.equiv.functor =
    (DisplayMap.reindex motiveMap root.equiv.functor).term branch :=
  eliminateSection_beta _ _ _

theorem chosenJ_selected_loop (n : ZMod 4) :
    Multiplicative.toAdd ((mappedJ.reindex root.equiv.functor).map (label n)) = n := by
  rw [mappedJ_branch]
  simp [DisplayMap.term, Section.ofOver, Section.lift,
    ContextualElimination.normalize, ContextualElimination.normalizeIso,
    ContextualElimination.normalizeObj, Grothendieck.transportIso, Grothendieck.isoMk,
    DisplayMap.reindex, DisplayMap.image, DisplayMap.imageOver, DisplayMap.ofNatural,
    branch, motiveMap, constant, Grpd.forgetToCat, Grpd.id_eq_id, label]
  rfl


/-- The comparison of chosen J terms is natural on every path-context arrow. -/
theorem chosenJ_arrow {a b : PathBase} (p : a ⟶ b) :
    mappedJ.lift.map p ≫ chosenJComparison.hom.app b =
      chosenJComparison.hom.app a ≫ targetJ.lift.map p :=
  chosenJComparison.hom.naturality p

end LoopFibers

namespace Shear
open Examples.GroupoidComprehensionBoundary
/-- The admitted display maps include a commuting shear that changes chosen lifts. -/
def comparison : DisplayMap (Γ := Grpd.of G) (Δ := Grpd.of G) A A where
  context := CategoryTheory.Equivalence.refl
  total := shear
  over := eqToIso shear_over_base

example : comparison.total.map (horizontal (Multiplicative.ofAdd (1 : ZMod 2))) ≠
    horizontal (Multiplicative.ofAdd (1 : ZMod 2)) := shear_not_horizontal
end Shear

end Examples.CoherentGroupoidPresentations
