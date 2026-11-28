import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.Tactic.Ring
import Mathlib.CategoryTheory.Bicategory.LocallyDiscrete
import Mathlib.Data.ZMod.Basic
import SquareKit.FiniteHigherUniversal

/-! A non-effective descent cone, a missing mixed two-cell, and preservation of nonzero two-cells by the actual completion unit. -/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
namespace Examples.FiniteHigherCompletion.Core
open CategoryTheory Bicategory
open SquareKit.PseudofunctorMapping
abbrev A := Multiplicative (ZMod 2)
abbrev K := LocallyDiscrete (Discrete Bool) × SquareKit.DoubleDelooping.Space A

def point (b : Bool) : K := (⟨⟨b⟩⟩, SquareKit.DoubleDelooping.point A)
def mixed : K × K := (point false, point true)
def diagonal : Pseudofunctor K (K × K) := pair (Pseudofunctor.id K) (Pseudofunctor.id K)

theorem mixed_not_generated (x : K) : ¬ Nonempty (diagonal.obj x ⟶ mixed) := by
  rintro ⟨f⟩
  have hf : x.1.as.as = false := Discrete.eq_of_hom f.1.1.as
  have ht : x.1.as.as = true := Discrete.eq_of_hom f.2.1.as
  exact Bool.false_ne_true (hf.symm.trans ht)

def cell (b : Bool) (a : A) : (𝟙 (point b)) ⟶ (𝟙 (point b)) := (𝟙 _, a)
def mixedCell : (𝟙 (point false, point false)) ⟶ (𝟙 (point false, point false)) :=
  (cell false 1, cell false (Multiplicative.ofAdd 1))

theorem mixedCell_not_generated : ¬ ∃ a : (𝟙 (point false)) ⟶ (𝟙 (point false)),
    diagonal.map₂ a = mixedCell := by
  rintro ⟨a,h⟩
  have h0 : a.2 = (1 : A) := congrArg (fun t => t.1.2) h
  have h1 : a.2 = Multiplicative.ofAdd (1 : ZMod 2) := congrArg (fun t => t.2.2) h
  have hz := congrArg Multiplicative.toAdd (h0.symm.trans h1)
  exact (by decide : (0 : ZMod 2) ≠ 1) hz

theorem mixedCell_nonidentity : mixedCell ≠ 𝟙 (𝟙 (point false, point false)) := by
  intro h
  have hz := congrArg (fun t => Multiplicative.toAdd t.2.2) h
  exact (by decide : (1 : ZMod 2) ≠ 0) hz

end Examples.FiniteHigherCompletion.Core
namespace Examples.FiniteHigherCompletion
open CategoryTheory Bicategory SquareKit.HigherCategory
open SquareKit.ContractibleBicategory SquareKit.FiniteHigherCompletion Examples.FiniteHigherCompletion.Core
open scoped Pseudofunctor.StrongTrans
abbrev input : FullDiagram.{0,0,0} where
  top := K
  left := K
  right := K
  empty := Terminal
  rL := Pseudofunctor.id K
  rR := Pseudofunctor.id K
  r0 := toTerminal
  sL := toTerminal
  sR := toTerminal
  cL := comparisonEquivalence _ _
  cR := comparisonEquivalence _ _

theorem actual_unit_top : (unit input).top = diagonal := rfl

theorem actual_unit_object_obstruction (x : input.top) :
    ¬ Nonempty ((unit input).top.obj x ⟶ (mixed : (completion input).top)) :=
  mixed_not_generated x

theorem actual_unit_cell_obstruction :
    ¬ ∃ a : (𝟙 (point false)) ⟶ (𝟙 (point false)),
      (unit input).top.map₂ a = mixedCell := mixedCell_not_generated

theorem actual_unit_preserves_nonzero_cell :
    (unit input).top.map₂ (cell false (Multiplicative.ofAdd 1)) ≠
      𝟙 ((unit input).top.map (𝟙 (point false))) := by
  intro h
  have hz := congrArg (fun t => Multiplicative.toAdd t.1.2) h
  exact (by decide : (1 : ZMod 2) ≠ 0) hz

end Examples.FiniteHigherCompletion

namespace Examples.FiniteHigherCompletion
open CategoryTheory Bicategory SquareKit.HigherCategory Examples.FiniteHigherCompletion.Core
open SquareKit.SieveCone SquareKit.FiniteHigherCompletion SquareKit.FiniteHigherDescent
noncomputable def mixedCone : BinaryCone input :=
  ⟨point false, ⟨point true, SquareKit.ContractibleBicategory.toTerminal.obj (point true),
    Bicategory.Equivalence.id _⟩, Bicategory.Equivalence.id _⟩

theorem mixedCone_not_effective (x : input.top) :
    ¬ Nonempty (Bicategory.Equivalence ((binaryRestriction input).obj x) mixedCone) := by
  rintro ⟨e⟩
  exact mixed_not_generated x ⟨(binaryProjection input).map e.hom⟩

theorem input_not_stack : ¬ IsStackOnAllCoveringSieves input := by
  intro h
  obtain ⟨x, hx⟩ := ((allCoveringSieves_iff input).mp h .binary).1 mixedCone
  exact mixedCone_not_effective x hx

theorem output_stack : IsStackOnAllCoveringSieves (completion input) :=
  SquareKit.FiniteHigherCompletionDescent.completion_allCoveringSieves input

end Examples.FiniteHigherCompletion

end

namespace Examples.FiniteHigherCompletion
open CategoryTheory Bicategory SquareKit.HigherCategory SquareKit.FiniteHigherCompletion
open SquareKit.PseudofunctorMapping SquareKit.FiniteHigherRecovery
open SquareKit.FiniteHigherMapComposition SquareKit.PseudofunctorComposition
open Core
open scoped Pseudofunctor.StrongTrans

/-- The preserved output two-cell cannot be encoded faithfully in the parallel
cells of any ordinary category. -/
theorem no_faithful_ordinary_encoding {C : Type} [Category C]
    (x y : LocallyDiscrete C) (f g : x ⟶ y)
    (forget : ((unit input).top.map (𝟙 (point false)) ⟶
      (unit input).top.map (𝟙 (point false))) → (f ⟶ g)) :
    ¬ Function.Injective forget := by
  intro h
  exact actual_unit_preserves_nonzero_cell (h (Subsingleton.elim _ _))

noncomputable abbrev completeInput := completion input

noncomputable def completePairCounit : Bicategory.Equivalence
    ((Pseudofunctor.id completeInput.top).comp (pair completeInput.rL completeInput.rR))
    (Pseudofunctor.id completeInput.top) :=
  equalityEquivalence (comp_id _)

noncomputable def completeInverseUnit : SquareKit.FiniteHigherMap.Map
    (F := completion completeInput) (T := completeInput) :=
  inverseUnit completeInput (Pseudofunctor.id _) completePairCounit
    (SquareKit.DoubleDelooping.point PUnit.{1})

/-- Recovery uses the actual unit of an independently proved complete input. -/
noncomputable def completeUnitLeftRecovery : Bicategory.Equivalence
    (compose (unit completeInput) completeInverseUnit) (identityMap completeInput) := by
  letI := atomicPairLocal input
  exact unitLeftRecovery completeInput (Pseudofunctor.id _) completePairCounit
    (SquareKit.DoubleDelooping.point PUnit.{1})

noncomputable def completeUnitRightRecovery : Bicategory.Equivalence
    (compose completeInverseUnit (unit completeInput)) (identityMap (completion completeInput)) :=
  unitRightRecovery completeInput (Pseudofunctor.id _) completePairCounit
    (SquareKit.DoubleDelooping.point PUnit.{1})

theorem maps_into_output (F : FullDiagram.{0,0,0}) :
    IsBiequivalence (SquareKit.FiniteHigherUniversal.precomposeStackUnit F completeInput
      output_stack) :=
  SquareKit.FiniteHigherUniversal.precomposeStackUnit_biequivalence F completeInput output_stack

end Examples.FiniteHigherCompletion

noncomputable section
namespace Examples.FiniteHigherCompletion.WeakMap
open CategoryTheory Bicategory SquareKit
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
abbrev A := ZMod 2
abbrev G := Multiplicative A
abbrev Source := LocallyDiscrete (SingleObj G)
abbrev Target := DoubleDelooping.Space G
abbrev point : Source := ⟨SingleObj.star G⟩
abbrev targetPoint : Target := DoubleDelooping.point G
abbrev targetArrow : targetPoint ⟶ targetPoint := DoubleDelooping.arrow G

def cellIso (a : A) : targetArrow ≅ targetArrow where
  hom := Multiplicative.ofAdd a
  inv := Multiplicative.ofAdd (-a)
  hom_inv_id := by change Multiplicative.ofAdd (-a + a) = Multiplicative.ofAdd 0; exact congrArg Multiplicative.ofAdd (neg_add_cancel a)
  inv_hom_id := by change Multiplicative.ofAdd (a + -a) = Multiplicative.ofAdd 0; exact congrArg Multiplicative.ofAdd (add_neg_cancel a)

def weakMap : Pseudofunctor Source Target :=
  LocallyDiscrete.mkPseudofunctor (B₀ := SingleObj G)
    (fun _ => targetPoint)
    (fun _ => targetArrow)
    (fun _ => cellIso 0)
    (fun f g => cellIso ((Multiplicative.toAdd (show G from f)) * (Multiplicative.toAdd (show G from g))))
    (by
      intro a b c d f g h
      dsimp [cellIso]
      let fv : A := Multiplicative.toAdd (show G from f)
      let gv : A := Multiplicative.toAdd (show G from g)
      let hv : A := Multiplicative.toAdd (show G from h)
      change Multiplicative.ofAdd ((((-(fv * (hv + gv)) + -(gv * hv)) + 0) + fv * gv) + (gv + fv) * hv) = Multiplicative.ofAdd 0
      congr 1
      ring)
    (by
      intro a b f
      dsimp [cellIso]
      change Multiplicative.ofAdd ((0 + 0) + 0 * (Multiplicative.toAdd (show G from f))) = Multiplicative.ofAdd 0
      simp)
    (by
      intro a b f
      dsimp [cellIso]
      change Multiplicative.ofAdd (0 + (0 + (Multiplicative.toAdd (show G from f)) * 0)) = Multiplicative.ofAdd 0
      simp)

def strictFunctor : SingleObj G ⥤ Target where
  obj _ := targetPoint
  map _ := targetArrow

def zeroMap : Pseudofunctor Source Target := strictFunctor.toPseudofunctor'

abbrev generator : point ⟶ point := ⟨Multiplicative.ofAdd (1 : A)⟩

theorem generator_square : generator ≫ generator = 𝟙 point := by
  rfl

theorem weakMap_generator_comparison :
    (weakMap.mapComp generator generator).hom = Multiplicative.ofAdd (1 : A) := rfl

theorem zeroMap_generator_comparison :
    (zeroMap.mapComp generator generator).hom = Multiplicative.ofAdd (0 : A) := rfl

theorem no_strong_to_zero (τ : Pseudofunctor.StrongTrans weakMap zeroMap) : False := by
  have hid := τ.naturality_id point
  change (1 : G) * (τ.naturality (𝟙 point)).hom = 1 * (1 * 1) at hid
  have hid' : (τ.naturality (𝟙 point)).hom = (1 : G) := by simpa using hid
  have hc := τ.naturality_comp generator generator
  rw [generator_square] at hc
  change (1 : G) * (τ.naturality (𝟙 point)).hom =
    (((((1 : G) * (τ.naturality generator).hom) * 1) *
      (τ.naturality generator).hom) * 1) * Multiplicative.ofAdd (1 : A) at hc
  rw [hid'] at hc
  have hv := congrArg Multiplicative.toAdd hc
  change (0 : A) =
    ((((0 + Multiplicative.toAdd (show G from (τ.naturality generator).hom)) + 0) +
      Multiplicative.toAdd (show G from (τ.naturality generator).hom)) + 0) + 1 at hv
  have twice (a : A) : a + a = 0 := by
    rw [← two_mul, show (2 : A) = 0 from rfl, zero_mul]
  simp only [zero_add, add_zero, twice] at hv
  exact zero_ne_one hv

instance noStrongToZero : IsEmpty (Pseudofunctor.StrongTrans weakMap zeroMap) := ⟨no_strong_to_zero⟩

theorem same_objects (x : Source) : weakMap.obj x = zeroMap.obj x := rfl

theorem same_arrows {x y : Source} (f : x ⟶ y) : weakMap.map f = zeroMap.map f := rfl

theorem zero_comparison {x y z : Source} (f : x ⟶ y) (g : y ⟶ z) :
    (zeroMap.mapComp f g).hom = (1 : G) := rfl

theorem weak_self_transformation : Nonempty (Pseudofunctor.StrongTrans weakMap weakMap) :=
  ⟨Pseudofunctor.StrongTrans.id weakMap⟩

theorem zero_self_transformation : Nonempty (Pseudofunctor.StrongTrans zeroMap zeroMap) :=
  ⟨Pseudofunctor.StrongTrans.id zeroMap⟩

theorem no_strong_from_zero (τ : Pseudofunctor.StrongTrans zeroMap weakMap) : False := by
  have hid := τ.naturality_id point
  change (1 : G) * (τ.naturality (𝟙 point)).hom = 1 * (1 * 1) at hid
  have hid' : (τ.naturality (𝟙 point)).hom = (1 : G) := by simpa using hid
  have hc := τ.naturality_comp generator generator
  rw [generator_square] at hc
  change Multiplicative.ofAdd (1 : A) * (τ.naturality (𝟙 point)).hom =
    (((((1 : G) * (τ.naturality generator).hom) * 1) *
      (τ.naturality generator).hom) * 1) * 1 at hc
  rw [hid'] at hc
  have hv := congrArg Multiplicative.toAdd hc
  change (1 : A) + 0 =
    ((((0 + Multiplicative.toAdd (show G from (τ.naturality generator).hom)) + 0) +
      Multiplicative.toAdd (show G from (τ.naturality generator).hom)) + 0) + 0 at hv
  have twice (a : A) : a + a = 0 := by
    rw [← two_mul, show (2 : A) = 0 from rfl, zero_mul]
  simp only [zero_add, add_zero, twice] at hv
  exact one_ne_zero hv

instance noStrongFromZero : IsEmpty (Pseudofunctor.StrongTrans zeroMap weakMap) :=
  ⟨no_strong_from_zero⟩

end Examples.FiniteHigherCompletion.WeakMap

namespace Examples.FiniteHigherCompletion.ChainControl
open CategoryTheory Bicategory SquareKit SquareKit.HigherCategory SquareKit.FiniteHigherMap SquareKit.FiniteHigherCell
open SquareKit.PseudofunctorMapping SquareKit.PseudofunctorPostcomposition SquareKit.PseudofunctorComposition
open SquareKit.ContractibleBicategory SquareKit.FiniteHigherCompletion
open scoped Pseudofunctor.StrongTrans
abbrev G := Multiplicative (ZMod 2)
abbrev D := DoubleDelooping.Space G
abbrev p : Terminal := DoubleDelooping.point PUnit.{1}

def zero : Pseudofunctor Terminal D where
  obj _ := DoubleDelooping.point G
  map _ := DoubleDelooping.arrow G
  map₂ _ := (1 : G)
  mapId _ := Iso.refl _
  mapComp _ _ := Iso.refl _
  map₂_id _ := rfl
  map₂_comp _ _ := rfl
  map₂_whisker_left := by intros; rfl
  map₂_whisker_right := by intros; rfl
  map₂_associator := by intros; rfl
  map₂_left_unitor := by intros; rfl
  map₂_right_unitor := by intros; rfl

theorem terminal_naturality {P Q : Pseudofunctor Terminal D} (a b : P ⟶ Q)
    {x y : Terminal} (f : x ⟶ y) : (a.naturality f).hom = (b.naturality f).hom := by
  have hy : y = x := Subsingleton.elim _ _
  subst y
  have hf : f = 𝟙 x := Subsingleton.elim _ _
  subst f
  simp only [Pseudofunctor.StrongTrans.naturality_id_hom]
  rfl

def scalarMod {P Q : Pseudofunctor Terminal D} (a b : P ⟶ Q) (g : G) : a ⟶ b where
  as.app _ := g
  as.naturality f := by
    change (show G from (b.naturality f).hom) * g = g * (show G from (a.naturality f).hom)
    rw [terminal_naturality a b f]
    exact mul_comm _ _

def scalarIso {P Q : Pseudofunctor Terminal D} (a b : P ⟶ Q) (g : G) : a ≅ b where
  hom := scalarMod a b g
  inv := scalarMod b a g⁻¹
  hom_inv_id := by ext x; change g⁻¹ * g = 1; exact inv_mul_cancel g
  inv_hom_id := by ext x; change g * g⁻¹ = 1; exact mul_inv_cancel g

def terminalDiagram : FullDiagram.{0,0,0} where
  top := Terminal
  left := Terminal
  right := Terminal
  empty := Terminal
  rL := Pseudofunctor.id _
  rR := Pseudofunctor.id _
  r0 := Pseudofunctor.id _
  sL := Pseudofunctor.id _
  sR := Pseudofunctor.id _
  cL := equalityEquivalence (id_comp (Pseudofunctor.id _))
  cR := equalityEquivalence (id_comp (Pseudofunctor.id _))

def observableDiagram : FullDiagram.{0,0,0} where
  top := Terminal
  left := Terminal
  right := Terminal
  empty := D
  rL := Pseudofunctor.id _
  rR := Pseudofunctor.id _
  r0 := zero
  sL := zero
  sR := zero
  cL := equalityEquivalence (id_comp zero)
  cR := equalityEquivalence (id_comp zero)

def commonCore : MapCore terminalDiagram observableDiagram where
  top := Pseudofunctor.id _
  left := Pseudofunctor.id _
  right := Pseudofunctor.id _
  empty := zero
  topLeft := equalityEquivalence rfl
  topRight := equalityEquivalence rfl
  topEmpty := equalityEquivalence rfl
  leftEmpty := equalityEquivalence rfl
  rightEmpty := equalityEquivalence rfl

def chiMap (g : G) : Map (F := terminalDiagram) (T := observableDiagram) where
  toMapCore := commonCore
  leftCoherence := scalarIso _ _ g
  rightCoherence := scalarIso _ _ 1

theorem same_components_and_edges (g h : G) : (chiMap g).toMapCore = (chiMap h).toMapCore := rfl

theorem observed_chi (g : G) : (leftChi (chiMap g) p).hom = g := by
  dsimp [leftChi, appIso, leftPastedAppIso, scalarIso, scalarMod, chiMap, observableDiagram]
  change ((1 : G) * 1) * 1 * g = g
  simp

theorem same_right_chain (g h : G) : (chiMap g).rightCoherence = (chiMap h).rightCoherence := rfl

theorem distinct_chains : chiMap 1 ≠ chiMap (Multiplicative.ofAdd (1 : ZMod 2)) := by
  intro h
  have hc := congrArg (fun H => (show G from (leftChi H p).hom)) h
  rw [observed_chi, observed_chi] at hc
  exact (show (0 : ZMod 2) ≠ 1 by decide) (congrArg Multiplicative.toAdd hc)

def identityCandidate : ArrowCore (chiMap 1) (chiMap (Multiplicative.ofAdd (1 : ZMod 2))) where
  top := (arrowCoreId (chiMap 1)).top
  left := (arrowCoreId (chiMap 1)).left
  right := (arrowCoreId (chiMap 1)).right
  empty := (arrowCoreId (chiMap 1)).empty
  topLeft := (arrowCoreId (chiMap 1)).topLeft
  topRight := (arrowCoreId (chiMap 1)).topRight
  topEmpty := (arrowCoreId (chiMap 1)).topEmpty
  leftEmpty := (arrowCoreId (chiMap 1)).leftEmpty
  rightEmpty := (arrowCoreId (chiMap 1)).rightEmpty

theorem identity_candidate_squares_zero :
    identityCandidate.topEmpty.hom.as.app p = (1 : G) ∧
    identityCandidate.leftEmpty.hom.as.app p = (1 : G) ∧
    identityCandidate.rightEmpty.hom.as.app p = (1 : G) := ⟨rfl, rfl, rfl⟩

theorem identity_candidate_rejected
    (a : Arrow (chiMap 1) (chiMap (Multiplicative.ofAdd (1 : ZMod 2))))
    (ha : a.toArrowCore = identityCandidate) : False := by
  have h := a.leftCoherence p
  change (leftChi (chiMap 1) p).hom ▷ observableDiagram.r0.map (a.toArrowCore.top.app p) ≫
      (leftPastedSquare a.toArrowCore p).hom =
    (leftDirectSquare a.toArrowCore p).hom ≫ a.toArrowCore.empty.app _ ◁
      (leftChi (chiMap (Multiplicative.ofAdd (1 : ZMod 2))) p).hom at h
  rw [ha] at h
  rw [observed_chi, observed_chi] at h
  change (1 : G) = Multiplicative.ofAdd (1 : ZMod 2) at h
  exact (show (0 : ZMod 2) ≠ 1 by decide) (congrArg Multiplicative.toAdd h)

def identityPositive (g : G) : Arrow (chiMap g) (chiMap g) := arrowId _

end Examples.FiniteHigherCompletion.ChainControl

namespace Examples.FiniteHigherCompletion.MappingControl
open CategoryTheory Bicategory SquareKit SquareKit.HigherCategory SquareKit.FiniteHigherMap SquareKit.FiniteHigherCell
open SquareKit.PseudofunctorMapping SquareKit.PseudofunctorPostcomposition SquareKit.PseudofunctorComposition
open SquareKit.ContractibleBicategory SquareKit.FiniteHigherCompletion SquareKit.FiniteHigherExtension
open SquareKit.FiniteHigherAtomicMapping SquareKit.FiniteHigherRecovery SquareKit.FiniteHigherUnitPrecomposition
open scoped Pseudofunctor.StrongTrans
open Examples.FiniteHigherCompletion.WeakMap

abbrev sourceDiagram : FullDiagram.{0,0,0} := atomicDiagram Source Terminal
abbrev targetDiagram : FullDiagram.{0,0,0} := atomicDiagram Target Terminal

theorem source_is_atomic_completion : completion sourceDiagram = sourceDiagram := rfl
theorem target_is_atomic_completion : completion targetDiagram = targetDiagram := rfl

def targetCounit : Bicategory.Equivalence
    ((Pseudofunctor.id targetDiagram.top).comp (pair targetDiagram.rL targetDiagram.rR))
    (Pseudofunctor.id _) := equalityEquivalence (by rw [id_comp]; rfl)

def completedMap (P : Pseudofunctor Source Target) :
    Map (F := completion sourceDiagram) (T := targetDiagram) :=
  extension sourceDiagram targetDiagram (Pseudofunctor.id _) targetCounit P
    (Pseudofunctor.id _) (DoubleDelooping.point PUnit.{1})

abbrev completedWeak := completedMap weakMap
abbrev completedZero := completedMap zeroMap

theorem completed_same_top_objects (x : (completion sourceDiagram).top) :
    completedWeak.top.obj x = completedZero.top.obj x := rfl

theorem completed_same_top_arrows {x y : (completion sourceDiagram).top} (f : x ⟶ y) :
    completedWeak.top.map f = completedZero.top.map f := rfl

theorem completed_same_left_objects (x : Source) :
    completedWeak.left.obj x = completedZero.left.obj x := rfl

theorem completed_same_left_arrows {x y : Source} (f : x ⟶ y) :
    completedWeak.left.map f = completedZero.left.map f := rfl

theorem completed_same_right : completedWeak.right = completedZero.right := rfl
theorem completed_same_empty : completedWeak.empty = completedZero.empty := rfl

theorem completed_weak_comparison :
    (completedWeak.left.mapComp generator generator).hom = Multiplicative.ofAdd (1 : A) := rfl

theorem completed_zero_comparison :
    (completedZero.left.mapComp generator generator).hom = Multiplicative.ofAdd (0 : A) := rfl

theorem no_completed_arrow_to_zero (a : Arrow completedWeak completedZero) : False :=
  no_strong_to_zero a.left

theorem no_completed_arrow_from_zero (a : Arrow completedZero completedWeak) : False :=
  no_strong_from_zero a.left

def completedIdentityPositive (P : Pseudofunctor Source Target) :
    Arrow (completedMap P) (completedMap P) := arrowId _

abbrev identityPseudofunctor : Pseudofunctor Target Target := Pseudofunctor.id _
abbrev t : identityPseudofunctor ⟶ identityPseudofunctor := Pseudofunctor.StrongTrans.id identityPseudofunctor

def coefficientCell (a : G) : t ⟶ t where
  as.app _ := a
  as.naturality f := by change (1 : G) * a = a * 1; simp

def diagonalDiagram : FullDiagram.{0,0,0} where
  top := Target
  left := Target
  right := Target
  empty := Terminal
  rL := identityPseudofunctor
  rR := identityPseudofunctor
  r0 := toTerminal
  sL := toTerminal
  sR := toTerminal
  cL := comparisonEquivalence _ _
  cR := comparisonEquivalence _ _

abbrev completedIdentity := identityMap (completion diagonalDiagram)
abbrev completedIdentityArrow := arrowId completedIdentity

def retainedCell : Cell completedIdentityArrow completedIdentityArrow :=
  liftCell (a := completedIdentityArrow) (b := completedIdentityArrow)
    (coefficientCell 1, coefficientCell (Multiplicative.ofAdd (1 : A)))

def actualUnitPullback := precomposeUnit (F := diagonalDiagram) (T := completion diagonalDiagram)

theorem actual_unit_retains_nonzero_coefficient :
    (actualUnitPullback.map₂ retainedCell).right.as.app targetPoint = Multiplicative.ofAdd (1 : A) := rfl

theorem actual_unit_retains_nonidentity :
    actualUnitPullback.map₂ retainedCell ≠ 𝟙 (actualUnitPullback.map completedIdentityArrow) := by
  intro h
  have hc := congrArg (fun m => m.right.as.app targetPoint) h
  change Multiplicative.ofAdd (1 : A) = Multiplicative.ofAdd (0 : A) at hc
  exact (show (1 : A) ≠ 0 by decide) (congrArg Multiplicative.toAdd hc)

theorem retainedCell_nonidentity : retainedCell ≠ 𝟙 completedIdentityArrow := by
  intro h
  apply actual_unit_retains_nonidentity
  rw [h]
  exact actualUnitPullback.map₂_id _

abbrev actualUnitHom := actualUnitPullback.toPrelaxFunctor.mapFunctor
  completedIdentity completedIdentity

instance actualUnitHom_isEquivalence : actualUnitHom.IsEquivalence :=
  precomposeUnit_local completedIdentity completedIdentity

def recoveredCell : Cell completedIdentityArrow completedIdentityArrow :=
  actualUnitHom.preimage (actualUnitPullback.map₂ retainedCell)

theorem modification_recovery : recoveredCell = retainedCell :=
  actualUnitHom.preimage_map retainedCell

theorem recoveredCell_nonidentity : recoveredCell ≠ 𝟙 completedIdentityArrow := by
  rw [modification_recovery]
  exact retainedCell_nonidentity

end Examples.FiniteHigherCompletion.MappingControl

end

namespace Examples.FiniteHigherCompletion
open CategoryTheory Bicategory SquareKit.HigherCategory Core
open SquareKit.FiniteHigherAtomicMapping

theorem input_bigroupoid : IsBigroupoid K := by
  refine ⟨?_, ?_⟩
  · intro x y
    change IsGroupoid (Discrete (x.1.as ⟶ y.1.as) × SingleObj Core.A)
    infer_instance
  rintro ⟨⟨⟨b⟩⟩, x⟩ ⟨⟨⟨c⟩⟩, y⟩ f
  cases x
  cases y
  have h : b = c := Discrete.eq_of_hom f.1.as
  subst c
  refine ⟨Bicategory.Equivalence.id _, ?_⟩
  apply Prod.ext
  · apply Discrete.ext
    apply Subsingleton.elim
  · cases f.2
    rfl

theorem product_bigroupoid {A B : Type} [Bicategory.{0,0} A] [Bicategory.{0,0} B]
    (hA : IsBigroupoid A) (hB : IsBigroupoid B) : IsBigroupoid (A × B) := by
  let := hA.1
  let := hB.1
  refine ⟨?_, ?_⟩
  · intro x y
    change IsGroupoid ((x.1 ⟶ y.1) × (x.2 ⟶ y.2))
    infer_instance
  intro x y f
  obtain ⟨e, he⟩ := hA.2 f.1
  obtain ⟨d, hd⟩ := hB.2 f.2
  exact ⟨productEquivalence e d, Prod.ext he hd⟩

theorem output_bigroupoid : IsBigroupoid completeInput.top :=
  product_bigroupoid input_bigroupoid input_bigroupoid
end Examples.FiniteHigherCompletion
