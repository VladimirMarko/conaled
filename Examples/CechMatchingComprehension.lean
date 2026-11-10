import SquareKit.Internal.PathTransport.CechMatchingComprehensionProducts
import SquareKit.Internal.PathTransport.CechMatchingComprehensionConstant
import SquareKit.Internal.PathTransport.CechMatchingComprehensionSets
import SquareKit.Internal.PathTransport.CechMatchingComprehensionIdentity
import Mathlib.CategoryTheory.SingleObj
import Mathlib.Algebra.Group.Int.Defs

noncomputable section
namespace Examples.CechMatchingComprehension
open CategoryTheory SquareKit.Internal.PathTransport.CechMatching
universe u v

/-- Both supplied local arrows survive product matching, including base action. -/
theorem product_arrows {D E : Diagram.{u,v}} {d d' : Datum D} {e e' : Datum E}
    (f : d ⟶ d') (g : e ⟶ e') :
    ((productEquivalence D E).functor.map (X := (d,e)) (Y := (d',e')) (f,g)).localArrow =
      (f.localArrow,g.localArrow) := rfl

abbrev Loops := SingleObj (Multiplicative ℤ)
abbrev star := SingleObj.star (Multiplicative ℤ)
abbrev loop : star ⟶ star := Multiplicative.ofAdd 1

theorem vertical_loop_survives (D : Diagram.{0,0}) (d : Datum D) :
    (constantProductEquivalence D (Grpd.of Loops)).functor.map (X := (d,star)) (Y := (d,star)) (𝟙 d, loop) ≠
      (constantProductEquivalence D (Grpd.of Loops)).functor.map (X := (d,star)) (Y := (d,star)) (𝟙 d, 𝟙 star) := by
  intro h
  have hh := (constantProductEquivalence D (Grpd.of Loops)).functor.map_injective h
  have hb := congrArg (fun f => f.2) hh
  change (1 : ℤ) = 0 at hb
  exact (by decide : (1 : ℤ) ≠ 0) hb

theorem rebase_keeps_selected_arrow {D : Diagram.{u,v}} (d : Datum D)
    {y : D.localCategory} (i : d.localObject ≅ y) :
    (Datum.rebaseIso d i).hom.localArrow = i.hom := Datum.rebaseIso_local d i

/-- Relative transport uses the declared local-family map, even for nonidentity arrows. -/
theorem relative_transport_local {D : StrictDiagram.{u,u}}
    {A : Comprehension.FamilyData D} {h : A.Coherence}
    {d e : Datum D.toDiagram} (f : d ⟶ e) (x : Comprehension.Fiber A h d) :
    (Comprehension.Fiber.transport f x).localFiber =
      (A.localFamily.map f.localArrow).obj x.localFiber :=
  Comprehension.Fiber.transport_localFiber f x

/-- Reconstruction retains the independently supplied base overlap. -/
theorem relative_reconstruction {D : StrictDiagram.{u,u}}
    {A : Comprehension.FamilyData D} {h : A.Coherence}
    {d : Datum D.toDiagram} (x : Comprehension.Fiber A h d) :
    (A.projection h).mapDatum x.datum = d :=
  Comprehension.Fiber.projection_datum x

open SquareKit.Internal.PathTransport.GroupoidModel
open Comprehension
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def identityDisplay (C : Grpd.{0,0}) : StrictDiagram.{0,0} where
  localCategory := C
  doubleCategory := C
  tripleCategory := C
  first := 𝟭 C
  second := 𝟭 C
  diagonal := 𝟭 C
  firstSecond := 𝟭 C
  firstThird := 𝟭 C
  secondThird := 𝟭 C
  diagonalFirst := rfl
  diagonalSecond := rfl
  tripleFirst := rfl
  tripleMiddle := rfl
  tripleLast := rfl

abbrev Point := Discrete Unit
abbrev pointCategory := @Grpd.of Point Groupoid.ofIsGroupoid
abbrev point := Discrete.mk ()
abbrev pointDisplay := identityDisplay pointCategory
local instance : Quiver.IsThin pointDisplay.localCategory := inferInstanceAs (Quiver.IsThin Point)
local instance : Quiver.IsThin pointDisplay.tripleCategory := inferInstanceAs (Quiver.IsThin Point)

def constantSet (X : Type) : pointCategory ⥤ Type :=
  (CategoryTheory.Functor.const pointCategory).obj X

def constantMap {X Y : Type} (f : X → Y) : constantSet X ⟶ constantSet Y where
  app _ := ↾f
  naturality {_ _} _ := rfl

/-- Local values on two patches, with all four overlaps and all eight triples. -/
def twoPatch : SetData pointDisplay where
  localFamily := constantSet (Bool → Bool)
  doubleFamily := constantSet (Bool × Bool → Bool)
  tripleFamily := constantSet (Bool × Bool × Bool → Bool)
  first := constantMap (fun f ij => f ij.1)
  second := constantMap (fun f ij => f ij.2)
  diagonal := constantMap (fun f i => f (i,i))
  firstSecond := constantMap (fun f ijk => f (ijk.1,ijk.2.1))
  firstThird := constantMap (fun f ijk => f (ijk.1,ijk.2.2))
  secondThird := constantMap (fun f ijk => f (ijk.2.1,ijk.2.2))

private theorem twoPatch_arrow {C : Grpd.{0,0}} (F : C ⥤ Grpd.{0,0})
    [Quiver.IsThin C] [∀ c, Quiver.IsThin (F.obj c)]
    {x y : Extend F} (f g : x ⟶ y) : f = g :=
  Grothendieck.ext f g (Subsingleton.elim _ _) (Subsingleton.elim _ _)

theorem twoPatchCoherence : twoPatch.toFamilyData.Coherence where
  diagonalFirst := by
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro x y f
    exact twoPatch_arrow twoPatch.toFamilyData.localFamily _ _
  diagonalSecond := by
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro x y f
    exact twoPatch_arrow twoPatch.toFamilyData.localFamily _ _
  tripleFirst := by
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro x y f
    exact twoPatch_arrow twoPatch.toFamilyData.tripleFamily _ _
  tripleMiddle := by
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro x y f
    exact twoPatch_arrow twoPatch.toFamilyData.tripleFamily _ _
  tripleLast := by
    refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
    intro x y f
    exact twoPatch_arrow twoPatch.toFamilyData.tripleFamily _ _

def pointDatum : Datum pointDisplay.toDiagram := constantDatum pointCategory point

def agreeingValues : twoPatch.MatchingSet pointDatum := ⟨fun _ => false, rfl⟩

def agreeingRelative : Fiber twoPatch.toFamilyData twoPatchCoherence pointDatum :=
  twoPatch.fromSet twoPatchCoherence pointDatum agreeingValues

example : twoPatch.setEquiv twoPatchCoherence pointDatum agreeingRelative = agreeingValues :=
  twoPatch.toSet_fromSet _ _ _

/-- Unequal local patch values fail the actual overlap equation. -/
theorem mismatched_values_rejected :
    ¬ ∃ x : Fiber twoPatch.toFamilyData twoPatchCoherence pointDatum,
      x.localFiber.as = id := by
  rintro ⟨x, hx⟩
  have hp := (twoPatch.toSet twoPatchCoherence pointDatum x).property
  change (fun ij : Bool × Bool => x.localFiber.as ij.1) =
    (fun ij : Bool × Bool => x.localFiber.as ij.2) at hp
  have hb := congrFun hp (false,true)
  rw [hx] at hb
  exact Bool.false_ne_true hb

example {D : StrictDiagram.{0,0}} (S : SetData D) (hs : S.toFamilyData.Coherence)
    {d e : Datum D.toDiagram} (f : d ⟶ e) (x : Fiber S.toFamilyData hs d) :
    S.setEquiv hs e (Fiber.transport f x) =
      SetFamily.map S.localFamily S.doubleFamily S.first S.second f (S.setEquiv hs d x) :=
  S.setEquiv_transport hs f x

/-- The full supplied total local arrow is recovered through the equivalence. -/
example {D : StrictDiagram.{0,0}} (A : FamilyData D) (h : A.Coherence)
    {x y : Comprehension.Total A h} (f : x.fiber.datum ⟶ y.fiber.datum) :
    ((Comprehension.equivalence A h).functor.map (recoverArrow A h f)).localArrow = f.localArrow :=
  congrArg Datum.Hom.localArrow (totalMap_recoverArrow A h f)

/-- An identity display admits arbitrary groupoid fibers, including loops. -/
def identityFamilyData (C : Grpd.{0,0}) (F : C ⥤ Grpd.{0,0}) : FamilyData (identityDisplay C) where
  localFamily := F
  doubleFamily := F
  tripleFamily := F
  first := 𝟙 F
  second := 𝟙 F
  diagonal := 𝟙 F
  firstSecond := 𝟙 F
  firstThird := 𝟙 F
  secondThird := 𝟙 F

theorem identityFamilyCoherence (C : Grpd.{0,0}) (F : C ⥤ Grpd.{0,0}) :
    (identityFamilyData C F).Coherence := by
  constructor <;>
    simp [identityFamilyData, FamilyData.firstMap, FamilyData.secondMap,
      FamilyData.diagonalMap, FamilyData.firstSecondMap, FamilyData.firstThirdMap,
      FamilyData.secondThirdMap, identityDisplay, Comparison.totalMap_id] <;> rfl

abbrev loopCategory := Grpd.of Loops
abbrev loopFamily : loopCategory ⥤ Grpd.{0,0} :=
  (CategoryTheory.Functor.const loopCategory).obj loopCategory
abbrev loopFamilyData := identityFamilyData loopCategory loopFamily
abbrev loopCoherence := identityFamilyCoherence loopCategory loopFamily
abbrev loopBase : Datum (identityDisplay loopCategory).toDiagram := constantDatum loopCategory star

def loopRelative : Fiber loopFamilyData loopCoherence loopBase where
  localFiber := star
  overlap := Iso.refl _
  diagonal := by simp [FamilyData.diagonalMap, eqToHom_app]
  cocycle := by simp [FamilyData.firstSecondMap, FamilyData.firstThirdMap,
    FamilyData.secondThirdMap]
  base_overlap := rfl

def relativeLoop : loopRelative ⟶ loopRelative where
  matchingArrow := {
    localArrow := ⟨𝟙 star, loop⟩
    commutes := by
      change loopFamilyData.firstMap.map _ ≫ 𝟙 _ = 𝟙 _ ≫ loopFamilyData.secondMap.map _
      simp only [Category.comp_id, Category.id_comp]
      rfl }
  vertical := rfl

theorem relativeLoop_nonidentity : relativeLoop ≠ 𝟙 loopRelative := by
  intro hh
  have hf := congrArg (fun f => f.matchingArrow.localArrow.fiber) hh
  change (1 : ℤ) = 0 at hf
  exact (by decide : (1 : ℤ) ≠ 0) hf

/-- Equal endpoints do not collapse selected relative identity paths. -/
theorem relativeIdentity_nontrivial :
    (Comprehension.Identity.arrowEquiv loopRelative loopRelative).symm relativeLoop ≠
      (Comprehension.Identity.arrowEquiv loopRelative loopRelative).symm (𝟙 loopRelative) := by
  intro hh
  exact relativeLoop_nonidentity
    ((Comprehension.Identity.arrowEquiv loopRelative loopRelative).symm.injective hh)

def loopTotal : Comprehension.Total loopFamilyData loopCoherence := ⟨loopBase,loopRelative⟩

def loopTotalArrow : loopTotal ⟶ loopTotal :=
  ⟨𝟙 loopBase, eqToHom (Fiber.transport_id loopRelative) ≫ relativeLoop⟩

/-- The general comprehension equivalence retains the integer-labelled vertical loop. -/
theorem relativeLoop_survives_total :
    (Comprehension.equivalence loopFamilyData loopCoherence).functor.map loopTotalArrow ≠
      𝟙 loopRelative.datum := by
  have hm : (Comprehension.equivalence loopFamilyData loopCoherence).functor.map loopTotalArrow =
      relativeLoop.matchingArrow := by
    change Fiber.lift (𝟙 loopBase) loopRelative ≫
      ((eqToHom (Fiber.transport_id loopRelative)).matchingArrow ≫ relativeLoop.matchingArrow) = _
    rw [Fiber.lift_id, Fiber.matchingArrow_eqToHom]
    simp
  rw [hm]
  intro hh
  exact relativeLoop_nonidentity (Fiber.Hom.ext _ _ hh)

/-- A nonidentity base loop still appears as exactly that base action. -/
example :
    (Fiber.lift ((constantFunctor loopCategory).map loop) loopRelative).localArrow.base = loop :=
  Fiber.lift_base _ _

/-- Reindexing a vertical arrow commutes with the actual local-family lift,
including its complete local arrow rather than only its endpoints. -/
example {D : StrictDiagram.{0,0}} {A : FamilyData D} {h : A.Coherence}
    {d e : Datum D.toDiagram} (f : d ⟶ e) {x y : Fiber A h d} (g : x ⟶ y) :
    g.matchingArrow.localArrow ≫ (Fiber.lift f y).localArrow =
      (Fiber.lift f x).localArrow ≫ (Fiber.transportMap f g).matchingArrow.localArrow :=
  congrArg Datum.Hom.localArrow (Fiber.lift_naturality f g)

/-- The generic constant comparison admits a non-discrete coefficient groupoid. -/
theorem constantLoopCoherence : (Comprehension.Constant.data
    (identityDisplay loopCategory) (identityDisplay loopCategory)).Coherence := loopCoherence

def independentLoopDatum : Datum (identityDisplay loopCategory).toDiagram :=
  constantDatum loopCategory star

/-- An independently supplied coefficient loop is recovered exactly, for every
base datum; no choice of global extension is involved. -/
example (d : Datum (identityDisplay loopCategory).toDiagram) :
    ((Comprehension.Constant.toFunctor _ _ constantLoopCoherence d).map
      (Comprehension.Constant.fromArrow _ _ constantLoopCoherence d
        ((constantFunctor loopCategory).map loop))).localArrow = loop := rfl

example {D E : StrictDiagram.{0,0}} (h : (Comprehension.Constant.data D E).Coherence)
    (d : Datum D.toDiagram) (e : Datum E.toDiagram) :
    Comprehension.Constant.toDatum D E h (Comprehension.Constant.fromDatum D E h d e) = e :=
  Comprehension.Constant.toDatum_fromDatum D E h d e

example {D E : StrictDiagram.{0,0}} (h : (Comprehension.Constant.data D E).Coherence)
    {d e : Datum D.toDiagram} (f : d ⟶ e) (x : Fiber (Comprehension.Constant.data D E) h d) :
    Comprehension.Constant.toDatum D E h (Fiber.transport f x) =
      Comprehension.Constant.toDatum D E h x :=
  Comprehension.Constant.transport_toDatum D E h f x

end Examples.CechMatchingComprehension
