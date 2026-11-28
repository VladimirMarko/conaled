import SquareKit.SheafGroupoidAtlasInvariance
import SquareKit.SheafGroupoidAtlasInvarianceRecovery
import Examples.GeneralGroupoidCompletion

/-! Disk refinements, ineffective isotropy, and the missing-cover obstruction for atlas invariance. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Examples.GeneralGroupoidCompletion.Disk
open CategoryTheory Opposite SquareKit
open SmoothOpenSite
open scoped CategoryTheory.Pseudofunctor.StrongTrans

def firstAmbientEquivalence := firstChart.completedAmbientEquivalence
def secondAmbientEquivalence := secondChart.completedAmbientEquivalence

def leftEquivalence := commonChart.completedEquivalenceOfSourceCover firstChart
  ActionMorita.commonLeft.total
  (by simpa only [Category.comp_id, ActionMorita.atlas, ActionMorita.commonAtlas,
    SmoothQuarterTurnArcs.diskSheaf] using ActionMorita.commonLeft.total_cover)
def rightEquivalence := commonChart.completedEquivalenceOfSourceCover secondChart
  ActionMorita.commonRight.total
  (by simpa only [Category.comp_id, ActionMorita.otherAtlas, ActionMorita.commonAtlas,
    SmoothQuarterTurnArcs.diskSheaf] using ActionMorita.commonRight.total_cover)

example : leftEquivalence.hom = completedLeft := rfl
example : rightEquivalence.hom = completedRight := rfl

/-- Common-refinement equivalences use the existing ambient comparison modification. -/
def equivalenceCommonComparison :
    leftEquivalence.hom ≫ firstAmbientEquivalence.hom ≅
      rightEquivalence.hom ≫ secondAmbientEquivalence.hom := commonComparison

/-- The actual completed comparison preserves distinct arrows between different lifts. -/
theorem left_retains_distinct {X : Sheaf topology Type}
    {P Q : SheafGroupoid.Bundle.Principal common X} (f g : P ⟶ Q) (h : f ≠ g) :
    (StackDescentTransformation.component completedLeft X).map f ≠
      (StackDescentTransformation.component completedLeft X).map g := by
  let e := commonChart.completedFiberEquivalenceOfSourceCover firstChart ActionMorita.commonLeft.total
    (by simpa only [Category.comp_id, ActionMorita.atlas, ActionMorita.commonAtlas,
      SmoothQuarterTurnArcs.diskSheaf] using ActionMorita.commonLeft.total_cover) X
  exact fun he => h (e.fullyFaithfulFunctor.map_injective he)

example (i j : Bool) : Nat.card (origin i ⟶ origin j) = 4 := origin_arrow_count i j
example : origin false ≠ origin true := distinct_lifts

end Examples.GeneralGroupoidCompletion.Disk

namespace Examples.AtlasInvarianceMissingCover
open CategoryTheory Opposite Limits SquareKit
open scoped CategoryTheory.Pseudofunctor.StrongTrans
abbrev Site := Discrete Unit
abbrev topology : GrothendieckTopology Site := ⊥
def constant (A : Type) : Sheaf topology Type :=
  ⟨(Functor.const Siteᵒᵖ).obj A, Presheaf.isSheaf_bot _⟩
abbrev empty := constant Empty
abbrev point := constant Unit
def emptyMap : empty ⟶ point := ⟨{ app := fun _ => TypeCat.ofHom (fun e : Empty => Empty.elim e) }⟩

/-- The identity groupoid needs no action presentation. -/
def operations : SheafGroupoid.Operations topology where
  objects := point
  arrows := point
  source := 𝟙 _
  target := 𝟙 _
  unit := 𝟙 _
  inverse := 𝟙 _
  comp := pullback.fst (𝟙 point) (𝟙 point)
  unit_source := Category.id_comp _
  unit_target := Category.id_comp _
  inverse_source := Category.id_comp _
  inverse_target := Category.id_comp _
  comp_source := (Category.comp_id _).symm
  comp_target := by simpa using pullback.condition (f := 𝟙 point) (g := 𝟙 point)

instance arrowSubsingleton {X : Sheaf topology Type} (m n : operations.Object X) :
    Subsingleton (operations.Arrow m n) := ⟨fun f g => by
  apply SheafGroupoid.Operations.Arrow.ext
  have hf := f.source
  have hg := g.source
  change f.map ≫ 𝟙 point = m.map at hf
  change g.map ≫ 𝟙 point = m.map at hg
  change (f.map : X ⟶ point) = g.map
  exact (Category.comp_id f.map).symm.trans (hf.trans (hg.symm.trans (Category.comp_id g.map)))⟩

instance : operations.Laws where
  id_comp _ := Subsingleton.elim _ _
  comp_id _ := Subsingleton.elim _ _
  assoc _ _ _ := Subsingleton.elim _ _
  inv_comp _ := Subsingleton.elim _ _
  comp_inv _ := Subsingleton.elim _ _

def missing := SheafGroupoid.Chart.canonical operations emptyMap emptyMap
def full := SheafGroupoid.Chart.canonical operations (𝟙 point) (𝟙 point)
def inputMap := missing.representedMap full emptyMap (Category.comp_id _)
def outputMap := missing.completedMap full emptyMap (Category.comp_id _)

theorem emptyMap_not_cover : ¬ Presheaf.IsLocallySurjective topology emptyMap.hom := by
  intro h
  let := h
  have ht := GrothendieckTopology.bot_covering.mp
    (Presheaf.imageSieve_mem topology emptyMap.hom (U := op (Discrete.mk ())) ())
  have hid : Presheaf.imageSieve emptyMap.hom () (𝟙 (Discrete.mk ())) := by rw [ht]; trivial
  obtain ⟨e, _⟩ := hid
  exact Empty.elim e

theorem no_source_bundle (P : SheafGroupoid.Bundle.Principal missing.atlasOperations point) : False := by
  have ht := GrothendieckTopology.bot_covering.mp
    (Presheaf.imageSieve_mem topology P.toAction.projection.hom
      (U := op (Discrete.mk ())) ())
  have hid : Presheaf.imageSieve P.toAction.projection.hom () (𝟙 (Discrete.mk ())) := by
    rw [ht]
    trivial
  obtain ⟨z, _⟩ := hid
  exact Empty.elim z.1.2

def targetObject : full.atlasOperations.Object point := ⟨𝟙 point⟩
def targetBundle := (SheafGroupoid.Bundle.regularFunctor full.atlasOperations).obj targetObject

theorem outputMap_not_essentiallySurjective :
    ¬ (StackDescentTransformation.component outputMap point).EssSurj := by
  intro h
  obtain ⟨P, _⟩ := h.mem_essImage targetBundle
  exact no_source_bundle P

/-- The input still has full arrow comparison; only the cover condition fails. -/
def inputFullyFaithful (X : Sheaf topology Type) :
    (StackDescentTransformation.component inputMap X).FullyFaithful :=
  missing.representedMapFullyFaithful full emptyMap (Category.comp_id _) X

end Examples.AtlasInvarianceMissingCover

namespace Examples.AtlasInvarianceMissingCover
open CategoryTheory Opposite SquareKit
open scoped CategoryTheory.Pseudofunctor.StrongTrans

theorem inputMap_not_locallyGenerating :
    ¬ StackLocalGeneration.LocallyGenerating (SheafCover.topology (J := topology)) inputMap := by
  intro h
  obtain ⟨Y, f, hf, n, _⟩ := h point targetObject
  obtain ⟨Z, g, hg, hmem⟩ := hf
  let := hg
  obtain ⟨i, k, _⟩ := (Sieve.mem_ofArrows_iff (fun _ : Unit => Y) (fun _ => f) g).mp hmem
  have ht := GrothendieckTopology.bot_covering.mp
    (Presheaf.imageSieve_mem topology g.hom (U := op (Discrete.mk ())) ())
  have hid : Presheaf.imageSieve g.hom () (𝟙 (Discrete.mk ())) := by rw [ht]; trivial
  obtain ⟨z, _⟩ := hid
  exact Empty.elim (n.map.hom.app _ (k.hom.app _ z))

/-- A genuine covering atlas of the same ambient groupoid satisfies the theorem. -/
def fullPositive := full.completedEquivalence full (𝟙 point) (Category.id_comp _)
end Examples.AtlasInvarianceMissingCover

namespace Examples.GeneralGroupoidCompletion.Ineffective
open CategoryTheory Opposite SquareKit
open SmoothOpenSite SmoothQuarterTurnQuotient Orbifolds.QuarterTurn
open scoped CategoryTheory.Pseudofunctor.StrongTrans

def identityAtlas := SheafGroupoid.Chart.canonical operations (𝟙 operations.objects) (𝟙 operations.objects)
def atlasEquivalence := identityAtlas.completedAmbientEquivalence

def atlasObject : identityAtlas.atlasOperations.Object SmoothTorsors.point :=
  ⟨(GroupoidCompletion.baseObject (Iso.refl _)).map⟩

def atlasLoop (g : C4) : atlasObject ⟶ atlasObject :=
  (identityAtlas.ambientFullyFaithful SmoothTorsors.point).preimage (GroupoidCompletion.loop (Iso.refl _) g)

theorem atlasLoop_distinct : atlasLoop quarterTurn ≠ atlasLoop 1 := by
  intro h
  apply GroupoidCompletion.loop_distinct (Iso.refl _)
  have he := congrArg (StackDescentTransformation.component identityAtlas.ambientTransformation SmoothTorsors.point).map h
  simpa only [atlasLoop, Functor.FullyFaithful.map_preimage] using he

def completedAtlasLoop (g : C4) :=
  (SheafGroupoid.Bundle.regularFunctor identityAtlas.atlasOperations).map (atlasLoop g)

theorem completedAtlasLoop_distinct : completedAtlasLoop quarterTurn ≠ completedAtlasLoop 1 := by
  intro h
  exact atlasLoop_distinct ((SheafGroupoid.Bundle.regularFullyFaithful identityAtlas.atlasOperations).map_injective h)

/-- The actual atlas equivalence retains ineffective isotropy, including after completion. -/
theorem atlasEquivalence_retains_ineffective :
    (StackDescentTransformation.component atlasEquivalence.hom SmoothTorsors.point).map
        (completedAtlasLoop quarterTurn) ≠
      (StackDescentTransformation.component atlasEquivalence.hom SmoothTorsors.point).map
        (completedAtlasLoop 1) := by
  let e := SheafGroupoid.Bundle.completeMapComponentEquivalence identityAtlas.ambientTransformation
    identityAtlas.ambientFullyFaithful identityAtlas.ambientLocallyGenerating SmoothTorsors.point
  exact fun h => completedAtlasLoop_distinct (e.fullyFaithfulFunctor.map_injective h)

end Examples.GeneralGroupoidCompletion.Ineffective

namespace Examples.GeneralGroupoidCompletion.Disk
open CategoryTheory Opposite SquareKit
open SmoothOpenSite SmoothQuarterTurnQuotient Orbifolds.QuarterTurn
open scoped CategoryTheory.Pseudofunctor.StrongTrans

def completedOrigin (i : Bool) :=
  (StackDescentTransformation.component firstAmbientEquivalence.hom realBase).obj
    ((SheafGroupoid.Bundle.regularFunctor first).obj (origin i))

/-- The covering-atlas equivalence recovers all four ambient arrows between either pair of lifts. -/
def completedOriginArrowEquiv (i j : Bool) : (completedOrigin i ⟶ completedOrigin j) ≃ C4 :=
  (SheafGroupoid.Bundle.completeMapComponentEquivalence firstChart.ambientTransformation
    firstChart.ambientFullyFaithful firstChart.ambientLocallyGenerating realBase).fullyFaithfulFunctor.homEquiv.symm.trans
      ((SheafGroupoid.Bundle.regularFullyFaithful first).homEquiv.symm.trans (originArrowEquiv i j))

theorem completed_origin_arrow_count (i j : Bool) :
    Nat.card (completedOrigin i ⟶ completedOrigin j) = 4 := by
  rw [Nat.card_congr (completedOriginArrowEquiv i j)]
  exact card_C4

end Examples.GeneralGroupoidCompletion.Disk

namespace Examples.AtlasInvarianceCoherence
open CategoryTheory Opposite SquareKit
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : SheafGroupoid.Operations J} [G.Laws]
variable {U V W : Sheaf J (Type (max u v))}
variable {p : U ⟶ G.objects} {q : V ⟶ G.objects} {s : W ⟶ G.objects}
variable (D : SheafGroupoid.Chart G p p) (E : SheafGroupoid.Chart G q q)
  (F : SheafGroupoid.Chart G s s)
variable (r : U ⟶ V) (comm : r ≫ q = p) (t : V ⟶ W) (comm' : t ≫ s = q)
variable [Presheaf.IsLocallySurjective J r.hom] [Presheaf.IsLocallySurjective J t.hom]

example : (D.completedEquivalence D (𝟙 U) (Category.id_comp p)).hom ≅
    𝟙 (SheafGroupoid.Bundle.pseudofunctor D.atlasOperations) := D.completedMap_id

example : (D.completedEquivalence E r comm).hom ≫ (E.completedEquivalence F t comm').hom ≅
    (D.completedEquivalence F (r ≫ t) (by rw [Category.assoc, comm', comm])).hom :=
  D.completedMap_comp E F r comm t comm'

example : SheafGroupoid.Bundle.unit D.atlasOperations ≫ (D.completedEquivalence E r comm).hom ≅
    D.representedMap E r comm ≫ SheafGroupoid.Bundle.unit E.atlasOperations :=
  D.completedMap_unit E r comm

example {X Y : Sheaf J (Type (max u v))} (k : Y ⟶ X) :
    SheafGroupoid.Bundle.restriction k ⋙
        StackDescentTransformation.component (D.completedEquivalence E r comm).hom Y ≅
      StackDescentTransformation.component (D.completedEquivalence E r comm).hom X ⋙
        SheafGroupoid.Bundle.restriction k := D.completedMap_restriction E r comm k

end Examples.AtlasInvarianceCoherence

namespace Examples.GeneralGroupoidCompletion.Disk
open CategoryTheory Opposite SquareKit
open SmoothOpenSite
open scoped CategoryTheory.Pseudofunctor.StrongTrans

def originalActionAtlasRecovery (X : Sheaf topology Type) :
    SheafGroupoid.Bundle.Principal first X ≌ SheafActionQuotient.Object ActionMorita.action X :=
  SheafGroupoid.Bundle.Recovery.atlasActionEquivalence ActionMorita.action (Iso.refl _) firstChart X

example (X : Sheaf topology Type) :
    SheafGroupoid.Bundle.regularFunctor first ⋙ (originalActionAtlasRecovery X).functor ≅
      firstChart.atlasToChart ⋙ SheafGroupoidCompletion.chartQuotient ActionMorita.action (Iso.refl _) firstChart :=
  SheafGroupoid.Bundle.Recovery.atlasActionEquivalence_unit ActionMorita.action (Iso.refl _) firstChart X

end Examples.GeneralGroupoidCompletion.Disk
