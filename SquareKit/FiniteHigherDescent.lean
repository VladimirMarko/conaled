import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finset.Union
import Mathlib.Tactic
import SquareKit.FiniteHigherDiagram
import SquareKit.BicategoryIsoComma
import SquareKit.ContractibleBicategory

/-! All covering sieves of the discrete two-point site and their normalized descent bicategories. The binary cone retains both empty-value comparisons. -/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
namespace SquareKit.RestrictionDescent
open CategoryTheory Bicategory
open scoped Pseudofunctor.StrongTrans
open SquareKit.BicategoryIsoComma SquareKit.HigherCategory
universe u v w u' v' w' u'' v'' w'' u''' v''' w'''
variable {X : Type u} [Bicategory.{w,v} X]
  {A : Type u'} [Bicategory.{w',v'} A]
  {B : Type u''} [Bicategory.{w'',v''} B]
  {E : Type u'''} [Bicategory.{w''',v'''} E]

noncomputable def equivalenceSymm {x y : E} (e : Bicategory.Equivalence x y) :
    Bicategory.Equivalence y x :=
  Bicategory.Equivalence.mkOfAdjointifyCounit e.counit.symm e.unit.symm

noncomputable def equivalenceComp {x y z : E} (e : Bicategory.Equivalence x y)
    (d : Bicategory.Equivalence y z) : Bicategory.Equivalence x z :=
  Bicategory.Equivalence.mkOfAdjointifyCounit
    (f := e.hom ≫ d.hom) (g := d.inv ≫ e.inv)
    (e.unit ≪⊗≫ whiskerLeftIso e.hom (whiskerRightIso d.unit e.inv) ≪⊗≫ Iso.refl _)
    (Iso.refl _ ≪⊗≫ whiskerLeftIso d.inv (whiskerRightIso e.counit d.hom) ≪⊗≫ d.counit)

def modificationAppIso {F G : Pseudofunctor X E} {a b : F ⟶ G}
    (m : a ≅ b) (x : X) : a.app x ≅ b.app x where
  hom := m.hom.as.app x
  inv := m.inv.as.app x
  hom_inv_id := congrArg (fun n => n.as.app x) m.hom_inv_id
  inv_hom_id := congrArg (fun n => n.as.app x) m.inv_hom_id

noncomputable def equivalenceApp {F G : Pseudofunctor X E}
    (e : Bicategory.Equivalence F G) (x : X) : Bicategory.Equivalence (F.obj x) (G.obj x) :=
  Bicategory.Equivalence.mkOfAdjointifyCounit
    (modificationAppIso e.unit x) (modificationAppIso e.counit x)

variable (L : Pseudofunctor A E) (R : Pseudofunctor B E)
  (F : Pseudofunctor X A) (G : Pseudofunctor X B)
  (e : Bicategory.Equivalence (F.comp L) (G.comp R))

noncomputable def liftObj (x : X) : Obj L R :=
  ⟨F.obj x, G.obj x, equivalenceApp e x⟩

noncomputable def liftArrow {x y : X} (f : x ⟶ y) :
    liftObj L R F G e x ⟶ liftObj L R F G e y where
  left := F.map f
  right := G.map f
  square := e.hom.naturality f

noncomputable def liftCell {x y : X} {f g : x ⟶ y} (a : f ⟶ g) :
    liftArrow L R F G e f ⟶ liftArrow L R F G e g where
  left := F.map₂ a
  right := G.map₂ a
  compatibility := e.hom.naturality_naturality a

noncomputable def liftId (x : X) : liftArrow L R F G e (𝟙 x) ≅ 𝟙 (liftObj L R F G e x) :=
  cellIso (F.mapId x) (G.mapId x) (by
    change L.map₂ (F.mapId x).hom ▷ e.hom.app x ≫
      (arrowId (liftObj L R F G e x)).square.hom =
      (e.hom.naturality (𝟙 x)).hom ≫ e.hom.app x ◁ R.map₂ (G.mapId x).hom
    dsimp [arrowId, liftObj, equivalenceApp, Bicategory.Equivalence.mkOfAdjointifyCounit]
    have h := congrArg (fun k => k ≫ e.hom.app x ◁ (R.mapId (G.obj x)).inv)
      (e.hom.naturality_id x)
    simpa [Pseudofunctor.comp, Category.assoc]
      using h.symm)

noncomputable def liftComp {x y z : X} (f : x ⟶ y) (g : y ⟶ z) :
    liftArrow L R F G e (f ≫ g) ≅ liftArrow L R F G e f ≫ liftArrow L R F G e g :=
  cellIso (F.mapComp f g) (G.mapComp f g) (by
    change L.map₂ (F.mapComp f g).hom ▷ e.hom.app z ≫
      (arrowComp (liftArrow L R F G e f) (liftArrow L R F G e g)).square.hom =
      (e.hom.naturality (f ≫ g)).hom ≫ e.hom.app x ◁ R.map₂ (G.mapComp f g).hom
    dsimp [arrowComp, liftArrow, liftObj, equivalenceApp, Bicategory.Equivalence.mkOfAdjointifyCounit]
    have h := congrArg (fun k => k ≫ e.hom.app x ◁ (R.mapComp (G.map f) (G.map g)).inv)
      (e.hom.naturality_comp f g)
    simpa [Pseudofunctor.comp, Category.assoc]
      using h.symm)

noncomputable def lift : Pseudofunctor X (Obj L R) where
  obj := liftObj L R F G e
  map := liftArrow L R F G e
  map₂ := liftCell L R F G e
  mapId := liftId L R F G e
  mapComp := liftComp L R F G e
  map₂_id f := Cell.ext (F.map₂_id f) (G.map₂_id f)
  map₂_comp a b := Cell.ext (F.map₂_comp a b) (G.map₂_comp a b)
  map₂_whisker_left := by intros; exact Cell.ext (F.map₂_whisker_left _ _) (G.map₂_whisker_left _ _)
  map₂_whisker_right a f := Cell.ext (F.map₂_whisker_right a f) (G.map₂_whisker_right a f)
  map₂_associator f g h := Cell.ext (F.map₂_associator f g h) (G.map₂_associator f g h)
  map₂_left_unitor f := Cell.ext (F.map₂_left_unitor f) (G.map₂_left_unitor f)
  map₂_right_unitor f := Cell.ext (F.map₂_right_unitor f) (G.map₂_right_unitor f)

noncomputable def restriction (D : FullDiagram.{u,v,w}) : Pseudofunctor D.top (Obj D.sL D.sR) :=
  lift D.sL D.sR D.rL D.rR (equivalenceComp D.cL (equivalenceSymm D.cR))

theorem projection_of_terminal_local_equivalence (T : Pseudofunctor E SquareKit.ContractibleBicategory.Terminal)
    (h : ∀ x y : E, (T.toPrelaxFunctor.mapFunctor x y).IsEquivalence) :
    IsBiequivalence (productProjection (L := L) (R := R)) := by
  let := SquareKit.ContractibleBicategory.arrows_of_terminal_hom_equivalence T h
  let := SquareKit.ContractibleBicategory.cellsOfTerminalHomEquivalence T h
  exact ⟨productProjection_essentially_surjective, productProjection_local⟩

theorem lift_productProjection :
    (lift L R F G e).comp productProjection = SquareKit.PseudofunctorMapping.pair F G := by
  dsimp only [Pseudofunctor.comp, lift, productProjection, leftProjection, rightProjection,
    SquareKit.PseudofunctorMapping.pair, liftObj, liftArrow, liftCell]
  congr 1
  · funext x
    apply Iso.ext
    simp [liftId, cellIso, PrelaxFunctor.map₂Iso, PrelaxFunctor.mapFunctor, Functor.mapIso]
  · funext x y z f g
    apply Iso.ext
    simp [liftComp, cellIso, PrelaxFunctor.map₂Iso, PrelaxFunctor.mapFunctor, Functor.mapIso]

theorem restriction_overlap (D : FullDiagram.{u,v,w}) (x : D.top) :
    ((restriction D).obj x).overlap.hom = D.cL.hom.app x ≫ D.cR.inv.app x := rfl

theorem restriction_square (D : FullDiagram.{u,v,w}) {x y : D.top} (f : x ⟶ y) :
    ((restriction D).map f).square = (D.cL.hom ≫ D.cR.inv).naturality f := rfl

theorem restriction_productProjection (D : FullDiagram.{u,v,w}) :
    (restriction D).comp productProjection = SquareKit.PseudofunctorMapping.pair D.rL D.rR :=
  lift_productProjection _ _ _ _ _

noncomputable def inverseArrow [IsLocallyGroupoid E] {x y : Obj L R}
    (l : Bicategory.Equivalence x.left y.left) (r : Bicategory.Equivalence x.right y.right)
    (s : L.map l.hom ≫ y.overlap.hom ≅ x.overlap.hom ≫ R.map r.hom) : y ⟶ x where
  left := l.inv
  right := r.inv
  square := asIso (mateEquiv (L.mapAdjunction l.adj) (R.mapAdjunction r.adj) s.inv)

end SquareKit.RestrictionDescent
namespace SquareKit.PullbackEquivalenceProjection
open CategoryTheory Bicategory SquareKit.BicategoryIsoComma SquareKit.HigherCategory
universe u v w u' v' w' u'' v'' w''
variable {A : Type u} [Bicategory.{w,v} A] {B : Type u'} [Bicategory.{w',v'} B]
  {E : Type u''} [Bicategory.{w'',v''} E]
variable (L : Pseudofunctor A E) (R : Pseudofunctor B E)
variable [∀ b c, (R.toPrelaxFunctor.mapFunctor b c).IsEquivalence]
def comparisonFunctor (x y : Obj L R) : (x.right ⟶ y.right) ⥤ (L.obj x.left ⟶ R.obj y.right) :=
  R.toPrelaxFunctor.mapFunctor x.right y.right ⋙
    SquareKit.HomWhiskering.left x.overlap.hom (R.obj y.right)
instance comparisonFunctor_equivalence (x y : Obj L R) :
    (comparisonFunctor L R x y).IsEquivalence := by
  let := SquareKit.HomWhiskering.left_isEquivalence x.overlap (R.obj y.right)
  unfold comparisonFunctor
  infer_instance
def liftCell {x y : Obj L R} {f g : x ⟶ y} (m : f.left ⟶ g.left) : f ⟶ g where
  left := m
  right := (comparisonFunctor L R x y).preimage
    (f.square.inv ≫ L.map₂ m ▷ y.overlap.hom ≫ g.square.hom)
  compatibility := by
    have h := (comparisonFunctor L R x y).map_preimage
      (f.square.inv ≫ L.map₂ m ▷ y.overlap.hom ≫ g.square.hom)
    change x.overlap.hom ◁ R.map₂ _ = _ at h
    rw [h]
    exact (f.square.hom_inv_id_assoc _).symm
instance projection_faithful (x y : Obj L R) :
    ((leftProjection (L := L) (R := R)).toPrelaxFunctor.mapFunctor x y).Faithful where
  map_injective := by
    intro f g m n h
    apply Cell.ext h
    apply (comparisonFunctor L R x y).map_injective
    change x.overlap.hom ◁ R.map₂ m.right = x.overlap.hom ◁ R.map₂ n.right
    apply (cancel_epi f.square.hom).mp
    rw [← m.compatibility, ← n.compatibility]
    rw [show m.left = n.left from h]
instance projection_full (x y : Obj L R) :
    ((leftProjection (L := L) (R := R)).toPrelaxFunctor.mapFunctor x y).Full where
  map_surjective m := ⟨liftCell L R m, rfl⟩
def liftArrow (x y : Obj L R) (f : x.left ⟶ y.left) : x ⟶ y where
  left := f
  right := (comparisonFunctor L R x y).objPreimage (L.map f ≫ y.overlap.hom)
  square := ((comparisonFunctor L R x y).objObjPreimageIso (L.map f ≫ y.overlap.hom)).symm
instance projection_local (x y : Obj L R) :
    ((leftProjection (L := L) (R := R)).toPrelaxFunctor.mapFunctor x y).IsEquivalence where
  essSurj := ⟨fun f => ⟨liftArrow L R x y f, ⟨Iso.refl _⟩⟩⟩
omit [∀ b c, (R.toPrelaxFunctor.mapFunctor b c).IsEquivalence] in
theorem projection_biequivalence (hR : IsBiequivalence R) :
    IsBiequivalence (leftProjection (L := L) (R := R)) := by
  let := hR.2
  constructor
  · intro a
    obtain ⟨b, ⟨e⟩⟩ := hR.1 (L.obj a)
    exact ⟨⟨a, b, SquareKit.Biequivalence.equivalenceSymm e⟩,
      ⟨Bicategory.Equivalence.id a⟩⟩
  · exact projection_local L R
end SquareKit.PullbackEquivalenceProjection
namespace SquareKit.SieveCone
open CategoryTheory Bicategory SquareKit.BicategoryIsoComma SquareKit.HigherCategory
open scoped Pseudofunctor.StrongTrans
universe u v w u1 v1 w1 u2 v2 w2 u3 v3 w3
variable {X : Type u} [Bicategory.{w,v} X] {A : Type u1} [Bicategory.{w1,v1} A]
  {E : Type u2} [Bicategory.{w2,v2} E] {B : Type u3} [Bicategory.{w3,v3} B]
noncomputable def graph (L : Pseudofunctor A E) : Pseudofunctor A (Obj L (Pseudofunctor.id E)) :=
  SquareKit.RestrictionDescent.lift L (Pseudofunctor.id E) (Pseudofunctor.id A) L (by
    rw [SquareKit.PseudofunctorComposition.id_comp, SquareKit.PseudofunctorComposition.comp_id]
    exact Bicategory.Equivalence.id L)
theorem lift_left (L : Pseudofunctor A E) (R : Pseudofunctor B E)
    (F : Pseudofunctor X A) (G : Pseudofunctor X B)
    (e : Bicategory.Equivalence (F.comp L) (G.comp R)) :
    (SquareKit.RestrictionDescent.lift L R F G e).comp leftProjection = F := by
  dsimp only [Pseudofunctor.comp, SquareKit.RestrictionDescent.lift, leftProjection,
    SquareKit.RestrictionDescent.liftObj, SquareKit.RestrictionDescent.liftArrow,
    SquareKit.RestrictionDescent.liftCell]
  conv_rhs => rw [show F = {F with mapId := F.mapId, mapComp := F.mapComp} from rfl]
  congr 1
  · funext x
    apply Iso.ext
    simp [SquareKit.RestrictionDescent.liftId, cellIso, PrelaxFunctor.map₂Iso,
      PrelaxFunctor.mapFunctor, Functor.mapIso]
  · funext x y z f g
    apply Iso.ext
    simp [SquareKit.RestrictionDescent.liftComp, cellIso, PrelaxFunctor.map₂Iso,
      PrelaxFunctor.mapFunctor, Functor.mapIso]
theorem lift_right (L : Pseudofunctor A E) (R : Pseudofunctor B E)
    (F : Pseudofunctor X A) (G : Pseudofunctor X B)
    (e : Bicategory.Equivalence (F.comp L) (G.comp R)) :
    (SquareKit.RestrictionDescent.lift L R F G e).comp rightProjection = G := by
  dsimp only [Pseudofunctor.comp, SquareKit.RestrictionDescent.lift, rightProjection,
    SquareKit.RestrictionDescent.liftObj, SquareKit.RestrictionDescent.liftArrow,
    SquareKit.RestrictionDescent.liftCell]
  conv_rhs => rw [show G = {G with mapId := G.mapId, mapComp := G.mapComp} from rfl]
  congr 1
  · funext x
    apply Iso.ext
    simp [SquareKit.RestrictionDescent.liftId, cellIso, PrelaxFunctor.map₂Iso,
      PrelaxFunctor.mapFunctor, Functor.mapIso]
  · funext x y z f g
    apply Iso.ext
    simp [SquareKit.RestrictionDescent.liftComp, cellIso, PrelaxFunctor.map₂Iso,
      PrelaxFunctor.mapFunctor, Functor.mapIso]
theorem graph_projection (L : Pseudofunctor A E) :
    (graph L).comp leftProjection = Pseudofunctor.id A := by
  unfold graph
  exact lift_left _ _ _ _ _
theorem graph_biequivalence (L : Pseudofunctor A E) : IsBiequivalence (graph L) := by
  apply SquareKit.Biequivalence.of_comp_right (graph L) leftProjection
  · rw [graph_projection]
    exact SquareKit.Biequivalence.id
  · exact SquareKit.PullbackEquivalenceProjection.projection_biequivalence L
      (Pseudofunctor.id E) SquareKit.Biequivalence.id

abbrev RightCone (D : FullDiagram.{0,0,0}) := Obj D.sR (Pseudofunctor.id D.empty)
abbrev BinaryCone (D : FullDiagram.{0,0,0}) :=
  Obj D.sL (rightProjection (L := D.sR) (R := Pseudofunctor.id D.empty))
noncomputable def rightRestriction (D : FullDiagram.{0,0,0}) : Pseudofunctor D.top (RightCone D) :=
  SquareKit.RestrictionDescent.lift D.sR (Pseudofunctor.id D.empty) D.rR D.r0 (by
    rw [SquareKit.PseudofunctorComposition.comp_id]
    exact D.cR)
theorem rightRestriction_right (D : FullDiagram.{0,0,0}) :
    (rightRestriction D).comp rightProjection = D.r0 :=
  lift_right _ _ _ _ _
noncomputable def binaryRestriction (D : FullDiagram.{0,0,0}) : Pseudofunctor D.top (BinaryCone D) :=
  SquareKit.RestrictionDescent.lift D.sL rightProjection D.rL (rightRestriction D) (by
    rw [rightRestriction_right]
    exact D.cL)
abbrev MaximalTopCone (D : FullDiagram.{0,0,0}) :=
  Obj (binaryRestriction D) (Pseudofunctor.id (BinaryCone D))
noncomputable def maximalTopRestriction (D : FullDiagram.{0,0,0}) :
    Pseudofunctor D.top (MaximalTopCone D) := graph (binaryRestriction D)
theorem maximalTopRestriction_biequivalence (D : FullDiagram.{0,0,0}) :
    IsBiequivalence (maximalTopRestriction D) := graph_biequivalence _

def binaryProjection (D : FullDiagram.{0,0,0}) : Pseudofunctor (BinaryCone D) (D.left × D.right) :=
  SquareKit.PseudofunctorMapping.pair leftProjection (rightProjection.comp leftProjection)
section BinaryProjection
variable (D : FullDiagram.{0,0,0})
variable [∀ (x y : D.empty) (f g : x ⟶ y), Unique (f ⟶ g)]
theorem binaryProjection_local (x y : BinaryCone D) :
    ((binaryProjection D).toPrelaxFunctor.mapFunctor x y).IsEquivalence where
  faithful := {
    map_injective := by
      intro f g m n h
      exact Cell.ext (congrArg Prod.fst h)
        (Cell.ext (congrArg Prod.snd h) (Subsingleton.elim _ _)) }
  full := {
    map_surjective := by
      intro f g m
      let n : f.right ⟶ g.right := {
        left := m.2
        right := default
        compatibility := Subsingleton.elim _ _ }
      exact ⟨{left := m.1, right := n, compatibility := Subsingleton.elim _ _}, rfl⟩ }
  essSurj := {
    mem_essImage := by
      intro f
      let g : x.right ⟶ y.right := {
        left := f.2
        right := x.right.overlap.inv ≫ D.sR.map f.2 ≫ y.right.overlap.hom
        square := uniqueIso _ _ }
      exact ⟨{left := f.1, right := g, square := uniqueIso _ _}, ⟨Iso.refl f⟩⟩ }
variable [∀ x y : D.empty, Nonempty (x ⟶ y)]
theorem binaryProjection_biequivalence : IsBiequivalence (binaryProjection D) := by
  constructor
  · intro p
    exact ⟨⟨p.1, ⟨p.2, D.sR.obj p.2, Bicategory.Equivalence.id _⟩,
      uniqueEquivalence _ _⟩, ⟨Bicategory.Equivalence.id p⟩⟩
  · exact binaryProjection_local D
end BinaryProjection

theorem comp_pair (H : Pseudofunctor X A) (F : Pseudofunctor A B)
    (G : Pseudofunctor A E) :
    H.comp (SquareKit.PseudofunctorMapping.pair F G) =
      SquareKit.PseudofunctorMapping.pair (H.comp F) (H.comp G) := by
  dsimp only [Pseudofunctor.comp, SquareKit.PseudofunctorMapping.pair]
  congr 1
theorem binaryRestriction_left (D : FullDiagram.{0,0,0}) :
    (binaryRestriction D).comp leftProjection = D.rL := lift_left _ _ _ _ _
theorem binaryRestriction_right (D : FullDiagram.{0,0,0}) :
    (binaryRestriction D).comp rightProjection = rightRestriction D := lift_right _ _ _ _ _
theorem rightRestriction_left (D : FullDiagram.{0,0,0}) :
    (rightRestriction D).comp leftProjection = D.rR := lift_left _ _ _ _ _
theorem binaryRestriction_projection (D : FullDiagram.{0,0,0}) :
    (binaryRestriction D).comp (binaryProjection D) = SquareKit.PseudofunctorMapping.pair D.rL D.rR := by
  unfold binaryProjection
  rw [comp_pair, binaryRestriction_left, ← SquareKit.PseudofunctorComposition.comp_assoc,
    binaryRestriction_right, rightRestriction_left]
theorem binary_criterion (D : FullDiagram.{0,0,0})
    (T : Pseudofunctor D.empty SquareKit.ContractibleBicategory.Terminal)
    (hT : ∀ x y, (T.toPrelaxFunctor.mapFunctor x y).IsEquivalence) :
    IsBiequivalence (binaryRestriction D) ↔
      IsBiequivalence (SquareKit.PseudofunctorMapping.pair D.rL D.rR) := by
  let := SquareKit.ContractibleBicategory.arrows_of_terminal_hom_equivalence T hT
  let := SquareKit.ContractibleBicategory.cellsOfTerminalHomEquivalence T hT
  constructor
  · intro h
    have hp := SquareKit.Biequivalence.comp (binaryRestriction D) (binaryProjection D) h
      (binaryProjection_biequivalence D)
    rwa [binaryRestriction_projection] at hp
  · intro h
    apply SquareKit.Biequivalence.of_comp_right (binaryRestriction D) (binaryProjection D)
    · rwa [binaryRestriction_projection]
    · exact binaryProjection_biequivalence D
end SquareKit.SieveCone

namespace SquareKit.SieveCone
open CategoryTheory Bicategory SquareKit.HigherCategory
open scoped Pseudofunctor.StrongTrans
theorem transport_comparison {X E : Type*} [Bicategory X] [Bicategory E]
    {F G G' : Pseudofunctor X E} (h : G = G')
    (e : Bicategory.Equivalence F G) (x : X) :
    HEq ((cast (congrArg (fun H => Bicategory.Equivalence F H) h) e).hom.app x) (e.hom.app x) := by
  subst G'
  rfl
theorem binaryRestriction_left_comparison (D : FullDiagram.{0,0,0}) (x : D.top) :
    ((binaryRestriction D).obj x).overlap.hom = D.cL.hom.app x := by
  simp [binaryRestriction, rightRestriction, SquareKit.RestrictionDescent.lift,
    SquareKit.RestrictionDescent.liftObj, SquareKit.RestrictionDescent.equivalenceApp,
    Bicategory.Equivalence.mkOfAdjointifyCounit]
  exact eq_of_heq (transport_comparison (rightRestriction_right D).symm D.cL x)
theorem binaryRestriction_right_comparison (D : FullDiagram.{0,0,0}) (x : D.top) :
    ((binaryRestriction D).obj x).right.overlap.hom = D.cR.hom.app x := by
  simp [binaryRestriction, rightRestriction, SquareKit.RestrictionDescent.lift,
    SquareKit.RestrictionDescent.liftObj, SquareKit.RestrictionDescent.equivalenceApp,
    Bicategory.Equivalence.mkOfAdjointifyCounit]
  exact eq_of_heq (transport_comparison (SquareKit.PseudofunctorComposition.comp_id D.r0).symm D.cR x)
end SquareKit.SieveCone
namespace SquareKit.TwoPointOpenSite
abbrev Open := Finset Bool
def bottom : Open := ∅
def left : Open := {false}
def right : Open := {true}
def top : Open := {false, true}
def Covers (U : Open) (S : Finset Open) : Prop :=
  (∀ V ∈ S, V ⊆ U) ∧ (∀ V ∈ S, ∀ W : Open, W ⊆ V → W ∈ S) ∧
    S.biUnion id = U
instance (U : Open) (S : Finset Open) : Decidable (Covers U S) := by
  unfold Covers
  infer_instance
theorem covers_iff (U : Open) (S : Finset Open) : Covers U S ↔
    (U = bottom ∧ S = ∅) ∨ (U = bottom ∧ S = {bottom}) ∨
    (U = left ∧ S = {bottom, left}) ∨ (U = right ∧ S = {bottom, right}) ∨
    (U = top ∧ S = {bottom, left, right}) ∨ (U = top ∧ S = {bottom, left, right, top}) := by
  revert U S
  decide

open CategoryTheory
def topology : GrothendieckTopology Open where
  sieves U := {S | ∀ p ∈ U, ∃ (V : Open) (f : V ⟶ U), S f ∧ p ∈ V}
  top_mem' U p hp := ⟨U, 𝟙 U, trivial, hp⟩
  pullback_stable' {U V S} f h p hp := by
    obtain ⟨W, g, hg, hW⟩ := h p (leOfHom f hp)
    refine ⟨W ∩ V, homOfLE Finset.inter_subset_right, ?_, Finset.mem_inter.mpr ⟨hW, hp⟩⟩
    exact S.downward_closed hg (homOfLE Finset.inter_subset_left)
  transitive' {U S} h R k p hp := by
    obtain ⟨V, f, hf, hV⟩ := h p hp
    obtain ⟨W, g, hg, hW⟩ := k hf p hV
    exact ⟨W, g ≫ f, hg, hW⟩
noncomputable def finiteSieve {U : Open} (S : Sieve U) : Finset Open := by
  classical
  exact Finset.univ.filter (fun V => ∃ f : V ⟶ U, S f)
@[simp] theorem mem_finiteSieve {U V : Open} (S : Sieve U) :
    V ∈ finiteSieve S ↔ ∃ f : V ⟶ U, S f := by
  classical
  simp [finiteSieve]
theorem finiteSieve_covers {U : Open} (S : Sieve U) :
    Covers U (finiteSieve S) ↔ S ∈ topology U := by
  classical
  constructor
  · rintro ⟨_, _, heq⟩ p hp
    rw [← heq, Finset.mem_biUnion] at hp
    obtain ⟨V, hV, hp⟩ := hp
    obtain ⟨f, hf⟩ := (mem_finiteSieve S).mp hV
    exact ⟨V, f, hf, hp⟩
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro V hV
      obtain ⟨f, _⟩ := (mem_finiteSieve S).mp hV
      exact leOfHom f
    · intro V hV W hW
      obtain ⟨f, hf⟩ := (mem_finiteSieve S).mp hV
      exact (mem_finiteSieve S).mpr ⟨homOfLE hW ≫ f, S.downward_closed hf _⟩
    · ext p
      simp only [Finset.mem_biUnion]
      constructor
      · rintro ⟨V, hV, hp⟩
        obtain ⟨f, _⟩ := (mem_finiteSieve S).mp hV
        exact leOfHom f hp
      · intro hp
        obtain ⟨V, f, hf, hV⟩ := h p hp
        exact ⟨V, (mem_finiteSieve S).mpr ⟨f, hf⟩, hV⟩

theorem finiteSieve_injective (U : Open) : Function.Injective (@finiteSieve U) := by
  intro S R h
  ext V f
  constructor
  · intro hf
    have hV : V ∈ finiteSieve R := h ▸ (mem_finiteSieve S).mpr ⟨f, hf⟩
    obtain ⟨g, hg⟩ := (mem_finiteSieve R).mp hV
    simpa only [Subsingleton.elim g f] using hg
  · intro hf
    have hV : V ∈ finiteSieve S := h.symm ▸ (mem_finiteSieve R).mpr ⟨f, hf⟩
    obtain ⟨g, hg⟩ := (mem_finiteSieve S).mp hV
    simpa only [Subsingleton.elim g f] using hg
inductive CoverKind where
  | empty | bottom | left | right | binary | top
  deriving DecidableEq
def CoverKind.base : CoverKind → Open
  | .empty | .bottom => SquareKit.TwoPointOpenSite.bottom
  | .left => SquareKit.TwoPointOpenSite.left
  | .right => SquareKit.TwoPointOpenSite.right
  | .binary | .top => SquareKit.TwoPointOpenSite.top
def CoverKind.members : CoverKind → Finset Open
  | .empty => ∅
  | .bottom => {SquareKit.TwoPointOpenSite.bottom}
  | .left => {SquareKit.TwoPointOpenSite.bottom, SquareKit.TwoPointOpenSite.left}
  | .right => {SquareKit.TwoPointOpenSite.bottom, SquareKit.TwoPointOpenSite.right}
  | .binary => {SquareKit.TwoPointOpenSite.bottom, SquareKit.TwoPointOpenSite.left, SquareKit.TwoPointOpenSite.right}
  | .top => {SquareKit.TwoPointOpenSite.bottom, SquareKit.TwoPointOpenSite.left, SquareKit.TwoPointOpenSite.right, SquareKit.TwoPointOpenSite.top}
theorem CoverKind.covers (c : CoverKind) : Covers c.base c.members := by
  cases c <;> decide
theorem covers_exists_kind (U : Open) (S : Finset Open) (h : Covers U S) :
    ∃ c : CoverKind, U = c.base ∧ S = c.members := by
  rcases (covers_iff U S).mp h with h | h | h | h | h | h
  · exact ⟨.empty, h⟩
  · exact ⟨.bottom, h⟩
  · exact ⟨.left, h⟩
  · exact ⟨.right, h⟩
  · exact ⟨.binary, h⟩
  · exact ⟨.top, h⟩
theorem covering_sieve_exists_kind {U : Open} (S : Sieve U) (h : S ∈ topology U) :
    ∃ c : CoverKind, U = c.base ∧ finiteSieve S = c.members :=
  covers_exists_kind U (finiteSieve S) ((finiteSieve_covers S).mpr h)

def sieveOfCover (U : Open) (S : Finset Open) (h : Covers U S) : Sieve U where
  arrows {V} _ := V ∈ S
  downward_closed {V W _f} hf g := h.2.1 V hf W (leOfHom g)
theorem finiteSieve_sieveOfCover (U : Open) (S : Finset Open) (h : Covers U S) :
    finiteSieve (sieveOfCover U S h) = S := by
  ext V
  rw [mem_finiteSieve]
  constructor
  · rintro ⟨f, hf⟩
    exact hf
  · intro hV
    exact ⟨homOfLE (h.1 V hV), hV⟩
theorem sieveOfCover_covering (U : Open) (S : Finset Open) (h : Covers U S) :
    sieveOfCover U S h ∈ topology U := by
  apply (finiteSieve_covers _).mp
  rwa [finiteSieve_sieveOfCover]
end SquareKit.TwoPointOpenSite
namespace SquareKit.FiniteHigherDescent
open CategoryTheory Bicategory SquareKit.BicategoryIsoComma SquareKit.HigherCategory
open SquareKit.SieveCone SquareKit.TwoPointOpenSite
open scoped Pseudofunctor.StrongTrans
abbrev Source (D : FullDiagram.{0,0,0}) : CoverKind → Type
  | .empty | .bottom => D.empty
  | .left => D.left
  | .right => D.right
  | .binary | .top => D.top
abbrev Cone (D : FullDiagram.{0,0,0}) : CoverKind → Type
  | .empty => SquareKit.ContractibleBicategory.Terminal
  | .bottom => D.empty
  | .left => Obj D.sL (Pseudofunctor.id D.empty)
  | .right => RightCone D
  | .binary => BinaryCone D
  | .top => MaximalTopCone D
instance sourceBicategory (D : FullDiagram.{0,0,0}) (c : CoverKind) : Bicategory (Source D c) := by
  cases c <;> dsimp [Source] <;> infer_instance
instance coneBicategory (D : FullDiagram.{0,0,0}) (c : CoverKind) : Bicategory (Cone D c) := by
  cases c <;> dsimp [Cone] <;> infer_instance
noncomputable def restriction (D : FullDiagram.{0,0,0}) (c : CoverKind) :
    Pseudofunctor (Source D c) (Cone D c) := by
  cases c
  · exact SquareKit.ContractibleBicategory.toTerminal
  · exact Pseudofunctor.id D.empty
  · exact graph D.sL
  · exact graph D.sR
  · exact binaryRestriction D
  · exact maximalTopRestriction D
def IsStack (D : FullDiagram.{0,0,0}) : Prop :=
  ∀ c : CoverKind, IsBiequivalence (restriction D c)
theorem stack_criterion (D : FullDiagram.{0,0,0}) :
    IsStack D ↔ IsBiequivalence (SquareKit.ContractibleBicategory.toTerminal (C := D.empty)) ∧
      IsBiequivalence (SquareKit.PseudofunctorMapping.pair D.rL D.rR) := by
  constructor
  · intro h
    exact ⟨h .empty, (binary_criterion D SquareKit.ContractibleBicategory.toTerminal (h .empty).2).mp
      (h .binary)⟩
  · rintro ⟨he, hb⟩ c
    cases c
    · exact he
    · exact SquareKit.Biequivalence.id
    · exact graph_biequivalence D.sL
    · exact graph_biequivalence D.sR
    · exact (binary_criterion D SquareKit.ContractibleBicategory.toTerminal he.2).mpr hb
    · exact maximalTopRestriction_biequivalence D

def IsStackOnAllCoveringSieves (D : FullDiagram.{0,0,0}) : Prop :=
  ∀ (U : Open) (S : Sieve U), S ∈ topology U →
    ∀ c : CoverKind, U = c.base → finiteSieve S = c.members →
      IsBiequivalence (restriction D c)
theorem allCoveringSieves_iff (D : FullDiagram.{0,0,0}) :
    IsStackOnAllCoveringSieves D ↔ IsStack D := by
  constructor
  · intro h c
    exact h c.base (sieveOfCover c.base c.members c.covers)
      (sieveOfCover_covering _ _ _) c rfl (finiteSieve_sieveOfCover _ _ _)
  · intro h U S hS c hU hC
    exact h c
end SquareKit.FiniteHigherDescent

end
