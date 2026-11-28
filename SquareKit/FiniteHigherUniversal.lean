import SquareKit.FiniteHigherCompletion
import SquareKit.PseudofunctorInverse

/-! The actual-unit mapping universal property and recovery on already complete finite diagrams. Target inverse data are constructed from descent. -/

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
namespace SquareKit.FiniteHigherExtension
open CategoryTheory Bicategory SquareKit.HigherCategory SquareKit.PseudofunctorMapping
open SquareKit.FiniteHigherMap SquareKit.FiniteHigherCompletion SquareKit.ContractibleBicategory
open SquareKit.PseudofunctorComposition SquareKit.PseudofunctorPostcomposition SquareKit.Biequivalence
open scoped Pseudofunctor.StrongTrans

variable (F T : FullDiagram.{0,0,0})
variable (Q : Pseudofunctor (T.left × T.right) T.top)
variable (counit : Bicategory.Equivalence (Q.comp (pair T.rL T.rR)) (Pseudofunctor.id _))

noncomputable def inverseLeft : Bicategory.Equivalence
    (Q.comp T.rL) (Bicategory.Prod.fst T.left T.right).toPseudofunctor := by
  have e := mapEquivalence (post (Bicategory.Prod.fst T.left T.right).toPseudofunctor) counit
  dsimp only [post] at e
  rw [comp_assoc, pair_fst, id_comp] at e
  exact e

noncomputable def inverseRight : Bicategory.Equivalence
    (Q.comp T.rR) (Bicategory.Prod.snd T.left T.right).toPseudofunctor := by
  have e := mapEquivalence (post (Bicategory.Prod.snd T.left T.right).toPseudofunctor) counit
  dsimp only [post] at e
  rw [comp_assoc, pair_snd, id_comp] at e
  exact e

variable (Hleft : Pseudofunctor F.left T.left) (Hright : Pseudofunctor F.right T.right)

def atomicPair : Pseudofunctor (F.left × F.right) (T.left × T.right) :=
  pair ((Bicategory.Prod.fst F.left F.right).toPseudofunctor.comp Hleft)
    ((Bicategory.Prod.snd F.left F.right).toPseudofunctor.comp Hright)

noncomputable def extensionLeft : Bicategory.Equivalence
    ((Bicategory.Prod.fst F.left F.right).toPseudofunctor.comp Hleft)
    (((atomicPair F T Hleft Hright).comp Q).comp T.rL) := by
  have e := mapEquivalence (pre (atomicPair F T Hleft Hright)) (inverseLeft T Q counit)
  dsimp only [pre] at e
  rw [← comp_assoc, atomicPair, pair_fst] at e
  exact equivalenceSymm e

noncomputable def extensionRight : Bicategory.Equivalence
    ((Bicategory.Prod.snd F.left F.right).toPseudofunctor.comp Hright)
    (((atomicPair F T Hleft Hright).comp Q).comp T.rR) := by
  have e := mapEquivalence (pre (atomicPair F T Hleft Hright)) (inverseRight T Q counit)
  dsimp only [pre] at e
  rw [← comp_assoc, atomicPair, pair_snd] at e
  exact equivalenceSymm e

variable [∀ x y : T.empty, Nonempty (x ⟶ y)]
  [∀ (x y : T.empty) (f g : x ⟶ y), Unique (f ⟶ g)]

noncomputable def extensionCore (c : T.empty) : MapCore (completion F) T where
  top := (atomicPair F T Hleft Hright).comp Q
  left := Hleft
  right := Hright
  empty := constant c
  topLeft := extensionLeft F T Q counit Hleft Hright
  topRight := extensionRight F T Q counit Hleft Hright
  topEmpty := comparisonEquivalence _ _
  leftEmpty := comparisonEquivalence _ _
  rightEmpty := comparisonEquivalence _ _

noncomputable def extension (c : T.empty) : Map (F := completion F) (T := T) where
  toMapCore := extensionCore F T Q counit Hleft Hright c
  leftCoherence := modificationIso _ _
  rightCoherence := modificationIso _ _

end SquareKit.FiniteHigherExtension
namespace SquareKit.FiniteHigherAtomicMapping
open CategoryTheory Bicategory CategoryTheory.Prod
open SquareKit.HigherCategory SquareKit.PseudofunctorMapping SquareKit.FiniteHigherMap SquareKit.FiniteHigherCell
open SquareKit.PseudofunctorPostcomposition SquareKit.Biequivalence SquareKit.ContractibleBicategory
open scoped Pseudofunctor.StrongTrans
universe u v w u' v' w' u'' v'' w''

variable {A : Type u} [Bicategory.{w,v} A] {B : Type u'} [Bicategory.{w',v'} B]

def productEquivalence {a a' : A} {b b' : B}
    (e : Bicategory.Equivalence a a') (d : Bicategory.Equivalence b b') :
    Bicategory.Equivalence (a,b) (a',b') where
  hom := e.hom ×ₘ d.hom
  inv := e.inv ×ₘ d.inv
  unit := Iso.prod e.unit d.unit
  counit := Iso.prod e.counit d.counit
  left_triangle := Iso.ext (Prod.ext (congrArg Iso.hom e.left_triangle)
    (congrArg Iso.hom d.left_triangle))

variable {X : Type u''} [Bicategory.{w'',v''} X]
noncomputable def pairEquivalence {f f' : Pseudofunctor X A} {g g' : Pseudofunctor X B}
    (e : Bicategory.Equivalence f f') (d : Bicategory.Equivalence g g') :
    Bicategory.Equivalence (pair f g) (pair f' g') :=
  mapEquivalence (pairPseudofunctor (X := X) (B := A) (C := B))
    (productEquivalence (A := Pseudofunctor X A) (B := Pseudofunctor X B) e d)

variable (F T : FullDiagram.{0,0,0})

def forgetAtoms : Pseudofunctor (Map (F := F) (T := T))
    (Pseudofunctor F.left T.left × Pseudofunctor F.right T.right) :=
  pair (evaluateLeft F T) (evaluateRight F T)

variable {F T}
noncomputable def topComparison (H : Map (F := F) (T := T)) :
    Bicategory.Equivalence (pair (F.rL.comp H.left) (F.rR.comp H.right))
      (H.top.comp (pair T.rL T.rR)) :=
  pairEquivalence H.topLeft H.topRight

end SquareKit.FiniteHigherAtomicMapping

namespace SquareKit.FiniteHigherAtomicMapping
open CategoryTheory Bicategory CategoryTheory.Prod
open SquareKit.HigherCategory SquareKit.PseudofunctorMapping SquareKit.FiniteHigherMap SquareKit.FiniteHigherCell
open SquareKit.PseudofunctorPostcomposition SquareKit.Biequivalence SquareKit.ContractibleBicategory
open scoped Pseudofunctor.StrongTrans
variable {F T : FullDiagram.{0,0,0}} {H K : Map (F := F) (T := T)}

def atomTransformation (a : (H.left ⟶ K.left) × (H.right ⟶ K.right)) :
    pair (F.rL.comp H.left) (F.rR.comp H.right) ⟶
      pair (F.rL.comp K.left) (F.rR.comp K.right) :=
  pairTrans (preTrans F.rL a.1) (preTrans F.rR a.2)

noncomputable def liftTarget (a : (H.left ⟶ K.left) × (H.right ⟶ K.right)) :
    H.top.comp (pair T.rL T.rR) ⟶ K.top.comp (pair T.rL T.rR) :=
  (topComparison H).inv ≫ atomTransformation a ≫ (topComparison K).hom

variable [∀ x y, ((pair T.rL T.rR).toPrelaxFunctor.mapFunctor x y).IsEquivalence]
noncomputable def liftTop (a : (H.left ⟶ K.left) × (H.right ⟶ K.right)) : H.top ⟶ K.top :=
  SquareKit.PostCompositionLift.liftTransformation (pair T.rL T.rR) (liftTarget a)

noncomputable def liftSquare (a : (H.left ⟶ K.left) × (H.right ⟶ K.right)) :
    (topComparison H).hom ≫ postTrans (pair T.rL T.rR) (liftTop a) ≅
      atomTransformation a ≫ (topComparison K).hom :=
  whiskerLeftIso (topComparison H).hom
    (SquareKit.PostCompositionLift.liftComparison (pair T.rL T.rR) (liftTarget a)) ≪≫
  (α_ (topComparison H).hom (topComparison H).inv
    (atomTransformation a ≫ (topComparison K).hom)).symm ≪≫
  whiskerRightIso (topComparison H).unit.symm
    (atomTransformation a ≫ (topComparison K).hom) ≪≫
  λ_ (atomTransformation a ≫ (topComparison K).hom)

noncomputable def liftSquareLeft (a : (H.left ⟶ K.left) × (H.right ⟶ K.right)) :
    H.topLeft.hom ≫ postTrans T.rL (liftTop a) ≅
      preTrans F.rL a.1 ≫ K.topLeft.hom :=
  (CategoryTheory.Prod.fst _ _).mapIso
    ((homEquivalence (F.rL.comp H.left) (K.top.comp T.rL)
      (F.rR.comp H.right) (K.top.comp T.rR)).inverse.mapIso (liftSquare a))

end SquareKit.FiniteHigherAtomicMapping

namespace SquareKit.FiniteHigherAtomicMapping
open CategoryTheory Bicategory CategoryTheory.Prod
open SquareKit.HigherCategory SquareKit.PseudofunctorMapping SquareKit.FiniteHigherMap SquareKit.FiniteHigherCell
open SquareKit.PseudofunctorPostcomposition SquareKit.Biequivalence SquareKit.ContractibleBicategory
open scoped Pseudofunctor.StrongTrans
variable {F T : FullDiagram.{0,0,0}} {H K : Map (F := F) (T := T)}

noncomputable def combinedSquare (a : Arrow H K) :
    (topComparison H).hom ≫ postTrans (pair T.rL T.rR) a.top ≅
      atomTransformation (a.left,a.right) ≫ (topComparison K).hom :=
  (homEquivalence _ _ _ _).functor.mapIso (Iso.prod a.topLeft a.topRight)

def atomModification {a b : (H.left ⟶ K.left) × (H.right ⟶ K.right)} (m : a ⟶ b) :
    atomTransformation a ⟶ atomTransformation b :=
  pairMod (preMod F.rL m.1) (preMod F.rR m.2)

theorem combined_compatibility {a b : Arrow H K} (m : Cell a b) :
    (combinedSquare a).hom ≫ (atomModification (m.left,m.right) ▷ (topComparison K).hom) =
      ((topComparison H).hom ◁ postMod (pair T.rL T.rR) m.top) ≫ (combinedSquare b).hom := by
  ext x
  exact Prod.ext (congrArg (fun n => n.as.app x) m.topLeft)
    (congrArg (fun n => n.as.app x) m.topRight)

variable [∀ x y, ((pair T.rL T.rR).toPrelaxFunctor.mapFunctor x y).IsEquivalence]
noncomputable def leftWhiskeredTop (H K : Map (F := F) (T := T)) :
    (H.top ⟶ K.top) ⥤ (pair (F.rL.comp H.left) (F.rR.comp H.right) ⟶ K.top.comp (pair T.rL T.rR)) :=
  postHom (pair T.rL T.rR) H.top K.top ⋙
    SquareKit.HomWhiskering.left (topComparison H).hom (K.top.comp (pair T.rL T.rR))

instance leftWhiskeredTop_isEquivalence (H K : Map (F := F) (T := T)) :
    (leftWhiskeredTop H K).IsEquivalence := by
  dsimp only [leftWhiskeredTop]
  infer_instance

noncomputable def liftCellTop {a b : Arrow H K}
    (m : (a.left,a.right) ⟶ (b.left,b.right)) : a.top ⟶ b.top :=
  (leftWhiskeredTop H K).preimage
    ((combinedSquare a).hom ≫ atomModification m ▷ (topComparison K).hom ≫ (combinedSquare b).inv)

theorem liftCellTop_compatibility {a b : Arrow H K}
    (m : (a.left,a.right) ⟶ (b.left,b.right)) :
    (combinedSquare a).hom ≫ atomModification m ▷ (topComparison K).hom =
      ((topComparison H).hom ◁ postMod (pair T.rL T.rR) (liftCellTop m)) ≫ (combinedSquare b).hom := by
  have h := (leftWhiskeredTop H K).map_preimage
    ((combinedSquare a).hom ≫ atomModification m ▷ (topComparison K).hom ≫ (combinedSquare b).inv)
  change (topComparison H).hom ◁ postMod (pair T.rL T.rR) (liftCellTop m) = _ at h
  rw [h]
  simp

variable [∀ x y : T.empty, Nonempty (x ⟶ y)]
  [∀ (x y : T.empty) (f g : x ⟶ y), Unique (f ⟶ g)]

noncomputable def liftCell {a b : Arrow H K}
    (m : (a.left,a.right) ⟶ (b.left,b.right)) : Cell a b where
  top := liftCellTop m
  left := m.1
  right := m.2
  empty := default
  topLeft := by
    ext x
    have h := liftCellTop_compatibility (a := a) (b := b) m
    exact congrArg (fun n => (n.as.app x).1) h
  topRight := by
    ext x
    have h := liftCellTop_compatibility (a := a) (b := b) m
    exact congrArg (fun n => (n.as.app x).2) h
  topEmpty := Subsingleton.elim _ _
  leftEmpty := Subsingleton.elim _ _
  rightEmpty := Subsingleton.elim _ _

def forgetHom (H K : Map (F := F) (T := T)) :
    Arrow H K ⥤ ((H.left ⟶ K.left) × (H.right ⟶ K.right)) where
  obj a := (a.left,a.right)
  map m := (m.left,m.right)

instance forgetHom_faithful (H K : Map (F := F) (T := T)) : (forgetHom H K).Faithful where
  map_injective {a b} m n h := by
    have hl : m.left = n.left := congrArg Prod.fst h
    have hr : m.right = n.right := congrArg Prod.snd h
    apply Cell.ext _ hl hr (Subsingleton.elim _ _)
    apply (leftWhiskeredTop H K).map_injective
    change (topComparison H).hom ◁ postMod (pair T.rL T.rR) m.top =
      (topComparison H).hom ◁ postMod (pair T.rL T.rR) n.top
    apply (cancel_mono (combinedSquare b).hom).mp
    rw [← combined_compatibility m, ← combined_compatibility n, hl, hr]

instance forgetHom_full (H K : Map (F := F) (T := T)) : (forgetHom H K).Full where
  map_surjective {a b} m := ⟨liftCell (a := a) (b := b) m, rfl⟩

end SquareKit.FiniteHigherAtomicMapping

namespace SquareKit.FiniteHigherAtomicMapping
open CategoryTheory Bicategory CategoryTheory.Prod
open SquareKit.HigherCategory SquareKit.PseudofunctorMapping SquareKit.FiniteHigherMap SquareKit.FiniteHigherCell
open SquareKit.PseudofunctorPostcomposition SquareKit.Biequivalence SquareKit.ContractibleBicategory
open SquareKit.PseudofunctorComposition SquareKit.FiniteHigherCompletion SquareKit.FiniteHigherExtension
open scoped Pseudofunctor.StrongTrans
variable {F T : FullDiagram.{0,0,0}} {H K : Map (F := F) (T := T)}
variable [∀ x y, ((pair T.rL T.rR).toPrelaxFunctor.mapFunctor x y).IsEquivalence]

noncomputable def liftSquareRight (a : (H.left ⟶ K.left) × (H.right ⟶ K.right)) :
    H.topRight.hom ≫ postTrans T.rR (liftTop a) ≅
      preTrans F.rR a.2 ≫ K.topRight.hom :=
  (CategoryTheory.Prod.snd _ _).mapIso
    ((homEquivalence (F.rL.comp H.left) (K.top.comp T.rL)
      (F.rR.comp H.right) (K.top.comp T.rR)).inverse.mapIso (liftSquare a))

variable [∀ x y : T.empty, Nonempty (x ⟶ y)]
  [∀ (x y : T.empty) (f g : x ⟶ y), Unique (f ⟶ g)]

noncomputable def liftArrow (a : (H.left ⟶ K.left) × (H.right ⟶ K.right)) : Arrow H K where
  top := liftTop a
  left := a.1
  right := a.2
  empty := comparison H.empty K.empty
  topLeft := liftSquareLeft a
  topRight := liftSquareRight a
  topEmpty := modificationIso _ _
  leftEmpty := modificationIso _ _
  rightEmpty := modificationIso _ _
  leftCoherence := by intro x; apply Subsingleton.elim
  rightCoherence := by intro x; apply Subsingleton.elim

instance forgetHom_essSurj (H K : Map (F := F) (T := T)) : (forgetHom H K).EssSurj where
  mem_essImage a := ⟨liftArrow a, ⟨Iso.refl _⟩⟩

instance forgetHom_isEquivalence (H K : Map (F := F) (T := T)) :
    (forgetHom H K).IsEquivalence := {}

theorem forgetAtoms_local (H K : Map (F := F) (T := T)) :
    ((forgetAtoms F T).toPrelaxFunctor.mapFunctor H K).IsEquivalence :=
  inferInstanceAs (forgetHom H K).IsEquivalence

variable (F T)
variable (Q : Pseudofunctor (T.left × T.right) T.top)
variable (counit : Bicategory.Equivalence (Q.comp (pair T.rL T.rR)) (Pseudofunctor.id _))
variable (hL : Pseudofunctor F.left T.left) (hR : Pseudofunctor F.right T.right)

noncomputable def realizeAtomsLeft : Bicategory.Equivalence (F.rL.comp hL)
    (((pair (F.rL.comp hL) (F.rR.comp hR)).comp Q).comp T.rL) := by
  have e := mapEquivalence (pre (pair (F.rL.comp hL) (F.rR.comp hR))) (inverseLeft T Q counit)
  dsimp only [pre] at e
  rw [← comp_assoc, pair_fst] at e
  exact equivalenceSymm e

noncomputable def realizeAtomsRight : Bicategory.Equivalence (F.rR.comp hR)
    (((pair (F.rL.comp hL) (F.rR.comp hR)).comp Q).comp T.rR) := by
  have e := mapEquivalence (pre (pair (F.rL.comp hL) (F.rR.comp hR))) (inverseRight T Q counit)
  dsimp only [pre] at e
  rw [← comp_assoc, pair_snd] at e
  exact equivalenceSymm e

noncomputable def realizeAtoms (c : T.empty) : Map (F := F) (T := T) where
  top := (pair (F.rL.comp hL) (F.rR.comp hR)).comp Q
  left := hL
  right := hR
  empty := constant c
  topLeft := realizeAtomsLeft F T Q counit hL hR
  topRight := realizeAtomsRight F T Q counit hL hR
  topEmpty := comparisonEquivalence _ _
  leftEmpty := comparisonEquivalence _ _
  rightEmpty := comparisonEquivalence _ _
  leftCoherence := modificationIso _ _
  rightCoherence := modificationIso _ _

include Q counit in
theorem forgetAtoms_biequivalence (c : T.empty) : IsBiequivalence (forgetAtoms F T) := by
  refine ⟨?_, forgetAtoms_local⟩
  intro a
  exact ⟨realizeAtoms F T Q counit a.1 a.2 c, ⟨Bicategory.Equivalence.id a⟩⟩

end SquareKit.FiniteHigherAtomicMapping
namespace SquareKit.FiniteHigherUnitPrecomposition
open CategoryTheory Bicategory SquareKit.HigherCategory SquareKit.PseudofunctorMapping SquareKit.FiniteHigherMap
open SquareKit.PseudofunctorPostcomposition SquareKit.ContractibleBicategory SquareKit.FiniteHigherCompletion
open scoped Pseudofunctor.StrongTrans
variable {F T : FullDiagram.{0,0,0}}
variable (K : Map (F := completion F) (T := T))

def leftForward : F.rL.comp K.left ⟶ ((pair F.rL F.rR).comp K.top).comp T.rL where
  app x := K.topLeft.hom.app ((pair F.rL F.rR).obj x)
  naturality f := K.topLeft.hom.naturality ((pair F.rL F.rR).map f)
  naturality_naturality η := K.topLeft.hom.naturality_naturality ((pair F.rL F.rR).map₂ η)
  naturality_id x := by
    have h := (preTrans (pair F.rL F.rR) K.topLeft.hom).naturality_id x
    simpa [Pseudofunctor.comp, pair, preTrans] using h
  naturality_comp f g := by
    have h := (preTrans (pair F.rL F.rR) K.topLeft.hom).naturality_comp f g
    simpa [Pseudofunctor.comp, pair, preTrans, Category.assoc] using h

def leftBackward : ((pair F.rL F.rR).comp K.top).comp T.rL ⟶ F.rL.comp K.left where
  app x := K.topLeft.inv.app ((pair F.rL F.rR).obj x)
  naturality f := K.topLeft.inv.naturality ((pair F.rL F.rR).map f)
  naturality_naturality η := K.topLeft.inv.naturality_naturality ((pair F.rL F.rR).map₂ η)
  naturality_id x := by
    have h := (preTrans (pair F.rL F.rR) K.topLeft.inv).naturality_id x
    simpa [Pseudofunctor.comp, pair, preTrans, Category.assoc] using h
  naturality_comp f g := by
    have h := (preTrans (pair F.rL F.rR) K.topLeft.inv).naturality_comp f g
    simpa [Pseudofunctor.comp, pair, preTrans, Category.assoc] using h

def leftUnit : 𝟙 (F.rL.comp K.left) ≅ leftForward K ≫ leftBackward K :=
  Pseudofunctor.StrongTrans.isoMk
    (fun x => SquareKit.FiniteHigherCell.appIso K.topLeft.unit ((pair F.rL F.rR).obj x))
    (by intro x y f; exact K.topLeft.unit.hom.as.naturality ((pair F.rL F.rR).map f))

def leftCounit : leftBackward K ≫ leftForward K ≅ 𝟙 (((pair F.rL F.rR).comp K.top).comp T.rL) :=
  Pseudofunctor.StrongTrans.isoMk
    (fun x => SquareKit.FiniteHigherCell.appIso K.topLeft.counit ((pair F.rL F.rR).obj x))
    (by intro x y f; exact K.topLeft.counit.hom.as.naturality ((pair F.rL F.rR).map f))

def leftComparison : Bicategory.Equivalence (F.rL.comp K.left)
    (((pair F.rL F.rR).comp K.top).comp T.rL) where
  hom := leftForward K
  inv := leftBackward K
  unit := leftUnit K
  counit := leftCounit K
  left_triangle := by
    apply Iso.ext
    ext x
    exact congrArg (fun m => m.as.app ((pair F.rL F.rR).obj x))
      (congrArg Iso.hom K.topLeft.left_triangle)

def rightForward : F.rR.comp K.right ⟶ ((pair F.rL F.rR).comp K.top).comp T.rR where
  app x := K.topRight.hom.app ((pair F.rL F.rR).obj x)
  naturality f := K.topRight.hom.naturality ((pair F.rL F.rR).map f)
  naturality_naturality η := K.topRight.hom.naturality_naturality ((pair F.rL F.rR).map₂ η)
  naturality_id x := by
    have h := (preTrans (pair F.rL F.rR) K.topRight.hom).naturality_id x
    simpa [Pseudofunctor.comp, pair, preTrans] using h
  naturality_comp f g := by
    have h := (preTrans (pair F.rL F.rR) K.topRight.hom).naturality_comp f g
    simpa [Pseudofunctor.comp, pair, preTrans, Category.assoc] using h

def rightBackward : ((pair F.rL F.rR).comp K.top).comp T.rR ⟶ F.rR.comp K.right where
  app x := K.topRight.inv.app ((pair F.rL F.rR).obj x)
  naturality f := K.topRight.inv.naturality ((pair F.rL F.rR).map f)
  naturality_naturality η := K.topRight.inv.naturality_naturality ((pair F.rL F.rR).map₂ η)
  naturality_id x := by
    have h := (preTrans (pair F.rL F.rR) K.topRight.inv).naturality_id x
    simpa [Pseudofunctor.comp, pair, preTrans, Category.assoc] using h
  naturality_comp f g := by
    have h := (preTrans (pair F.rL F.rR) K.topRight.inv).naturality_comp f g
    simpa [Pseudofunctor.comp, pair, preTrans, Category.assoc] using h

def rightUnit : 𝟙 (F.rR.comp K.right) ≅ rightForward K ≫ rightBackward K :=
  Pseudofunctor.StrongTrans.isoMk
    (fun x => SquareKit.FiniteHigherCell.appIso K.topRight.unit ((pair F.rL F.rR).obj x))
    (by intro x y f; exact K.topRight.unit.hom.as.naturality ((pair F.rL F.rR).map f))

def rightCounit : rightBackward K ≫ rightForward K ≅ 𝟙 (((pair F.rL F.rR).comp K.top).comp T.rR) :=
  Pseudofunctor.StrongTrans.isoMk
    (fun x => SquareKit.FiniteHigherCell.appIso K.topRight.counit ((pair F.rL F.rR).obj x))
    (by intro x y f; exact K.topRight.counit.hom.as.naturality ((pair F.rL F.rR).map f))

def rightComparison : Bicategory.Equivalence (F.rR.comp K.right)
    (((pair F.rL F.rR).comp K.top).comp T.rR) where
  hom := rightForward K
  inv := rightBackward K
  unit := rightUnit K
  counit := rightCounit K
  left_triangle := by
    apply Iso.ext
    ext x
    exact congrArg (fun m => m.as.app ((pair F.rL F.rR).obj x))
      (congrArg Iso.hom K.topRight.left_triangle)


end SquareKit.FiniteHigherUnitPrecomposition

namespace SquareKit.FiniteHigherUnitPrecomposition
open CategoryTheory Bicategory SquareKit.HigherCategory SquareKit.PseudofunctorMapping SquareKit.FiniteHigherMap
open SquareKit.FiniteHigherCell SquareKit.PseudofunctorPostcomposition SquareKit.ContractibleBicategory SquareKit.FiniteHigherCompletion
open SquareKit.FiniteHigherAtomicMapping
open scoped Pseudofunctor.StrongTrans
variable {F T : FullDiagram.{0,0,0}}
variable [∀ x y : T.empty, Nonempty (x ⟶ y)]
  [∀ (x y : T.empty) (f g : x ⟶ y), Unique (f ⟶ g)]

def restrict (K : Map (F := completion F) (T := T)) : Map (F := F) (T := T) where
  top := (pair F.rL F.rR).comp K.top
  left := K.left
  right := K.right
  empty := toTerminal.comp K.empty
  topLeft := leftComparison K
  topRight := rightComparison K
  topEmpty := comparisonEquivalence _ _
  leftEmpty := comparisonEquivalence _ _
  rightEmpty := comparisonEquivalence _ _
  leftCoherence := modificationIso _ _
  rightCoherence := modificationIso _ _

variable {H K : Map (F := completion F) (T := T)}

def restrictLeftSquare (a : Arrow H K) :
    (restrict H).topLeft.hom ≫ postTrans T.rL (preTrans (pair F.rL F.rR) a.top) ≅
      preTrans F.rL a.left ≫ (restrict K).topLeft.hom :=
  Pseudofunctor.StrongTrans.isoMk
    (fun x => appIso a.topLeft ((pair F.rL F.rR).obj x))
    (by intro x y f; exact a.topLeft.hom.as.naturality ((pair F.rL F.rR).map f))

def restrictRightSquare (a : Arrow H K) :
    (restrict H).topRight.hom ≫ postTrans T.rR (preTrans (pair F.rL F.rR) a.top) ≅
      preTrans F.rR a.right ≫ (restrict K).topRight.hom :=
  Pseudofunctor.StrongTrans.isoMk
    (fun x => appIso a.topRight ((pair F.rL F.rR).obj x))
    (by intro x y f; exact a.topRight.hom.as.naturality ((pair F.rL F.rR).map f))

def restrictArrow (a : Arrow H K) : Arrow (restrict H) (restrict K) where
  top := preTrans (pair F.rL F.rR) a.top
  left := a.left
  right := a.right
  empty := preTrans toTerminal a.empty
  topLeft := restrictLeftSquare a
  topRight := restrictRightSquare a
  topEmpty := modificationIso _ _
  leftEmpty := modificationIso _ _
  rightEmpty := modificationIso _ _
  leftCoherence := by intro x; apply Subsingleton.elim
  rightCoherence := by intro x; apply Subsingleton.elim

def restrictCell {a b : Arrow H K} (m : Cell a b) : Cell (restrictArrow a) (restrictArrow b) where
  top := preMod (pair F.rL F.rR) m.top
  left := m.left
  right := m.right
  empty := preMod toTerminal m.empty
  topLeft := by
    ext x
    exact congrArg (fun n => n.as.app ((pair F.rL F.rR).obj x)) m.topLeft
  topRight := by
    ext x
    exact congrArg (fun n => n.as.app ((pair F.rL F.rR).obj x)) m.topRight
  topEmpty := Subsingleton.elim _ _
  leftEmpty := Subsingleton.elim _ _
  rightEmpty := Subsingleton.elim _ _

end SquareKit.FiniteHigherUnitPrecomposition

namespace SquareKit.FiniteHigherUnitPrecomposition
open CategoryTheory Bicategory SquareKit.HigherCategory SquareKit.PseudofunctorMapping SquareKit.FiniteHigherMap
open SquareKit.FiniteHigherCell SquareKit.PseudofunctorPostcomposition SquareKit.ContractibleBicategory SquareKit.FiniteHigherCompletion
open SquareKit.FiniteHigherAtomicMapping
open scoped Pseudofunctor.StrongTrans
variable {F T : FullDiagram.{0,0,0}}
variable [∀ x y : T.empty, Nonempty (x ⟶ y)]
  [∀ (x y : T.empty) (f g : x ⟶ y), Unique (f ⟶ g)]
variable {H K J : Map (F := completion F) (T := T)}

def restrictId (K : Map (F := completion F) (T := T)) :
    restrictArrow (𝟙 K) ≅ 𝟙 (restrict K) :=
  cellIso ((pre (pair F.rL F.rR)).mapId K.top) (Iso.refl _) (Iso.refl _)
    ((pre toTerminal).mapId K.empty)
    (by
      ext x
      change (arrowId K).topLeft.hom.as.app ((pair F.rL F.rR).obj x) ≫
        𝟙 _ ▷ K.topLeft.hom.app ((pair F.rL F.rR).obj x) =
        K.topLeft.hom.app ((pair F.rL F.rR).obj x) ◁ T.rL.map₂ (𝟙 _) ≫
          (arrowId K).topLeft.hom.as.app ((pair F.rL F.rR).obj x)
      simp)
    (by
      ext x
      change (arrowId K).topRight.hom.as.app ((pair F.rL F.rR).obj x) ≫
        𝟙 _ ▷ K.topRight.hom.app ((pair F.rL F.rR).obj x) =
        K.topRight.hom.app ((pair F.rL F.rR).obj x) ◁ T.rR.map₂ (𝟙 _) ≫
          (arrowId K).topRight.hom.as.app ((pair F.rL F.rR).obj x)
      simp)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _) (Subsingleton.elim _ _)

def restrictComp (a : Arrow H K) (b : Arrow K J) :
    restrictArrow (arrowComp a b) ≅ arrowComp (restrictArrow a) (restrictArrow b) :=
  cellIso ((pre (pair F.rL F.rR)).mapComp a.top b.top) (Iso.refl _) (Iso.refl _)
    ((pre toTerminal).mapComp a.empty b.empty)
    (by
      ext x
      change (arrowComp a b).topLeft.hom.as.app ((pair F.rL F.rR).obj x) ≫
        𝟙 _ ▷ J.topLeft.hom.app ((pair F.rL F.rR).obj x) =
        H.topLeft.hom.app ((pair F.rL F.rR).obj x) ◁ T.rL.map₂ (𝟙 _) ≫
          (arrowComp a b).topLeft.hom.as.app ((pair F.rL F.rR).obj x)
      simp)
    (by
      ext x
      change (arrowComp a b).topRight.hom.as.app ((pair F.rL F.rR).obj x) ≫
        𝟙 _ ▷ J.topRight.hom.app ((pair F.rL F.rR).obj x) =
        H.topRight.hom.app ((pair F.rL F.rR).obj x) ◁ T.rR.map₂ (𝟙 _) ≫
          (arrowComp a b).topRight.hom.as.app ((pair F.rL F.rR).obj x)
      simp)
    (Subsingleton.elim _ _) (Subsingleton.elim _ _) (Subsingleton.elim _ _)

def precomposeUnit : Pseudofunctor (Map (F := completion F) (T := T)) (Map (F := F) (T := T)) where
  obj := restrict
  map := restrictArrow
  map₂ := restrictCell
  mapId := restrictId
  mapComp := restrictComp
  map₂_id a := Cell.ext rfl rfl rfl rfl
  map₂_comp m n := Cell.ext rfl rfl rfl rfl
  map₂_whisker_left := by
    intro H K J a b c m
    apply Cell.ext
    · exact (pre (pair F.rL F.rR)).map₂_whisker_left a.top m.top
    · change a.left ◁ m.left = 𝟙 _ ≫ a.left ◁ m.left ≫ 𝟙 _
      simp
    · change a.right ◁ m.right = 𝟙 _ ≫ a.right ◁ m.right ≫ 𝟙 _
      simp
    · exact (pre toTerminal).map₂_whisker_left a.empty m.empty
  map₂_whisker_right := by
    intro H K J a b m c
    apply Cell.ext
    · exact (pre (pair F.rL F.rR)).map₂_whisker_right m.top c.top
    · change m.left ▷ c.left = 𝟙 _ ≫ m.left ▷ c.left ≫ 𝟙 _
      simp
    · change m.right ▷ c.right = 𝟙 _ ≫ m.right ▷ c.right ≫ 𝟙 _
      simp
    · exact (pre toTerminal).map₂_whisker_right m.empty c.empty
  map₂_associator := by
    intro H K J I a b c
    apply Cell.ext
    · exact (pre (pair F.rL F.rR)).map₂_associator a.top b.top c.top
    · change (α_ a.left b.left c.left).hom = 𝟙 _ ≫ 𝟙 _ ▷ c.left ≫
        (α_ a.left b.left c.left).hom ≫ a.left ◁ 𝟙 _ ≫ 𝟙 _
      simp
    · change (α_ a.right b.right c.right).hom = 𝟙 _ ≫ 𝟙 _ ▷ c.right ≫
        (α_ a.right b.right c.right).hom ≫ a.right ◁ 𝟙 _ ≫ 𝟙 _
      simp
    · exact (pre toTerminal).map₂_associator a.empty b.empty c.empty
  map₂_left_unitor := by
    intro H K a
    apply Cell.ext
    · exact (pre (pair F.rL F.rR)).map₂_left_unitor a.top
    · change (λ_ a.left).hom = 𝟙 _ ≫ 𝟙 _ ▷ a.left ≫ (λ_ a.left).hom
      simp
    · change (λ_ a.right).hom = 𝟙 _ ≫ 𝟙 _ ▷ a.right ≫ (λ_ a.right).hom
      simp
    · exact (pre toTerminal).map₂_left_unitor a.empty
  map₂_right_unitor := by
    intro H K a
    apply Cell.ext
    · exact (pre (pair F.rL F.rR)).map₂_right_unitor a.top
    · change (ρ_ a.left).hom = 𝟙 _ ≫ a.left ◁ 𝟙 _ ≫ (ρ_ a.left).hom
      simp
    · change (ρ_ a.right).hom = 𝟙 _ ≫ a.right ◁ 𝟙 _ ≫ (ρ_ a.right).hom
      simp
    · exact (pre toTerminal).map₂_right_unitor a.empty

end SquareKit.FiniteHigherUnitPrecomposition

namespace SquareKit.FiniteHigherUnitPrecomposition
open CategoryTheory Bicategory SquareKit.HigherCategory SquareKit.PseudofunctorMapping SquareKit.FiniteHigherMap
open SquareKit.FiniteHigherCell SquareKit.PseudofunctorPostcomposition SquareKit.ContractibleBicategory SquareKit.FiniteHigherCompletion
open SquareKit.FiniteHigherAtomicMapping SquareKit.FiniteHigherExtension SquareKit.Biequivalence
open scoped Pseudofunctor.StrongTrans
variable {F T : FullDiagram.{0,0,0}}
variable [∀ x y : T.empty, Nonempty (x ⟶ y)]
  [∀ (x y : T.empty) (f g : x ⟶ y), Unique (f ⟶ g)]
  [∀ x y, ((pair T.rL T.rR).toPrelaxFunctor.mapFunctor x y).IsEquivalence]

theorem precomposeUnit_local (H K : Map (F := completion F) (T := T)) :
    ((precomposeUnit (F := F) (T := T)).toPrelaxFunctor.mapFunctor H K).IsEquivalence := by
  let A := (precomposeUnit (F := F) (T := T)).toPrelaxFunctor.mapFunctor H K
  let B := forgetHom (restrict H) (restrict K)
  have : B.IsEquivalence := inferInstanceAs (forgetHom (restrict H) (restrict K)).IsEquivalence
  have : (A ⋙ B).IsEquivalence := inferInstanceAs (forgetHom H K).IsEquivalence
  exact Functor.isEquivalence_of_comp_right A B

variable (F T)
variable (Q : Pseudofunctor (T.left × T.right) T.top)
variable (counit : Bicategory.Equivalence (Q.comp (pair T.rL T.rR)) (Pseudofunctor.id _))
variable (c : T.empty)

noncomputable def extensionRecovery (H : Map (F := F) (T := T)) :
    Bicategory.Equivalence (restrict (extension F T Q counit H.left H.right c)) H :=
  reflectObjectEquivalence (forgetAtoms F T) forgetAtoms_local
    (Bicategory.Equivalence.id (H.left,H.right))

noncomputable def restrictionRecovery (K : Map (F := completion F) (T := T)) :
    Bicategory.Equivalence
      (extension F T Q counit (restrict K).left (restrict K).right c) K :=
  reflectObjectEquivalence (forgetAtoms (completion F) T) forgetAtoms_local
    (Bicategory.Equivalence.id (K.left,K.right))

include Q counit c in
theorem precomposeUnit_biequivalence : IsBiequivalence (precomposeUnit (F := F) (T := T)) := by
  refine ⟨?_, precomposeUnit_local⟩
  intro H
  exact ⟨extension F T Q counit H.left H.right c, ⟨extensionRecovery F T Q counit c H⟩⟩

end SquareKit.FiniteHigherUnitPrecomposition
namespace SquareKit.FiniteHigherMapComposition
open CategoryTheory Bicategory SquareKit.HigherCategory SquareKit.PseudofunctorMapping SquareKit.FiniteHigherMap
open SquareKit.FiniteHigherCell SquareKit.PseudofunctorPostcomposition SquareKit.ContractibleBicategory SquareKit.FiniteHigherCompletion
open SquareKit.FiniteHigherAtomicMapping SquareKit.FiniteHigherExtension SquareKit.Biequivalence SquareKit.PseudofunctorComposition
open scoped Pseudofunctor.StrongTrans

variable {A B C D E G : Type} [Bicategory.{0,0} A] [Bicategory.{0,0} B]
  [Bicategory.{0,0} C] [Bicategory.{0,0} D] [Bicategory.{0,0} E] [Bicategory.{0,0} G]

noncomputable def composeComparison
    (R : Pseudofunctor A B) (S : Pseudofunctor C D) (U : Pseudofunctor E G)
    (hTop : Pseudofunctor A C) (hBottom : Pseudofunctor B D)
    (kTop : Pseudofunctor C E) (kBottom : Pseudofunctor D G)
    (e : Bicategory.Equivalence (R.comp hBottom) (hTop.comp S))
    (d : Bicategory.Equivalence (S.comp kBottom) (kTop.comp U)) :
    Bicategory.Equivalence (R.comp (hBottom.comp kBottom)) ((hTop.comp kTop).comp U) :=
  equivalenceComp (equalityEquivalence (comp_assoc R hBottom kBottom).symm)
    (equivalenceComp (mapEquivalence (post kBottom) e)
      (equivalenceComp (equalityEquivalence (comp_assoc hTop S kBottom))
        (equivalenceComp (mapEquivalence (pre hTop) d)
          (equalityEquivalence (comp_assoc hTop kTop U).symm))))

variable {F S T : FullDiagram.{0,0,0}}
noncomputable def composeCore (H : Map (F := F) (T := S)) (K : Map (F := S) (T := T)) : MapCore F T where
  top := H.top.comp K.top
  left := H.left.comp K.left
  right := H.right.comp K.right
  empty := H.empty.comp K.empty
  topLeft := composeComparison F.rL S.rL T.rL H.top H.left K.top K.left H.topLeft K.topLeft
  topRight := composeComparison F.rR S.rR T.rR H.top H.right K.top K.right H.topRight K.topRight
  topEmpty := composeComparison F.r0 S.r0 T.r0 H.top H.empty K.top K.empty H.topEmpty K.topEmpty
  leftEmpty := composeComparison F.sL S.sL T.sL H.left H.empty K.left K.empty H.leftEmpty K.leftEmpty
  rightEmpty := composeComparison F.sR S.sR T.sR H.right H.empty K.right K.empty H.rightEmpty K.rightEmpty

variable [∀ x y : T.empty, Nonempty (x ⟶ y)]
  [∀ (x y : T.empty) (f g : x ⟶ y), Unique (f ⟶ g)]
noncomputable def compose (H : Map (F := F) (T := S)) (K : Map (F := S) (T := T)) : Map (F := F) (T := T) where
  toMapCore := composeCore H K
  leftCoherence := modificationIso _ _
  rightCoherence := modificationIso _ _

variable [∀ x y, ((pair T.rL T.rR).toPrelaxFunctor.mapFunctor x y).IsEquivalence]
noncomputable def unitNormalization (K : Map (F := completion F) (T := T)) :
    Bicategory.Equivalence (compose (unit F) K) (SquareKit.FiniteHigherUnitPrecomposition.restrict K) :=
  reflectObjectEquivalence (forgetAtoms F T) forgetAtoms_local
    (productEquivalence (equalityEquivalence (id_comp K.left))
      (equalityEquivalence (id_comp K.right)))

variable (Q : Pseudofunctor (T.left × T.right) T.top)
variable (counit : Bicategory.Equivalence (Q.comp (pair T.rL T.rR)) (Pseudofunctor.id _))
variable (c : T.empty)

noncomputable def literalExtensionRecovery (H : Map (F := F) (T := T)) :
    Bicategory.Equivalence (compose (unit F) (extension F T Q counit H.left H.right c)) H :=
  equivalenceComp (unitNormalization (extension F T Q counit H.left H.right c))
    (SquareKit.FiniteHigherUnitPrecomposition.extensionRecovery F T Q counit c H)

end SquareKit.FiniteHigherMapComposition
namespace SquareKit.FiniteHigherRecovery
open CategoryTheory Bicategory SquareKit.HigherCategory SquareKit.PseudofunctorMapping SquareKit.FiniteHigherMap
open SquareKit.FiniteHigherCell SquareKit.PseudofunctorPostcomposition SquareKit.ContractibleBicategory SquareKit.FiniteHigherCompletion
open SquareKit.FiniteHigherAtomicMapping SquareKit.FiniteHigherExtension SquareKit.FiniteHigherMapComposition
open SquareKit.Biequivalence SquareKit.PseudofunctorComposition
open scoped Pseudofunctor.StrongTrans

variable (F : FullDiagram.{0,0,0})
variable [∀ x y : F.empty, Nonempty (x ⟶ y)]
  [∀ (x y : F.empty) (f g : x ⟶ y), Unique (f ⟶ g)]

noncomputable def identityMap : Map (F := F) (T := F) where
  top := Pseudofunctor.id _
  left := Pseudofunctor.id _
  right := Pseudofunctor.id _
  empty := Pseudofunctor.id _
  topLeft := equalityEquivalence ((comp_id F.rL).trans (id_comp F.rL).symm)
  topRight := equalityEquivalence ((comp_id F.rR).trans (id_comp F.rR).symm)
  topEmpty := equalityEquivalence ((comp_id F.r0).trans (id_comp F.r0).symm)
  leftEmpty := equalityEquivalence ((comp_id F.sL).trans (id_comp F.sL).symm)
  rightEmpty := equalityEquivalence ((comp_id F.sR).trans (id_comp F.sR).symm)
  leftCoherence := modificationIso _ _
  rightCoherence := modificationIso _ _

variable (Q : Pseudofunctor (F.left × F.right) F.top)
variable (counit : Bicategory.Equivalence (Q.comp (pair F.rL F.rR)) (Pseudofunctor.id _))
variable (c : F.empty)

noncomputable def inverseUnit : Map (F := completion F) (T := F) :=
  extension F F Q counit (Pseudofunctor.id _) (Pseudofunctor.id _) c

variable [∀ x y, ((pair F.rL F.rR).toPrelaxFunctor.mapFunctor x y).IsEquivalence]

noncomputable def unitLeftRecovery :
    Bicategory.Equivalence (compose (unit F) (inverseUnit F Q counit c)) (identityMap F) :=
  reflectObjectEquivalence (forgetAtoms F F) forgetAtoms_local
    (productEquivalence (equalityEquivalence (id_comp (Pseudofunctor.id F.left)))
      (equalityEquivalence (id_comp (Pseudofunctor.id F.right))))

instance atomicPairLocal (x y : (completion F).top) :
    ((pair (completion F).rL (completion F).rR).toPrelaxFunctor.mapFunctor x y).IsEquivalence := by
  change (𝟭 (x ⟶ y)).IsEquivalence
  infer_instance

noncomputable def unitRightRecovery :
    Bicategory.Equivalence (compose (inverseUnit F Q counit c) (unit F)) (identityMap (completion F)) :=
  reflectObjectEquivalence (forgetAtoms (completion F) (completion F)) forgetAtoms_local
    (productEquivalence (equalityEquivalence (id_comp (Pseudofunctor.id F.left)))
      (equalityEquivalence (id_comp (Pseudofunctor.id F.right))))

end SquareKit.FiniteHigherRecovery
namespace SquareKit.FiniteHigherUniversal
open CategoryTheory Bicategory SquareKit.HigherCategory SquareKit.PseudofunctorMapping SquareKit.FiniteHigherMap
open SquareKit.ContractibleBicategory SquareKit.FiniteHigherCompletion SquareKit.FiniteHigherUnitPrecomposition
open scoped Pseudofunctor.StrongTrans
variable (F T : FullDiagram.{0,0,0})

noncomputable def precomposeUnitOfDescent
    (hEmpty : IsBiequivalence (toTerminal (C := T.empty))) :
    Pseudofunctor (Map (F := completion F) (T := T)) (Map (F := F) (T := T)) := by
  have := arrows_of_terminal_hom_equivalence (toTerminal (C := T.empty)) hEmpty.2
  letI := cellsOfTerminalHomEquivalence (toTerminal (C := T.empty)) hEmpty.2
  exact precomposeUnit

theorem mapping_universal_property
    (hEmpty : IsBiequivalence (toTerminal (C := T.empty)))
    (hPair : IsBiequivalence (pair T.rL T.rR)) :
    IsBiequivalence (precomposeUnitOfDescent F T hEmpty) := by
  have := arrows_of_terminal_hom_equivalence (toTerminal (C := T.empty)) hEmpty.2
  let := cellsOfTerminalHomEquivalence (toTerminal (C := T.empty)) hEmpty.2
  have := hPair.2
  let q (b : T.left × T.right) : T.top := Classical.choose (hPair.1 b)
  let e (b : T.left × T.right) : Bicategory.Equivalence ((pair T.rL T.rR).obj (q b)) b :=
    Classical.choice (Classical.choose_spec (hPair.1 b))
  let Q := SquareKit.PseudofunctorInverse.inverse (pair T.rL T.rR) q e
  let ε := SquareKit.PseudofunctorInverse.counitEquivalence (pair T.rL T.rR) q e
  let c : T.empty := Classical.choose (hEmpty.1 (SquareKit.DoubleDelooping.point PUnit))
  exact precomposeUnit_biequivalence F T Q ε c

end SquareKit.FiniteHigherUniversal

end

namespace SquareKit.FiniteHigherUniversal
open CategoryTheory Bicategory HigherCategory FiniteHigherMap FiniteHigherCompletion
open FiniteHigherDescent
open scoped Pseudofunctor.StrongTrans

/-- Precomposition by the named completion unit, with empty-fiber data derived
from descent on the actual Grothendieck site. -/
noncomputable def precomposeStackUnit (F T : FullDiagram.{0,0,0})
    (hT : IsStackOnAllCoveringSieves T) :
    Pseudofunctor (Map (F := completion F) (T := T)) (Map (F := F) (T := T)) :=
  precomposeUnitOfDescent F T ((stack_criterion T).mp ((allCoveringSieves_iff T).mp hT)).1

/-- The mapping universal property quantifies over full weak maps, strong
transformations with their five squares, and compatible modifications. -/
theorem precomposeStackUnit_biequivalence (F T : FullDiagram.{0,0,0})
    (hT : IsStackOnAllCoveringSieves T) :
    IsBiequivalence (precomposeStackUnit F T hT) := by
  have h := (stack_criterion T).mp ((allCoveringSieves_iff T).mp hT)
  exact mapping_universal_property F T h.1 h.2

end SquareKit.FiniteHigherUniversal
