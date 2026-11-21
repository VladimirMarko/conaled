import SquareKit.SheafSliceTorsor
import SquareKit.SheafActionQuotient

/-! Equivariant targets on independent principal sheaves on the slice site. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafSliceQuotient
open CategoryTheory Opposite
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)}
variable (a : SheafActionQuotient.Action G M) (U : C)

abbrev restrictedTarget : Sheaf (J.over U) (Type u) := (J.overPullback (Type u) U).obj M

/-- A quotient on the actual slice site has a principal sheaf and a natural
equivariant map into the restricted target. -/
structure Object where
  torsor : SheafSliceTorsor.Torsor J U G
  value : torsor.sheaf ⟶ restrictedTarget (M := M) U
  equivariant (X : (Over U)ᵒᵖ) (g) (p) :
    value.hom.app X (torsor.act X g p) = a.act (op X.unop.left) g (value.hom.app X p)

variable {a U}
structure Arrow (P Q : Object a U) where
  torsorArrow : SheafSliceTorsor.Arrow P.torsor Q.torsor
  preserves : torsorArrow.iso.hom ≫ Q.value = P.value

@[ext] theorem Arrow.ext {P Q : Object a U} (f g : Arrow P Q)
    (h : f.torsorArrow = g.torsorArrow) : f = g := by
  cases f; cases g; cases h; rfl

instance : Category (Object a U) where
  Hom := Arrow
  id P := ⟨(show P.torsor ⟶ P.torsor from 𝟙 _), by change 𝟙 _ ≫ _ = _; exact Category.id_comp _⟩
  comp {P Q R} f g := ⟨(show P.torsor ⟶ R.torsor from f.torsorArrow ≫ g.torsorArrow), by
    change (f.torsorArrow.iso.hom ≫ g.torsorArrow.iso.hom) ≫ _ = _
    rw [Category.assoc, g.preserves, f.preserves]⟩
  id_comp f := by apply Arrow.ext; exact Category.id_comp _
  comp_id f := by apply Arrow.ext; exact Category.comp_id _
  assoc f g h := by apply Arrow.ext; exact Category.assoc _ _ _

def Arrow.toIso {P Q : Object a U} (h : Arrow P Q) : P ≅ Q where
  hom := h
  inv :=
    { torsorArrow := h.torsorArrow.inverse
      preserves := by
        apply (cancel_epi h.torsorArrow.iso.hom).mp
        change h.torsorArrow.iso.hom ≫ h.torsorArrow.iso.inv ≫ P.value = _
        rw [← Category.assoc, h.torsorArrow.iso.hom_inv_id, Category.id_comp]
        exact h.preserves.symm }
  hom_inv_id := by apply Arrow.ext; exact h.torsorArrow.toIso.hom_inv_id
  inv_hom_id := by apply Arrow.ext; exact h.torsorArrow.toIso.inv_hom_id

/-- An arbitrary equivariant natural map compatible with the target. -/
structure EquivariantMap (P Q : Object a U) where
  torsorMap : SheafSliceTorsor.EquivariantMap P.torsor Q.torsor
  preserves : torsorMap.hom ≫ Q.value = P.value

variable (a U) [J.Subcanonical]

def forwardObject (P : SheafActionQuotient.Object a (J.yoneda.obj U)) : Object a U where
  torsor := SheafSliceTorsor.forwardObject J U P.torsor
  value := ⟨{
    app X := ↾P.value ((yoneda.obj U).elementsMk (op X.unop.left) X.unop.hom)
    naturality {X Y} f := by ext p; exact (P.natural ((SheafSliceTorsor.toElements U).map f.unop).unop p).symm }⟩
  equivariant X := P.equivariant ((yoneda.obj U).elementsMk (op X.unop.left) X.unop.hom)

def backwardObject (P : Object a U) : SheafActionQuotient.Object a (J.yoneda.obj U) where
  torsor := SheafSliceTorsor.backwardObject J U P.torsor
  value x := P.value.hom.app (op (Over.mk x.val))
  natural f p := (NatTrans.naturality_apply P.value.hom
    ((SheafSliceTorsor.fromElements U).map f.op).op p).symm
  equivariant x := P.equivariant (op (Over.mk x.val))

def forward : SheafActionQuotient.Object a (J.yoneda.obj U) ⥤ Object a U where
  obj := forwardObject a U
  map h :=
    { torsorArrow := (SheafSliceTorsor.forward J U).map h.torsorArrow
      preserves := by ext X p; exact h.preserves _ p }
  map_id P := by apply Arrow.ext; rfl
  map_comp h k := by apply Arrow.ext; rfl

def backward : Object a U ⥤ SheafActionQuotient.Object a (J.yoneda.obj U) where
  obj := backwardObject a U
  map h :=
    { torsorArrow := (SheafSliceTorsor.backward J U).map h.torsorArrow
      preserves x p := congrArg (fun k => k.hom.app (op (Over.mk x.val)) p) h.preserves }
  map_id P := by apply SheafActionQuotient.Arrow.ext; rfl
  map_comp h k := by apply SheafActionQuotient.Arrow.ext; rfl

def unitComponent (P : SheafActionQuotient.Object a (J.yoneda.obj U)) :
    P ≅ (forward a U ⋙ backward a U).obj P where
  hom := ⟨(SheafSliceTorsor.unitComponent J U P.torsor).hom, fun _ _ => rfl⟩
  inv := ⟨(SheafSliceTorsor.unitComponent J U P.torsor).inv, fun _ _ => rfl⟩
  hom_inv_id := by apply SheafActionQuotient.Arrow.ext; exact (SheafSliceTorsor.unitComponent J U P.torsor).hom_inv_id
  inv_hom_id := by apply SheafActionQuotient.Arrow.ext; exact (SheafSliceTorsor.unitComponent J U P.torsor).inv_hom_id

def counitComponent (P : Object a U) : (backward a U ⋙ forward a U).obj P ≅ P where
  hom := ⟨(SheafSliceTorsor.counitComponent J U P.torsor).hom, rfl⟩
  inv := ⟨(SheafSliceTorsor.counitComponent J U P.torsor).inv, rfl⟩
  hom_inv_id := by apply Arrow.ext; exact (SheafSliceTorsor.counitComponent J U P.torsor).hom_inv_id
  inv_hom_id := by apply Arrow.ext; exact (SheafSliceTorsor.counitComponent J U P.torsor).inv_hom_id

/-- All equivariant target maps and compatible arrows survive slice recovery. -/
def equivalence : SheafActionQuotient.Object a (J.yoneda.obj U) ≌ Object a U :=
  CategoryTheory.Equivalence.mk (forward a U) (backward a U)
    (NatIso.ofComponents (unitComponent a U) (by intro P Q h; apply SheafActionQuotient.Arrow.ext; apply SheafTorsor.Arrow.ext; rfl))
    (NatIso.ofComponents (counitComponent a U) (by intro P Q h; apply Arrow.ext; apply SheafSliceTorsor.Arrow.ext; rfl))

@[simp] theorem recovery_target (P : SheafActionQuotient.Object a (J.yoneda.obj U))
    (x) (p) :
    ((backward a U).obj ((forward a U).obj P)).value x
      ((unitComponent a U P).hom.torsorArrow.iso.hom.app x p) = P.value x p := rfl

variable {U} {V W : C}

/-- Ordinary slice restriction retains the independently supplied target map. -/
def restrictObject (f : V ⟶ U) (P : Object a U) : Object a V where
  torsor := SheafSliceTorsor.restrictObject J f P.torsor
  value := ⟨Functor.whiskerLeft (Over.map f).op P.value.hom⟩
  equivariant X := P.equivariant (op ((Over.map f).obj X.unop))

def restriction (f : V ⟶ U) : Object a U ⥤ Object a V where
  obj := restrictObject a f
  map h :=
    { torsorArrow := (SheafSliceTorsor.restriction J f).map h.torsorArrow
      preserves := by ext X p; exact congrArg (fun k => k.hom.app (op ((Over.map f).obj X.unop)) p) h.preserves }
  map_id P := by apply Arrow.ext; rfl
  map_comp h k := by apply Arrow.ext; rfl

def restrictionComparison (f : V ⟶ U) :
    SheafActionQuotient.restriction (a := a) (J.yoneda.map f) ⋙ forward a V ≅
      forward a U ⋙ restriction a f :=
  NatIso.ofComponents (fun P =>
    { hom := ⟨((SheafSliceTorsor.restrictionComparison J f).app P.torsor).hom, rfl⟩
      inv := ⟨((SheafSliceTorsor.restrictionComparison J f).app P.torsor).inv, rfl⟩
      hom_inv_id := by apply Arrow.ext; exact ((SheafSliceTorsor.restrictionComparison J f).app P.torsor).hom_inv_id
      inv_hom_id := by apply Arrow.ext; exact ((SheafSliceTorsor.restrictionComparison J f).app P.torsor).inv_hom_id })
    (by intro P Q h; apply Arrow.ext; apply SheafSliceTorsor.Arrow.ext; rfl)

def restrictionIdComponent (P : Object a U) : (restriction a (𝟙 U)).obj P ≅ P :=
  Arrow.toIso
    { torsorArrow := (SheafSliceTorsor.restrictionIdComponent J P.torsor).hom
      preserves := by
        ext X p
        have h := NatTrans.naturality_apply P.value.hom ((Over.mapId U).inv.app X.unop).op p
        have hm : (restrictedTarget (M := M) U).obj.map ((Over.mapId U).inv.app X.unop).op
            (P.value.hom.app _ p) = P.value.hom.app _ p := by
          change M.obj.map (𝟙 _) _ = _
          rw [M.obj.map_id]
          rfl
        rw [hm] at h
        exact h }

def restrictionCompComponent (f : V ⟶ U) (g : W ⟶ V) (P : Object a U) :
    (restriction a (g ≫ f)).obj P ≅ (restriction a g).obj ((restriction a f).obj P) :=
  Arrow.toIso
    { torsorArrow := (SheafSliceTorsor.restrictionCompComponent J f g P.torsor).hom
      preserves := by
        ext X p
        have h := NatTrans.naturality_apply P.value.hom ((Over.mapComp g f).inv.app X.unop).op p
        have hm : (restrictedTarget (M := M) U).obj.map ((Over.mapComp g f).inv.app X.unop).op
            (P.value.hom.app _ p) = P.value.hom.app _ p := by
          change M.obj.map (𝟙 _) _ = _
          rw [M.obj.map_id]
          rfl
        rw [hm] at h
        exact h }

def restrictionId : restriction a (𝟙 U) ≅ 𝟭 (Object a U) :=
  NatIso.ofComponents (restrictionIdComponent a) (by
    intro P Q h
    apply Arrow.ext
    exact (SheafSliceTorsor.restrictionId J).hom.naturality h.torsorArrow)

def restrictionComp (f : V ⟶ U) (g : W ⟶ V) :
    restriction a (g ≫ f) ≅ restriction a f ⋙ restriction a g :=
  NatIso.ofComponents (restrictionCompComponent a f g) (by
    intro P Q h
    apply Arrow.ext
    exact (SheafSliceTorsor.restrictionComp J f g).hom.naturality h.torsorArrow)

/-- Local principality supplies the inverse; target compatibility survives it. -/
def EquivariantMap.toArrow {P Q : Object a U} (f : EquivariantMap P Q) : Arrow P Q where
  torsorArrow := f.torsorMap.toArrow J
  preserves := f.preserves

def equivariantArrowEquiv {P Q : Object a U} : EquivariantMap P Q ≃ Arrow P Q where
  toFun := EquivariantMap.toArrow a
  invFun f := ⟨⟨f.torsorArrow.iso.hom, f.torsorArrow.equivariant⟩, f.preserves⟩
  left_inv f := by cases f; rfl
  right_inv f := by apply Arrow.ext; apply SheafSliceTorsor.Arrow.ext; rfl

end SquareKit.SheafSliceQuotient
