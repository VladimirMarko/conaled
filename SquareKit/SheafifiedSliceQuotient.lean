import SquareKit.SheafifiedSliceTorsor
import SquareKit.SheafSliceQuotient

/-! Action quotients on ordinary slices over arbitrary sites. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafifiedSliceQuotient
open CategoryTheory Opposite SheafifiedSliceTorsor
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)}
variable (a : SheafActionQuotient.Action G M) (U : C)

abbrev elementTarget : Sheaf (elementTopology J U) (Type u) :=
  ((ElementSite.projection (context J U).obj).sheafPushforwardContinuous (Type u)
    (elementTopology J U) J).obj M

def targetMap (P : SheafActionQuotient.Object a (context J U)) :
    SplitSheaf.elementSheaf P.torsor.family ⟶ elementTarget (M := M) U := ⟨{
  app X := ↾P.value X.unop.unop
  naturality {X Y} f := by ext p; exact (P.natural f.unop.unop p).symm }⟩

def forwardObject (P : SheafActionQuotient.Object a (context J U)) :
    SheafSliceQuotient.Object a U where
  torsor := SheafifiedSliceTorsor.forwardObject J U P.torsor
  value := (sheafEquivalence J U).functor.map (targetMap a U P)
  equivariant X := P.equivariant ((sliceElements J U).obj X)

def forward : SheafActionQuotient.Object a (context J U) ⥤ SheafSliceQuotient.Object a U where
  obj := forwardObject a U
  map h :=
    { torsorArrow := (SheafifiedSliceTorsor.forward J U).map h.torsorArrow
      preserves := by ext X p; exact h.preserves _ p }
  map_id _ := by apply SheafSliceQuotient.Arrow.ext; rfl
  map_comp _ _ := by apply SheafSliceQuotient.Arrow.ext; rfl

/-- Equality of target maps is detected by ordinary slice restriction. -/
theorem target_ext {P : SheafTorsor.Torsor G (context J U)}
    {f g : SplitSheaf.elementSheaf P.family ⟶ elementTarget (M := M) U}
    (h : (sheafEquivalence J U).functor.map f = (sheafEquivalence J U).functor.map g) :
    f = g := (sheafEquivalence J U).functor.map_injective h

def liftArrow {P Q : SheafActionQuotient.Object a (context J U)}
    (h : (forward a U).obj P ⟶ (forward a U).obj Q) : P ⟶ Q := by
  let t := SheafifiedSliceTorsor.liftArrow J U h.torsorArrow
  let m : SplitSheaf.elementSheaf P.torsor.family ⟶ SplitSheaf.elementSheaf Q.torsor.family :=
    ⟨Functor.whiskerLeft (opOpEquivalence _).functor t.iso.hom⟩
  have hm : (sheafEquivalence J U).functor.map m = h.torsorArrow.iso.hom :=
    congrArg (fun k => k.iso.hom) (SheafifiedSliceTorsor.forward_liftArrow J U h.torsorArrow)
  have ht : m ≫ targetMap a U Q = targetMap a U P := by
    apply target_ext U
    rw [Functor.map_comp, hm]
    exact h.preserves
  exact ⟨t, fun x p => congrArg (fun k => k.hom.app (op (op x)) p) ht⟩

instance forward_full : (forward a U).Full where
  map_surjective h := ⟨liftArrow a U h, by
    apply SheafSliceQuotient.Arrow.ext
    exact SheafifiedSliceTorsor.forward_liftArrow J U h.torsorArrow⟩

instance forward_faithful : (forward a U).Faithful where
  map_injective {P Q} {f g} h := by
    apply SheafActionQuotient.Arrow.ext
    apply (SheafifiedSliceTorsor.forward J U).map_injective
    exact congrArg SheafSliceQuotient.Arrow.torsorArrow h

/-- Equivariance into any acted-on sheaf can be checked on the dense slice. -/
theorem target_equivariant {P : SheafTorsor.Torsor G (context J U)}
    (m : SplitSheaf.elementSheaf P.family ⟶ elementTarget (M := M) U)
    (h : ∀ X g p, ((sheafEquivalence J U).functor.map m).hom.app X
      ((SheafifiedSliceTorsor.forwardObject J U P).act X g p) =
        a.act (op X.unop.left) g (((sheafEquivalence J U).functor.map m).hom.app X p))
    (x : (context J U).obj.Elements) (g) (p) :
    m.hom.app (op (op x)) (P.act x g p) = a.act x.obj g (m.hom.app (op (op x)) p) := by
  apply PrincipalSheaf.section_ext (rawTopology J U) (elementTopology J U) (unitSite J U)
    (elementTarget (M := M) U) (op x)
  intro Y f
  have hn := NatTrans.naturality_apply m.hom f.op (P.act x g p)
  have hp := NatTrans.naturality_apply m.hom f.op p
  change m.hom.app (op ((unitSite J U).obj Y)) (P.family.family.map f.unop (P.act x g p)) = _ at hn
  exact hn.symm.trans ((congrArg (m.hom.app (op ((unitSite J U).obj Y)))
    (P.natural f.unop g p)).trans
      ((h (op (Over.mk Y.unop.val)) _ _).trans
        ((congrArg (a.act _ (G.obj.map f.unop.hom g)) hp).trans
          (a.natural f.unop.hom g _).symm)))

abbrev backwardTarget (Q : SheafSliceQuotient.Object a U) :
    SplitSheaf.elementSheaf (SheafifiedSliceTorsor.backwardObject J U Q.torsor).family ⟶
      elementTarget (M := M) U :=
  (sheafEquivalence J U).functor.preimage
    ((SheafifiedSliceTorsor.counitSheaf J U Q.torsor).hom ≫ Q.value)

def backwardObject (Q : SheafSliceQuotient.Object a U) :
    SheafActionQuotient.Object a (context J U) where
  torsor := SheafifiedSliceTorsor.backwardObject J U Q.torsor
  value x := (backwardTarget a U Q).hom.app (op (op x))
  natural f p := (NatTrans.naturality_apply (backwardTarget a U Q).hom f.op.op p).symm
  equivariant := target_equivariant a U (backwardTarget a U Q) (by
    intro X g p
    rw [Functor.map_preimage]
    change Q.value.hom.app X ((SheafifiedSliceTorsor.counitComponent J U Q.torsor).hom.iso.hom.hom.app X _) = _
    exact (congrArg (Q.value.hom.app X)
      ((SheafifiedSliceTorsor.counitComponent J U Q.torsor).hom.equivariant X g p)).trans
        (Q.equivariant X g _))

def counitComponent (Q : SheafSliceQuotient.Object a U) :
    (forward a U).obj (backwardObject a U Q) ≅ Q :=
  SheafSliceQuotient.Arrow.toIso
    { torsorArrow := (SheafifiedSliceTorsor.counitComponent J U Q.torsor).hom
      preserves := by
        change (SheafifiedSliceTorsor.counitSheaf J U Q.torsor).hom ≫ Q.value =
          (sheafEquivalence J U).functor.map (backwardTarget a U Q)
        exact ((sheafEquivalence J U).functor.map_preimage
          (Y := elementTarget (M := M) U)
          ((SheafifiedSliceTorsor.counitSheaf J U Q.torsor).hom ≫ Q.value)).symm }

instance forward_essSurj : (forward a U).EssSurj where
  mem_essImage Q := ⟨backwardObject a U Q, ⟨counitComponent a U Q⟩⟩
instance forward_isEquivalence : (forward a U).IsEquivalence := {}

/-- Recovery retains every target map and every compatible torsor arrow. -/
def equivalence : SheafActionQuotient.Object a (context J U) ≌ SheafSliceQuotient.Object a U :=
  (forward a U).asEquivalence

/-- A compatible natural map gains an inverse from principality, with its target fixed. -/
def equivariantMapArrow {P Q : SheafSliceQuotient.Object a U}
    (f : SheafSliceQuotient.EquivariantMap P Q) : P ⟶ Q where
  torsorArrow := SheafifiedSliceTorsor.equivariantMapArrow J U f.torsorMap
  preserves := by rw [SheafifiedSliceTorsor.equivariantMapArrow_hom]; exact f.preserves

def equivariantArrowEquiv {P Q : SheafSliceQuotient.Object a U} :
    SheafSliceQuotient.EquivariantMap P Q ≃ (P ⟶ Q) where
  toFun := equivariantMapArrow a U
  invFun f := ⟨⟨f.torsorArrow.iso.hom, f.torsorArrow.equivariant⟩, f.preserves⟩
  left_inv f := by
    cases f with
    | mk m h =>
      cases m
      simp only [equivariantMapArrow, SheafifiedSliceTorsor.equivariantMapArrow_hom]
  right_inv f := by
    apply SheafSliceQuotient.Arrow.ext
    apply SheafSliceTorsor.Arrow.ext
    exact SheafifiedSliceTorsor.equivariantMapArrow_hom J U _

/-- No automorphism labels are collapsed, including stabilizers of target sections. -/
def stabilizerEquiv (P : SheafActionQuotient.Object a (context J U)) :
    (P ⟶ P) ≃ ((forward a U).obj P ⟶ (forward a U).obj P) :=
  (equivalence a U).fullyFaithfulFunctor.homEquiv

/-- The recovered total display preserves its independently supplied target map. -/
def displayComparison (P : SheafActionQuotient.Object a (context J U)) :
    SplitSheaf.extension P.torsor.family ≅
      SplitSheaf.extension (((equivalence a U).functor ⋙ (equivalence a U).inverse).obj P).torsor.family :=
  ObjectProperty.isoMk _ (ElementFamilies.totalFunctor _ |>.mapIso
    ((equivalence a U).unitIso.app P).hom.torsorArrow.iso |> (Over.forget _).mapIso)

@[simp] theorem displayComparison_projection (P : SheafActionQuotient.Object a (context J U)) :
    (displayComparison a U P).hom ≫
      SplitSheaf.p (((equivalence a U).functor ⋙ (equivalence a U).inverse).obj P).torsor.family =
        SplitSheaf.p P.torsor.family := rfl

theorem displayComparison_target (P : SheafActionQuotient.Object a (context J U)) :
    (displayComparison a U P).hom ≫
      (((equivalence a U).functor ⋙ (equivalence a U).inverse).obj P).totalMap = P.totalMap := by
  ext X p
  exact ((equivalence a U).unitIso.app P).hom.preserves _ p.2

variable {U} {V : C}

def restrictionComparison (f : V ⟶ U) :
    SheafActionQuotient.restriction (a := a) ((SheafifiedYoneda.functor J).map f) ⋙ forward a V ≅
      forward a U ⋙ SheafSliceQuotient.restriction a f :=
  NatIso.ofComponents (fun P => SheafSliceQuotient.Arrow.toIso
    { torsorArrow := ((SheafifiedSliceTorsor.restrictionComparison J f).app P.torsor).hom
      preserves := by
        ext X p
        have h := P.natural ((restrictionElementIso J f).hom.app X) p
        have hm : M.obj.map ((restrictionElementIso J f).hom.app X).hom
            (P.value _ p) = P.value _ p := by
          change M.obj.map (𝟙 _) _ = _
          rw [M.obj.map_id]
          rfl
        rw [hm] at h
        exact h.symm }) (by
      intro P Q h
      apply SheafSliceQuotient.Arrow.ext
      exact (SheafifiedSliceTorsor.restrictionComparison J f).hom.naturality h.torsorArrow)

end SquareKit.SheafifiedSliceQuotient
