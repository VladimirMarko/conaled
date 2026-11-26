import SquareKit.SheafSiteComparisonTorsor
import SquareKit.SheafifiedSliceQuotient
import Mathlib.CategoryTheory.Endomorphism

/-! Dense site comparison for torsors with equivariant target maps. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafSiteComparison
open CategoryTheory Opposite
universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
variable {G : Sheaf K GrpCat.{u}} {M X Y Z : Sheaf K (Type u)}
variable (a : SheafActionQuotient.Action G M)

/-- The parameter element site carries the original target sheaf by projection. -/
abbrev elementTarget (X M : Sheaf K (Type u)) :
    Sheaf (ElementSite.topology X.obj K) (Type u) :=
  ((ElementSite.projection X.obj).sheafPushforwardContinuous (Type u)
    (ElementSite.topology X.obj K) K).obj M

def targetMap (P : SheafActionQuotient.Object a X) :
    SplitSheaf.elementSheaf P.torsor.family ⟶ elementTarget K X M := ⟨{
  app x := ↾P.value x.unop.unop
  naturality {x y} f := by ext p; exact (P.natural f.unop.unop p).symm }⟩

section Forward
variable [F.IsContinuous J K] [F.IsCocontinuous J K]

/-- Restrict the torsor and its independently supplied target map componentwise. -/
def quotientObject (P : SheafActionQuotient.Object a X) :
    SheafActionQuotient.Object (action J K F a) (sheaf J K F X) where
  torsor := torsor J K F P.torsor
  value x := P.value ((elements K F X).obj x)
  natural f := P.natural ((elements K F X).map f)
  equivariant x := P.equivariant ((elements K F X).obj x)

def quotientFunctor : SheafActionQuotient.Object a X ⥤
    SheafActionQuotient.Object (action J K F a) (sheaf J K F X) where
  obj := quotientObject J K F a
  map h :=
    { torsorArrow := (torsorFunctor J K F).map h.torsorArrow
      preserves x := h.preserves ((elements K F X).obj x) }

theorem quotient_totalMap (P : SheafActionQuotient.Object a X) :
    (quotientObject J K F a P).totalMap = map J K F P.totalMap := rfl

/-- Regular chart objects retain their orbit map after restriction. -/
theorem quotient_chart (m : X ⟶ M) :
    quotientObject J K F a (SheafActionQuotient.chart a m) =
      SheafActionQuotient.chart (action J K F a) (map J K F m) := rfl

end Forward

variable [F.Full] [F.Faithful] [F.IsDenseSubsite J K]

/-- Dense restriction detects equality of every target map. -/
theorem target_ext {P : SheafTorsor.Torsor G X}
    {f g : SplitSheaf.elementSheaf P.family ⟶ elementTarget K X M}
    (h : (elementEquivalence J K F X).inverse.map f =
      (elementEquivalence J K F X).inverse.map g) : f = g :=
  (elementEquivalence J K F X).inverse.map_injective h

def liftQuotientArrow {P Q : SheafActionQuotient.Object a X}
    (h : (quotientFunctor J K F a).obj P ⟶ (quotientFunctor J K F a).obj Q) : P ⟶ Q := by
  let t := liftTorsorArrow J K F h.torsorArrow
  let m : SplitSheaf.elementSheaf P.torsor.family ⟶ SplitSheaf.elementSheaf Q.torsor.family :=
    ⟨Functor.whiskerLeft (opOpEquivalence _).functor t.iso.hom⟩
  have ht : m ≫ targetMap K a Q = targetMap K a P := by
    apply target_ext J K F
    rw [Functor.map_comp]
    have hm : (elementEquivalence J K F X).inverse.map m =
        (show SplitSheaf.elementSheaf (torsor J K F P.torsor).family ⟶
          SplitSheaf.elementSheaf (torsor J K F Q.torsor).family from
          ⟨Functor.whiskerLeft (opOpEquivalence _).functor h.torsorArrow.iso.hom⟩) := by
      have he := torsorFunctor_lift J K F h.torsorArrow
      exact congrArg (fun k =>
        (show SplitSheaf.elementSheaf (torsor J K F P.torsor).family ⟶
          SplitSheaf.elementSheaf (torsor J K F Q.torsor).family from
          ⟨Functor.whiskerLeft (opOpEquivalence _).functor k.iso.hom⟩)) he
    rw [hm]
    ext x p
    exact h.preserves x.unop.unop p
  exact ⟨t, fun x p => congrArg (fun k => k.hom.app (op (op x)) p) ht⟩

instance quotientFunctor_full : (quotientFunctor (X := X) J K F a).Full where
  map_surjective h := ⟨liftQuotientArrow J K F a h, by
    apply SheafActionQuotient.Arrow.ext
    exact torsorFunctor_lift J K F h.torsorArrow⟩

instance quotientFunctor_faithful : (quotientFunctor (X := X) J K F a).Faithful where
  map_injective h := by
    apply SheafActionQuotient.Arrow.ext
    apply (torsorFunctor J K F).map_injective
    exact congrArg SheafActionQuotient.Arrow.torsorArrow h

/-- Equivariance into an arbitrary acted-on sheaf can be checked on the dense subsite. -/
theorem target_equivariant {P : SheafTorsor.Torsor G X}
    (m : SplitSheaf.elementSheaf P.family ⟶ elementTarget K X M)
    (h : ∀ x g p, ((elementEquivalence J K F X).inverse.map m).hom.app (op (op x))
      ((torsor J K F P).act x g p) =
        (action J K F a).act x.obj g
          (((elementEquivalence J K F X).inverse.map m).hom.app (op (op x)) p))
    (x : X.obj.Elements) (g) (p) :
    m.hom.app (op (op x)) (P.act x g p) =
      a.act x.obj g (m.hom.app (op (op x)) p) := by
  apply PrincipalSheaf.section_ext (ElementSite.topology (sheaf J K F X).obj J)
    (ElementSite.topology X.obj K) (ElementSite.comparison F X.obj)
    (elementTarget K X M) (op x)
  intro V f
  have hn := NatTrans.naturality_apply m.hom f.op (P.act x g p)
  have hp := NatTrans.naturality_apply m.hom f.op p
  change m.hom.app (op ((ElementSite.comparison F X.obj).obj V))
    (P.family.family.map f.unop (P.act x g p)) = _ at hn
  exact hn.symm.trans ((congrArg (m.hom.app (op ((ElementSite.comparison F X.obj).obj V)))
    (P.natural f.unop g p)).trans
      ((h V.unop _ _).trans
        ((congrArg (a.act _ (G.obj.map f.unop.hom g)) hp).trans
          (a.natural f.unop.hom g _).symm)))

abbrev extendedTarget (Q : SheafActionQuotient.Object (action J K F a) (sheaf J K F X)) :
    SplitSheaf.elementSheaf (extendTorsor J K F Q.torsor).family ⟶ elementTarget K X M :=
  (elementEquivalence J K F X).inverse.preimage
    ((show SplitSheaf.elementSheaf (torsor J K F (extendTorsor J K F Q.torsor)).family ⟶
        SplitSheaf.elementSheaf Q.torsor.family from
      ⟨Functor.whiskerLeft (opOpEquivalence _).functor (torsorCounit J K F Q.torsor).hom.iso.hom⟩) ≫
        targetMap J (action J K F a) Q)

def extendQuotient (Q : SheafActionQuotient.Object (action J K F a) (sheaf J K F X)) :
    SheafActionQuotient.Object a X where
  torsor := extendTorsor J K F Q.torsor
  value x := (extendedTarget J K F a Q).hom.app (op (op x))
  natural f p := (NatTrans.naturality_apply (extendedTarget J K F a Q).hom f.op.op p).symm
  equivariant := target_equivariant J K F a (extendedTarget J K F a Q) (by
    intro x g p
    rw [Functor.map_preimage]
    exact (congrArg (Q.value x) ((torsorCounit J K F Q.torsor).hom.equivariant x g p)).trans
      (Q.equivariant x g _))

def quotientCounit (Q : SheafActionQuotient.Object (action J K F a) (sheaf J K F X)) :
    (quotientFunctor J K F a).obj (extendQuotient J K F a Q) ≅ Q :=
  SheafActionQuotient.Arrow.toIso
    { torsorArrow := (torsorCounit J K F Q.torsor).hom
      preserves x p := by
        have h := (elementEquivalence J K F X).inverse.map_preimage
          (show (elementEquivalence J K F X).inverse.obj
              (SplitSheaf.elementSheaf (extendTorsor J K F Q.torsor).family) ⟶
              (elementEquivalence J K F X).inverse.obj (elementTarget K X M) from
            (show SplitSheaf.elementSheaf (torsor J K F (extendTorsor J K F Q.torsor)).family ⟶
              SplitSheaf.elementSheaf Q.torsor.family from
                ⟨Functor.whiskerLeft (opOpEquivalence _).functor
                  (torsorCounit J K F Q.torsor).hom.iso.hom⟩) ≫ targetMap J (action J K F a) Q)
        exact (congrArg (fun k => k.hom.app (op (op x)) p) h).symm }

instance quotientFunctor_essSurj : (quotientFunctor (X := X) J K F a).EssSurj where
  mem_essImage Q := ⟨extendQuotient J K F a Q, ⟨quotientCounit J K F a Q⟩⟩
instance quotientFunctor_isEquivalence : (quotientFunctor (X := X) J K F a).IsEquivalence := {}

/-- The comparison retains all torsors, target maps, and compatible arrows. -/
def quotientEquivalence : SheafActionQuotient.Object a X ≌
    SheafActionQuotient.Object (action J K F a) (sheaf J K F X) :=
  (quotientFunctor J K F a).asEquivalence

def quotientStabilizerEquiv (P : SheafActionQuotient.Object a X) :
    (P ⟶ P) ≃ ((quotientFunctor J K F a).obj P ⟶ (quotientFunctor J K F a).obj P) :=
  (quotientEquivalence J K F a).fullyFaithfulFunctor.homEquiv

/-- The stabilizer comparison preserves group multiplication. -/
def quotientAutEquiv (P : SheafActionQuotient.Object a X) :
    Aut P ≃* Aut ((quotientFunctor J K F a).obj P) :=
  (quotientEquivalence J K F a).fullyFaithfulFunctor.autMulEquivOfFullyFaithful P

/-- Recovery gives an isomorphism of the original total displays. -/
def quotientDisplayComparison (P : SheafActionQuotient.Object a X) :
    SplitSheaf.extension P.torsor.family ≅
      SplitSheaf.extension (((quotientEquivalence J K F a).functor ⋙
        (quotientEquivalence J K F a).inverse).obj P).torsor.family :=
  ObjectProperty.isoMk _ (ElementFamilies.totalFunctor _ |>.mapIso
    ((quotientEquivalence J K F a).unitIso.app P).hom.torsorArrow.iso |>
      (Over.forget _).mapIso)

theorem quotientDisplayComparison_projection (P : SheafActionQuotient.Object a X) :
    (quotientDisplayComparison J K F a P).hom ≫
      SplitSheaf.p (((quotientEquivalence J K F a).functor ⋙
        (quotientEquivalence J K F a).inverse).obj P).torsor.family =
          SplitSheaf.p P.torsor.family := rfl

theorem quotientDisplayComparison_target (P : SheafActionQuotient.Object a X) :
    (quotientDisplayComparison J K F a P).hom ≫
      (((quotientEquivalence J K F a).functor ⋙
        (quotientEquivalence J K F a).inverse).obj P).totalMap = P.totalMap := by
  ext x p
  exact ((quotientEquivalence J K F a).unitIso.app P).hom.preserves _ p.2

omit [F.Full] [F.Faithful] in
theorem quotient_reindex (P : SheafActionQuotient.Object a X) (f : Y ⟶ X) :
    quotientObject J K F a (SheafActionQuotient.reindex P f) =
      SheafActionQuotient.reindex (quotientObject J K F a P) (map J K F f) := rfl

def quotientRestrictionComparison (f : Y ⟶ X) :
    SheafActionQuotient.restriction (a := a) f ⋙ quotientFunctor J K F a ≅
      quotientFunctor J K F a ⋙ SheafActionQuotient.restriction (map J K F f) := Iso.refl _

omit [F.Full] [F.Faithful] in
theorem quotient_reindex_id (P : SheafActionQuotient.Object a X) :
    quotientObject J K F a (SheafActionQuotient.reindex P (𝟙 X)) =
      quotientObject J K F a P := rfl

omit [F.Full] [F.Faithful] in
theorem quotient_reindex_comp (P : SheafActionQuotient.Object a X) (f : Y ⟶ X) (g : Z ⟶ Y) :
    quotientObject J K F a (SheafActionQuotient.reindex (SheafActionQuotient.reindex P f) g) =
      SheafActionQuotient.reindex (quotientObject J K F a P) (map J K F (g ≫ f)) := rfl

end SquareKit.SheafSiteComparison

namespace SquareKit.SheafSiteComparison
open CategoryTheory Opposite
universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
variable [F.Full] [F.Faithful] [F.IsDenseSubsite J K]
variable {G : Sheaf K GrpCat.{u}} {M : Sheaf K (Type u)}
variable (a : SheafActionQuotient.Action G M) (U : D)

omit [F.Full] [F.Faithful] [F.IsDenseSubsite J K] in
/-- The target presentation agrees with the existing original-slice construction. -/
theorem targetMap_slice (P : SheafActionQuotient.Object a (SheafifiedSliceTorsor.context K U)) :
    targetMap K a P = SheafifiedSliceQuotient.targetMap a U P := rfl

/-- Site restriction commutes naturally with recovery through the original slice. -/
def sliceQuotientRecovery :
    quotientFunctor (X := SheafifiedSliceTorsor.context K U) J K F a ≅
      ((SheafifiedSliceQuotient.equivalence a U).functor ⋙
        (SheafifiedSliceQuotient.equivalence a U).inverse) ⋙ quotientFunctor J K F a :=
  Functor.isoWhiskerRight (SheafifiedSliceQuotient.equivalence a U).unitIso (quotientFunctor J K F a)

omit [F.Full] [F.Faithful] in
theorem sliceQuotientRecovery_natural
    {P Q : SheafActionQuotient.Object a (SheafifiedSliceTorsor.context K U)} (h : P ⟶ Q) :
    (quotientFunctor J K F a).map h ≫ (sliceQuotientRecovery J K F a U).hom.app Q =
      (sliceQuotientRecovery J K F a U).hom.app P ≫
        (quotientFunctor J K F a).map (((SheafifiedSliceQuotient.equivalence a U).functor ⋙
          (SheafifiedSliceQuotient.equivalence a U).inverse).map h) :=
  (sliceQuotientRecovery J K F a U).hom.naturality h

omit [F.Full] [F.Faithful] in
theorem sliceQuotientRecovery_projection
    (P : SheafActionQuotient.Object a (SheafifiedSliceTorsor.context K U)) :
    SplitSheaf.totalMap ((sliceQuotientRecovery J K F a U).hom.app P).torsorArrow.iso.hom ≫
      SplitSheaf.p (quotientObject J K F a (((SheafifiedSliceQuotient.equivalence a U).functor ⋙
        (SheafifiedSliceQuotient.equivalence a U).inverse).obj P)).torsor.family =
          SplitSheaf.p (quotientObject J K F a P).torsor.family := rfl

omit [F.Full] [F.Faithful] in
theorem sliceQuotientRecovery_target
    (P : SheafActionQuotient.Object a (SheafifiedSliceTorsor.context K U)) :
    SplitSheaf.totalMap ((sliceQuotientRecovery J K F a U).hom.app P).torsorArrow.iso.hom ≫
      (quotientObject J K F a (((SheafifiedSliceQuotient.equivalence a U).functor ⋙
        (SheafifiedSliceQuotient.equivalence a U).inverse).obj P)).totalMap =
          (quotientObject J K F a P).totalMap :=
  (SheafActionQuotient.preserves_iff_totalMap _).mp
    ((sliceQuotientRecovery J K F a U).hom.app P).preserves

end SquareKit.SheafSiteComparison
