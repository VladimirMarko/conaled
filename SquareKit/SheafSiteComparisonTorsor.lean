import SquareKit.SheafSiteComparison
import SquareKit.SheafifiedSliceTorsor
import Mathlib.CategoryTheory.Endomorphism

/-! Dense site restriction retains the complete torsor category over every parameter sheaf. -/
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
variable [F.IsContinuous J K] [F.IsCocontinuous J K]
variable {G : Sheaf K GrpCat.{u}} {X Y Z : Sheaf K (Type u)}

/-- The forward torsor retains each original fiber, action and restriction. -/
def torsor (P : SheafTorsor.Torsor G X) :
    SheafTorsor.Torsor (group J K F G) (sheaf J K F X) where
  family := family J K F P.family
  act x := P.act ((elements K F X).obj x)
  one_act x := P.one_act ((elements K F X).obj x)
  mul_act x := P.mul_act ((elements K F X).obj x)
  natural f := P.natural ((elements K F X).map f)
  principal x := P.principal ((elements K F X).obj x)
  locallySurjective := ⟨fun x => F.cover_lift J K
    (Presheaf.imageSieve_mem K (SplitSheaf.p P.family).hom x)⟩

/-- Restriction on every equivariant arrow is componentwise restriction. -/
def torsorFunctor : SheafTorsor.Torsor G X ⥤
    SheafTorsor.Torsor (group J K F G) (sheaf J K F X) where
  obj := torsor J K F
  map h :=
    { iso := Functor.isoWhiskerLeft (elements K F X) h.iso
      equivariant x := h.equivariant ((elements K F X).obj x) }

variable [F.Full] [F.Faithful] [F.IsDenseSubsite J K]

instance elementComparison_dense (X : Sheaf K (Type u)) :
    (ElementSite.comparison F X.obj).IsDenseSubsite
      (ElementSite.topology (sheaf J K F X).obj J) (ElementSite.topology X.obj K) :=
  ElementSite.comparison_isDenseSubsite F X.obj J K

abbrev elementEquivalence (X : Sheaf K (Type u)) :
    Sheaf (ElementSite.topology (sheaf J K F X).obj J) (Type u) ≌
      Sheaf (ElementSite.topology X.obj K) (Type u) :=
  @Functor.IsDenseSubsite.sheafEquiv _ _ _ _
    (ElementSite.topology (F.op ⋙ X.obj) J) (ElementSite.topology X.obj K)
    (ElementSite.comparison F X.obj) (Type u) _
    (ElementSite.comparison_isDenseSubsite F X.obj J K) _

/-- Dense element restriction detects equivariance of every map of dependent families. -/
theorem equivariant_of_restrict {P Q : SheafTorsor.Torsor G X}
    (f : SplitSheaf.elementSheaf P.family ⟶ SplitSheaf.elementSheaf Q.family)
    (h : PrincipalSheaf.Equivariant
      (PrincipalSheafContext.structureOf _ _ (torsor J K F P))
      (PrincipalSheafContext.structureOf _ _ (torsor J K F Q))
      ((elementEquivalence J K F X).inverse.map f)) :
    PrincipalSheaf.Equivariant (PrincipalSheafContext.structureOf X G P)
      (PrincipalSheafContext.structureOf X G Q) f := by
  let := elementComparison_dense J K F X
  exact (PrincipalSheaf.equivariant_iff _ _ (ElementSite.comparison F X.obj) _ _ f).mpr h

def liftTorsorArrow {P Q : SheafTorsor.Torsor G X}
    (h : (torsorFunctor J K F).obj P ⟶ (torsorFunctor J K F).obj Q) : P ⟶ Q := by
  let h' : SplitSheaf.elementSheaf (torsor J K F P).family ≅
      SplitSheaf.elementSheaf (torsor J K F Q).family :=
    ObjectProperty.isoMk _ (Functor.isoWhiskerLeft (opOpEquivalence _).functor h.iso)
  let i := (elementEquivalence J K F X).inverse.preimageIso (X := SplitSheaf.elementSheaf P.family)
    (Y := SplitSheaf.elementSheaf Q.family) h'
  have hi : (elementEquivalence J K F X).inverse.map i.hom = h'.hom :=
    (elementEquivalence J K F X).inverse.map_preimage _
  have he : PrincipalSheaf.Equivariant (PrincipalSheafContext.structureOf X G P)
      (PrincipalSheafContext.structureOf X G Q) i.hom := by
    apply equivariant_of_restrict J K F
    rw [hi]
    intro x g p
    exact h.equivariant x.unop.unop g p
  exact
    { iso := Functor.isoWhiskerLeft (opOpEquivalence _).inverse
        ((sheafToPresheaf _ _).mapIso i)
      equivariant x := he (op (op x)) }

theorem torsorFunctor_lift {P Q : SheafTorsor.Torsor G X}
    (h : (torsorFunctor J K F).obj P ⟶ (torsorFunctor J K F).obj Q) :
    (torsorFunctor J K F).map (liftTorsorArrow J K F h) = h := by
  apply SheafTorsor.Arrow.ext
  have he := (elementEquivalence J K F X).inverse.map_preimage
    (X := SplitSheaf.elementSheaf P.family) (Y := SplitSheaf.elementSheaf Q.family)
    (show SplitSheaf.elementSheaf (torsor J K F P).family ⟶
      SplitSheaf.elementSheaf (torsor J K F Q).family from
        ⟨Functor.whiskerLeft (opOpEquivalence _).functor h.iso.hom⟩)
  ext x p
  exact congrArg (fun f => f.hom.app (op (op x)) p) he

instance torsorFunctor_full : (torsorFunctor (G := G) (X := X) J K F).Full where
  map_surjective h := ⟨liftTorsorArrow J K F h, torsorFunctor_lift J K F h⟩

instance torsorFunctor_faithful : (torsorFunctor (G := G) (X := X) J K F).Faithful where
  map_injective {P Q} {f g} h := by
    apply SheafTorsor.Arrow.ext
    have hh : (elementEquivalence J K F X).inverse.map
        (show SplitSheaf.elementSheaf P.family ⟶ SplitSheaf.elementSheaf Q.family from
          ⟨Functor.whiskerLeft (opOpEquivalence _).functor f.iso.hom⟩) =
      (elementEquivalence J K F X).inverse.map
        (show SplitSheaf.elementSheaf P.family ⟶ SplitSheaf.elementSheaf Q.family from
          ⟨Functor.whiskerLeft (opOpEquivalence _).functor g.iso.hom⟩) := by
      exact congrArg (fun k =>
        (show SplitSheaf.elementSheaf (torsor J K F P).family ⟶
          SplitSheaf.elementSheaf (torsor J K F Q).family from
          ⟨Functor.whiskerLeft (opOpEquivalence _).functor k.iso.hom⟩)) h
    have hi := (elementEquivalence J K F X).inverse.map_injective hh
    ext x p
    exact congrArg (fun k => k.hom.app (op (op x)) p) hi

abbrev extendedSheaf (Q : SheafTorsor.Torsor (group J K F G) (sheaf J K F X)) :=
  (elementEquivalence J K F X).functor.obj (SplitSheaf.elementSheaf Q.family)

/-- Extend action and division through the proved dense comparison. -/
def extendedStructure (Q : SheafTorsor.Torsor (group J K F G) (sheaf J K F X)) :
    PrincipalSheaf.Structure (PrincipalSheafContext.group X G) (extendedSheaf J K F Q) :=
  PrincipalSheaf.extend (PrincipalSheaf.transport
    (PrincipalSheafContext.structureOf _ _ Q)
    ((elementEquivalence J K F X).unitIso.symm.app (SplitSheaf.elementSheaf Q.family)))

def extendTorsor (Q : SheafTorsor.Torsor (group J K F G) (sheaf J K F X)) :
    SheafTorsor.Torsor G X :=
  PrincipalSheafContext.torsor X G (extendedSheaf J K F Q) (extendedStructure J K F Q)

/-- The comparison recovers the independently supplied source-site torsor and action. -/
def torsorCounit (Q : SheafTorsor.Torsor (group J K F G) (sheaf J K F X)) :
    (torsorFunctor J K F).obj (extendTorsor J K F Q) ≅ Q := by
  let e := (elementEquivalence J K F X).unitIso.symm.app (SplitSheaf.elementSheaf Q.family)
  let A := PrincipalSheaf.transport (PrincipalSheafContext.structureOf _ _ Q) e
  have he : PrincipalSheaf.Equivariant A (PrincipalSheafContext.structureOf _ _ Q) e.hom := by
    intro x g p
    exact congrArg (fun k => k.hom.app x
      ((PrincipalSheafContext.structureOf _ _ Q).act x g (e.hom.hom.app x p))) e.inv_hom_id
  have hr := PrincipalSheaf.restrict_extend
    (J := ElementSite.topology (sheaf J K F X).obj J)
    (K := ElementSite.topology X.obj K) (F := ElementSite.comparison F X.obj)
    (G := PrincipalSheafContext.group X G) (Q := extendedSheaf J K F Q) A
  rw [← hr] at he
  exact SheafTorsor.Arrow.toIso
    { iso := Functor.isoWhiskerLeft (opOpEquivalence _).inverse
        ((sheafToPresheaf _ _).mapIso e)
      equivariant x g p := he (op (op x)) g p }

instance torsorFunctor_essSurj : (torsorFunctor (G := G) (X := X) J K F).EssSurj where
  mem_essImage Q := ⟨extendTorsor J K F Q, ⟨torsorCounit J K F Q⟩⟩
instance torsorFunctor_isEquivalence : (torsorFunctor (G := G) (X := X) J K F).IsEquivalence := {}

/-- Torsor comparison retains the category, including every equivariant arrow. -/
def torsorEquivalence : SheafTorsor.Torsor G X ≌
    SheafTorsor.Torsor (group J K F G) (sheaf J K F X) :=
  (torsorFunctor J K F).asEquivalence

omit [F.Full] [F.Faithful] [F.IsDenseSubsite J K] in
/-- Reindexing the parameter commutes strictly with forward site restriction. -/
theorem torsor_reindex (P : SheafTorsor.Torsor G X) (f : Y ⟶ X) :
    torsor J K F (SheafTorsor.reindex P f) =
      SheafTorsor.reindex (torsor J K F P) (map J K F f) := rfl

def torsorRestrictionComparison (f : Y ⟶ X) :
    SheafTorsor.restriction (G := G) f ⋙ torsorFunctor J K F ≅
      torsorFunctor J K F ⋙ SheafTorsor.restriction (map J K F f) := Iso.refl _

omit [F.Full] [F.Faithful] [F.IsDenseSubsite J K] in
/-- The two-step restriction uses the actual composite map under site restriction. -/
theorem torsor_reindex_comp (P : SheafTorsor.Torsor G X) (f : Y ⟶ X) (g : Z ⟶ Y) :
    torsor J K F (SheafTorsor.reindex (SheafTorsor.reindex P f) g) =
      SheafTorsor.reindex (torsor J K F P) (map J K F (g ≫ f)) := rfl

omit [F.Full] [F.Faithful] [F.IsDenseSubsite J K] in
theorem torsor_reindex_id (P : SheafTorsor.Torsor G X) :
    torsor J K F (SheafTorsor.reindex P (𝟙 X)) = torsor J K F P := rfl

omit [F.Full] [F.Faithful] [F.IsDenseSubsite J K] in
/-- Restriction recovers the regular object, so it detects global triviality. -/
theorem torsor_trivial : torsor J K F (SheafTorsor.trivial G X) =
    SheafTorsor.trivial (group J K F G) (sheaf J K F X) := rfl

end SquareKit.SheafSiteComparison

namespace SquareKit.SheafSiteComparison
open CategoryTheory Opposite
universe u
variable {C D : Type u} [Category.{u} C] [Category.{u} D]
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
variable [F.Full] [F.Faithful] [F.IsDenseSubsite J K]
variable {G : Sheaf K GrpCat.{u}} {X : Sheaf K (Type u)}

/-- Site restriction preserves the automorphism group of every torsor. -/
def torsorAutEquiv (P : SheafTorsor.Torsor G X) :
    Aut P ≃* Aut ((torsorFunctor J K F).obj P) :=
  (torsorEquivalence J K F).fullyFaithfulFunctor.autMulEquivOfFullyFaithful P

variable (U : D)

omit [F.Full] [F.Faithful] [F.IsDenseSubsite J K] in
/-- The general parameter structure specializes to the existing original-slice structure. -/
theorem contextStructure_eq (P : SheafTorsor.Torsor G (SheafifiedSliceTorsor.context K U)) :
    PrincipalSheafContext.structureOf _ G P = SheafifiedSliceTorsor.elementStructure K U P := rfl

/-- The original-slice recovery unit remains natural after site restriction. -/
def sliceTorsorRecovery :
    torsorFunctor (G := G) (X := SheafifiedSliceTorsor.context K U) J K F ≅
      ((SheafifiedSliceTorsor.equivalence K U).functor ⋙
        (SheafifiedSliceTorsor.equivalence K U).inverse) ⋙ torsorFunctor J K F :=
  Functor.isoWhiskerRight (SheafifiedSliceTorsor.equivalence K U).unitIso (torsorFunctor J K F)

omit [F.Full] [F.Faithful] in
theorem sliceTorsorRecovery_natural
    {P Q : SheafTorsor.Torsor G (SheafifiedSliceTorsor.context K U)} (h : P ⟶ Q) :
    (torsorFunctor J K F).map h ≫ (sliceTorsorRecovery J K F U).hom.app Q =
      (sliceTorsorRecovery J K F U).hom.app P ≫
        (torsorFunctor J K F).map (((SheafifiedSliceTorsor.equivalence K U).functor ⋙
          (SheafifiedSliceTorsor.equivalence K U).inverse).map h) :=
  (sliceTorsorRecovery J K F U).hom.naturality h

omit [F.Full] [F.Faithful] in
/-- Recovery retains the projection of the restricted total display. -/
theorem sliceTorsorRecovery_projection
    (P : SheafTorsor.Torsor G (SheafifiedSliceTorsor.context K U)) :
    SplitSheaf.totalMap ((sliceTorsorRecovery J K F U).hom.app P).iso.hom ≫
      SplitSheaf.p (torsor J K F (((SheafifiedSliceTorsor.equivalence K U).functor ⋙
        (SheafifiedSliceTorsor.equivalence K U).inverse).obj P)).family =
          SplitSheaf.p (torsor J K F P).family := rfl

end SquareKit.SheafSiteComparison
