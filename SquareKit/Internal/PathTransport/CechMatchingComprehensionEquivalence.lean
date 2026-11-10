import SquareKit.Internal.PathTransport.CechMatchingComprehensionAction

/-! Independent total matching data are the Grothendieck total of the explicit
relative matching family. No evaluation or descent effectiveness is assumed. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension
open CategoryTheory
open SquareKit.Internal.PathTransport.GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {D : StrictDiagram.{u,u}} (A : FamilyData D) (h : A.Coherence)

abbrev Total := Extend (family A h)

def totalMap {x y : Total A h} (f : x ⟶ y) : x.fiber.datum ⟶ y.fiber.datum :=
  Fiber.lift f.base x.fiber ≫ f.fiber.matchingArrow

@[simp] theorem totalMap_base {x y : Total A h} (f : x ⟶ y) :
    (totalMap A h f).localArrow.base = f.base.localArrow := by
  change (Fiber.lift f.base x.fiber).localArrow.base ≫ f.fiber.matchingArrow.localArrow.base = _
  rw [Fiber.lift_base, f.fiber.vertical]
  exact Category.comp_id _

def totalFunctor : Total A h ⥤ Datum (A.total h).toDiagram where
  obj x := x.fiber.datum
  map := totalMap A h
  map_id x := by
    change Fiber.lift (𝟙 x.base) x.fiber ≫
      (eqToHom (show Fiber.transport (𝟙 x.base) x.fiber = x.fiber from
        Fiber.transport_id x.fiber)).matchingArrow = 𝟙 _
    rw [Fiber.lift_id, Fiber.matchingArrow_eqToHom]
    simp
  map_comp {x y z} f g := by
    change Fiber.lift (f.base ≫ g.base) x.fiber ≫
      ((eqToHom (show Fiber.transport (f.base ≫ g.base) x.fiber =
        Fiber.transport g.base (Fiber.transport f.base x.fiber) from
        Fiber.transport_comp f.base g.base x.fiber)).matchingArrow ≫
        (Fiber.transportMap g.base f.fiber).matchingArrow ≫ g.fiber.matchingArrow) =
      (Fiber.lift f.base x.fiber ≫ f.fiber.matchingArrow) ≫
        (Fiber.lift g.base y.fiber ≫ g.fiber.matchingArrow)
    rw [Fiber.matchingArrow_eqToHom, ← Category.assoc, Fiber.lift_comp]
    dsimp only [Fiber.transportMap]
    change (Fiber.lift f.base x.fiber ≫ Fiber.lift g.base (Fiber.transport f.base x.fiber)) ≫
      (inv (Fiber.lift g.base (Fiber.transport f.base x.fiber)) ≫
        f.fiber.matchingArrow ≫ Fiber.lift g.base y.fiber) ≫ g.fiber.matchingArrow = _
    simp

/-- The base projection recovers every supplied local base arrow. -/
def projectionComparison : totalFunctor A h ⋙ (A.projection h).functor ≅
    Grothendieck.forget (family A h ⋙ Grpd.forgetToCat) :=
  NatIso.ofComponents (fun x => eqToIso (Fiber.projection_datum x.fiber)) (by
    intro x y f
    apply Datum.Hom.ext
    simp only [Functor.comp_map, eqToIso.hom, Datum.comp_localArrow,
      Datum.eqToHom_localArrow, eqToHom_refl]
    change (totalMap A h f).localArrow.base ≫ 𝟙 _ = 𝟙 _ ≫ f.base.localArrow
    rw [totalMap_base]
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-- Recover the base matching arrow from its total local arrow. -/
def baseArrow {x y : Total A h} (f : x.fiber.datum ⟶ y.fiber.datum) : x.base ⟶ y.base :=
  eqToHom (Fiber.projection_datum x.fiber).symm ≫ (A.projection h).functor.map f ≫
    eqToHom (Fiber.projection_datum y.fiber)

@[simp] theorem baseArrow_local {x y : Total A h} (f : x.fiber.datum ⟶ y.fiber.datum) :
    (baseArrow A h f).localArrow = f.localArrow.base := by
  simp only [baseArrow, Datum.comp_localArrow, Datum.eqToHom_localArrow, eqToHom_refl]
  change 𝟙 _ ≫ f.localArrow.base ≫ 𝟙 _ = _
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The residual arrow is vertical after removing the canonical base lift. -/
def residual {x y : Total A h} (f : x.fiber.datum ⟶ y.fiber.datum) :
    Fiber.transport (baseArrow A h f) x.fiber ⟶ y.fiber where
  matchingArrow := inv (Fiber.lift (baseArrow A h f) x.fiber) ≫ f
  vertical := by
    change (Datum.localFunctor ⋙ Grothendieck.forget
      (A.localFamily ⋙ Grpd.forgetToCat)).map
      (inv (Fiber.lift (baseArrow A h f) x.fiber) ≫ f) = _
    simp only [Functor.map_comp, Functor.map_inv]
    change inv (Fiber.lift (baseArrow A h f) x.fiber).localArrow.base ≫ f.localArrow.base = _
    rw [Fiber.lift_base, baseArrow_local]
    exact IsIso.inv_hom_id _

def recoverArrow {x y : Total A h} (f : x.fiber.datum ⟶ y.fiber.datum) : x ⟶ y :=
  ⟨baseArrow A h f, residual A h f⟩

@[simp] theorem totalMap_recoverArrow {x y : Total A h} (f : x.fiber.datum ⟶ y.fiber.datum) :
    totalMap A h (recoverArrow A h f) = f := by
  change Fiber.lift (baseArrow A h f) x.fiber ≫
    inv (Fiber.lift (baseArrow A h f) x.fiber) ≫ f = f
  simp

instance : (totalFunctor A h).Full where
  map_surjective f := ⟨recoverArrow A h f, totalMap_recoverArrow A h f⟩

instance : (totalFunctor A h).Faithful where
  map_injective {x y} {f g} he := by
    have hb : f.base = g.base := by
      apply Datum.Hom.ext
      have hl := congrArg (fun a => a.localArrow.base) he
      exact (totalMap_base A h f).symm.trans (hl.trans (totalMap_base A h g))
    cases f with
    | mk fb ff =>
      cases g with
      | mk gb gf =>
        dsimp only at hb
        subst gb
        have hf : ff = gf := by
          apply Fiber.Hom.ext
          exact (cancel_epi (Fiber.lift fb x.fiber)).1 he
        subst gf
        rfl

instance : (totalFunctor A h).EssSurj where
  mem_essImage e := ⟨⟨(A.projection h).mapDatum e, Fiber.ofDatum e rfl⟩,
    ⟨eqToIso (Fiber.datum_ofDatum e rfl)⟩⟩

instance : (totalFunctor A h).IsEquivalence where

/-- Every independent total datum decomposes into a base datum and explicit
relative matching data, preserving all matching arrows. -/
def equivalence : Total A h ≌ Datum (A.total h).toDiagram := (totalFunctor A h).asEquivalence

@[simp] theorem equivalence_localArrow {x y : Total A h} (f : x ⟶ y) :
    ((equivalence A h).functor.map f).localArrow =
      (Fiber.lift f.base x.fiber).localArrow ≫ f.fiber.matchingArrow.localArrow := rfl

end SquareKit.Internal.PathTransport.CechMatching.Comprehension
