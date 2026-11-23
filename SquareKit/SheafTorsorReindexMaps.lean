import SquareKit.SheafActionQuotient
import SquareKit.SplitSheafCategory

/-! Maps into reindexed sheaf families, their total-space observations,
and transport of torsor and quotient arrows along base isomorphisms. -/

noncomputable section

namespace SquareKit.SplitSheaf
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {X Y : Sheaf J (Type w)} {A : Ty Y} {B : Ty X}

/-- Factor a map over a base arrow through the reindexed family. -/
def mapAlong (f : Y ⟶ X) (k : Ext A ⟶ Ext B) (hk : k ≫ p B = p A ≫ f) :
    A.family ⟶ (tySub B f).family :=
  mapOfTotal ((extension_pullback B f).lift k (p A) hk)
    ((extension_pullback B f).lift_snd k (p A) hk)

theorem mapAlong_total (f : Y ⟶ X) (k : Ext A ⟶ Ext B) (hk : k ≫ p B = p A ≫ f) :
    totalMap (mapAlong f k hk) ≫ lift B f = k := by
  rw [mapAlong, totalMap_mapOfTotal]
  exact (extension_pullback B f).lift_fst k (p A) hk

theorem mapAlong_value (f : Y ⟶ X) (k : Ext A ⟶ Ext B) (hk : k ≫ p B = p A ≫ f)
    (x : Y.obj.Elements) (a : A.family.obj x) :
    (⟨f.hom.app x.obj x.val, (mapAlong f k hk).app x a⟩ : (Ext B).obj.obj x.obj) =
      k.hom.app x.obj ⟨x.val, a⟩ :=
  congrArg (fun h => h.hom.app x.obj ⟨x.val, a⟩) (mapAlong_total f k hk)

end SquareKit.SplitSheaf

namespace SquareKit.SplitSheaf
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {X Y Z W : Sheaf J (Type w)} {A : Ty Y} {B : Ty X}

theorem mapAlong_value_of_comp (f : Y ⟶ X) (k : Ext A ⟶ Ext B)
    (hk : k ≫ p B = p A ≫ f) (u : Ext A ⟶ W) (v : W ⟶ Z) (t : Ext B ⟶ Z)
    (he : k ≫ t = u ≫ v) (x : Y.obj.Elements) (a : A.family.obj x) :
    t.hom.app x.obj ⟨f.hom.app x.obj x.val, (mapAlong f k hk).app x a⟩ =
      v.hom.app x.obj (u.hom.app x.obj ⟨x.val, a⟩) := by
  rw [mapAlong_value]
  exact congrArg (fun h => h.hom.app x.obj ⟨x.val, a⟩) he

end SquareKit.SplitSheaf

namespace SquareKit.SplitSheaf
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {X Y : Sheaf J (Type w)} {A : Ty Y} {B D : Ty X}

/-- The induced isomorphism on total spaces of isomorphic families. -/
def totalIso {T : Sheaf J (Type w)} {A B : Ty T} (e : A.family ≅ B.family) : Ext A ≅ Ext B :=
  (toOver ⋙ Over.forget T).mapIso (isoMk e)

theorem reindex_map_ext (f : Y ⟶ X) (h k : A.family ⟶ (tySub B f).family)
    (he : totalMap h ≫ lift B f = totalMap k ≫ lift B f) : h = k := by
  apply totalMap_injective
  apply (extension_pullback B f).hom_ext he
  rw [totalMap_projection, totalMap_projection]

theorem totalMap_reindex_lift (h : B.family ⟶ D.family) (f : Y ⟶ X) :
    totalMap ((restriction f).map h) ≫ lift D f = lift B f ≫ totalMap h := rfl

end SquareKit.SplitSheaf

namespace SquareKit.SheafTorsor
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G : Sheaf J GrpCat.{w}} {X Y : Sheaf J (Type w)}
  (P : Torsor G X) {f g : Y ⟶ X}

/-- Explicit transport when two base arrows are propositionally equal. -/
def reindexCongr (he : f = g) : Arrow (reindex P f) (reindex P g) :=
  eqToHom (congrArg (reindex P) he)

theorem reindexCongr_lift (he : f = g) :
    SplitSheaf.totalMap (reindexCongr P he).iso.hom ≫ SplitSheaf.lift P.family g =
      SplitSheaf.lift P.family f := by
  subst g
  rfl

end SquareKit.SheafTorsor

namespace SquareKit.SheafActionQuotient
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G : Sheaf J GrpCat.{w}} {M X Y : Sheaf J (Type w)} {a : Action G M}
/-- Restriction along a base isomorphism retains all quotient objects and arrows. -/
def restrictionEquivalence (e : X ≅ Y) : Object a Y ≌ Object a X :=
  CategoryTheory.Equivalence.mk (restriction e.hom) (restriction e.inv)
    (eqToIso (by rw [restriction_comp, e.inv_hom_id]; rfl))
    (eqToIso (by rw [restriction_comp, e.hom_inv_id]; rfl))
end SquareKit.SheafActionQuotient

namespace SquareKit.SheafActionQuotient
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G : Sheaf J GrpCat.{w}} {M X Y : Sheaf J (Type w)} {a : Action G M}
  {P Q R : Object a X} {P' Q' R' : Object a Y}

def Arrow.reindexTransport (h : Arrow P Q) (f : Y ⟶ X)
    (hp : SheafActionQuotient.reindex P f = P') (hq : SheafActionQuotient.reindex Q f = Q') : Arrow P' Q' :=
  eqToHom hp.symm ≫ h.reindex f ≫ eqToHom hq

theorem Arrow.reindexTransport_ident (f : Y ⟶ X) (hp : SheafActionQuotient.reindex P f = P') :
    (Arrow.ident P).reindexTransport f hp hp = Arrow.ident P' := by
  subst P'
  rfl

theorem Arrow.reindexTransport_comp (h : Arrow P Q) (k : Arrow Q R) (f : Y ⟶ X)
    (hp : SheafActionQuotient.reindex P f = P') (hq : SheafActionQuotient.reindex Q f = Q') (hr : SheafActionQuotient.reindex R f = R') :
    (h.comp k).reindexTransport f hp hr =
      (h.reindexTransport f hp hq).comp (k.reindexTransport f hq hr) := by
  subst P'; subst Q'; subst R'
  apply Arrow.ext
  apply SheafTorsor.Arrow.ext
  ext x z
  rfl

theorem Arrow.reindexTransport_inverse (h : Arrow P Q) (f : Y ⟶ X)
    (hp : SheafActionQuotient.reindex P f = P') (hq : SheafActionQuotient.reindex Q f = Q') :
    h.inverse.reindexTransport f hq hp = (h.reindexTransport f hp hq).inverse := by
  subst P'; subst Q'
  apply Arrow.ext
  apply SheafTorsor.Arrow.ext
  ext x z
  rfl

end SquareKit.SheafActionQuotient

namespace SquareKit.SheafActionQuotient
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G : Sheaf J GrpCat.{w}} {M X Y : Sheaf J (Type w)} {a : Action G M}
  (P : Object a X) {f g : Y ⟶ X}

/-- Equality transport of quotient reindexing keeps the target data. -/
def reindexCongr (he : f = g) : Arrow (reindex P f) (reindex P g) :=
  eqToHom (congrArg (reindex P) he)

theorem reindexCongr_torsorArrow (he : f = g) :
    (reindexCongr P he).torsorArrow = SheafTorsor.reindexCongr P.torsor he := by
  subst g
  rfl

end SquareKit.SheafActionQuotient

namespace SquareKit.SheafTorsor
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G : Sheaf J GrpCat.{w}} {X Y Z : Sheaf J (Type w)}
/-- Typed equality transport for successive torsor restrictions. -/
def reindexCompositeCongr (P : Torsor G X) (f : Y ⟶ X) (g : Z ⟶ Y)
    (h : Z ⟶ X) (he : g ≫ f = h) : Arrow (reindex (reindex P f) g) (reindex P h) :=
  reindexCongr P he
theorem reindexCompositeCongr_lift (P : Torsor G X) (f : Y ⟶ X) (g : Z ⟶ Y)
    (h : Z ⟶ X) (he : g ≫ f = h) :
    SplitSheaf.totalMap (reindexCompositeCongr P f g h he).iso.hom ≫ SplitSheaf.lift P.family h =
      SplitSheaf.lift (reindex P f).family g ≫ SplitSheaf.lift P.family f :=
  reindexCongr_lift P he

/-- Observe a composite of restriction arrows on its original total space. -/
theorem reindexCompositeCongr_comp_total (P : Torsor G X) (Q : Torsor G Y) (R : Torsor G Z)
    (f : Y ⟶ X) (g : Z ⟶ Y) (h : Z ⟶ X) (he : g ≫ f = h)
    (a : Arrow R (reindex Q g)) (b : Arrow Q (reindex P f)) :
    SplitSheaf.totalMap ((a.comp (b.reindex g)).comp
      (reindexCompositeCongr P f g h he)).iso.hom ≫ SplitSheaf.lift P.family h =
    SplitSheaf.totalMap a.iso.hom ≫ SplitSheaf.lift Q.family g ≫
      SplitSheaf.totalMap b.iso.hom ≫ SplitSheaf.lift P.family f := by
  subst h
  rfl

end SquareKit.SheafTorsor

namespace SquareKit.SheafActionQuotient
open CategoryTheory
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G : Sheaf J GrpCat.{w}} {M X Y Z : Sheaf J (Type w)} {a : Action G M}

/-- Transport successive quotient restrictions along an equality of base maps. -/
def reindexCompositeCongr (P : Object a X) (f : Y ⟶ X) (g : Z ⟶ Y)
    (h : Z ⟶ X) (he : g ≫ f = h) : Arrow (reindex (reindex P f) g) (reindex P h) :=
  reindexCongr P he

theorem reindexCompositeCongr_torsorArrow (P : Object a X) (f : Y ⟶ X) (g : Z ⟶ Y)
    (h : Z ⟶ X) (he : g ≫ f = h) :
    (reindexCompositeCongr P f g h he).torsorArrow =
      SheafTorsor.reindexCompositeCongr P.torsor f g h he := by
  subst h
  rfl

end SquareKit.SheafActionQuotient
