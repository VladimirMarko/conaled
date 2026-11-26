import SquareKit.SheafTorsor
import Mathlib.CategoryTheory.Sites.Canonical
import SquareKit.RepresentableElementSite

/-! Principal sheaves on the ordinary slice site and represented-context torsors. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafSliceTorsor
open CategoryTheory Opposite
universe u
variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C) (U : C)

/-- The shared slice/element-site comparison, oriented from the ordinary slice. -/
abbrev toElements := RepresentableElementSite.overElement U
abbrev fromElements := RepresentableElementSite.elementOver U
abbrev siteEquivalence := (RepresentableElementSite.elementOverEquivalence U).symm

instance toElements_cocontinuous :
    (toElements U).IsCocontinuous (J.over U) (ElementSite.topology (yoneda.obj U) J) :=
  inferInstanceAs ((RepresentableElementSite.overElement U).IsCocontinuous _ _)

instance fromElements_cocontinuous :
    (fromElements U).IsCocontinuous (ElementSite.topology (yoneda.obj U) J) (J.over U) :=
  inferInstanceAs ((RepresentableElementSite.elementOver U).IsCocontinuous _ _)

/-- The group sheaf is restricted along the ordinary forgetful slice functor. -/
abbrev restrictedGroup (G : Sheaf J GrpCat.{u}) : Sheaf (J.over U) GrpCat.{u} :=
  (J.overPullback GrpCat.{u} U).obj G

/-- Sections locally inhabit the sheaf; no global section is chosen. -/
def inhabitedSieve (Q : Sheaf (J.over U) (Type u)) (X : Over U) : Sieve X where
  arrows {Y} _ := Nonempty (Q.obj.obj (op Y))
  downward_closed := by
    rintro Y Z f ⟨s⟩ g
    exact ⟨Q.obj.map g.op s⟩

/-- An independently specified principal sheaf on the slice site. -/
structure Torsor (G : Sheaf J GrpCat.{u}) where
  sheaf : Sheaf (J.over U) (Type u)
  act (X : (Over U)ᵒᵖ) : (restrictedGroup J U G).obj.obj X → sheaf.obj.obj X → sheaf.obj.obj X
  one_act (X) (p : sheaf.obj.obj X) : act X 1 p = p
  mul_act (X) (g h : (restrictedGroup J U G).obj.obj X) (p) :
    act X (g * h) p = act X g (act X h p)
  natural {X Y} (f : X ⟶ Y) (g) (p) :
    sheaf.obj.map f (act X g p) = act Y ((restrictedGroup J U G).obj.map f g) (sheaf.obj.map f p)
  principal (X) (p q : sheaf.obj.obj X) : ∃! g, act X g p = q
  locallyInhabited (X : Over U) : inhabitedSieve J U sheaf X ∈ (J.over U) X

variable {J U} {G : Sheaf J GrpCat.{u}}

/-- Every arrow retains its actual natural isomorphism and equivariance. -/
structure Arrow (P Q : Torsor J U G) where
  iso : P.sheaf ≅ Q.sheaf
  equivariant (X) (g) (p) : iso.hom.hom.app X (P.act X g p) = Q.act X g (iso.hom.hom.app X p)

@[ext] theorem Arrow.ext {P Q : Torsor J U G} (f g : Arrow P Q)
    (h : f.iso.hom = g.iso.hom) : f = g := by
  cases f; cases g; congr 1; exact Iso.ext h

instance : Category (Torsor J U G) where
  Hom := Arrow
  id P := ⟨Iso.refl _, fun _ _ _ => rfl⟩
  comp f g := ⟨f.iso ≪≫ g.iso, fun X h p => by
    change g.iso.hom.hom.app X (f.iso.hom.hom.app X _) = _
    rw [f.equivariant, g.equivariant]; rfl⟩
  id_comp f := by apply Arrow.ext; exact Category.id_comp _
  comp_id f := by apply Arrow.ext; exact Category.comp_id _
  assoc f g h := by apply Arrow.ext; exact Category.assoc _ _ _

def Arrow.inverse {P Q : Torsor J U G} (h : Arrow P Q) : Arrow Q P where
  iso := h.iso.symm
  equivariant X g q := by
    have hinj : Function.Injective (h.iso.hom.hom.app X) := by
      intro x y he
      have hx := congrArg (fun k : P.sheaf ⟶ P.sheaf => k.hom.app X x) h.iso.hom_inv_id
      have hy := congrArg (fun k : P.sheaf ⟶ P.sheaf => k.hom.app X y) h.iso.hom_inv_id
      exact hx.symm.trans ((congrArg (h.iso.inv.hom.app X) he).trans hy)
    apply hinj
    have hq (z : Q.sheaf.obj.obj X) : h.iso.hom.hom.app X (h.iso.inv.hom.app X z) = z :=
      congrArg (fun k : Q.sheaf ⟶ Q.sheaf => k.hom.app X z) h.iso.inv_hom_id
    change h.iso.hom.hom.app X (h.iso.inv.hom.app X (Q.act X g q)) = _
    rw [hq, h.equivariant]
    exact congrArg (Q.act X g) (hq q).symm

def Arrow.toIso {P Q : Torsor J U G} (h : Arrow P Q) : P ≅ Q where
  hom := h
  inv := h.inverse
  hom_inv_id := by apply Arrow.ext; exact h.iso.hom_inv_id
  inv_hom_id := by apply Arrow.ext; exact h.iso.inv_hom_id

/-- An equivariant natural map, without a supplied inverse. -/
structure EquivariantMap (P Q : Torsor J U G) where
  hom : P.sheaf ⟶ Q.sheaf
  equivariant (X) (g) (p) : hom.hom.app X (P.act X g p) = Q.act X g (hom.hom.app X p)

variable (J U) [J.Subcanonical]

instance : (toElements U).IsContinuous (J.over U) (ElementSite.topology ((J.yoneda).obj U).obj J) := by
  change (toElements U).IsContinuous (J.over U) (ElementSite.topology (yoneda.obj U) J)
  infer_instance

instance : (fromElements U).IsContinuous (ElementSite.topology ((J.yoneda).obj U).obj J) (J.over U) := by
  change (fromElements U).IsContinuous (ElementSite.topology (yoneda.obj U) J) (J.over U)
  infer_instance

/-- Restriction to an ordinary slice arrow reads the corresponding represented fiber. -/
def forwardSheaf (P : SheafTorsor.Torsor G ((J.yoneda).obj U)) :
    Sheaf (J.over U) (Type u) :=
  ⟨(toElements U).op ⋙ (SplitSheaf.elementSheaf P.family).obj,
    (toElements U).op_comp_isSheaf _ _ (SplitSheaf.elementSheaf P.family)⟩

/-- The sheaf-context torsor induces an independently specified principal slice sheaf. -/
def forwardObject (P : SheafTorsor.Torsor G ((J.yoneda).obj U)) : Torsor J U G where
  sheaf := forwardSheaf J U P
  act X := P.act ((yoneda.obj U).elementsMk (op X.unop.left) X.unop.hom)
  one_act _X := P.one_act _
  mul_act X g h p := P.mul_act ((yoneda.obj U).elementsMk (op X.unop.left) X.unop.hom) g h p
  natural f g p := P.natural ((toElements U).map f.unop).unop g p
  principal _X := P.principal _
  locallyInhabited X := by
    change Sieve.overEquiv X (inhabitedSieve J U (forwardSheaf J U P) X) ∈ J X.left
    apply J.superset_covering _ (Presheaf.imageSieve_mem J (SplitSheaf.p P.family).hom (U := op X.left) X.hom)
    intro V f hf
    rw [Sieve.overEquiv_iff]
    obtain ⟨⟨x,p⟩,hp⟩ := hf
    change x = f ≫ X.hom at hp
    subst x
    exact ⟨p⟩

/-- A slice sheaf supplies the family over each represented section. -/
def backwardFamily (Q : Sheaf (J.over U) (Type u)) : SplitSheaf.Ty ((J.yoneda).obj U) where
  family := ElementSheaf.family (yoneda.obj U) ((fromElements U).op ⋙ Q.obj)
  isSheaf := (isSheaf_iff_isSheaf_of_type _ _).2
    (ElementSheaf.total_isSheaf _
      ((isSheaf_iff_isSheaf_of_type _ _).1 ((J.yoneda).obj U).property) _
      ((fromElements U).op_comp_isSheaf_of_types _ _ Q))

/-- Assemble the original display, principal action and local existence from the slice sheaf. -/
def backwardObject (Q : Torsor J U G) : SheafTorsor.Torsor G ((J.yoneda).obj U) where
  family := backwardFamily J U Q.sheaf
  act x := Q.act (op (Over.mk x.val))
  one_act x := Q.one_act _
  mul_act x g h p := Q.mul_act (op (Over.mk x.val)) g h p
  natural f g p := Q.natural ((fromElements U).map f.op).op g p
  principal x := Q.principal _
  locallySurjective := ⟨by
    intro V x
    apply J.superset_covering _ (Q.locallyInhabited (Over.mk x))
    intro W f hf
    rw [Sieve.overEquiv_iff] at hf
    obtain ⟨p⟩ := hf
    exact ⟨⟨f ≫ x,p⟩,rfl⟩⟩

def forward : SheafTorsor.Torsor G ((J.yoneda).obj U) ⥤ Torsor J U G where
  obj := forwardObject J U
  map h :=
    { iso := ObjectProperty.isoMk _
        (Functor.isoWhiskerLeft ((toElements U).op ⋙ (opOpEquivalence _).functor) h.iso)
      equivariant X := h.equivariant ((yoneda.obj U).elementsMk (op X.unop.left) X.unop.hom) }
  map_id P := by apply Arrow.ext; rfl
  map_comp f g := by apply Arrow.ext; rfl

def backward : Torsor J U G ⥤ SheafTorsor.Torsor G ((J.yoneda).obj U) where
  obj := backwardObject J U
  map h :=
    { iso := Functor.isoWhiskerLeft ((opOpEquivalence _).inverse ⋙ (fromElements U).op)
        ((sheafToPresheaf _ _).mapIso h.iso)
      equivariant x := h.equivariant (op (Over.mk x.val)) }
  map_id P := by apply SheafTorsor.Arrow.ext; rfl
  map_comp f g := by apply SheafTorsor.Arrow.ext; rfl

/-- Recovery retains each fiber and its action, rather than only its isomorphism class. -/
def unitComponent (P : SheafTorsor.Torsor G ((J.yoneda).obj U)) :
    P ≅ (forward J U ⋙ backward J U).obj P :=
  SheafTorsor.Arrow.toIso
    { iso := NatIso.ofComponents (fun _ => Iso.refl _) (by intro x y f; rfl)
      equivariant _ _ _ := rfl }

def counitComponent (Q : Torsor J U G) :
    (backward J U ⋙ forward J U).obj Q ≅ Q where
  hom :=
    { iso := ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ => Iso.refl _)
        (by intro x y f; rfl))
      equivariant _ _ _ := rfl }
  inv :=
    { iso := ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ => Iso.refl _)
        (by intro x y f; rfl))
      equivariant _ _ _ := rfl }
  hom_inv_id := by apply Arrow.ext; rfl
  inv_hom_id := by apply Arrow.ext; rfl

/-- The represented-context category and independently defined slice torsors agree on all maps. -/
def equivalence : SheafTorsor.Torsor G ((J.yoneda).obj U) ≌ Torsor J U G :=
  CategoryTheory.Equivalence.mk (forward J U) (backward J U)
    (NatIso.ofComponents (unitComponent J U) (by intro P Q h; apply SheafTorsor.Arrow.ext; rfl))
    (NatIso.ofComponents (counitComponent J U) (by intro P Q h; apply Arrow.ext; rfl))

/-- Reconstruction is an isomorphism over the original represented base. -/
def displayComparison (P : SheafTorsor.Torsor G ((J.yoneda).obj U)) :
    SplitSheaf.extension P.family ≅ SplitSheaf.extension ((backward J U).obj ((forward J U).obj P)).family :=
  ObjectProperty.isoMk _ (ElementFamilies.totalFunctor _ |>.mapIso (unitComponent J U P).hom.iso |>
    (Over.forget _).mapIso)

@[simp] theorem displayComparison_projection
    (P : SheafTorsor.Torsor G ((J.yoneda).obj U)) :
    (displayComparison J U P).hom ≫
      SplitSheaf.p ((backward J U).obj ((forward J U).obj P)).family = SplitSheaf.p P.family := rfl

/-- The forward comparison computes the action of the restricted group section. -/
@[simp] theorem forward_action (P : SheafTorsor.Torsor G ((J.yoneda).obj U))
    (X : Over U) (g) (p) :
    (forwardObject J U P).act (op X) g p =
      P.act ((yoneda.obj U).elementsMk (op X.left) X.hom) g p := rfl

variable {U} {V W : C}

/-- Restriction is ordinary precomposition on the slice site, including arrows. -/
def restrictObject (f : V ⟶ U) (P : Torsor J U G) : Torsor J V G where
  sheaf := ⟨(Over.map f).op ⋙ P.sheaf.obj, (Over.map f).op_comp_isSheaf _ _ P.sheaf⟩
  act X := P.act (op ((Over.map f).obj X.unop))
  one_act _X := P.one_act _
  mul_act X g h p := P.mul_act (op ((Over.map f).obj X.unop)) g h p
  natural k g p := P.natural ((Over.map f).map k.unop).op g p
  principal _X := P.principal _
  locallyInhabited X := (Over.map f).cover_lift (J.over V) (J.over U)
    (P.locallyInhabited ((Over.map f).obj X))

def restriction (f : V ⟶ U) : Torsor J U G ⥤ Torsor J V G where
  obj := restrictObject J f
  map h :=
    { iso := ObjectProperty.isoMk _
        (Functor.isoWhiskerLeft (Over.map f).op ((sheafToPresheaf _ _).mapIso h.iso))
      equivariant X := h.equivariant (op ((Over.map f).obj X.unop)) }
  map_id P := by apply Arrow.ext; rfl
  map_comp h k := by apply Arrow.ext; rfl

/-- The independently defined slice restriction computes the existing represented pullback. -/
def restrictionComparison (f : V ⟶ U) :
    SheafTorsor.restriction (G := G) (J.yoneda.map f) ⋙ forward J V ≅
      forward J U ⋙ restriction J f :=
  NatIso.ofComponents (fun P =>
    { hom := ⟨ObjectProperty.isoMk _ (Iso.refl _), fun _ _ _ => rfl⟩
      inv := ⟨ObjectProperty.isoMk _ (Iso.refl _), fun _ _ _ => rfl⟩
      hom_inv_id := by apply Arrow.ext; rfl
      inv_hom_id := by apply Arrow.ext; rfl })
    (by intro P Q h; apply Arrow.ext; rfl)

/-- Identity coherence for the independently defined ordinary-slice restriction. -/
def restrictionIdComponent (P : Torsor J U G) : (restriction J (𝟙 U)).obj P ≅ P :=
  Arrow.toIso
    { iso := ObjectProperty.isoMk _
        (Functor.isoWhiskerRight (NatIso.op (Over.mapId U)).symm P.sheaf.obj ≪≫ Functor.leftUnitor _)
      equivariant X g p := by
        have h := P.natural ((Over.mapId U).inv.app X.unop).op g p
        have hg : (restrictedGroup J U G).obj.map ((Over.mapId U).inv.app X.unop).op g = g := by
          change G.obj.map (𝟙 _) g = g
          rw [G.obj.map_id]
          rfl
        rw [hg] at h
        exact h }

/-- Composite restriction compares the actual slice sheaves and all action maps. -/
def restrictionCompComponent (f : V ⟶ U) (g : W ⟶ V) (P : Torsor J U G) :
    (restriction J (g ≫ f)).obj P ≅ (restriction J g).obj ((restriction J f).obj P) :=
  Arrow.toIso
    { iso := ObjectProperty.isoMk _
        (Functor.isoWhiskerRight (NatIso.op (Over.mapComp g f)).symm P.sheaf.obj)
      equivariant X h p := by
        have hh := P.natural ((Over.mapComp g f).inv.app X.unop).op h p
        have hg : (restrictedGroup J U G).obj.map ((Over.mapComp g f).inv.app X.unop).op h = h := by
          change G.obj.map (𝟙 _) h = h
          rw [G.obj.map_id]
          rfl
        rw [hg] at hh
        exact hh }

def restrictionId : restriction (G := G) J (𝟙 U) ≅ 𝟭 (Torsor J U G) :=
  NatIso.ofComponents (restrictionIdComponent J) (by
    intro P Q h
    apply Arrow.ext
    ext X p
    exact (NatTrans.naturality_apply h.iso.hom.hom ((Over.mapId U).inv.app X.unop).op p).symm)

def restrictionComp (f : V ⟶ U) (g : W ⟶ V) :
    restriction (G := G) J (g ≫ f) ≅ restriction J f ⋙ restriction J g :=
  NatIso.ofComponents (restrictionCompComponent J f g) (by
    intro P Q h
    apply Arrow.ext
    ext X p
    exact (NatTrans.naturality_apply h.iso.hom.hom ((Over.mapComp g f).inv.app X.unop).op p).symm)

/-- The represented comparison constructs an inverse for every equivariant
slice map, using local existence and principality of the reconstructed torsors. -/
def EquivariantMap.toArrow {P Q : Torsor J U G} (f : EquivariantMap P Q) : Arrow P Q :=
  (counitComponent J U P).inv ≫
    (forward J U).map ((show SheafTorsor.EquivariantMap (backwardObject J U P)
      (backwardObject J U Q) from
        { hom := Functor.whiskerLeft ((opOpEquivalence _).inverse ⋙ (fromElements U).op) f.hom.hom
          equivariant x := f.equivariant (op (Over.mk x.val)) }).toArrow) ≫
    (counitComponent J U Q).hom

@[simp] theorem EquivariantMap.toArrow_hom {P Q : Torsor J U G} (f : EquivariantMap P Q) :
    (f.toArrow J).iso.hom = f.hom := rfl

/-- The groupoid contains every equivariant natural map on the independent slice sheaves. -/
def equivariantArrowEquiv {P Q : Torsor J U G} : EquivariantMap P Q ≃ Arrow P Q where
  toFun := EquivariantMap.toArrow J
  invFun f := ⟨f.iso.hom, f.equivariant⟩
  left_inv f := by cases f; rfl
  right_inv f := by apply Arrow.ext; rfl

end SquareKit.SheafSliceTorsor
