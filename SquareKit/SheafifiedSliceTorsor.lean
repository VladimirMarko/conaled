import SquareKit.SheafifiedYoneda
import SquareKit.SheafSliceTorsor
import SquareKit.ElementSiteLocalEquivalence
import SquareKit.PrincipalSheafLocalEquivalence

/-! Independent slice torsors and torsors over sheafified representables on arbitrary sites. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafifiedSliceTorsor
open CategoryTheory Opposite
universe u
variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C) (U : C)

abbrev context := (SheafifiedYoneda.functor J).obj U
abbrev rawTopology := ElementSite.topology (yoneda.obj U) J
abbrev elementTopology := ElementSite.topology (context J U).obj J
abbrev unitSite := ElementSite.mapSite (toSheafify J (yoneda.obj U))

abbrev rawSheafEquivalence : Sheaf (rawTopology J U) (Type u) ≌ Sheaf (J.over U) (Type u) :=
  (RepresentableElementSite.elementOverEquivalence U).sheafCongr _ _ (Type u)
abbrev unitSheafEquivalence :
    Sheaf (rawTopology J U) (Type u) ≌ Sheaf (elementTopology J U) (Type u) :=
  ElementSite.sheafificationEquivalence J (yoneda.obj U)

/-- Restriction uses the sheafification unit at each ordinary arrow into U. -/
abbrev sheafEquivalence :
    Sheaf (elementTopology J U) (Type u) ≌ Sheaf (J.over U) (Type u) :=
  (unitSheafEquivalence J U).symm.trans (rawSheafEquivalence J U)

abbrev elementGroup (G : Sheaf J GrpCat.{u}) : Sheaf (elementTopology J U) GrpCat.{u} :=
  ((ElementSite.projection (context J U).obj).sheafPushforwardContinuous GrpCat.{u}
    (elementTopology J U) J).obj G

variable {G : Sheaf J GrpCat.{u}}

/-- A split torsor gives the same principal action on its element-site sheaf. -/
def elementStructure (P : SheafTorsor.Torsor G (context J U)) :
    PrincipalSheaf.Structure (elementGroup J U G) (SplitSheaf.elementSheaf P.family) where
  act X := P.act X.unop.unop
  one_act _ := P.one_act _
  mul_act X g h p := P.mul_act _ g h p
  natural f := P.natural f.unop.unop
  principal _ := P.principal _
  locally_inhabited X := by
    apply J.superset_covering ?_
      (Presheaf.imageSieve_mem J (SplitSheaf.p P.family).hom X.unop.val)
    rintro V f ⟨⟨x,p⟩, hp⟩
    exact ⟨x, hp.symm, ⟨p⟩⟩

abbrev forwardSheaf (P : SheafTorsor.Torsor G (context J U)) :=
  (sheafEquivalence J U).functor.obj (SplitSheaf.elementSheaf P.family)

def forwardObject (P : SheafTorsor.Torsor G (context J U)) : SheafSliceTorsor.Torsor J U G where
  sheaf := forwardSheaf J U P
  act X := P.act ((context J U).obj.elementsMk (op X.unop.left)
    ((toSheafify J (yoneda.obj U)).app (op X.unop.left) X.unop.hom))
  one_act _ := P.one_act _
  mul_act X g h p := P.mul_act ((context J U).obj.elementsMk (op X.unop.left)
    ((toSheafify J (yoneda.obj U)).app (op X.unop.left) X.unop.hom)) g h p
  natural f := P.natural (((unitSite J U).map
    ((RepresentableElementSite.overElement U).map f.unop)).unop)
  principal _ := P.principal _
  locally_inhabited X :=
    (RepresentableElementSite.overElement U).cover_lift (J.over U) (rawTopology J U)
      ((PrincipalSheaf.restrict (rawTopology J U) (elementTopology J U) (unitSite J U)
        (elementStructure J U P)).locally_inhabited
          ((RepresentableElementSite.overElement U).obj X))

def forward : SheafTorsor.Torsor G (context J U) ⥤ SheafSliceTorsor.Torsor J U G where
  obj := forwardObject J U
  map h :=
    { iso := (sheafEquivalence J U).functor.mapIso (ObjectProperty.isoMk _
        (Functor.isoWhiskerLeft (opOpEquivalence _).functor h.iso))
      equivariant X := h.equivariant ((context J U).obj.elementsMk (op X.unop.left)
        ((toSheafify J (yoneda.obj U)).app (op X.unop.left) X.unop.hom)) }
  map_id _ := by apply SheafSliceTorsor.Arrow.ext; rfl
  map_comp _ _ := by apply SheafSliceTorsor.Arrow.ext; rfl

abbrev rawSheaf (Q : SheafSliceTorsor.Torsor J U G) :=
  (rawSheafEquivalence J U).inverse.obj Q.sheaf

def rawStructure (Q : SheafSliceTorsor.Torsor J U G) :
    PrincipalSheaf.Structure
      (PrincipalSheaf.restrictGroup (rawTopology J U) (elementTopology J U) (unitSite J U)
        (elementGroup J U G)) (rawSheaf J U Q) where
  act X := Q.act (op (Over.mk X.unop.unop.val))
  one_act _ := Q.one_act _
  mul_act X g h p := Q.mul_act (op (Over.mk X.unop.unop.val)) g h p
  natural f := Q.natural (((RepresentableElementSite.elementOver U).map f.unop).op)
  principal _ := Q.principal _
  locally_inhabited X := (RepresentableElementSite.elementOver U).cover_lift
    (rawTopology J U) (J.over U) (Q.locally_inhabited
      ((RepresentableElementSite.elementOver U).obj X))

abbrev extensionSheaf (Q : SheafSliceTorsor.Torsor J U G) :=
  (unitSheafEquivalence J U).functor.obj (rawSheaf J U Q)

def extensionStructure (Q : SheafSliceTorsor.Torsor J U G) :
    PrincipalSheaf.Structure (elementGroup J U G) (extensionSheaf J U Q) :=
  PrincipalSheaf.extend (PrincipalSheaf.transport (rawStructure J U Q)
    ((unitSheafEquivalence J U).unitIso.symm.app (rawSheaf J U Q)))

def backwardFamily (Q : SheafSliceTorsor.Torsor J U G) : SplitSheaf.Ty (context J U) where
  family := ElementSheaf.family (context J U).obj (extensionSheaf J U Q).obj
  isSheaf := (SheafSlice.totalSheaf (context J U) (extensionSheaf J U Q)).property

def backwardObject (Q : SheafSliceTorsor.Torsor J U G) : SheafTorsor.Torsor G (context J U) where
  family := backwardFamily J U Q
  act x := (extensionStructure J U Q).act (op (op x))
  one_act _ := (extensionStructure J U Q).one_act _
  mul_act x g h p := (extensionStructure J U Q).mul_act (op (op x)) g h p
  natural f := (extensionStructure J U Q).natural f.op.op
  principal _ := (extensionStructure J U Q).principal _
  isLocallySurjective := ⟨by
    intro V x
    apply J.superset_covering ?_ ((extensionStructure J U Q).locally_inhabited
      (ElementSite.point (context J U).obj V x))
    rintro W f ⟨y, hy, ⟨p⟩⟩
    exact ⟨⟨y,p⟩, hy.symm⟩⟩

/-- Dense restriction detects equivariance on the whole element-site sheaf. -/
theorem equivariant_of_forward {P Q : SheafTorsor.Torsor G (context J U)}
    (f : SplitSheaf.elementSheaf P.family ⟶ SplitSheaf.elementSheaf Q.family)
    (h : ∀ X g p, ((sheafEquivalence J U).functor.map f).hom.app X
      ((forwardObject J U P).act X g p) = (forwardObject J U Q).act X g
        (((sheafEquivalence J U).functor.map f).hom.app X p)) :
    PrincipalSheaf.Equivariant (elementStructure J U P) (elementStructure J U Q) f := by
  apply (PrincipalSheaf.equivariant_iff (rawTopology J U) (elementTopology J U)
    (unitSite J U) (elementStructure J U P) (elementStructure J U Q) f).mpr
  intro X g p
  exact h (op (Over.mk X.unop.unop.val)) g p

def liftArrow {P Q : SheafTorsor.Torsor G (context J U)}
    (h : (forward J U).obj P ⟶ (forward J U).obj Q) : P ⟶ Q := by
  let i := (sheafEquivalence J U).functor.preimageIso h.iso
  have hi : (sheafEquivalence J U).functor.map i.hom = h.iso.hom :=
    (sheafEquivalence J U).functor.map_preimage _
  have he : PrincipalSheaf.Equivariant (elementStructure J U P) (elementStructure J U Q) i.hom := by
    apply equivariant_of_forward J U
    intro X g p
    rw [hi]
    exact h.equivariant X g p
  exact
    { iso := Functor.isoWhiskerLeft (opOpEquivalence _).inverse
        ((sheafToPresheaf _ _).mapIso i)
      equivariant x := he (op (op x)) }

theorem forward_liftArrow {P Q : SheafTorsor.Torsor G (context J U)}
    (h : (forward J U).obj P ⟶ (forward J U).obj Q) :
    (forward J U).map (liftArrow J U h) = h := by
  apply SheafSliceTorsor.Arrow.ext
  exact (sheafEquivalence J U).functor.map_preimage h.iso.hom

instance forward_full : (forward (G := G) J U).Full where
  map_surjective h := ⟨liftArrow J U h, forward_liftArrow J U h⟩

instance forward_faithful : (forward (G := G) J U).Faithful where
  map_injective {P Q} {f g} h := by
    apply SheafTorsor.Arrow.ext
    have hh : (sheafEquivalence J U).functor.map
        (show SplitSheaf.elementSheaf P.family ⟶ SplitSheaf.elementSheaf Q.family from
          ⟨Functor.whiskerLeft (opOpEquivalence _).functor f.iso.hom⟩) =
      (sheafEquivalence J U).functor.map
        (show SplitSheaf.elementSheaf P.family ⟶ SplitSheaf.elementSheaf Q.family from
          ⟨Functor.whiskerLeft (opOpEquivalence _).functor g.iso.hom⟩) :=
      congrArg (fun k => k.iso.hom) h
    have hi := (sheafEquivalence J U).functor.map_injective hh
    ext x p
    exact congrArg (fun k => k.hom.app (op (op x)) p) hi

/-- The sheafification-unit recovery, followed by the ordinary slice recovery. -/
def counitSheaf (Q : SheafSliceTorsor.Torsor J U G) :
    (forwardObject J U (backwardObject J U Q)).sheaf ≅ Q.sheaf :=
  (rawSheafEquivalence J U).functor.mapIso
    ((unitSheafEquivalence J U).unitIso.symm.app (rawSheaf J U Q)) ≪≫
      ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ => Iso.refl _) (by intro X Y f; rfl))

/-- Recovery includes the group action on the independently defined slice sheaf. -/
def counitComponent (Q : SheafSliceTorsor.Torsor J U G) :
    (forward J U).obj (backwardObject J U Q) ≅ Q :=
  SheafSliceTorsor.Arrow.toIso
    { iso := counitSheaf J U Q
      equivariant X g p := by
        let e := (unitSheafEquivalence J U).unitIso.symm.app (rawSheaf J U Q)
        let A := PrincipalSheaf.transport (rawStructure J U Q) e
        let x := (RepresentableElementSite.overElement U).obj X.unop
        have h := PrincipalSheaf.extend_act_image A x g p
        change e.hom.hom.app (op x) ((PrincipalSheaf.extend A).act
          (op ((unitSite J U).obj x)) g p) =
            Q.act X g (e.hom.hom.app (op x) p)
        rw [h]
        exact congrArg (fun k => k.hom.app (op x)
          ((rawStructure J U Q).act (op x) g (e.hom.hom.app (op x) p))) e.inv_hom_id }

instance forward_essSurj : (forward (G := G) J U).EssSurj where
  mem_essImage Q := ⟨backwardObject J U Q, ⟨counitComponent J U Q⟩⟩

instance forward_isEquivalence : (forward (G := G) J U).IsEquivalence := {}

/-- Categorical recovery over any Grothendieck site, including all equivariant arrows. -/
def equivalence : SheafTorsor.Torsor G (context J U) ≌ SheafSliceTorsor.Torsor J U G :=
  (forward J U).asEquivalence

/-- Fullness also lifts natural equivariant maps before any inverse is chosen. -/
def liftEquivariantMap {P Q : SheafTorsor.Torsor G (context J U)}
    (h : SheafSliceTorsor.EquivariantMap ((forward J U).obj P) ((forward J U).obj Q)) :
    SheafTorsor.EquivariantMap P Q := by
  let f := (sheafEquivalence J U).functor.preimage h.hom
  have hf : (sheafEquivalence J U).functor.map f = h.hom :=
    (sheafEquivalence J U).functor.map_preimage _
  have he : PrincipalSheaf.Equivariant (elementStructure J U P) (elementStructure J U Q) f := by
    apply equivariant_of_forward J U
    intro X g p
    rw [hf]
    exact h.equivariant X g p
  exact
    { hom := Functor.whiskerLeft (opOpEquivalence _).inverse f.hom
      equivariant x := he (op (op x)) }

theorem forward_liftEquivariantMap {P Q : SheafTorsor.Torsor G (context J U)}
    (h : SheafSliceTorsor.EquivariantMap ((forward J U).obj P) ((forward J U).obj Q)) :
    ((forward J U).map (liftEquivariantMap J U h).toArrow).iso.hom = h.hom :=
  (sheafEquivalence J U).functor.map_preimage h.hom

/-- Principality supplies the inverse for every independently specified slice map. -/
def equivariantMapArrow {P Q : SheafSliceTorsor.Torsor J U G}
    (f : SheafSliceTorsor.EquivariantMap P Q) : P ⟶ Q :=
  (counitComponent J U P).inv ≫
    (forward J U).map ((liftEquivariantMap J U
      { hom := (counitComponent J U P).hom.iso.hom ≫ f.hom ≫
          (counitComponent J U Q).inv.iso.hom
        equivariant X g p := by
          change (counitComponent J U Q).inv.iso.hom.hom.app X
            (f.hom.hom.app X ((counitComponent J U P).hom.iso.hom.hom.app X _)) = _
          rw [(counitComponent J U P).hom.equivariant, f.equivariant,
            (counitComponent J U Q).inv.equivariant]
          rfl }).toArrow) ≫
    (counitComponent J U Q).hom

@[simp] theorem equivariantMapArrow_hom {P Q : SheafSliceTorsor.Torsor J U G}
    (f : SheafSliceTorsor.EquivariantMap P Q) : (equivariantMapArrow J U f).iso.hom = f.hom := by
  change (counitComponent J U P).inv.iso.hom ≫
    ((forward J U).map (liftEquivariantMap J U _).toArrow).iso.hom ≫
      (counitComponent J U Q).hom.iso.hom = _
  rw [forward_liftEquivariantMap]
  have hp := congrArg (fun h => h.iso.hom) (counitComponent J U P).inv_hom_id
  have hq := congrArg (fun h => h.iso.hom) (counitComponent J U Q).inv_hom_id
  change (counitComponent J U P).inv.iso.hom ≫ (counitComponent J U P).hom.iso.hom = 𝟙 _ at hp
  change (counitComponent J U Q).inv.iso.hom ≫ (counitComponent J U Q).hom.iso.hom = 𝟙 _ at hq
  simp only [← Category.assoc, hp, Category.id_comp]
  rw [Category.assoc, hq, Category.comp_id]

def equivariantArrowEquiv {P Q : SheafSliceTorsor.Torsor J U G} :
    SheafSliceTorsor.EquivariantMap P Q ≃ (P ⟶ Q) where
  toFun := equivariantMapArrow J U
  invFun f := ⟨f.iso.hom, f.equivariant⟩
  left_inv f := by cases f; simp only [equivariantMapArrow_hom]
  right_inv f := by apply SheafSliceTorsor.Arrow.ext; exact equivariantMapArrow_hom J U _

/-- The category equivalence recovers the total display over the sheafified base. -/
def displayComparison (P : SheafTorsor.Torsor G (context J U)) :
    SplitSheaf.extension P.family ≅
      SplitSheaf.extension (((equivalence J U).functor ⋙ (equivalence J U).inverse).obj P).family :=
  ObjectProperty.isoMk _ (ElementFamilies.totalFunctor _ |>.mapIso
    ((equivalence J U).unitIso.app P).hom.iso |> (Over.forget _).mapIso)

@[simp] theorem displayComparison_projection (P : SheafTorsor.Torsor G (context J U)) :
    (displayComparison J U P).hom ≫
      SplitSheaf.p (((equivalence J U).functor ⋙ (equivalence J U).inverse).obj P).family =
        SplitSheaf.p P.family := rfl

/-- Ordinary slice arrows are evaluated through the sheafification unit. -/
def sliceElements : (Over U)ᵒᵖ ⥤ (context J U).obj.Elements where
  obj X := (context J U).obj.elementsMk (op X.unop.left)
    ((toSheafify J (yoneda.obj U)).app (op X.unop.left) X.unop.hom)
  map f := ((unitSite J U).map ((RepresentableElementSite.overElement U).map f.unop)).unop

variable {U} {V W : C}

/-- Naturality of the unit supplies the fiber comparison for ordinary restriction. -/
def restrictionElementIso (f : V ⟶ U) :
    sliceElements J V ⋙ ((SheafifiedYoneda.functor J).map f).hom.mapElements ≅
      (Over.map f).op ⋙ sliceElements J U :=
  NatIso.ofComponents (fun X =>
    let h : ((SheafifiedYoneda.functor J).map f).hom.app (op X.unop.left)
        ((toSheafify J (yoneda.obj V)).app (op X.unop.left) X.unop.hom) =
      (toSheafify J (yoneda.obj U)).app (op X.unop.left) (X.unop.hom ≫ f) :=
        (ConcreteCategory.congr_hom (NatTrans.congr_app
          (toSheafify_naturality J (yoneda.map f)) (op X.unop.left)) X.unop.hom).symm
    { hom := ElementFamilies.vertical _ h
      inv := ElementFamilies.vertical _ h.symm
      hom_inv_id := by apply Functor.Elements.hom_ext; simp [ElementFamilies.vertical, sliceElements]
      inv_hom_id := by apply Functor.Elements.hom_ext; simp [ElementFamilies.vertical, sliceElements] }) (by
      intro X Y k
      apply Functor.Elements.hom_ext
      simp [ElementFamilies.vertical, sliceElements, RepresentableElementSite.overElement])

def restrictionComparison (f : V ⟶ U) :
    SheafTorsor.restriction (G := G) ((SheafifiedYoneda.functor J).map f) ⋙ forward J V ≅
      forward J U ⋙ SheafSliceTorsor.restriction J f :=
  NatIso.ofComponents (fun P => SheafSliceTorsor.Arrow.toIso
    { iso := ObjectProperty.isoMk _ (Functor.isoWhiskerRight (restrictionElementIso J f) P.family.family)
      equivariant X g p := by
        have h := P.natural ((restrictionElementIso J f).hom.app X) g p
        have hg : G.obj.map ((restrictionElementIso J f).hom.app X).hom g = g := by
          change G.obj.map (𝟙 _) g = g
          rw [G.obj.map_id]
          rfl
        rw [hg] at h
        exact h }) (by
      intro P Q h
      apply SheafSliceTorsor.Arrow.ext
      ext X p
      exact (NatTrans.naturality_apply h.iso.hom ((restrictionElementIso J f).hom.app X) p).symm)

/-- Composition of the sheafified base maps identifies their actual section functors. -/
def contextCompIso (f : V ⟶ U) (g : W ⟶ V) :
    ((SheafifiedYoneda.functor J).map g).hom.mapElements ⋙
      ((SheafifiedYoneda.functor J).map f).hom.mapElements ≅
        ((SheafifiedYoneda.functor J).map (g ≫ f)).hom.mapElements :=
  NatIso.ofComponents (fun x =>
    let h : ((SheafifiedYoneda.functor J).map f).hom.app x.obj
        (((SheafifiedYoneda.functor J).map g).hom.app x.obj x.val) =
      ((SheafifiedYoneda.functor J).map (g ≫ f)).hom.app x.obj x.val :=
        (congrArg (fun k => k.hom.app x.obj x.val) ((SheafifiedYoneda.functor J).map_comp g f)).symm
    { hom := ElementFamilies.vertical _ h
      inv := ElementFamilies.vertical _ h.symm
      hom_inv_id := by apply Functor.Elements.hom_ext; simp [ElementFamilies.vertical]
      inv_hom_id := by apply Functor.Elements.hom_ext; simp [ElementFamilies.vertical] }) (by
      intro x y k
      apply Functor.Elements.hom_ext
      simp [ElementFamilies.vertical])

/-- The restriction comparisons commute with composing two ordinary base maps. -/
theorem restrictionElement_comp (f : V ⟶ U) (g : W ⟶ V) (X : (Over W)ᵒᵖ) :
    ((SheafifiedYoneda.functor J).map f).hom.mapElements.map
        ((restrictionElementIso J g).hom.app X) ≫
      (restrictionElementIso J f).hom.app ((Over.map g).op.obj X) =
    (contextCompIso J f g).hom.app ((sliceElements J W).obj X) ≫
      (restrictionElementIso J (g ≫ f)).hom.app X ≫
        (Functor.isoWhiskerRight (NatIso.op (Over.mapComp g f)).symm
          (sliceElements J U)).hom.app X := by
  apply Functor.Elements.hom_ext
  simp [contextCompIso, restrictionElementIso, ElementFamilies.vertical,
    sliceElements, RepresentableElementSite.overElement]

/-- The identity base map acts as the identity on the sheafified element category. -/
def contextIdIso (U : C) :
    ((SheafifiedYoneda.functor J).map (𝟙 U)).hom.mapElements ≅ 𝟭 (context J U).obj.Elements :=
  NatIso.ofComponents (fun x =>
    let h : ((SheafifiedYoneda.functor J).map (𝟙 U)).hom.app x.obj x.val = x.val :=
      congrArg (fun k => k.hom.app x.obj x.val) ((SheafifiedYoneda.functor J).map_id U)
    { hom := ElementFamilies.vertical _ h
      inv := ElementFamilies.vertical _ h.symm
      hom_inv_id := by apply Functor.Elements.hom_ext; simp [ElementFamilies.vertical]
      inv_hom_id := by apply Functor.Elements.hom_ext; simp [ElementFamilies.vertical] }) (by
      intro x y k
      apply Functor.Elements.hom_ext
      simp [ElementFamilies.vertical])

/-- Identity restriction commutes with the actual slice and context identity comparisons. -/
theorem restrictionElement_id (X : (Over U)ᵒᵖ) :
    (restrictionElementIso J (𝟙 U)).hom.app X ≫
      (Functor.isoWhiskerRight (NatIso.op (Over.mapId U)).symm
        (sliceElements J U)).hom.app X =
      (contextIdIso J U).hom.app ((sliceElements J U).obj X) := by
  apply Functor.Elements.hom_ext
  simp [contextIdIso, restrictionElementIso, ElementFamilies.vertical,
    sliceElements, RepresentableElementSite.overElement]

end SquareKit.SheafifiedSliceTorsor
