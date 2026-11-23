import SquareKit.SheafifiedTorsor
import SquareKit.SheafFamilyDescent

/-! Original-site descent through sheafified representables. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafifiedSheafStack
open CategoryTheory Limits Opposite
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

abbrev torsorFunctor (G : Sheaf J GrpCat.{u}) : Cᵒᵖ ⥤ Cat :=
  (SheafifiedYoneda.functor J).op ⋙ SheafTorsor.Stack.functor G

abbrev torsorPseudofunctor (G : Sheaf J GrpCat.{u}) := (torsorFunctor G).toPseudofunctor'

abbrev quotientFunctor {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)}
    (a : SheafActionQuotient.Action G M) : Cᵒᵖ ⥤ Cat :=
  (SheafifiedYoneda.functor J).op ⋙ SheafActionQuotient.Stack.functor a

abbrev quotientPseudofunctor {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)}
    (a : SheafActionQuotient.Action G M) := (quotientFunctor a).toPseudofunctor'

abbrev represented (U : C) : Sheaf J (Type u) := (SheafifiedYoneda.functor J).obj U

abbrev sectionOfArrow {U V : C} (f : U ⟶ V) : (represented (J := J) V).obj.obj (op U) :=
  (toSheafify J (yoneda.obj V)).app (op U) f

theorem map_sectionOfArrow {U V W : C} (f : U ⟶ V) (g : V ⟶ W) :
    ((SheafifiedYoneda.functor J).map g).hom.app (op U) (sectionOfArrow (J := J) f) =
      sectionOfArrow (J := J) (f ≫ g) := by
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app
    (toSheafify_naturality J (yoneda.map g)) (op U)) f).symm

theorem restrict_sectionOfArrow {U V W : C} (f : U ⟶ V) (g : V ⟶ W) :
    (represented (J := J) W).obj.map f.op (sectionOfArrow (J := J) g) =
      sectionOfArrow (J := J) (f ≫ g) :=
  (NatTrans.naturality_apply (toSheafify J (yoneda.obj W)) f.op g).symm

theorem map_generic {U V : C} (f : U ⟶ V) :
    ((SheafifiedYoneda.functor J).map f).hom.app (op U) (sectionOfArrow (J := J) (𝟙 U)) =
      sectionOfArrow (J := J) f := by
  rw [map_sectionOfArrow, Category.id_comp]

namespace TorsorExtension
open SheafTorsor
variable {G : Sheaf J GrpCat.{u}}

lemma eqToHom_reindex_app {X Y : Sheaf J (Type u)} (P : Torsor G X)
    {f g : Y ⟶ X} (h : f = g) (x : Y.obj.Elements) :
    (eqToHom (congrArg (reindex P) h)).iso.hom.app x =
      P.family.family.map (ElementFamilies.vertical X.obj
        (congrArg (fun k : Y ⟶ X => k.hom.app x.obj x.val) h)) := by
  subst g
  simp only [eqToHom_refl, ElementFamilies.vertical_rfl]
  change 𝟙 _ = P.family.family.map (𝟙 _)
  rw [P.family.family.map_id]

def compositionIso {V U W : C} (P : Torsor G (represented V))
    (f : U ⟶ V) (k : W ⟶ U) :
    reindex P ((SheafifiedYoneda.functor J).map (k ≫ f)) ≅ reindex (reindex P ((SheafifiedYoneda.functor J).map f)) ((SheafifiedYoneda.functor J).map k) :=
  eqToIso (by rw [(SheafifiedYoneda.functor J).map_comp]; rfl)

lemma compositionIso_hom_app {V U W : C} (P : Torsor G (represented V))
    (f : U ⟶ V) (k : W ⟶ U) (x : (represented (J := J) W).obj.Elements) :
    (compositionIso P f k).hom.iso.hom.app x =
      P.family.family.map (ElementFamilies.vertical _
        (congrArg (fun m => m.hom.app x.obj x.val) ((SheafifiedYoneda.functor J).map_comp k f))) := by
  exact eqToHom_reindex_app P ((SheafifiedYoneda.functor J).map_comp k f) x

lemma compositionIso_inv_app {V U W : C} (P : Torsor G (represented V))
    (f : U ⟶ V) (k : W ⟶ U) (x : (represented (J := J) W).obj.Elements) :
    (compositionIso P f k).inv.iso.hom.app x =
      P.family.family.map (ElementFamilies.vertical _
        (congrArg (fun m => m.hom.app x.obj x.val) ((SheafifiedYoneda.functor J).map_comp k f).symm)) := by
  exact eqToHom_reindex_app P ((SheafifiedYoneda.functor J).map_comp k f).symm x

lemma pullHom_eq {V W U T : C} {P : Torsor G (represented V)}
    {Q : Torsor G (represented W)} {f : U ⟶ V} {g : U ⟶ W}
    (h : reindex P ((SheafifiedYoneda.functor J).map f) ⟶ reindex Q ((SheafifiedYoneda.functor J).map g)) (k : T ⟶ U) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := torsorPseudofunctor G)
      h k (k ≫ f) (k ≫ g) =
    (compositionIso P f k).hom ≫ h.reindex ((SheafifiedYoneda.functor J).map k) ≫ (compositionIso Q g k).inv := by
  simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    Pseudofunctor.mapComp', torsorPseudofunctor, Functor.toPseudofunctor'_mapComp,
    PrelaxFunctor.map₂Iso_eqToIso, Iso.trans_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv,
    eqToHom_trans, Cat.eqToHom_app]
  rfl


abbrev fiber {V : C} (P : Torsor G (represented V)) {U : C} (f : U ⟶ V) :=
  P.family.family.obj ((represented V).obj.elementsMk (op U) (sectionOfArrow (J := J) f))

def evaluate {V W U : C} {P : Torsor G (represented V)} {Q : Torsor G (represented W)}
    {f : U ⟶ V} {g : U ⟶ W}
    (h : reindex P ((SheafifiedYoneda.functor J).map f) ⟶
      reindex Q ((SheafifiedYoneda.functor J).map g)) : fiber P f → fiber Q g := fun p =>
  Q.family.family.map (ElementFamilies.vertical _ (map_generic g))
    (h.iso.hom.app ((represented U).obj.elementsMk (op U) (sectionOfArrow (J := J) (𝟙 U)))
      (P.family.family.map (ElementFamilies.vertical _ (map_generic f).symm) p))

lemma evaluate_id {V U : C} {P : Torsor G (represented V)} (f : U ⟶ V)
    (p : fiber P f) : evaluate (𝟙 (reindex P ((SheafifiedYoneda.functor J).map f))) p = p := by
  change P.family.family.map _ (P.family.family.map _ p) = p
  rw [← ConcreteCategory.comp_apply, ← P.family.family.map_comp]
  have h : ElementFamilies.vertical (represented (J := J) V).obj (map_generic f).symm ≫
      ElementFamilies.vertical _ (map_generic (J := J) f) = 𝟙 _ := by
    apply Functor.Elements.hom_ext
    simp [ElementFamilies.vertical]
  rw [h, P.family.family.map_id]
  rfl

lemma evaluate_comp {V W T U : C} {P : Torsor G (represented V)}
    {Q : Torsor G (represented W)} {R : Torsor G (represented T)}
    {f : U ⟶ V} {g : U ⟶ W} {k : U ⟶ T}
    (h : reindex P ((SheafifiedYoneda.functor J).map f) ⟶ reindex Q ((SheafifiedYoneda.functor J).map g))
    (l : reindex Q ((SheafifiedYoneda.functor J).map g) ⟶ reindex R ((SheafifiedYoneda.functor J).map k)) (p : fiber P f) :
    evaluate (h ≫ l) p = evaluate l (evaluate h p) := by
  dsimp only [evaluate]
  change R.family.family.map _
      (l.iso.hom.app ((represented U).obj.elementsMk (op U) (sectionOfArrow (J := J) (𝟙 U)))
        (h.iso.hom.app ((represented U).obj.elementsMk (op U) (sectionOfArrow (J := J) (𝟙 U)))
          (P.family.family.map (ElementFamilies.vertical _ (map_generic f).symm) p))) =
    R.family.family.map _
      (l.iso.hom.app ((represented U).obj.elementsMk (op U) (sectionOfArrow (J := J) (𝟙 U)))
        (Q.family.family.map (ElementFamilies.vertical _ (map_generic g).symm)
          (Q.family.family.map (ElementFamilies.vertical _ (map_generic g))
            (h.iso.hom.app ((represented U).obj.elementsMk (op U) (sectionOfArrow (J := J) (𝟙 U)))
              (P.family.family.map (ElementFamilies.vertical _ (map_generic f).symm) p)))))
  have hh : ElementFamilies.vertical (represented (J := J) W).obj (map_generic (J := J) g) ≫
      ElementFamilies.vertical _ (map_generic g).symm = 𝟙 _ := by
    apply Functor.Elements.hom_ext
    simp [ElementFamilies.vertical]
  have cancel (q : (reindex Q ((SheafifiedYoneda.functor J).map g)).family.family.obj ((represented U).obj.elementsMk (op U) (sectionOfArrow (J := J) (𝟙 U)))) :
      Q.family.family.map (ElementFamilies.vertical _ (map_generic g).symm)
        (Q.family.family.map (ElementFamilies.vertical _ (map_generic g)) q) = q := by
    rw [← ConcreteCategory.comp_apply, ← Q.family.family.map_comp, hh, Q.family.family.map_id]
    rfl
  rw [cancel]



def evaluateAt {V W U T : C} {P : Torsor G (represented V)}
    {Q : Torsor G (represented W)} {f : U ⟶ V} {g : U ⟶ W}
    (h : reindex P ((SheafifiedYoneda.functor J).map f) ⟶
      reindex Q ((SheafifiedYoneda.functor J).map g)) (k : T ⟶ U) :
    fiber P (k ≫ f) → fiber Q (k ≫ g) := fun p =>
  Q.family.family.map (ElementFamilies.vertical _ (map_sectionOfArrow k g))
    (h.iso.hom.app ((represented U).obj.elementsMk (op T) (sectionOfArrow (J := J) k))
      (P.family.family.map (ElementFamilies.vertical _ (map_sectionOfArrow k f).symm) p))

lemma evaluate_pullHom {V W U T : C} {P : Torsor G (represented V)}
    {Q : Torsor G (represented W)} {f : U ⟶ V} {g : U ⟶ W}
    (h : reindex P ((SheafifiedYoneda.functor J).map f) ⟶
      reindex Q ((SheafifiedYoneda.functor J).map g)) (k : T ⟶ U)
    (p : fiber P (k ≫ f)) :
    evaluate (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := torsorPseudofunctor G) h k (k ≫ f) (k ≫ g)) p = evaluateAt h k p := by
  rw [pullHom_eq]
  let z := (represented (J := J) T).obj.elementsMk (op T) (sectionOfArrow (J := J) (𝟙 T))
  let x := ((SheafifiedYoneda.functor J).map k).hom.mapElements.obj z
  let y := (represented (J := J) U).obj.elementsMk (op T) (sectionOfArrow (J := J) k)
  let e : x ⟶ y := ElementFamilies.vertical _ (map_generic k)
  have hp : P.family.family.map (ElementFamilies.vertical _ (map_generic (k ≫ f)).symm) ≫
      (compositionIso P f k).hom.iso.hom.app z ≫
      (reindex P ((SheafifiedYoneda.functor J).map f)).family.family.map e =
    P.family.family.map (ElementFamilies.vertical _ (map_sectionOfArrow k f).symm) := by
    rw [compositionIso_hom_app]
    change P.family.family.map _ ≫ P.family.family.map _ ≫ P.family.family.map _ =
      P.family.family.map _
    simp only [← P.family.family.map_comp]
    congr 1
    apply Functor.Elements.hom_ext
    simp [e, ElementFamilies.vertical]
    rfl
  have hq : (compositionIso Q g k).inv.iso.hom.app z ≫
      Q.family.family.map (ElementFamilies.vertical _ (map_generic (k ≫ g))) =
    (reindex Q ((SheafifiedYoneda.functor J).map g)).family.family.map e ≫
      Q.family.family.map (ElementFamilies.vertical _ (map_sectionOfArrow k g)) := by
    rw [compositionIso_inv_app]
    change Q.family.family.map _ ≫ Q.family.family.map _ =
      Q.family.family.map _ ≫ Q.family.family.map _
    simp only [← Q.family.family.map_comp]
    congr 1
  change ((compositionIso Q g k).inv.iso.hom.app z ≫
      Q.family.family.map (ElementFamilies.vertical _ (map_generic (k ≫ g))))
    (h.iso.hom.app x
      ((P.family.family.map (ElementFamilies.vertical _ (map_generic (k ≫ f)).symm) ≫
        (compositionIso P f k).hom.iso.hom.app z) p)) = _
  rw [hq]
  change Q.family.family.map _
    ((reindex Q ((SheafifiedYoneda.functor J).map g)).family.family.map e
      (h.iso.hom.app x _)) = _
  rw [← NatTrans.naturality_apply]
  change Q.family.family.map _ (h.iso.hom.app y
    ((P.family.family.map _ ≫ (compositionIso P f k).hom.iso.hom.app z ≫
      (reindex P ((SheafifiedYoneda.functor J).map f)).family.family.map e) p)) = _
  rw [hp]
  rfl

def fiberRestriction {V U W : C} (P : Torsor G (represented V))
    {f : U ⟶ V} (k : W ⟶ U) {kf : W ⟶ V} (hkf : k ≫ f = kf) :
    fiber P f ⟶ fiber P kf :=
  P.family.family.map (Functor.Elements.homMk k.op
    ((restrict_sectionOfArrow (J := J) k f).trans (congrArg (sectionOfArrow (J := J)) hkf)))

lemma evaluate_natural {V W U T : C} {P : Torsor G (represented V)}
    {Q : Torsor G (represented W)} {f : U ⟶ V} {g : U ⟶ W}
    (h : reindex P ((SheafifiedYoneda.functor J).map f) ⟶
      reindex Q ((SheafifiedYoneda.functor J).map g)) (k : T ⟶ U)
    (kf : T ⟶ V) (kg : T ⟶ W) (hkf : k ≫ f = kf) (hkg : k ≫ g = kg)
    (p : fiber P f) :
    fiberRestriction Q k hkg (evaluate h p) =
      evaluate (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := torsorPseudofunctor G) h k kf kg hkf hkg) (fiberRestriction P k hkf p) := by
  subst kf kg
  rw [pullHom_eq]
  let xt := (represented (J := J) T).obj.elementsMk (op T) (sectionOfArrow (J := J) (𝟙 T))
  let xp := (represented (J := J) U).obj.elementsMk (op U) (sectionOfArrow (J := J) (𝟙 U))
  let t : xp ⟶ ((SheafifiedYoneda.functor J).map k).hom.mapElements.obj xt :=
    Functor.Elements.homMk k.op (by
      change (represented (J := J) U).obj.map k.op (sectionOfArrow (J := J) (𝟙 U)) =
        ((SheafifiedYoneda.functor J).map k).hom.app (op T) (sectionOfArrow (J := J) (𝟙 T))
      rw [restrict_sectionOfArrow, map_generic, Category.comp_id])
  have hp : P.family.family.map (ElementFamilies.vertical _ (map_generic f).symm) ≫
      (reindex P ((SheafifiedYoneda.functor J).map f)).family.family.map t =
      fiberRestriction P k rfl ≫
        P.family.family.map (ElementFamilies.vertical _ (map_generic (k ≫ f)).symm) ≫
          (compositionIso P f k).hom.iso.hom.app xt := by
    rw [compositionIso_hom_app]
    change P.family.family.map _ ≫ P.family.family.map _ =
      P.family.family.map _ ≫ P.family.family.map _ ≫ P.family.family.map _
    simp only [← P.family.family.map_comp]
    congr 1
    apply Functor.Elements.hom_ext
    simp [t, ElementFamilies.vertical]
    change k.op = k.op ≫ 𝟙 (op T)
    exact (Category.comp_id k.op).symm
  have hq : Q.family.family.map (ElementFamilies.vertical _ (map_generic g)) ≫
      fiberRestriction Q k rfl =
      (reindex Q ((SheafifiedYoneda.functor J).map g)).family.family.map t ≫
        (compositionIso Q g k).inv.iso.hom.app xt ≫
          Q.family.family.map (ElementFamilies.vertical _ (map_generic (k ≫ g))) := by
    rw [compositionIso_inv_app]
    change Q.family.family.map _ ≫ Q.family.family.map _ =
      Q.family.family.map _ ≫ Q.family.family.map _ ≫ Q.family.family.map _
    simp only [← Q.family.family.map_comp]
    congr 1
    apply Functor.Elements.hom_ext
    simp [t, ElementFamilies.vertical]
  change (Q.family.family.map (ElementFamilies.vertical _ (map_generic g)) ≫
      fiberRestriction Q k rfl)
    (h.iso.hom.app xp (P.family.family.map (ElementFamilies.vertical _ (map_generic f).symm) p)) = _
  rw [hq]
  change ((compositionIso Q g k).inv.iso.hom.app xt ≫ Q.family.family.map _)
    ((reindex Q ((SheafifiedYoneda.functor J).map g)).family.family.map t
      (h.iso.hom.app xp (P.family.family.map _ p))) = _
  rw [← NatTrans.naturality_apply]
  change ((compositionIso Q g k).inv.iso.hom.app xt ≫ Q.family.family.map _)
    (h.iso.hom.app _ ((P.family.family.map _ ≫
      (reindex P ((SheafifiedYoneda.functor J).map f)).family.family.map t) p)) = _
  rw [hp]
  rfl

lemma section_naturality {Z : Cᵒᵖ ⥤ Type u} {U : C} (a : Z ⟶ yoneda.obj U)
    {x y : Z.Elements} (k : x ⟶ y) :
    k.hom.unop ≫ a.app x.obj x.val = a.app y.obj y.val := by
  have h := a.naturality_apply k.hom x.val
  change a.app y.obj (Z.map k.hom x.val) = k.hom.unop ≫ a.app x.obj x.val at h
  rw [k.map_val] at h
  exact h.symm

lemma vertical_act {X : Sheaf J (Type u)} (P : Torsor G X) {U : Cᵒᵖ}
    {x y : X.obj.obj U} (h : x = y) (g : G.obj.obj U)
    (p : P.family.family.obj (X.obj.elementsMk U x)) :
    P.family.family.map (ElementFamilies.vertical _ h) (P.act _ g p) =
      P.act _ g (P.family.family.map (ElementFamilies.vertical _ h) p) := by
  simpa [ElementFamilies.vertical] using P.natural (ElementFamilies.vertical _ h) g p

lemma evaluate_equivariant {V W U : C} {P : Torsor G (represented V)}
    {Q : Torsor G (represented W)} {f : U ⟶ V} {g : U ⟶ W}
    (h : reindex P ((SheafifiedYoneda.functor J).map f) ⟶ reindex Q ((SheafifiedYoneda.functor J).map g))
    (a : G.obj.obj (op U)) (p : fiber P f) :
    evaluate h (P.act _ a p) = Q.act _ a (evaluate h p) := by
  dsimp only [evaluate]
  rw [vertical_act]
  change Q.family.family.map _ (h.iso.hom.app _ ((reindex P ((SheafifiedYoneda.functor J).map f)).act ((represented U).obj.elementsMk (op U) (sectionOfArrow (J := J) (𝟙 U))) a _)) = _
  rw [h.equivariant]
  change Q.family.family.map _
    (Q.act ((represented W).obj.elementsMk (op U) (((SheafifiedYoneda.functor J).map g).hom.app (op U) (sectionOfArrow (J := J) (𝟙 U)))) a _) = _
  rw [vertical_act]

lemma evaluate_reindex {V U : C} {P Q : Torsor G (represented V)}
    (h : P ⟶ Q) (f : U ⟶ V) (p : fiber P f) :
    evaluate (h.reindex ((SheafifiedYoneda.functor J).map f)) p =
      h.iso.hom.app ((represented V).obj.elementsMk (op U) (sectionOfArrow (J := J) f)) p := by
  let x := (represented V).obj.elementsMk (op U)
    (((SheafifiedYoneda.functor J).map f).hom.app (op U) (sectionOfArrow (J := J) (𝟙 U)))
  let y := (represented V).obj.elementsMk (op U) (sectionOfArrow (J := J) f)
  let e : x ⟶ y := ElementFamilies.vertical _ (map_generic f)
  let ei : y ⟶ x := ElementFamilies.vertical _ (map_generic f).symm
  change Q.family.family.map e (h.iso.hom.app x (P.family.family.map ei p)) = _
  erw [h.iso.hom.naturality_apply ei p]
  change Q.family.family.map e (Q.family.family.map ei (h.iso.hom.app y p)) = _
  have he : ei ≫ e = 𝟙 y := by
    apply Functor.Elements.hom_ext
    simp [ei, e, x, y, ElementFamilies.vertical]
  have hz := congrArg (fun m => m (h.iso.hom.app y p)) (Q.family.family.map_comp ei e)
  rw [he, Q.family.family.map_id] at hz
  exact hz.symm

variable {I : Type u} {S : C} {V : I → C} {f : ∀ i, V i ⟶ S}

def localHom (D : (torsorPseudofunctor G).DescentData f)
    {Z : Cᵒᵖ ⥤ Type u} (q : Z ⟶ yoneda.obj S) {i j : I}
    (a : Z ⟶ yoneda.obj (V i)) (b : Z ⟶ yoneda.obj (V j))
    (ha : a ≫ yoneda.map (f i) = q) (hb : b ≫ yoneda.map (f j) = q)
    (x : Z.Elements) :
    reindex (D.obj i) ((SheafifiedYoneda.functor J).map (a.app x.obj x.val)) ⟶
      reindex (D.obj j) ((SheafifiedYoneda.functor J).map (b.app x.obj x.val)) :=
  D.hom (q.app x.obj x.val) (a.app x.obj x.val) (b.app x.obj x.val)
    (congrArg (fun m : Z ⟶ yoneda.obj S => m.app x.obj x.val) ha)
    (congrArg (fun m : Z ⟶ yoneda.obj S => m.app x.obj x.val) hb)

lemma localHom_self (D : (torsorPseudofunctor G).DescentData f)
    {Z : Cᵒᵖ ⥤ Type u} (q : Z ⟶ yoneda.obj S) {i : I}
    (a : Z ⟶ yoneda.obj (V i)) (ha : a ≫ yoneda.map (f i) = q)
    (x : Z.Elements) : localHom D q a a ha ha x = 𝟙 _ :=
  D.hom_self _ _ (congrArg (fun m : Z ⟶ yoneda.obj S => m.app x.obj x.val) ha)

lemma localHom_comp (D : (torsorPseudofunctor G).DescentData f)
    {Z : Cᵒᵖ ⥤ Type u} (q : Z ⟶ yoneda.obj S) {i j k : I}
    (a : Z ⟶ yoneda.obj (V i)) (b : Z ⟶ yoneda.obj (V j))
    (c : Z ⟶ yoneda.obj (V k))
    (ha : a ≫ yoneda.map (f i) = q) (hb : b ≫ yoneda.map (f j) = q)
    (hc : c ≫ yoneda.map (f k) = q) (x : Z.Elements) :
    localHom D q a b ha hb x ≫ localHom D q b c hb hc x =
      localHom D q a c ha hc x := D.hom_comp _ _ _ _ _ _ _

abbrev rawFamily {Z : Cᵒᵖ ⥤ Type u} {U : C} (P : Torsor G (represented U))
    (a : Z ⟶ yoneda.obj U) : Z.Elements ⥤ Type u :=
  (a ≫ toSheafify J (yoneda.obj U)).mapElements ⋙ P.family.family

lemma rawFamily_map {Z : Cᵒᵖ ⥤ Type u} {U : C} (P : Torsor G (represented U))
    (a : Z ⟶ yoneda.obj U) {x y : Z.Elements} (k : x ⟶ y) :
    (rawFamily P a).map k = fiberRestriction P k.hom.unop (section_naturality a k) := by
  change P.family.family.map _ = P.family.family.map _
  congr 1

def rawNat (D : (torsorPseudofunctor G).DescentData f)
    {Z : Cᵒᵖ ⥤ Type u} (q : Z ⟶ yoneda.obj S) {i j : I}
    (a : Z ⟶ yoneda.obj (V i)) (b : Z ⟶ yoneda.obj (V j))
    (ha : a ≫ yoneda.map (f i) = q) (hb : b ≫ yoneda.map (f j) = q) :
    rawFamily (D.obj i) a ⟶ rawFamily (D.obj j) b where
  app x := ↾evaluate (localHom D q a b ha hb x)
  naturality {x y} k := by
    apply ConcreteCategory.hom_ext
    intro p
    have hn := evaluate_natural (localHom D q a b ha hb x) k.hom.unop
      (a.app y.obj y.val) (b.app y.obj y.val)
      (section_naturality a k) (section_naturality b k) p
    dsimp only [localHom] at hn
    rw [D.pullHom_hom k.hom.unop (q.app x.obj x.val) (q.app y.obj y.val)
      (section_naturality q k) (a.app x.obj x.val) (b.app x.obj x.val)
      (congrArg (fun m : Z ⟶ yoneda.obj S => m.app x.obj x.val) ha)
      (congrArg (fun m : Z ⟶ yoneda.obj S => m.app x.obj x.val) hb)
      (a.app y.obj y.val) (b.app y.obj y.val)
      (section_naturality a k) (section_naturality b k)] at hn
    change evaluate (localHom D q a b ha hb y) ((rawFamily (D.obj i) a).map k p) =
      (rawFamily (D.obj j) b).map k (evaluate (localHom D q a b ha hb x) p)
    rw [rawFamily_map, rawFamily_map]
    exact hn.symm



lemma rawNat_precomp (D : (torsorPseudofunctor G).DescentData f)
    {Z W : Cᵒᵖ ⥤ Type u} (q : Z ⟶ yoneda.obj S) {i j : I}
    (a : Z ⟶ yoneda.obj (V i)) (b : Z ⟶ yoneda.obj (V j))
    (ha : a ≫ yoneda.map (f i) = q) (hb : b ≫ yoneda.map (f j) = q) (k : W ⟶ Z) :
    Functor.whiskerLeft k.mapElements (rawNat D q a b ha hb) =
      rawNat D (k ≫ q) (k ≫ a) (k ≫ b)
        (by rw [Category.assoc, ha]) (by rw [Category.assoc, hb]) := by
  ext x p
  rfl

def rawIso (D : (torsorPseudofunctor G).DescentData f)
    {Z : Cᵒᵖ ⥤ Type u} (q : Z ⟶ yoneda.obj S) {i j : I}
    (a : Z ⟶ yoneda.obj (V i)) (b : Z ⟶ yoneda.obj (V j))
    (ha : a ≫ yoneda.map (f i) = q) (hb : b ≫ yoneda.map (f j) = q) :
    rawFamily (D.obj i) a ≅ rawFamily (D.obj j) b where
  hom := rawNat D q a b ha hb
  inv := rawNat D q b a hb ha
  hom_inv_id := by
    ext x p
    change evaluate (localHom D q b a hb ha x) (evaluate (localHom D q a b ha hb x) p) = p
    rw [← evaluate_comp, localHom_comp, localHom_self, evaluate_id]
  inv_hom_id := by
    ext x p
    change evaluate (localHom D q a b ha hb x) (evaluate (localHom D q b a hb ha x) p) = p
    rw [← evaluate_comp, localHom_comp, localHom_self, evaluate_id]


def familyComparison {Z : Cᵒᵖ ⥤ Type u} {X : Sheaf J (Type u)} (P : Torsor G X)
    {a b : Z ⟶ X.obj} (h : a = b) :
    a.mapElements ⋙ P.family.family ≅ b.mapElements ⋙ P.family.family :=
  eqToIso (congrArg (fun m => m.mapElements ⋙ P.family.family) h)

lemma familyComparison_hom_app {Z : Cᵒᵖ ⥤ Type u} {X : Sheaf J (Type u)} (P : Torsor G X)
    {a b : Z ⟶ X.obj} (h : a = b) (x : Z.Elements) :
    (familyComparison P h).hom.app x = P.family.family.map
      (ElementFamilies.vertical _ (congrArg (fun m => m.app x.obj x.val) h)) := by
  subst b
  simp only [familyComparison, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    ElementFamilies.vertical_rfl, P.family.family.map_id]
  rfl

lemma familyComparison_equivariant {Z : Cᵒᵖ ⥤ Type u} {X : Sheaf J (Type u)}
    (P : Torsor G X) {a b : Z ⟶ X.obj}
    (h : a = b) (x : Z.Elements) (g : G.obj.obj x.obj) (p) :
    (familyComparison P h).hom.app x (P.act (a.mapElements.obj x) g p) =
      P.act (b.mapElements.obj x) g ((familyComparison P h).hom.app x p) := by
  rw [familyComparison_hom_app]
  exact vertical_act P _ g p


@[reassoc] lemma familyComparison_trans {Z : Cᵒᵖ ⥤ Type u} {X : Sheaf J (Type u)}
    (P : Torsor G X) {a b c : Z ⟶ X.obj} (h : a = b) (k : b = c) :
    (familyComparison P h).hom ≫ (familyComparison P k).hom =
      (familyComparison P (h.trans k)).hom := by
  subst b c
  simp [familyComparison]

@[reassoc] lemma familyComparison_natural {Z : Cᵒᵖ ⥤ Type u} {X : Sheaf J (Type u)}
    (P Q : Torsor G X) (t : P ⟶ Q) {a b : Z ⟶ X.obj} (h : a = b) :
    (familyComparison P h).hom ≫ Functor.whiskerLeft b.mapElements t.iso.hom =
      Functor.whiskerLeft a.mapElements t.iso.hom ≫ (familyComparison Q h).hom := by
  subst b
  simp [familyComparison]


lemma familyComparison_conjugate {Z : Cᵒᵖ ⥤ Type u} {X : Sheaf J (Type u)}
    (P Q : Torsor G X) (t : P ⟶ Q) {a b : Z ⟶ X.obj} (h : a = b) :
    Functor.whiskerLeft a.mapElements t.iso.hom =
      (familyComparison P h).hom ≫ Functor.whiskerLeft b.mapElements t.iso.hom ≫
        (familyComparison Q h.symm).hom := by
  subst b
  simp [familyComparison]

lemma whiskerLeft_eqToHom_reindex {Z : Cᵒᵖ ⥤ Type u} {X Y : Sheaf J (Type u)}
    (P : Torsor G X) (η : Z ⟶ Y.obj) {a b : Y ⟶ X} (h : a = b) :
    Functor.whiskerLeft η.mapElements (eqToHom (congrArg (reindex P) h)).iso.hom =
      (familyComparison P (congrArg (fun m => η ≫ m.hom) h)).hom := by
  subst b
  rfl

lemma whiskerLeft_familyComparison {Z W : Cᵒᵖ ⥤ Type u} {X : Sheaf J (Type u)}
    (P : Torsor G X) (k : W ⟶ Z) {a b : Z ⟶ X.obj} (h : a = b) :
    Functor.whiskerLeft k.mapElements (familyComparison P h).hom =
      (familyComparison P (congrArg (fun m => k ≫ m) h)).hom := by
  subst b
  rfl

lemma familyComparison_reindex {Z : Cᵒᵖ ⥤ Type u} {X Y : Sheaf J (Type u)}
    (P : Torsor G X) (t : Y ⟶ X) {a b : Z ⟶ Y.obj} (h : a = b) :
    (familyComparison (reindex P t) h).hom =
      (familyComparison P (congrArg (fun m => m ≫ t.hom) h)).hom := by
  subst b
  rfl

def comparisonToRaw {Z : Cᵒᵖ ⥤ Type u} {U : C} (P : Torsor G (represented U))
    (a : Z ⟶ yoneda.obj U) :
    (toSheafify J Z).mapElements ⋙
      (reindex P ((presheafToSheaf J (Type u)).map a)).family.family ≅ rawFamily P a :=
  familyComparison P (toSheafify_naturality J a).symm


lemma comparisonToRaw_hom {Z : Cᵒᵖ ⥤ Type u} {U : C} (P : Torsor G (represented U))
    (a : Z ⟶ yoneda.obj U) : (comparisonToRaw P a).hom =
      (familyComparison P (toSheafify_naturality J a).symm).hom := rfl

lemma comparisonToRaw_inv {Z : Cᵒᵖ ⥤ Type u} {U : C} (P : Torsor G (represented U))
    (a : Z ⟶ yoneda.obj U) : (comparisonToRaw P a).inv =
      (familyComparison P (toSheafify_naturality J a)).hom := rfl

lemma rawIso_hom (D : (torsorPseudofunctor G).DescentData f)
    {Z : Cᵒᵖ ⥤ Type u} (q : Z ⟶ yoneda.obj S) {i j : I}
    (a : Z ⟶ yoneda.obj (V i)) (b : Z ⟶ yoneda.obj (V j))
    (ha : a ≫ yoneda.map (f i) = q) (hb : b ≫ yoneda.map (f j) = q) :
    (rawIso D q a b ha hb).hom = rawNat D q a b ha hb := rfl

def sheafifyHom (D : (torsorPseudofunctor G).DescentData f)
    {Z : Cᵒᵖ ⥤ Type u} (q : Z ⟶ yoneda.obj S) {i j : I}
    (a : Z ⟶ yoneda.obj (V i)) (b : Z ⟶ yoneda.obj (V j))
    (ha : a ≫ yoneda.map (f i) = q) (hb : b ≫ yoneda.map (f j) = q) :
    reindex (D.obj i) ((presheafToSheaf J (Type u)).map a) ⟶
      reindex (D.obj j) ((presheafToSheaf J (Type u)).map b) :=
  LocalPresentation.extendArrow (toSheafify J Z) _ _
    ((comparisonToRaw (D.obj i) a) ≪≫ rawIso D q a b ha hb ≪≫
      (comparisonToRaw (D.obj j) b).symm) (by
      intro x g p
      change (comparisonToRaw (D.obj j) b).inv.app x
        (evaluate (localHom D q a b ha hb x)
          ((comparisonToRaw (D.obj i) a).hom.app x ((D.obj i).act _ g p))) = _
      rw [show (comparisonToRaw (D.obj i) a).hom =
        (familyComparison (D.obj i) (toSheafify_naturality J a).symm).hom from rfl]
      erw [familyComparison_equivariant, evaluate_equivariant]
      change (familyComparison (D.obj j) (toSheafify_naturality J b)).hom.app x
        ((D.obj j).act _ g _) = _
      erw [familyComparison_equivariant]
      rfl)



lemma sheafifyHom_restrict (D : (torsorPseudofunctor G).DescentData f)
    {Z : Cᵒᵖ ⥤ Type u} (q : Z ⟶ yoneda.obj S) {i j : I}
    (a : Z ⟶ yoneda.obj (V i)) (b : Z ⟶ yoneda.obj (V j))
    (ha : a ≫ yoneda.map (f i) = q) (hb : b ≫ yoneda.map (f j) = q) :
    Functor.whiskerLeft (toSheafify J Z).mapElements (sheafifyHom D q a b ha hb).iso.hom =
      (comparisonToRaw (D.obj i) a).hom ≫ (rawIso D q a b ha hb).hom ≫
        (comparisonToRaw (D.obj j) b).inv :=
  LocalPresentation.extendArrow_restrict _ _ _ _ _

lemma sheafifyHom_self (D : (torsorPseudofunctor G).DescentData f)
    {Z : Cᵒᵖ ⥤ Type u} (q : Z ⟶ yoneda.obj S) {i : I}
    (a : Z ⟶ yoneda.obj (V i)) (ha : a ≫ yoneda.map (f i) = q) :
    sheafifyHom D q a a ha ha = 𝟙 _ := by
  apply LocalPresentation.arrow_ext (toSheafify J Z)
  rw [sheafifyHom_restrict]
  have hh : (rawIso D q a a ha ha).hom = 𝟙 _ := by
    ext x p
    change evaluate (localHom D q a a ha ha x) p = p
    rw [localHom_self, evaluate_id]
  erw [hh, Category.id_comp, Iso.hom_inv_id]
  rfl

lemma sheafifyHom_comp (D : (torsorPseudofunctor G).DescentData f)
    {Z : Cᵒᵖ ⥤ Type u} (q : Z ⟶ yoneda.obj S) {i j k : I}
    (a : Z ⟶ yoneda.obj (V i)) (b : Z ⟶ yoneda.obj (V j))
    (c : Z ⟶ yoneda.obj (V k))
    (ha : a ≫ yoneda.map (f i) = q) (hb : b ≫ yoneda.map (f j) = q)
    (hc : c ≫ yoneda.map (f k) = q) :
    sheafifyHom D q a b ha hb ≫ sheafifyHom D q b c hb hc =
      sheafifyHom D q a c ha hc := by
  apply LocalPresentation.arrow_ext (toSheafify J Z)
  change Functor.whiskerLeft _ ((sheafifyHom D q a b ha hb).iso.hom ≫
    (sheafifyHom D q b c hb hc).iso.hom) = _
  rw [Functor.whiskerLeft_comp, sheafifyHom_restrict, sheafifyHom_restrict,
    sheafifyHom_restrict]
  have hh : (rawIso D q a b ha hb).hom ≫ (rawIso D q b c hb hc).hom =
      (rawIso D q a c ha hc).hom := by
    ext x p
    change evaluate (localHom D q b c hb hc x) (evaluate (localHom D q a b ha hb x) p) =
      evaluate (localHom D q a c ha hc x) p
    rw [← evaluate_comp, localHom_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (rawIso D q a b ha hb).hom, hh]

def pullArrow {X Y A B : Sheaf J (Type u)} (P : Torsor G A) (Q : Torsor G B)
    {a : X ⟶ A} {b : X ⟶ B} (h : reindex P a ⟶ reindex Q b)
    (t : Y ⟶ X) (ta : Y ⟶ A) (tb : Y ⟶ B)
    (ha : t ≫ a = ta) (hb : t ≫ b = tb) : reindex P ta ⟶ reindex Q tb :=
  eqToHom (congrArg (reindex P) ha.symm) ≫ h.reindex t ≫
    eqToHom (congrArg (reindex Q) hb)



lemma pullArrow_restrict {Z : Cᵒᵖ ⥤ Type u} {X Y A B : Sheaf J (Type u)}
    (P : Torsor G A) (Q : Torsor G B) {a : X ⟶ A} {b : X ⟶ B}
    (h : reindex P a ⟶ reindex Q b) (t : Y ⟶ X) (ta : Y ⟶ A) (tb : Y ⟶ B)
    (ha : t ≫ a = ta) (hb : t ≫ b = tb) (η : Z ⟶ Y.obj) :
    Functor.whiskerLeft η.mapElements (pullArrow P Q h t ta tb ha hb).iso.hom =
      (familyComparison P (congrArg (fun m => η ≫ m.hom) ha.symm)).hom ≫
      Functor.whiskerLeft (η ≫ t.hom).mapElements h.iso.hom ≫
      (familyComparison Q (congrArg (fun m => η ≫ m.hom) hb)).hom := by
  subst ta tb
  rfl

lemma pullArrow_reindex {X Y Z A B : Sheaf J (Type u)} (P : Torsor G A) (Q : Torsor G B)
    {a : X ⟶ A} {b : X ⟶ B} (h : reindex P a ⟶ reindex Q b)
    (t : Y ⟶ X) (ta : Y ⟶ A) (tb : Y ⟶ B)
    (ha : t ≫ a = ta) (hb : t ≫ b = tb) (k : Z ⟶ Y) :
    (pullArrow P Q h t ta tb ha hb).reindex k =
      pullArrow P Q h (k ≫ t) (k ≫ ta) (k ≫ tb)
        (by rw [Category.assoc, ha]) (by rw [Category.assoc, hb]) := by
  subst ta tb
  apply SheafTorsor.Arrow.ext
  ext x p
  rfl


lemma sheafifyHom_natural (D : (torsorPseudofunctor G).DescentData f)
    {Z W : Cᵒᵖ ⥤ Type u} (q : Z ⟶ yoneda.obj S) {i j : I}
    (a : Z ⟶ yoneda.obj (V i)) (b : Z ⟶ yoneda.obj (V j))
    (ha : a ≫ yoneda.map (f i) = q) (hb : b ≫ yoneda.map (f j) = q) (k : W ⟶ Z)
    (q' : W ⟶ yoneda.obj S) (ka : W ⟶ yoneda.obj (V i)) (kb : W ⟶ yoneda.obj (V j))
    (hq : k ≫ q = q') (hka : k ≫ a = ka) (hkb : k ≫ b = kb) :
    pullArrow (D.obj i) (D.obj j) (sheafifyHom D q a b ha hb)
      ((presheafToSheaf J (Type u)).map k)
      ((presheafToSheaf J (Type u)).map ka)
      ((presheafToSheaf J (Type u)).map kb)
      (((presheafToSheaf J (Type u)).map_comp k a).symm.trans
        (congrArg ((presheafToSheaf J (Type u)).map) hka))
      (((presheafToSheaf J (Type u)).map_comp k b).symm.trans
        (congrArg ((presheafToSheaf J (Type u)).map) hkb)) =
    sheafifyHom D q' ka kb
      (by rw [← hka, Category.assoc, ha, hq])
      (by rw [← hkb, Category.assoc, hb, hq]) := by
  subst q' ka kb
  apply LocalPresentation.arrow_ext (toSheafify J W)
  rw [pullArrow_restrict, sheafifyHom_restrict]
  rw [familyComparison_conjugate _ _ (sheafifyHom D q a b ha hb)
    (toSheafify_naturality J k).symm]
  have hw : Functor.whiskerLeft (k ≫ toSheafify J Z).mapElements
      (sheafifyHom D q a b ha hb).iso.hom =
      Functor.whiskerLeft k.mapElements
        (Functor.whiskerLeft (toSheafify J Z).mapElements
          (sheafifyHom D q a b ha hb).iso.hom) := rfl
  rw [hw, sheafifyHom_restrict, Functor.whiskerLeft_comp, Functor.whiskerLeft_comp]
  simp only [comparisonToRaw_hom, comparisonToRaw_inv, rawIso_hom]
  rw [rawNat_precomp, whiskerLeft_familyComparison, whiskerLeft_familyComparison,
    familyComparison_reindex, familyComparison_reindex]
  simp only [Category.assoc, familyComparison_trans_assoc, familyComparison_trans]


abbrev overlap (i j : I) : Cᵒᵖ ⥤ Type u :=
  pullback (yoneda.map (f i)) (yoneda.map (f j))

abbrev overlapFst (i j : I) : overlap (f := f) i j ⟶ yoneda.obj (V i) :=
  pullback.fst (yoneda.map (f i)) (yoneda.map (f j))

abbrev overlapSnd (i j : I) : overlap (f := f) i j ⟶ yoneda.obj (V j) :=
  pullback.snd (yoneda.map (f i)) (yoneda.map (f j))

def overlapHom (D : (torsorPseudofunctor G).DescentData f) (i j : I) :
    reindex (D.obj i) ((presheafToSheaf J (Type u)).map (overlapFst (f := f) i j)) ⟶
      reindex (D.obj j) ((presheafToSheaf J (Type u)).map (overlapSnd (f := f) i j)) :=
  sheafifyHom D (overlapFst i j ≫ yoneda.map (f i)) (overlapFst i j) (overlapSnd i j)
    rfl pullback.condition.symm

def overlapLift {Z : Sheaf J (Type u)} (q : Z ⟶ represented S) {i j : I}
    (a : Z ⟶ represented (V i)) (b : Z ⟶ represented (V j))
    (ha : a ≫ (SheafifiedYoneda.functor J).map (f i) = q)
    (hb : b ≫ (SheafifiedYoneda.functor J).map (f j) = q) :
    Z ⟶ (presheafToSheaf J (Type u)).obj (overlap (f := f) i j) :=
  pullback.lift a b (ha.trans hb.symm) ≫
    (PreservesPullback.iso (presheafToSheaf J (Type u))
      (yoneda.map (f i)) (yoneda.map (f j))).inv

lemma overlapLift_fst {Z : Sheaf J (Type u)} (q : Z ⟶ represented S) {i j : I}
    (a : Z ⟶ represented (V i)) (b : Z ⟶ represented (V j))
    (ha : a ≫ (SheafifiedYoneda.functor J).map (f i) = q)
    (hb : b ≫ (SheafifiedYoneda.functor J).map (f j) = q) :
    overlapLift q a b ha hb ≫ (presheafToSheaf J (Type u)).map (overlapFst i j) = a := by
  simp only [overlapLift, Category.assoc, overlapFst, PreservesPullback.iso_inv_fst]
  exact pullback.lift_fst _ _ _

lemma overlapLift_snd {Z : Sheaf J (Type u)} (q : Z ⟶ represented S) {i j : I}
    (a : Z ⟶ represented (V i)) (b : Z ⟶ represented (V j))
    (ha : a ≫ (SheafifiedYoneda.functor J).map (f i) = q)
    (hb : b ≫ (SheafifiedYoneda.functor J).map (f j) = q) :
    overlapLift q a b ha hb ≫ (presheafToSheaf J (Type u)).map (overlapSnd i j) = b := by
  simp only [overlapLift, Category.assoc, overlapSnd, PreservesPullback.iso_inv_snd]
  exact pullback.lift_snd _ _ _

def extendHom (D : (torsorPseudofunctor G).DescentData f)
    {Z : Sheaf J (Type u)} (q : Z ⟶ represented S) {i j : I}
    (a : Z ⟶ represented (V i)) (b : Z ⟶ represented (V j))
    (ha : a ≫ (SheafifiedYoneda.functor J).map (f i) = q)
    (hb : b ≫ (SheafifiedYoneda.functor J).map (f j) = q) :
    reindex (D.obj i) a ⟶ reindex (D.obj j) b :=
  pullArrow (D.obj i) (D.obj j) (overlapHom D i j) (overlapLift q a b ha hb) a b
    (overlapLift_fst q a b ha hb) (overlapLift_snd q a b ha hb)


lemma overlapLift_precomp {Z W : Sheaf J (Type u)} (q : Z ⟶ represented S) {i j : I}
    (a : Z ⟶ represented (V i)) (b : Z ⟶ represented (V j))
    (ha : a ≫ (SheafifiedYoneda.functor J).map (f i) = q)
    (hb : b ≫ (SheafifiedYoneda.functor J).map (f j) = q) (k : W ⟶ Z) :
    overlapLift (k ≫ q) (k ≫ a) (k ≫ b)
      (by rw [Category.assoc, ha]) (by rw [Category.assoc, hb]) =
      k ≫ overlapLift q a b ha hb := by
  unfold overlapLift
  conv_rhs => rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp

lemma extendHom_reindex (D : (torsorPseudofunctor G).DescentData f)
    {Z W : Sheaf J (Type u)} (q : Z ⟶ represented S) {i j : I}
    (a : Z ⟶ represented (V i)) (b : Z ⟶ represented (V j))
    (ha : a ≫ (SheafifiedYoneda.functor J).map (f i) = q)
    (hb : b ≫ (SheafifiedYoneda.functor J).map (f j) = q) (k : W ⟶ Z) :
    (extendHom D q a b ha hb).reindex k =
      extendHom D (k ≫ q) (k ≫ a) (k ≫ b)
        (by rw [Category.assoc, ha]) (by rw [Category.assoc, hb]) := by
  unfold extendHom
  rw [pullArrow_reindex]
  congr 1
  exact (overlapLift_precomp q a b ha hb k).symm


lemma overlapLift_sheafify {Z : Cᵒᵖ ⥤ Type u} (q : Z ⟶ yoneda.obj S) {i j : I}
    (a : Z ⟶ yoneda.obj (V i)) (b : Z ⟶ yoneda.obj (V j))
    (ha : a ≫ yoneda.map (f i) = q) (hb : b ≫ yoneda.map (f j) = q) :
    overlapLift ((presheafToSheaf J (Type u)).map q)
      ((presheafToSheaf J (Type u)).map a) ((presheafToSheaf J (Type u)).map b)
      (((presheafToSheaf J (Type u)).map_comp a (yoneda.map (f i))).symm.trans
        (congrArg ((presheafToSheaf J (Type u)).map) ha))
      (((presheafToSheaf J (Type u)).map_comp b (yoneda.map (f j))).symm.trans
        (congrArg ((presheafToSheaf J (Type u)).map) hb)) =
    (presheafToSheaf J (Type u)).map (pullback.lift a b (ha.trans hb.symm)) := by
  apply (cancel_mono (PreservesPullback.iso (presheafToSheaf J (Type u))
    (yoneda.map (f i)) (yoneda.map (f j))).hom).1
  apply pullback.hom_ext
  · simp only [Category.assoc, PreservesPullback.iso_hom_fst]
    rw [overlapLift_fst, ← Functor.map_comp, pullback.lift_fst]
  · simp only [Category.assoc, PreservesPullback.iso_hom_snd]
    rw [overlapLift_snd, ← Functor.map_comp, pullback.lift_snd]

lemma extendHom_sheafify (D : (torsorPseudofunctor G).DescentData f)
    {Z : Cᵒᵖ ⥤ Type u} (q : Z ⟶ yoneda.obj S) {i j : I}
    (a : Z ⟶ yoneda.obj (V i)) (b : Z ⟶ yoneda.obj (V j))
    (ha : a ≫ yoneda.map (f i) = q) (hb : b ≫ yoneda.map (f j) = q) :
    extendHom D ((presheafToSheaf J (Type u)).map q)
      ((presheafToSheaf J (Type u)).map a) ((presheafToSheaf J (Type u)).map b)
      (((presheafToSheaf J (Type u)).map_comp a (yoneda.map (f i))).symm.trans
        (congrArg ((presheafToSheaf J (Type u)).map) ha))
      (((presheafToSheaf J (Type u)).map_comp b (yoneda.map (f j))).symm.trans
        (congrArg ((presheafToSheaf J (Type u)).map) hb)) =
    sheafifyHom D q a b ha hb := by
  unfold extendHom
  have hn := sheafifyHom_natural D (overlapFst i j ≫ yoneda.map (f i))
    (overlapFst i j) (overlapSnd i j) rfl pullback.condition.symm
    (pullback.lift a b (ha.trans hb.symm)) q a b
    (by exact (pullback.lift_fst_assoc a b (ha.trans hb.symm) _).trans ha)
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  refine Eq.trans ?_ hn
  congr 1
  exact overlapLift_sheafify q a b ha hb




lemma extendHom_pull (D : (torsorPseudofunctor G).DescentData f)
    {Z W : Sheaf J (Type u)} (q : Z ⟶ represented S) {i j : I}
    (a : Z ⟶ represented (V i)) (b : Z ⟶ represented (V j))
    (ha : a ≫ (SheafifiedYoneda.functor J).map (f i) = q)
    (hb : b ≫ (SheafifiedYoneda.functor J).map (f j) = q) (k : W ⟶ Z)
    (q' : W ⟶ represented S) (ka : W ⟶ represented (V i)) (kb : W ⟶ represented (V j))
    (hq : k ≫ q = q') (hka : k ≫ a = ka) (hkb : k ≫ b = kb) :
    pullArrow (D.obj i) (D.obj j) (extendHom D q a b ha hb) k ka kb hka hkb =
      extendHom D q' ka kb
        (by rw [← hka, Category.assoc, ha, hq])
        (by rw [← hkb, Category.assoc, hb, hq]) := by
  subst q' ka kb
  exact extendHom_reindex D q a b ha hb k

lemma pullArrow_id {X Y A : Sheaf J (Type u)} (P : Torsor G A)
    (a : X ⟶ A) (k : Y ⟶ X) (ka : Y ⟶ A) (hka : k ≫ a = ka) :
    pullArrow P P (𝟙 (reindex P a)) k ka ka hka hka = 𝟙 _ := by
  subst ka
  apply SheafTorsor.Arrow.ext
  ext x p
  rfl

lemma extendHom_self (D : (torsorPseudofunctor G).DescentData f)
    {Z : Sheaf J (Type u)} (q : Z ⟶ represented S) {i : I}
    (a : Z ⟶ represented (V i))
    (ha : a ≫ (SheafifiedYoneda.functor J).map (f i) = q) :
    extendHom D q a a ha ha = 𝟙 _ := by
  have hbase := (extendHom_sheafify D (yoneda.map (f i)) (𝟙 (yoneda.obj (V i)))
    (𝟙 (yoneda.obj (V i))) (Category.id_comp _) (Category.id_comp _)).trans
      (sheafifyHom_self D (yoneda.map (f i)) (𝟙 _) (Category.id_comp _))
  have hka : a ≫ (presheafToSheaf J (Type u)).map (𝟙 (yoneda.obj (V i))) = a := by
    rw [CategoryTheory.Functor.map_id]
    exact Category.comp_id a
  have hn := extendHom_pull D ((presheafToSheaf J (Type u)).map (yoneda.map (f i)))
    ((presheafToSheaf J (Type u)).map (𝟙 (yoneda.obj (V i))))
    ((presheafToSheaf J (Type u)).map (𝟙 (yoneda.obj (V i))))
    (by rw [CategoryTheory.Functor.map_id, Category.id_comp]; rfl) (by rw [CategoryTheory.Functor.map_id, Category.id_comp]; rfl)
    a q a a ha hka hka
  rw [hbase, pullArrow_id] at hn
  exact hn.symm


def liftPresheafPullback {P Q R : Cᵒᵖ ⥤ Type u} (f : P ⟶ R) (g : Q ⟶ R)
    {Z : Sheaf J (Type u)} (a : Z ⟶ (presheafToSheaf J (Type u)).obj P)
    (b : Z ⟶ (presheafToSheaf J (Type u)).obj Q)
    (h : a ≫ (presheafToSheaf J (Type u)).map f =
      b ≫ (presheafToSheaf J (Type u)).map g) :
    Z ⟶ (presheafToSheaf J (Type u)).obj (pullback f g) :=
  pullback.lift a b h ≫ (PreservesPullback.iso (presheafToSheaf J (Type u)) f g).inv

lemma liftPresheafPullback_fst {P Q R : Cᵒᵖ ⥤ Type u} (f : P ⟶ R) (g : Q ⟶ R)
    {Z : Sheaf J (Type u)} (a : Z ⟶ (presheafToSheaf J (Type u)).obj P)
    (b : Z ⟶ (presheafToSheaf J (Type u)).obj Q)
    (h : a ≫ (presheafToSheaf J (Type u)).map f =
      b ≫ (presheafToSheaf J (Type u)).map g) :
    liftPresheafPullback f g a b h ≫ (presheafToSheaf J (Type u)).map (pullback.fst f g) = a := by
  simp only [liftPresheafPullback, Category.assoc, PreservesPullback.iso_inv_fst,
    pullback.lift_fst]

lemma liftPresheafPullback_snd {P Q R : Cᵒᵖ ⥤ Type u} (f : P ⟶ R) (g : Q ⟶ R)
    {Z : Sheaf J (Type u)} (a : Z ⟶ (presheafToSheaf J (Type u)).obj P)
    (b : Z ⟶ (presheafToSheaf J (Type u)).obj Q)
    (h : a ≫ (presheafToSheaf J (Type u)).map f =
      b ≫ (presheafToSheaf J (Type u)).map g) :
    liftPresheafPullback f g a b h ≫ (presheafToSheaf J (Type u)).map (pullback.snd f g) = b := by
  simp only [liftPresheafPullback, Category.assoc, PreservesPullback.iso_inv_snd,
    pullback.lift_snd]

lemma pullArrow_comp {X Y A B E : Sheaf J (Type u)}
    (P : Torsor G A) (Q : Torsor G B) (R : Torsor G E)
    {a : X ⟶ A} {b : X ⟶ B} {c : X ⟶ E}
    (h : reindex P a ⟶ reindex Q b) (l : reindex Q b ⟶ reindex R c)
    (t : Y ⟶ X) (ta : Y ⟶ A) (tb : Y ⟶ B) (tc : Y ⟶ E)
    (ha : t ≫ a = ta) (hb : t ≫ b = tb) (hc : t ≫ c = tc) :
    pullArrow P Q h t ta tb ha hb ≫ pullArrow Q R l t tb tc hb hc =
      pullArrow P R (h ≫ l) t ta tc ha hc := by
  subst ta tb tc
  apply SheafTorsor.Arrow.ext
  ext x p
  rfl


lemma extendHom_comp (D : (torsorPseudofunctor G).DescentData f)
    {Z : Sheaf J (Type u)} (q : Z ⟶ represented S) {i j k : I}
    (a : Z ⟶ represented (V i)) (b : Z ⟶ represented (V j))
    (c : Z ⟶ represented (V k))
    (ha : a ≫ (SheafifiedYoneda.functor J).map (f i) = q)
    (hb : b ≫ (SheafifiedYoneda.functor J).map (f j) = q)
    (hc : c ≫ (SheafifiedYoneda.functor J).map (f k) = q) :
    extendHom D q a b ha hb ≫ extendHom D q b c hb hc = extendHom D q a c ha hc := by
  let r := overlapSnd (f := f) i j
  let s := overlapFst (f := f) j k
  let R := pullback r s
  let pr : R ⟶ overlap (f := f) i j := pullback.fst r s
  let ps : R ⟶ overlap (f := f) j k := pullback.snd r s
  let a₀ := pr ≫ overlapFst (f := f) i j
  let b₀ := pr ≫ r
  let c₀ := ps ≫ overlapSnd (f := f) j k
  let q₀ := a₀ ≫ yoneda.map (f i)
  have ha₀ : a₀ ≫ yoneda.map (f i) = q₀ := rfl
  have hb₀ : b₀ ≫ yoneda.map (f j) = q₀ := by
    dsimp only [b₀, q₀, a₀, r, overlapFst, overlapSnd]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc]
  have hc₀ : c₀ ≫ yoneda.map (f k) = q₀ := by
    calc
      c₀ ≫ yoneda.map (f k) = ps ≫ s ≫ yoneda.map (f j) := by
        dsimp only [c₀, s, overlapFst, overlapSnd]
        rw [Category.assoc, pullback.condition]
      _ = b₀ ≫ yoneda.map (f j) := by
        dsimp only [b₀, pr, ps]
        rw [← Category.assoc, pullback.condition]
      _ = q₀ := hb₀
  let ab := overlapLift q a b ha hb
  let bc := overlapLift q b c hb hc
  have habc : ab ≫ (presheafToSheaf J (Type u)).map r =
      bc ≫ (presheafToSheaf J (Type u)).map s := by
    exact (overlapLift_snd q a b ha hb).trans (overlapLift_fst q b c hb hc).symm
  let t := liftPresheafPullback r s ab bc habc
  have hpr : t ≫ (presheafToSheaf J (Type u)).map pr = ab :=
    liftPresheafPullback_fst r s ab bc habc
  have hps : t ≫ (presheafToSheaf J (Type u)).map ps = bc :=
    liftPresheafPullback_snd r s ab bc habc
  have hta : t ≫ (presheafToSheaf J (Type u)).map a₀ = a := by
    dsimp only [a₀]
    rw [Functor.map_comp, ← Category.assoc, hpr]
    exact overlapLift_fst q a b ha hb
  have htb : t ≫ (presheafToSheaf J (Type u)).map b₀ = b := by
    dsimp only [b₀]
    rw [Functor.map_comp, ← Category.assoc, hpr]
    exact overlapLift_snd q a b ha hb
  have htc : t ≫ (presheafToSheaf J (Type u)).map c₀ = c := by
    dsimp only [c₀]
    rw [Functor.map_comp, ← Category.assoc, hps]
    exact overlapLift_snd q b c hb hc
  have htq : t ≫ (presheafToSheaf J (Type u)).map q₀ = q := by
    dsimp only [q₀]
    rw [Functor.map_comp, ← Category.assoc, hta]
    exact ha
  have hfa : (presheafToSheaf J (Type u)).map a₀ ≫
      (SheafifiedYoneda.functor J).map (f i) = (presheafToSheaf J (Type u)).map q₀ :=
    ((presheafToSheaf J (Type u)).map_comp a₀ (yoneda.map (f i))).symm
  have hfb : (presheafToSheaf J (Type u)).map b₀ ≫
      (SheafifiedYoneda.functor J).map (f j) = (presheafToSheaf J (Type u)).map q₀ :=
    ((presheafToSheaf J (Type u)).map_comp b₀ (yoneda.map (f j))).symm.trans
      (congrArg ((presheafToSheaf J (Type u)).map) hb₀)
  have hfc : (presheafToSheaf J (Type u)).map c₀ ≫
      (SheafifiedYoneda.functor J).map (f k) = (presheafToSheaf J (Type u)).map q₀ :=
    ((presheafToSheaf J (Type u)).map_comp c₀ (yoneda.map (f k))).symm.trans
      (congrArg ((presheafToSheaf J (Type u)).map) hc₀)
  have hs := sheafifyHom_comp D q₀ a₀ b₀ c₀ ha₀ hb₀ hc₀
  rw [← extendHom_sheafify D q₀ a₀ b₀ ha₀ hb₀,
    ← extendHom_sheafify D q₀ b₀ c₀ hb₀ hc₀,
    ← extendHom_sheafify D q₀ a₀ c₀ ha₀ hc₀] at hs
  have hh := congrArg (fun h => pullArrow (D.obj i) (D.obj k) h t a c hta htc) hs
  rw [← pullArrow_comp (D.obj i) (D.obj j) (D.obj k) _ _ t a b c hta htb htc] at hh
  rw [extendHom_pull D _ _ _ hfa hfb t q a b htq hta htb,
    extendHom_pull D _ _ _ hfb hfc t q b c htq htb htc,
    extendHom_pull D _ _ _ hfa hfc t q a c htq hta htc] at hh
  exact hh


/-- Original-site descent data extend to all sheaf tests, including their cocycle laws. -/
def extend (D : (torsorPseudofunctor G).DescentData f) :
    (SheafTorsor.Stack.pseudofunctor G).DescentData
      (fun i => (SheafifiedYoneda.functor J).map (f i)) where
  obj := D.obj
  hom Z q i j a b ha hb := extendHom D q a b ha hb
  pullHom_hom Z' Z k q q' hq i j a b ha hb ka kb hka hkb := by
    subst q' ka kb
    exact extendHom_reindex D q a b ha hb k
  hom_self Z q i a ha := extendHom_self D q a ha
  hom_comp Z q i j k a b c ha hb hc := extendHom_comp D q a b c ha hb hc


lemma rawNat_yoneda (D : (torsorPseudofunctor G).DescentData f)
    {U : C} (q : U ⟶ S) {i j : I} (a : U ⟶ V i) (b : U ⟶ V j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    rawNat D (yoneda.map q) (yoneda.map a) (yoneda.map b)
      (by rw [← yoneda.map_comp, ha]) (by rw [← yoneda.map_comp, hb]) =
    (comparisonToRaw (D.obj i) (yoneda.map a)).inv ≫
      Functor.whiskerLeft (toSheafify J (yoneda.obj U)).mapElements (D.hom q a b ha hb).iso.hom ≫
      (comparisonToRaw (D.obj j) (yoneda.map b)).hom := by
  ext x p
  simp only [NatTrans.comp_app, comparisonToRaw_inv, comparisonToRaw_hom,
    familyComparison_hom_app]
  change evaluate (D.hom (x.val ≫ q) (x.val ≫ a) (x.val ≫ b) _ _) p =
    evaluateAt (D.hom q a b ha hb) x.val p
  rw [← D.pullHom_hom x.val q (x.val ≫ q) rfl a b ha hb
    (x.val ≫ a) (x.val ≫ b) rfl rfl, evaluate_pullHom]

lemma extendHom_yoneda (D : (torsorPseudofunctor G).DescentData f)
    {U : C} (q : U ⟶ S) {i j : I} (a : U ⟶ V i) (b : U ⟶ V j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    extendHom D ((SheafifiedYoneda.functor J).map q)
      ((SheafifiedYoneda.functor J).map a) ((SheafifiedYoneda.functor J).map b)
      (by rw [← (SheafifiedYoneda.functor J).map_comp, ha])
      (by rw [← (SheafifiedYoneda.functor J).map_comp, hb]) = D.hom q a b ha hb := by
  erw [extendHom_sheafify D (yoneda.map q) (yoneda.map a) (yoneda.map b)
    (by rw [← yoneda.map_comp, ha]) (by rw [← yoneda.map_comp, hb])]
  apply LocalPresentation.arrow_ext (toSheafify J (yoneda.obj U))
  rw [sheafifyHom_restrict, rawIso_hom, rawNat_yoneda D q a b ha hb]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]


lemma whiskerLeft_reindex {Z : Cᵒᵖ ⥤ Type u} {X Y : Sheaf J (Type u)}
    {P Q : Torsor G X} (h : P ⟶ Q) (a : Y ⟶ X) (η : Z ⟶ Y.obj) :
    Functor.whiskerLeft η.mapElements (h.reindex a).iso.hom =
      Functor.whiskerLeft (η ≫ a.hom).mapElements h.iso.hom := rfl

@[reassoc] lemma rawNat_comm {D E : (torsorPseudofunctor G).DescentData f} (φ : D ⟶ E)
    {Z : Cᵒᵖ ⥤ Type u} (q : Z ⟶ yoneda.obj S) {i j : I}
    (a : Z ⟶ yoneda.obj (V i)) (b : Z ⟶ yoneda.obj (V j))
    (ha : a ≫ yoneda.map (f i) = q) (hb : b ≫ yoneda.map (f j) = q) :
    Functor.whiskerLeft (a ≫ toSheafify J (yoneda.obj (V i))).mapElements (φ.hom i).iso.hom ≫
      rawNat E q a b ha hb = rawNat D q a b ha hb ≫
      Functor.whiskerLeft (b ≫ toSheafify J (yoneda.obj (V j))).mapElements (φ.hom j).iso.hom := by
  ext x p
  have hc := congrArg (fun h => evaluate h p)
    (φ.comm (q.app x.obj x.val) (a.app x.obj x.val) (b.app x.obj x.val)
      (congrArg (fun m : Z ⟶ yoneda.obj S => m.app x.obj x.val) ha)
      (congrArg (fun m : Z ⟶ yoneda.obj S => m.app x.obj x.val) hb))
  change evaluate ((φ.hom i).reindex ((SheafifiedYoneda.functor J).map (a.app x.obj x.val)) ≫
    localHom E q a b ha hb x) p =
    evaluate (localHom D q a b ha hb x ≫
      (φ.hom j).reindex ((SheafifiedYoneda.functor J).map (b.app x.obj x.val))) p at hc
  rw [evaluate_comp, evaluate_comp, evaluate_reindex, evaluate_reindex] at hc
  exact hc


lemma sheafifyHom_comm {D E : (torsorPseudofunctor G).DescentData f} (φ : D ⟶ E)
    {Z : Cᵒᵖ ⥤ Type u} (q : Z ⟶ yoneda.obj S) {i j : I}
    (a : Z ⟶ yoneda.obj (V i)) (b : Z ⟶ yoneda.obj (V j))
    (ha : a ≫ yoneda.map (f i) = q) (hb : b ≫ yoneda.map (f j) = q) :
    (φ.hom i).reindex ((presheafToSheaf J (Type u)).map a) ≫ sheafifyHom E q a b ha hb =
      sheafifyHom D q a b ha hb ≫ (φ.hom j).reindex ((presheafToSheaf J (Type u)).map b) := by
  apply LocalPresentation.arrow_ext (toSheafify J Z)
  change Functor.whiskerLeft _ ((φ.hom i).reindex _).iso.hom ≫
      Functor.whiskerLeft _ (sheafifyHom E q a b ha hb).iso.hom =
    Functor.whiskerLeft _ (sheafifyHom D q a b ha hb).iso.hom ≫
      Functor.whiskerLeft _ ((φ.hom j).reindex _).iso.hom
  rw [sheafifyHom_restrict, sheafifyHom_restrict, whiskerLeft_reindex, whiskerLeft_reindex]
  simp only [comparisonToRaw_hom, comparisonToRaw_inv, rawIso_hom]
  rw [← familyComparison_natural_assoc (D.obj i) (E.obj i) (φ.hom i)
    (toSheafify_naturality J a).symm]
  simp only [Category.assoc]
  rw [rawNat_comm_assoc φ q a b ha hb]
  rw [familyComparison_natural (D.obj j) (E.obj j) (φ.hom j)
    (toSheafify_naturality J b)]

lemma pullArrow_comm {X Y A B : Sheaf J (Type u)}
    {P P' : Torsor G A} {Q Q' : Torsor G B} (φ : P ⟶ P') (ψ : Q ⟶ Q')
    {a : X ⟶ A} {b : X ⟶ B} (h : reindex P a ⟶ reindex Q b)
    (h' : reindex P' a ⟶ reindex Q' b) (hh : φ.reindex a ≫ h' = h ≫ ψ.reindex b)
    (t : Y ⟶ X) (ta : Y ⟶ A) (tb : Y ⟶ B)
    (ha : t ≫ a = ta) (hb : t ≫ b = tb) :
    φ.reindex ta ≫ pullArrow P' Q' h' t ta tb ha hb =
      pullArrow P Q h t ta tb ha hb ≫ ψ.reindex tb := by
  subst ta tb
  exact congrArg (fun m => m.reindex t) hh

lemma extendHom_comm {D E : (torsorPseudofunctor G).DescentData f} (φ : D ⟶ E)
    {Z : Sheaf J (Type u)} (q : Z ⟶ represented S) {i j : I}
    (a : Z ⟶ represented (V i)) (b : Z ⟶ represented (V j))
    (ha : a ≫ (SheafifiedYoneda.functor J).map (f i) = q)
    (hb : b ≫ (SheafifiedYoneda.functor J).map (f j) = q) :
    (φ.hom i).reindex a ≫ extendHom E q a b ha hb =
      extendHom D q a b ha hb ≫ (φ.hom j).reindex b :=
  pullArrow_comm (φ.hom i) (φ.hom j) _ _
    (sheafifyHom_comm φ _ _ _ rfl pullback.condition.symm) _ _ _ _ _

def extendFunctor : (torsorPseudofunctor G).DescentData f ⥤
    (SheafTorsor.Stack.pseudofunctor G).DescentData
      (fun i => (SheafifiedYoneda.functor J).map (f i)) where
  obj := extend
  map φ := { hom := φ.hom, comm := fun _ q _ _ a b ha hb => extendHom_comm φ q a b ha hb }

/-- The extension adds test objects without changing compatible morphisms. -/
def extendFullyFaithful : (extendFunctor (G := G) (f := f)).FullyFaithful where
  preimage {D E} φ :=
    { hom := φ.hom
      comm U q i j a b ha hb := by
        have hc := φ.comm ((SheafifiedYoneda.functor J).map q) ((SheafifiedYoneda.functor J).map a) ((SheafifiedYoneda.functor J).map b)
          (by rw [← (SheafifiedYoneda.functor J).map_comp, ha]) (by rw [← (SheafifiedYoneda.functor J).map_comp, hb])
        change (φ.hom i).reindex ((SheafifiedYoneda.functor J).map a) ≫
          extendHom E ((SheafifiedYoneda.functor J).map q) ((SheafifiedYoneda.functor J).map a) ((SheafifiedYoneda.functor J).map b) _ _ =
          extendHom D ((SheafifiedYoneda.functor J).map q) ((SheafifiedYoneda.functor J).map a) ((SheafifiedYoneda.functor J).map b) _ _ ≫
          (φ.hom j).reindex ((SheafifiedYoneda.functor J).map b) at hc
        rw [extendHom_yoneda, extendHom_yoneda] at hc
        exact hc }
  map_preimage _ := by apply Pseudofunctor.DescentData.hom_ext; intro i; rfl
  preimage_map _ := by apply Pseudofunctor.DescentData.hom_ext; intro i; rfl

set_option backward.defeqAttrib.useBackward true in
/-- Canonical original-site transitions are the transport of the equality of base maps. -/
lemma canonicalHom_eq (P : Torsor G (represented S))
    {U : C} (q : U ⟶ S) {i j : I} (a : U ⟶ V i) (b : U ⟶ V j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (((torsorPseudofunctor G).toDescentData f).obj P).hom q a b ha hb =
      eqToHom (congrArg (reindex P)
        (show (SheafifiedYoneda.functor J).map a ≫ (SheafifiedYoneda.functor J).map (f i) =
          (SheafifiedYoneda.functor J).map b ≫ (SheafifiedYoneda.functor J).map (f j) by rw [← (SheafifiedYoneda.functor J).map_comp,
            ← (SheafifiedYoneda.functor J).map_comp, ha, hb])) := by
  simp only [Pseudofunctor.toDescentData_obj, Pseudofunctor.DescentData.ofObj_hom,
    Pseudofunctor.mapComp', torsorPseudofunctor, Functor.toPseudofunctor'_mapComp,
    PrelaxFunctor.map₂Iso_eqToIso, Iso.trans_hom, Iso.trans_inv, eqToIso.hom,
    eqToIso.inv, eqToHom_trans, Cat.eqToHom_app]

set_option backward.defeqAttrib.useBackward true in
/-- Canonical sheaf-context transitions use the same equality transport. -/
lemma sheafCanonicalHom_eq {X : Sheaf J (Type u)} {Y : I → Sheaf J (Type u)}
    (f : ∀ i, Y i ⟶ X) (P : Torsor G X)
    {Z : Sheaf J (Type u)} (q : Z ⟶ X) {i j : I} (a : Z ⟶ Y i) (b : Z ⟶ Y j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (((SheafTorsor.Stack.pseudofunctor G).toDescentData f).obj P).hom q a b ha hb =
      eqToHom (congrArg (reindex P) (ha.trans hb.symm)) := by
  simp only [Pseudofunctor.toDescentData_obj, Pseudofunctor.DescentData.ofObj_hom,
    Pseudofunctor.mapComp', SheafTorsor.Stack.pseudofunctor, Functor.toPseudofunctor'_mapComp,
    PrelaxFunctor.map₂Iso_eqToIso, Iso.trans_hom, Iso.trans_inv, eqToIso.hom,
    eqToIso.inv, eqToHom_trans, Cat.eqToHom_app]


lemma rawCanonicalCondition {Z : Cᵒᵖ ⥤ Type u} (q : Z ⟶ yoneda.obj S) {i j : I}
    (a : Z ⟶ yoneda.obj (V i)) (b : Z ⟶ yoneda.obj (V j))
    (ha : a ≫ yoneda.map (f i) = q) (hb : b ≫ yoneda.map (f j) = q) :
    (a ≫ toSheafify J (yoneda.obj (V i))) ≫ ((SheafifiedYoneda.functor J).map (f i)).hom =
      (b ≫ toSheafify J (yoneda.obj (V j))) ≫ ((SheafifiedYoneda.functor J).map (f j)).hom := by
  change (a ≫ toSheafify J (yoneda.obj (V i))) ≫
      ((presheafToSheaf J (Type u)).map (yoneda.map (f i))).hom =
    (b ≫ toSheafify J (yoneda.obj (V j))) ≫
      ((presheafToSheaf J (Type u)).map (yoneda.map (f j))).hom
  rw [Category.assoc, Category.assoc, ← toSheafify_naturality, ← toSheafify_naturality,
    ← Category.assoc, ← Category.assoc, ha, hb]

lemma rawNat_canonical (P : Torsor G (represented S))
    {Z : Cᵒᵖ ⥤ Type u} (q : Z ⟶ yoneda.obj S) {i j : I}
    (a : Z ⟶ yoneda.obj (V i)) (b : Z ⟶ yoneda.obj (V j))
    (ha : a ≫ yoneda.map (f i) = q) (hb : b ≫ yoneda.map (f j) = q) :
    rawNat (((torsorPseudofunctor G).toDescentData f).obj P) q a b ha hb =
      (familyComparison P (rawCanonicalCondition q a b ha hb)).hom := by
  ext x p
  rw [familyComparison_hom_app]
  change evaluate ((((torsorPseudofunctor G).toDescentData f).obj P).hom
    (q.app x.obj x.val) (a.app x.obj x.val) (b.app x.obj x.val) _ _) p = _
  rw [canonicalHom_eq]
  dsimp only [evaluate]
  have he : (SheafifiedYoneda.functor J).map (a.app x.obj x.val) ≫
      (SheafifiedYoneda.functor J).map (f i) =
      (SheafifiedYoneda.functor J).map (b.app x.obj x.val) ≫
        (SheafifiedYoneda.functor J).map (f j) := by
    rw [← (SheafifiedYoneda.functor J).map_comp, ← (SheafifiedYoneda.functor J).map_comp]
    exact congrArg (SheafifiedYoneda.functor J).map
      ((congrArg (fun m : Z ⟶ yoneda.obj S => m.app x.obj x.val) ha).trans
        (congrArg (fun m : Z ⟶ yoneda.obj S => m.app x.obj x.val) hb).symm)
  rw [eqToHom_reindex_app P he]
  change (P.family.family.map _ ≫ P.family.family.map _ ≫ P.family.family.map _) p =
    P.family.family.map _ p
  congr 1
  rw [← P.family.family.map_comp, ← P.family.family.map_comp]
  apply congrArg ConcreteCategory.hom
  apply congrArg P.family.family.map
  apply Functor.Elements.hom_ext
  simp [ElementFamilies.vertical]


lemma sheafCanonicalCondition {Z : Cᵒᵖ ⥤ Type u} (q : Z ⟶ yoneda.obj S) {i j : I}
    (a : Z ⟶ yoneda.obj (V i)) (b : Z ⟶ yoneda.obj (V j))
    (ha : a ≫ yoneda.map (f i) = q) (hb : b ≫ yoneda.map (f j) = q) :
    (presheafToSheaf J (Type u)).map a ≫ (SheafifiedYoneda.functor J).map (f i) =
      (presheafToSheaf J (Type u)).map b ≫ (SheafifiedYoneda.functor J).map (f j) :=
  ((presheafToSheaf J (Type u)).map_comp a (yoneda.map (f i))).symm.trans
    ((congrArg ((presheafToSheaf J (Type u)).map) (ha.trans hb.symm)).trans
      ((presheafToSheaf J (Type u)).map_comp b (yoneda.map (f j))))

lemma sheafifyHom_canonical (P : Torsor G (represented S))
    {Z : Cᵒᵖ ⥤ Type u} (q : Z ⟶ yoneda.obj S) {i j : I}
    (a : Z ⟶ yoneda.obj (V i)) (b : Z ⟶ yoneda.obj (V j))
    (ha : a ≫ yoneda.map (f i) = q) (hb : b ≫ yoneda.map (f j) = q) :
    sheafifyHom (((torsorPseudofunctor G).toDescentData f).obj P) q a b ha hb =
      eqToHom (congrArg (reindex P) (sheafCanonicalCondition q a b ha hb)) := by
  apply LocalPresentation.arrow_ext (toSheafify J Z)
  rw [sheafifyHom_restrict, whiskerLeft_eqToHom_reindex P (toSheafify J Z)
    (sheafCanonicalCondition q a b ha hb)]
  simp only [comparisonToRaw_hom, comparisonToRaw_inv, rawIso_hom, rawNat_canonical]
  erw [familyComparison_reindex, familyComparison_reindex]
  simp only [familyComparison_trans]

lemma pullArrow_eqToHom {X Y A B T : Sheaf J (Type u)} (P : Torsor G T)
    (f : A ⟶ T) (g : B ⟶ T) (a : X ⟶ A) (b : X ⟶ B) (h : a ≫ f = b ≫ g)
    (t : Y ⟶ X) (ta : Y ⟶ A) (tb : Y ⟶ B)
    (ha : t ≫ a = ta) (hb : t ≫ b = tb) (ht : ta ≫ f = tb ≫ g) :
    pullArrow (reindex P f) (reindex P g) (eqToHom (congrArg (reindex P) h))
      t ta tb ha hb = eqToHom (congrArg (reindex P) ht) := by
  unfold pullArrow
  change eqToHom _ ≫ (restriction (G := G) t).map
    (eqToHom (congrArg (reindex P) h)) ≫ eqToHom _ = _
  rw [eqToHom_map, eqToHom_trans, eqToHom_trans]

lemma extendCanonicalHom (P : Torsor G (represented S))
    {Z : Sheaf J (Type u)} (q : Z ⟶ represented S) {i j : I}
    (a : Z ⟶ represented (V i)) (b : Z ⟶ represented (V j))
    (ha : a ≫ (SheafifiedYoneda.functor J).map (f i) = q)
    (hb : b ≫ (SheafifiedYoneda.functor J).map (f j) = q) :
    extendHom (((torsorPseudofunctor G).toDescentData f).obj P) q a b ha hb =
      (((SheafTorsor.Stack.pseudofunctor G).toDescentData
        (fun i => (SheafifiedYoneda.functor J).map (f i))).obj P).hom q a b ha hb := by
  unfold extendHom overlapHom
  rw [sheafifyHom_canonical, sheafCanonicalHom_eq]
  exact pullArrow_eqToHom P _ _ _ _
    (sheafCanonicalCondition (overlapFst i j ≫ yoneda.map (f i))
      (overlapFst i j) (overlapSnd i j) rfl pullback.condition.symm)
    _ _ _ _ _ (ha.trans hb.symm)

/-- The comparison with canonical descent retains the actual restriction functor. -/
def canonicalIso : (torsorPseudofunctor G).toDescentData f ⋙ extendFunctor ≅
    (SheafTorsor.Stack.pseudofunctor G).toDescentData (fun i => (SheafifiedYoneda.functor J).map (f i)) :=
  NatIso.ofComponents (fun P => Pseudofunctor.DescentData.isoMk (fun _ => Iso.refl _)
    (by
      intro Z q i j a b ha hb
      change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
      exact (extendCanonicalHom P q a b ha hb).symm))
    (by
      intro P Q h
      apply Pseudofunctor.DescentData.hom_ext
      intro i
      change (h.reindex ((SheafifiedYoneda.functor J).map (f i)) :
        reindex P ((SheafifiedYoneda.functor J).map (f i)) ⟶ reindex Q ((SheafifiedYoneda.functor J).map (f i))) ≫
        𝟙 (reindex Q ((SheafifiedYoneda.functor J).map (f i))) =
        𝟙 (reindex P ((SheafifiedYoneda.functor J).map (f i))) ≫ (h.reindex ((SheafifiedYoneda.functor J).map (f i)) :
          reindex P ((SheafifiedYoneda.functor J).map (f i)) ⟶ reindex Q ((SheafifiedYoneda.functor J).map (f i)))
      rw [Category.id_comp, Category.comp_id])


end TorsorExtension
theorem isEquivalence_of_comparison
    {A B D : Type*} [Category A] [Category B] [Category D]
    (F : A ⥤ B) (E : B ⥤ D) (H : A ⥤ D)
    (hE : E.FullyFaithful) (e : F ⋙ E ≅ H) [H.IsEquivalence] : F.IsEquivalence := by
  let : E.Full := hE.full
  let : E.Faithful := hE.faithful
  let : (F ⋙ E).IsEquivalence := Functor.isEquivalence_of_iso e.symm
  let : F.Full := Functor.Full.of_comp_faithful F E
  let : F.Faithful := Functor.Faithful.of_comp F E
  let : F.EssSurj := Functor.essSurj_of_comp_fully_faithful F E
  exact {}

/-- Every original covering family has effective torsor descent. -/
theorem torsor_isEquivalence_toDescentData (G : Sheaf J GrpCat.{u})
    {I : Type u} {U : C} {V : I → C} (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ J U) :
    ((torsorPseudofunctor G).toDescentData f).IsEquivalence := by
  let : ((SheafTorsor.Stack.pseudofunctor G).toDescentData
      (fun i => (SheafifiedYoneda.functor J).map (f i))).IsEquivalence :=
    ((SheafTorsor.Stack.pseudofunctor G).isStackFor_ofArrows_iff _).mp
      (SheafFamilyDescent.torsor_isStackFor G _ (SheafifiedYoneda.jointlyLocallySurjective J f hf))
  exact isEquivalence_of_comparison _ _ _ TorsorExtension.extendFullyFaithful
    TorsorExtension.canonicalIso

instance torsor_isStack (G : Sheaf J GrpCat.{u}) : (torsorPseudofunctor G).IsStack J := by
  apply Pseudofunctor.IsStack.of_isStackFor
  intro U R hR
  rw [Pseudofunctor.isStackFor_iff]
  exact torsor_isEquivalence_toDescentData G (fun g : R.arrows.category => g.obj.hom)
    (by simpa only [Sieve.ofArrows_category] using hR)

end SquareKit.SheafifiedSheafStack
