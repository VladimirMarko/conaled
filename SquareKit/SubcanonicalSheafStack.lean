import SquareKit.SheafFamilyDescent
import Mathlib.CategoryTheory.Sites.Subcanonical

/-! Restriction of sheaf-context torsor and quotient stacks to a subcanonical site. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.SubcanonicalSheafStack
open CategoryTheory Limits Opposite
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} [J.Subcanonical]

/-- The local lifting sieve of a represented family is the pullback of its generated sieve. -/
theorem yoneda_imageSieve {I : Type u} {U : C} {V : I → C} (f : ∀ i, V i ⟶ U)
    {W : C} (g : W ⟶ U) :
    SheafFamilyCover.imageSieve (fun i => J.yoneda.map (f i)) g =
      (Sieve.ofArrows V f).pullback g := by
  ext T k
  constructor
  · rintro ⟨i, a, h⟩
    exact ⟨_, a, _, ⟨i⟩, h⟩
  · rintro ⟨T, a, b, ⟨i⟩, h⟩
    exact ⟨i, a, h⟩

/-- Original covering families become jointly locally-surjective sheaf families. -/
theorem yoneda_jointlyLocallySurjective {I : Type u} {U : C} {V : I → C}
    (f : ∀ i, V i ⟶ U) (hf : Sieve.ofArrows V f ∈ J U) :
    SheafFamilyCover.JointlyLocallySurjective (fun i => J.yoneda.map (f i)) := by
  intro W g
  rw [yoneda_imageSieve]
  exact J.pullback_stable g hf

/-- The covering condition is also reflected by the represented generic section. -/
theorem yoneda_jointlyLocallySurjective_iff {I : Type u} {U : C} {V : I → C}
    (f : ∀ i, V i ⟶ U) :
    SheafFamilyCover.JointlyLocallySurjective (fun i => J.yoneda.map (f i)) ↔
      Sieve.ofArrows V f ∈ J U := by
  refine ⟨fun h => ?_, yoneda_jointlyLocallySurjective f⟩
  simpa [yoneda_imageSieve] using h (𝟙 U)

/-- The original-site torsor functor keeps every equivariant arrow. -/
abbrev torsorFunctor (G : Sheaf J GrpCat.{u}) : Cᵒᵖ ⥤ Cat :=
  J.yoneda.op ⋙ SheafTorsor.Stack.functor G

/-- The induced torsor pseudofunctor, including identity and composition coherence. -/
abbrev torsorPseudofunctor (G : Sheaf J GrpCat.{u}) := (torsorFunctor G).toPseudofunctor'

/-- Restriction of the action quotient retains the equivariant target map. -/
abbrev quotientFunctor {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)}
    (a : SheafActionQuotient.Action G M) : Cᵒᵖ ⥤ Cat :=
  J.yoneda.op ⋙ SheafActionQuotient.Stack.functor a

/-- The induced action-quotient pseudofunctor. -/
abbrev quotientPseudofunctor {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)}
    (a : SheafActionQuotient.Action G M) := (quotientFunctor a).toPseudofunctor'

@[simp] theorem torsor_reindex_id (G : Sheaf J GrpCat.{u}) {U : C}
    (P : SheafTorsor.Torsor G (J.yoneda.obj U)) :
    SheafTorsor.reindex P (J.yoneda.map (𝟙 U)) = P := by simp

@[simp] theorem torsor_reindex_comp (G : Sheaf J GrpCat.{u}) {U V W : C}
    (f : V ⟶ U) (g : W ⟶ V) (P : SheafTorsor.Torsor G (J.yoneda.obj U)) :
    SheafTorsor.reindex (SheafTorsor.reindex P (J.yoneda.map f)) (J.yoneda.map g) =
      SheafTorsor.reindex P (J.yoneda.map (g ≫ f)) := by simp

@[simp] theorem quotient_reindex_id {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)}
    (a : SheafActionQuotient.Action G M) {U : C}
    (P : SheafActionQuotient.Object a (J.yoneda.obj U)) :
    SheafActionQuotient.reindex P (J.yoneda.map (𝟙 U)) = P := by simp

@[simp] theorem quotient_reindex_comp {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)}
    (a : SheafActionQuotient.Action G M) {U V W : C} (f : V ⟶ U) (g : W ⟶ V)
    (P : SheafActionQuotient.Object a (J.yoneda.obj U)) :
    SheafActionQuotient.reindex (SheafActionQuotient.reindex P (J.yoneda.map f)) (J.yoneda.map g) =
      SheafActionQuotient.reindex P (J.yoneda.map (g ≫ f)) := by simp

namespace TorsorExtension
open SheafTorsor
variable {G : Sheaf J GrpCat.{u}}

omit [J.Subcanonical] in
lemma eqToHom_reindex_app {X Y : Sheaf J (Type u)} (P : Torsor G X)
    {f g : Y ⟶ X} (h : f = g) (x : Y.obj.Elements) :
    (eqToHom (congrArg (reindex P) h)).iso.hom.app x =
      P.family.family.map (ElementFamilies.vertical X.obj
        (congrArg (fun k : Y ⟶ X => k.hom.app x.obj x.val) h)) := by
  subst g
  simp only [eqToHom_refl, ElementFamilies.vertical_rfl]
  change 𝟙 _ = P.family.family.map (𝟙 _)
  rw [P.family.family.map_id]

def compositionIso {V U W : C} (P : Torsor G (J.yoneda.obj V))
    (f : U ⟶ V) (k : W ⟶ U) :
    reindex P (J.yoneda.map (k ≫ f)) ≅ reindex (reindex P (J.yoneda.map f)) (J.yoneda.map k) :=
  eqToIso (by rw [J.yoneda.map_comp]; rfl)

lemma compositionIso_hom_app {V U W : C} (P : Torsor G (J.yoneda.obj V))
    (f : U ⟶ V) (k : W ⟶ U) (x : (J.yoneda.obj W).obj.Elements) :
    (compositionIso P f k).hom.iso.hom.app x =
      P.family.family.map (ElementFamilies.vertical _ (Category.assoc x.val k f).symm) := by
  exact eqToHom_reindex_app P (J.yoneda.map_comp k f) x

lemma compositionIso_inv_app {V U W : C} (P : Torsor G (J.yoneda.obj V))
    (f : U ⟶ V) (k : W ⟶ U) (x : (J.yoneda.obj W).obj.Elements) :
    (compositionIso P f k).inv.iso.hom.app x =
      P.family.family.map (ElementFamilies.vertical _ (Category.assoc x.val k f)) := by
  exact eqToHom_reindex_app P (J.yoneda.map_comp k f).symm x

lemma pullHom_eq {V W U T : C} {P : Torsor G (J.yoneda.obj V)}
    {Q : Torsor G (J.yoneda.obj W)} {f : U ⟶ V} {g : U ⟶ W}
    (h : reindex P (J.yoneda.map f) ⟶ reindex Q (J.yoneda.map g)) (k : T ⟶ U) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := torsorPseudofunctor G)
      h k (k ≫ f) (k ≫ g) =
    (compositionIso P f k).hom ≫ h.reindex (J.yoneda.map k) ≫ (compositionIso Q g k).inv := by
  simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    Pseudofunctor.mapComp', torsorPseudofunctor, Functor.toPseudofunctor'_mapComp,
    PrelaxFunctor.map₂Iso_eqToIso, Iso.trans_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv,
    eqToHom_trans, Cat.eqToHom_app]
  rfl

/-- The fiber over an arrow, without a choice of pullback model. -/
abbrev fiber {V : C} (P : Torsor G (J.yoneda.obj V)) {U : C} (f : U ⟶ V) :=
  P.family.family.obj ((J.yoneda.obj V).obj.elementsMk (op U) f)

/-- Evaluation at a generic represented section, with the unit transport displayed. -/
def evaluate {V W U : C} {P : Torsor G (J.yoneda.obj V)}
    {Q : Torsor G (J.yoneda.obj W)} {f : U ⟶ V} {g : U ⟶ W}
    (h : reindex P (J.yoneda.map f) ⟶ reindex Q (J.yoneda.map g)) :
    fiber P f → fiber Q g := fun p =>
  Q.family.family.map (ElementFamilies.vertical _ (Category.id_comp g))
    (h.iso.hom.app ((J.yoneda.obj U).obj.elementsMk (op U) (𝟙 U))
      (P.family.family.map (ElementFamilies.vertical _ (Category.id_comp f).symm) p))

lemma evaluate_id {V U : C} {P : Torsor G (J.yoneda.obj V)} (f : U ⟶ V)
    (p : fiber P f) : evaluate (𝟙 (reindex P (J.yoneda.map f))) p = p := by
  change P.family.family.map _ (P.family.family.map _ p) = p
  rw [← ConcreteCategory.comp_apply, ← P.family.family.map_comp]
  have h : ElementFamilies.vertical (J.yoneda.obj V).obj (Category.id_comp f).symm ≫
      ElementFamilies.vertical _ (Category.id_comp f) = 𝟙 _ := by
    apply Functor.Elements.hom_ext
    simp [ElementFamilies.vertical]
  rw [h, P.family.family.map_id]
  rfl

lemma evaluate_comp {V W T U : C} {P : Torsor G (J.yoneda.obj V)}
    {Q : Torsor G (J.yoneda.obj W)} {R : Torsor G (J.yoneda.obj T)}
    {f : U ⟶ V} {g : U ⟶ W} {k : U ⟶ T}
    (h : reindex P (J.yoneda.map f) ⟶ reindex Q (J.yoneda.map g))
    (l : reindex Q (J.yoneda.map g) ⟶ reindex R (J.yoneda.map k)) (p : fiber P f) :
    evaluate (h ≫ l) p = evaluate l (evaluate h p) := by
  dsimp only [evaluate]
  change R.family.family.map _
      (l.iso.hom.app ((J.yoneda.obj U).obj.elementsMk (op U) (𝟙 U))
        (h.iso.hom.app ((J.yoneda.obj U).obj.elementsMk (op U) (𝟙 U))
          (P.family.family.map (ElementFamilies.vertical _ (Category.id_comp f).symm) p))) =
    R.family.family.map _
      (l.iso.hom.app ((J.yoneda.obj U).obj.elementsMk (op U) (𝟙 U))
        (Q.family.family.map (ElementFamilies.vertical _ (Category.id_comp g).symm)
          (Q.family.family.map (ElementFamilies.vertical _ (Category.id_comp g))
            (h.iso.hom.app ((J.yoneda.obj U).obj.elementsMk (op U) (𝟙 U))
              (P.family.family.map (ElementFamilies.vertical _ (Category.id_comp f).symm) p)))))
  have hh : ElementFamilies.vertical (J.yoneda.obj W).obj (Category.id_comp g) ≫
      ElementFamilies.vertical _ (Category.id_comp g).symm = 𝟙 _ := by
    apply Functor.Elements.hom_ext
    simp [ElementFamilies.vertical]
  have cancel (q : fiber Q (𝟙 U ≫ g)) :
      Q.family.family.map (ElementFamilies.vertical _ (Category.id_comp g).symm)
        (Q.family.family.map (ElementFamilies.vertical _ (Category.id_comp g)) q) = q := by
    rw [← ConcreteCategory.comp_apply, ← Q.family.family.map_comp, hh, Q.family.family.map_id]
    rfl
  rw [cancel]

/-- Pulling a transition back and evaluating generically equals evaluation at that arrow. -/
lemma evaluate_pullHom {V W U T : C} {P : Torsor G (J.yoneda.obj V)}
    {Q : Torsor G (J.yoneda.obj W)} {f : U ⟶ V} {g : U ⟶ W}
    (h : reindex P (J.yoneda.map f) ⟶ reindex Q (J.yoneda.map g)) (k : T ⟶ U)
    (p : fiber P (k ≫ f)) :
    evaluate (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
      (F := torsorPseudofunctor G) h k (k ≫ f) (k ≫ g)) p =
      h.iso.hom.app ((J.yoneda.obj U).obj.elementsMk (op T) k) p := by
  rw [pullHom_eq]
  let x := (J.yoneda.obj U).obj.elementsMk (op T) (𝟙 T ≫ k)
  let y := (J.yoneda.obj U).obj.elementsMk (op T) k
  let e : x ⟶ y := ElementFamilies.vertical _ (Category.id_comp k)
  let ei : y ⟶ x := ElementFamilies.vertical _ (Category.id_comp k).symm
  have ha :
      P.family.family.map (ElementFamilies.vertical _ (Category.id_comp (k ≫ f)).symm) ≫
        P.family.family.map (ElementFamilies.vertical _ (Category.assoc (𝟙 T) k f).symm) =
      (reindex P (J.yoneda.map f)).family.family.map ei := by
    rw [← P.family.family.map_comp]
    change P.family.family.map _ = P.family.family.map _
    congr 1
    apply Functor.Elements.hom_ext
    simp [ei, ElementFamilies.vertical]
  have hb :
      Q.family.family.map (ElementFamilies.vertical _ (Category.assoc (𝟙 T) k g)) ≫
        Q.family.family.map (ElementFamilies.vertical _ (Category.id_comp (k ≫ g))) =
      (reindex Q (J.yoneda.map g)).family.family.map e := by
    rw [← Q.family.family.map_comp]
    change Q.family.family.map _ = Q.family.family.map _
    congr 1
    apply Functor.Elements.hom_ext
    simp [e, ElementFamilies.vertical]
  change Q.family.family.map (ElementFamilies.vertical _ (Category.id_comp (k ≫ g)))
    ((compositionIso Q g k).inv.iso.hom.app ((J.yoneda.obj T).obj.elementsMk (op T) (𝟙 T))
      (h.iso.hom.app x
        ((compositionIso P f k).hom.iso.hom.app ((J.yoneda.obj T).obj.elementsMk (op T) (𝟙 T))
          (P.family.family.map (ElementFamilies.vertical _ (Category.id_comp (k ≫ f)).symm) p)))) = _
  rw [compositionIso_hom_app, compositionIso_inv_app]
  change (Q.family.family.map _ ≫ Q.family.family.map _)
      (h.iso.hom.app x ((P.family.family.map _ ≫ P.family.family.map _) p)) = _
  rw [ha, hb]
  erw [h.iso.hom.naturality_apply ei p]
  change (reindex Q (J.yoneda.map g)).family.family.map e
    ((reindex Q (J.yoneda.map g)).family.family.map ei (h.iso.hom.app y p)) = _
  have he : ei ≫ e = 𝟙 y := by
    apply Functor.Elements.hom_ext
    simp [ei, e, x, y, ElementFamilies.vertical]
  have hz := congrArg (fun m => m (h.iso.hom.app y p))
    ((reindex Q (J.yoneda.map g)).family.family.map_comp ei e)
  rw [he, (reindex Q (J.yoneda.map g)).family.family.map_id] at hz
  exact hz.symm

/-- Restriction of an arrow-indexed fiber, including a specified equality of composites. -/
def fiberRestriction {V U W : C} (P : Torsor G (J.yoneda.obj V))
    {f : U ⟶ V} (k : W ⟶ U) {kf : W ⟶ V} (hkf : k ≫ f = kf) :
    fiber P f ⟶ fiber P kf :=
  P.family.family.map (Functor.Elements.homMk k.op hkf)

/-- Generic evaluation respects the actual original-site pullback operation. -/
lemma evaluate_natural {V W U T : C} {P : Torsor G (J.yoneda.obj V)}
    {Q : Torsor G (J.yoneda.obj W)} {f : U ⟶ V} {g : U ⟶ W}
    (h : reindex P (J.yoneda.map f) ⟶ reindex Q (J.yoneda.map g)) (k : T ⟶ U)
    (kf : T ⟶ V) (kg : T ⟶ W) (hkf : k ≫ f = kf) (hkg : k ≫ g = kg)
    (p : fiber P f) :
    fiberRestriction Q k hkg (evaluate h p) =
      evaluate (Pseudofunctor.LocallyDiscreteOpToCat.pullHom
        (F := torsorPseudofunctor G) h k kf kg hkf hkg) (fiberRestriction P k hkf p) := by
  subst kf kg
  rw [evaluate_pullHom]
  let t : (J.yoneda.obj U).obj.elementsMk (op U) (𝟙 U) ⟶
      (J.yoneda.obj U).obj.elementsMk (op T) k :=
    Functor.Elements.homMk k.op (Category.comp_id k)
  have hp : P.family.family.map (ElementFamilies.vertical _ (Category.id_comp f).symm) ≫
      (reindex P (J.yoneda.map f)).family.family.map t = fiberRestriction P k rfl := by
    change P.family.family.map _ ≫ P.family.family.map _ = P.family.family.map _
    rw [← P.family.family.map_comp]
    congr 1
    apply Functor.Elements.hom_ext
    simp [t, ElementFamilies.vertical]
  have hq : Q.family.family.map (ElementFamilies.vertical _ (Category.id_comp g)) ≫
      fiberRestriction Q k rfl = (reindex Q (J.yoneda.map g)).family.family.map t := by
    change Q.family.family.map _ ≫ Q.family.family.map _ = Q.family.family.map _
    rw [← Q.family.family.map_comp]
    congr 1
    apply Functor.Elements.hom_ext
    simp [t, ElementFamilies.vertical]
  change (Q.family.family.map (ElementFamilies.vertical _ (Category.id_comp g)) ≫
      fiberRestriction Q k rfl)
      (h.iso.hom.app ((J.yoneda.obj U).obj.elementsMk (op U) (𝟙 U))
        (P.family.family.map (ElementFamilies.vertical _ (Category.id_comp f).symm) p)) = _
  rw [hq]
  erw [← h.iso.hom.naturality_apply t]
  change h.iso.hom.app _ ((P.family.family.map _ ≫
      (reindex P (J.yoneda.map f)).family.family.map t) p) = _
  rw [hp]
  rfl

omit [J.Subcanonical] in
/-- Vertical fiber transport does not change the acting group section. -/
lemma vertical_act {X : Sheaf J (Type u)} (P : Torsor G X) {U : Cᵒᵖ}
    {x y : X.obj.obj U} (h : x = y) (g : G.obj.obj U)
    (p : P.family.family.obj (X.obj.elementsMk U x)) :
    P.family.family.map (ElementFamilies.vertical _ h) (P.act _ g p) =
      P.act _ g (P.family.family.map (ElementFamilies.vertical _ h) p) := by
  simpa [ElementFamilies.vertical] using P.natural (ElementFamilies.vertical _ h) g p

lemma evaluate_equivariant {V W U : C} {P : Torsor G (J.yoneda.obj V)}
    {Q : Torsor G (J.yoneda.obj W)} {f : U ⟶ V} {g : U ⟶ W}
    (h : reindex P (J.yoneda.map f) ⟶ reindex Q (J.yoneda.map g))
    (a : G.obj.obj (op U)) (p : fiber P f) :
    evaluate h (P.act _ a p) = Q.act _ a (evaluate h p) := by
  dsimp only [evaluate]
  rw [vertical_act]
  change Q.family.family.map _ (h.iso.hom.app _ ((reindex P (J.yoneda.map f)).act ((J.yoneda.obj U).obj.elementsMk (op U) (𝟙 U)) a _)) = _
  rw [h.equivariant]
  change Q.family.family.map _
    (Q.act ((J.yoneda.obj W).obj.elementsMk (op U) (𝟙 U ≫ g)) a _) = _
  rw [vertical_act]

lemma evaluate_reindex {V U : C} {P Q : Torsor G (J.yoneda.obj V)}
    (h : P ⟶ Q) (f : U ⟶ V) (p : fiber P f) :
    evaluate (h.reindex (J.yoneda.map f)) p =
      h.iso.hom.app ((J.yoneda.obj V).obj.elementsMk (op U) f) p := by
  let x := (J.yoneda.obj V).obj.elementsMk (op U) (𝟙 U ≫ f)
  let y := (J.yoneda.obj V).obj.elementsMk (op U) f
  let e : x ⟶ y := ElementFamilies.vertical _ (Category.id_comp f)
  let ei : y ⟶ x := ElementFamilies.vertical _ (Category.id_comp f).symm
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

/-- Naturality of a map to a representable, expressed as composition in the site. -/
lemma section_naturality {Z : Sheaf J (Type u)} {U : C} (a : Z ⟶ J.yoneda.obj U)
    {x y : Z.obj.Elements} (k : x ⟶ y) :
    k.hom.unop ≫ a.hom.app x.obj x.val = a.hom.app y.obj y.val := by
  have h := a.hom.naturality_apply k.hom x.val
  change a.hom.app y.obj (Z.obj.map k.hom x.val) =
    k.hom.unop ≫ a.hom.app x.obj x.val at h
  rw [k.map_val] at h
  exact h.symm

/-- A transition on the represented test object determined by one section. -/
def localHom (D : (torsorPseudofunctor G).DescentData f)
    {Z : Sheaf J (Type u)} (q : Z ⟶ J.yoneda.obj S) {i j : I}
    (a : Z ⟶ J.yoneda.obj (V i)) (b : Z ⟶ J.yoneda.obj (V j))
    (ha : a ≫ J.yoneda.map (f i) = q) (hb : b ≫ J.yoneda.map (f j) = q)
    (x : Z.obj.Elements) :
    reindex (D.obj i) (J.yoneda.map (a.hom.app x.obj x.val)) ⟶
      reindex (D.obj j) (J.yoneda.map (b.hom.app x.obj x.val)) :=
  D.hom (q.hom.app x.obj x.val) (a.hom.app x.obj x.val) (b.hom.app x.obj x.val)
    (congrArg (fun m : Z ⟶ J.yoneda.obj S => m.hom.app x.obj x.val) ha)
    (congrArg (fun m : Z ⟶ J.yoneda.obj S => m.hom.app x.obj x.val) hb)

lemma localHom_self (D : (torsorPseudofunctor G).DescentData f)
    {Z : Sheaf J (Type u)} (q : Z ⟶ J.yoneda.obj S) {i : I}
    (a : Z ⟶ J.yoneda.obj (V i)) (ha : a ≫ J.yoneda.map (f i) = q)
    (x : Z.obj.Elements) : localHom D q a a ha ha x = 𝟙 _ :=
  D.hom_self _ _ (congrArg (fun m : Z ⟶ J.yoneda.obj S => m.hom.app x.obj x.val) ha)

lemma localHom_comp (D : (torsorPseudofunctor G).DescentData f)
    {Z : Sheaf J (Type u)} (q : Z ⟶ J.yoneda.obj S) {i j k : I}
    (a : Z ⟶ J.yoneda.obj (V i)) (b : Z ⟶ J.yoneda.obj (V j))
    (c : Z ⟶ J.yoneda.obj (V k))
    (ha : a ≫ J.yoneda.map (f i) = q) (hb : b ≫ J.yoneda.map (f j) = q)
    (hc : c ≫ J.yoneda.map (f k) = q) (x : Z.obj.Elements) :
    localHom D q a b ha hb x ≫ localHom D q b c hb hc x =
      localHom D q a c ha hc x := D.hom_comp _ _ _ _ _ _ _

/-- Transition maps on arbitrary sheaf tests are obtained by represented generic evaluation. -/
def extendNat (D : (torsorPseudofunctor G).DescentData f)
    {Z : Sheaf J (Type u)} (q : Z ⟶ J.yoneda.obj S) {i j : I}
    (a : Z ⟶ J.yoneda.obj (V i)) (b : Z ⟶ J.yoneda.obj (V j))
    (ha : a ≫ J.yoneda.map (f i) = q) (hb : b ≫ J.yoneda.map (f j) = q) :
    (reindex (D.obj i) a).family.family ⟶ (reindex (D.obj j) b).family.family where
  app x := ↾evaluate (localHom D q a b ha hb x)
  naturality {x y} k := by
    apply ConcreteCategory.hom_ext
    intro p
    have hn := evaluate_natural (localHom D q a b ha hb x) k.hom.unop
      (a.hom.app y.obj y.val) (b.hom.app y.obj y.val)
      (section_naturality a k) (section_naturality b k) p
    dsimp only [localHom] at hn
    rw [D.pullHom_hom k.hom.unop (q.hom.app x.obj x.val) (q.hom.app y.obj y.val)
      (section_naturality q k) (a.hom.app x.obj x.val) (b.hom.app x.obj x.val)
      (congrArg (fun m : Z ⟶ J.yoneda.obj S => m.hom.app x.obj x.val) ha)
      (congrArg (fun m : Z ⟶ J.yoneda.obj S => m.hom.app x.obj x.val) hb)
      (a.hom.app y.obj y.val) (b.hom.app y.obj y.val)
      (section_naturality a k) (section_naturality b k)] at hn
    exact hn.symm

/-- The extension preserves inverse transitions and the group action. -/
def extendHom (D : (torsorPseudofunctor G).DescentData f)
    {Z : Sheaf J (Type u)} (q : Z ⟶ J.yoneda.obj S) {i j : I}
    (a : Z ⟶ J.yoneda.obj (V i)) (b : Z ⟶ J.yoneda.obj (V j))
    (ha : a ≫ J.yoneda.map (f i) = q) (hb : b ≫ J.yoneda.map (f j) = q) :
    reindex (D.obj i) a ⟶ reindex (D.obj j) b where
  iso :=
    { hom := extendNat D q a b ha hb
      inv := extendNat D q b a hb ha
      hom_inv_id := by
        ext x p
        change evaluate (localHom D q b a hb ha x) (evaluate (localHom D q a b ha hb x) p) = p
        rw [← evaluate_comp, localHom_comp, localHom_self, evaluate_id]
      inv_hom_id := by
        ext x p
        change evaluate (localHom D q a b ha hb x) (evaluate (localHom D q b a hb ha x) p) = p
        rw [← evaluate_comp, localHom_comp, localHom_self, evaluate_id] }
  equivariant x g p := evaluate_equivariant (localHom D q a b ha hb x) g p

/-- Extend original-site descent data to all sheaf test objects. -/
def extend (D : (torsorPseudofunctor G).DescentData f) :
    (SheafTorsor.Stack.pseudofunctor G).DescentData (fun i => J.yoneda.map (f i)) where
  obj := D.obj
  hom Z q i j a b ha hb := extendHom D q a b ha hb
  pullHom_hom Z' Z k q q' hq i j a b ha hb ka kb hka hkb := by
    subst q' ka kb
    change (extendHom D q a b ha hb).reindex k = extendHom D (k ≫ q) (k ≫ a) (k ≫ b) _ _
    apply SheafTorsor.Arrow.ext
    ext x p
    rfl
  hom_self Z q i a ha := by
    apply SheafTorsor.Arrow.ext
    ext x p
    change evaluate (localHom D q a a ha ha x) p = p
    rw [localHom_self, evaluate_id]
  hom_comp Z q i j k a b c ha hb hc := by
    apply SheafTorsor.Arrow.ext
    ext x p
    change evaluate (localHom D q b c hb hc x) (evaluate (localHom D q a b ha hb x) p) =
      evaluate (localHom D q a c ha hc x) p
    rw [← evaluate_comp, localHom_comp]

/-- On represented test objects the extension recovers the supplied transition exactly. -/
lemma extendHom_yoneda (D : (torsorPseudofunctor G).DescentData f)
    {U : C} (q : U ⟶ S) {i j : I} (a : U ⟶ V i) (b : U ⟶ V j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    extendHom D (J.yoneda.map q) (J.yoneda.map a) (J.yoneda.map b)
      (by rw [← J.yoneda.map_comp, ha]) (by rw [← J.yoneda.map_comp, hb]) =
      D.hom q a b ha hb := by
  apply SheafTorsor.Arrow.ext
  ext x p
  change evaluate (D.hom (x.val ≫ q) (x.val ≫ a) (x.val ≫ b) _ _) p =
    (D.hom q a b ha hb).iso.hom.app x p
  rw [← D.pullHom_hom x.val q (x.val ≫ q) rfl a b ha hb
    (x.val ≫ a) (x.val ≫ b) rfl rfl]
  exact evaluate_pullHom (D.hom q a b ha hb) x.val p

/-- Extension carries all compatible equivariant arrows, with their original components. -/
def extendFunctor : (torsorPseudofunctor G).DescentData f ⥤
    (SheafTorsor.Stack.pseudofunctor G).DescentData (fun i => J.yoneda.map (f i)) where
  obj := extend
  map {D E} φ :=
    { hom := φ.hom
      comm Z q i j a b ha hb := by
        apply SheafTorsor.Arrow.ext
        ext x p
        have hc := congrArg (fun h => evaluate h p)
          (φ.comm (q.hom.app x.obj x.val) (a.hom.app x.obj x.val) (b.hom.app x.obj x.val)
            (congrArg (fun m : Z ⟶ J.yoneda.obj S => m.hom.app x.obj x.val) ha)
            (congrArg (fun m : Z ⟶ J.yoneda.obj S => m.hom.app x.obj x.val) hb))
        change evaluate ((φ.hom i).reindex (J.yoneda.map (a.hom.app x.obj x.val)) ≫
          localHom E q a b ha hb x) p =
          evaluate (localHom D q a b ha hb x ≫
            (φ.hom j).reindex (J.yoneda.map (b.hom.app x.obj x.val))) p at hc
        rw [evaluate_comp, evaluate_comp, evaluate_reindex, evaluate_reindex] at hc
        exact hc }

/-- The extension adds test objects without changing compatible morphisms. -/
def extendFullyFaithful : (extendFunctor (G := G) (f := f)).FullyFaithful where
  preimage {D E} φ :=
    { hom := φ.hom
      comm U q i j a b ha hb := by
        have hc := φ.comm (J.yoneda.map q) (J.yoneda.map a) (J.yoneda.map b)
          (by rw [← J.yoneda.map_comp, ha]) (by rw [← J.yoneda.map_comp, hb])
        change (φ.hom i).reindex (J.yoneda.map a) ≫
          extendHom E (J.yoneda.map q) (J.yoneda.map a) (J.yoneda.map b) _ _ =
          extendHom D (J.yoneda.map q) (J.yoneda.map a) (J.yoneda.map b) _ _ ≫
          (φ.hom j).reindex (J.yoneda.map b) at hc
        rw [extendHom_yoneda, extendHom_yoneda] at hc
        exact hc }
  map_preimage _ := by apply Pseudofunctor.DescentData.hom_ext; intro i; rfl
  preimage_map _ := by apply Pseudofunctor.DescentData.hom_ext; intro i; rfl

/-- Canonical original-site transitions are the transport of the equality of base maps. -/
lemma canonicalHom_eq (P : Torsor G (J.yoneda.obj S))
    {U : C} (q : U ⟶ S) {i j : I} (a : U ⟶ V i) (b : U ⟶ V j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (((torsorPseudofunctor G).toDescentData f).obj P).hom q a b ha hb =
      eqToHom (congrArg (reindex P)
        (show J.yoneda.map a ≫ J.yoneda.map (f i) =
          J.yoneda.map b ≫ J.yoneda.map (f j) by rw [← J.yoneda.map_comp,
            ← J.yoneda.map_comp, ha, hb])) := by
  simp only [Pseudofunctor.toDescentData_obj, Pseudofunctor.DescentData.ofObj_hom,
    Pseudofunctor.mapComp', torsorPseudofunctor, Functor.toPseudofunctor'_mapComp,
    PrelaxFunctor.map₂Iso_eqToIso, Iso.trans_hom, Iso.trans_inv, eqToIso.hom,
    eqToIso.inv, eqToHom_trans, Cat.eqToHom_app]

omit [J.Subcanonical] in
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

/-- Extension commutes with the canonical descent transition on every sheaf test. -/
lemma extendCanonicalHom (P : Torsor G (J.yoneda.obj S))
    {Z : Sheaf J (Type u)} (q : Z ⟶ J.yoneda.obj S) {i j : I}
    (a : Z ⟶ J.yoneda.obj (V i)) (b : Z ⟶ J.yoneda.obj (V j))
    (ha : a ≫ J.yoneda.map (f i) = q) (hb : b ≫ J.yoneda.map (f j) = q) :
    extendHom (((torsorPseudofunctor G).toDescentData f).obj P) q a b ha hb =
      (((SheafTorsor.Stack.pseudofunctor G).toDescentData
        (fun i => J.yoneda.map (f i))).obj P).hom q a b ha hb := by
  apply SheafTorsor.Arrow.ext
  ext x p
  change evaluate ((((torsorPseudofunctor G).toDescentData f).obj P).hom
      (q.hom.app x.obj x.val) (a.hom.app x.obj x.val) (b.hom.app x.obj x.val) _ _) p = _
  rw [canonicalHom_eq, sheafCanonicalHom_eq]
  dsimp only [evaluate]
  have he : J.yoneda.map (a.hom.app x.obj x.val) ≫ J.yoneda.map (f i) =
      J.yoneda.map (b.hom.app x.obj x.val) ≫ J.yoneda.map (f j) := by
    rw [← J.yoneda.map_comp, ← J.yoneda.map_comp]
    exact congrArg J.yoneda.map ((congrArg (fun m : Z ⟶ J.yoneda.obj S =>
      m.hom.app x.obj x.val) ha).trans (congrArg (fun m : Z ⟶ J.yoneda.obj S =>
      m.hom.app x.obj x.val) hb).symm)
  rw [eqToHom_reindex_app P he, eqToHom_reindex_app P (ha.trans hb.symm)]
  change (P.family.family.map _ ≫ P.family.family.map _ ≫ P.family.family.map _) p =
    P.family.family.map _ p
  congr 1
  rw [← P.family.family.map_comp, ← P.family.family.map_comp]
  apply congrArg ConcreteCategory.hom
  apply congrArg P.family.family.map
  apply Functor.Elements.hom_ext
  simp [ElementFamilies.vertical]

/-- The comparison with canonical descent retains the actual restriction functor. -/
def canonicalIso : (torsorPseudofunctor G).toDescentData f ⋙ extendFunctor ≅
    (SheafTorsor.Stack.pseudofunctor G).toDescentData (fun i => J.yoneda.map (f i)) :=
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
      change (h.reindex (J.yoneda.map (f i)) :
        reindex P (J.yoneda.map (f i)) ⟶ reindex Q (J.yoneda.map (f i))) ≫
        𝟙 (reindex Q (J.yoneda.map (f i))) =
        𝟙 (reindex P (J.yoneda.map (f i))) ≫ (h.reindex (J.yoneda.map (f i)) :
          reindex P (J.yoneda.map (f i)) ⟶ reindex Q (J.yoneda.map (f i)))
      rw [Category.id_comp, Category.comp_id])

end TorsorExtension

namespace QuotientExtension
open SheafActionQuotient
variable {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)}
variable {act : Action G M}

omit [J.Subcanonical] in
lemma eqToHom_torsorArrow {X : Sheaf J (Type u)} {P Q : Object act X} (h : P = Q) :
    (eqToHom h).torsorArrow = eqToHom (congrArg Object.torsor h) := by
  subst Q
  rfl

lemma pullHom_torsorArrow {V W U T : C} {P : Object act (J.yoneda.obj V)}
    {Q : Object act (J.yoneda.obj W)} {f : U ⟶ V} {g : U ⟶ W}
    (h : reindex P (J.yoneda.map f) ⟶ reindex Q (J.yoneda.map g)) (k : T ⟶ U)
    (kf : T ⟶ V) (kg : T ⟶ W) (hkf : k ≫ f = kf) (hkg : k ≫ g = kg) :
    (Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := quotientPseudofunctor act)
      h k kf kg hkf hkg).torsorArrow =
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := torsorPseudofunctor G)
      h.torsorArrow k kf kg hkf hkg := by
  simp only [Pseudofunctor.LocallyDiscreteOpToCat.pullHom,
    Pseudofunctor.mapComp', quotientPseudofunctor, torsorPseudofunctor,
    Functor.toPseudofunctor'_mapComp, PrelaxFunctor.map₂Iso_eqToIso,
    Iso.trans_hom, Iso.trans_inv, eqToIso.hom, eqToIso.inv, eqToHom_trans,
    Cat.eqToHom_app]
  have hf : reindex P (J.yoneda.map kf) =
      reindex (reindex P (J.yoneda.map f)) (J.yoneda.map k) := by
    rw [← hkf, J.yoneda.map_comp]
    rfl
  have hg : reindex (reindex Q (J.yoneda.map g)) (J.yoneda.map k) =
      reindex Q (J.yoneda.map kg) := by
    rw [← hkg, J.yoneda.map_comp]
    rfl
  change (forget (a := act) (X := J.yoneda.obj T)).map
    (eqToHom hf ≫ h.reindex (J.yoneda.map k) ≫ eqToHom hg) = _
  simp only [Functor.map_comp, eqToHom_map]
  rfl

variable {I : Type u} {S : C} {V : I → C} {f : ∀ i, V i ⟶ S}

/-- Forget only the equivariant target map when extending quotient transitions. -/
def underlyingData (D : (quotientPseudofunctor act).DescentData f) :
    (torsorPseudofunctor G).DescentData f where
  obj i := (D.obj i).torsor
  hom U q i j a b ha hb := (D.hom q a b ha hb).torsorArrow
  pullHom_hom U' U k q q' hq i j a b ha hb ka kb hka hkb := by
    rw [← pullHom_torsorArrow]
    exact congrArg (fun h => h.torsorArrow) (D.pullHom_hom k q q' hq a b ha hb ka kb hka hkb)
  hom_self U q i a ha := congrArg (fun h => h.torsorArrow) (D.hom_self q a ha)
  hom_comp U q i j k a b c ha hb hc :=
    congrArg (fun h => h.torsorArrow) (D.hom_comp q a b c ha hb hc)

def underlyingHom {D E : (quotientPseudofunctor act).DescentData f} (φ : D ⟶ E) :
    underlyingData D ⟶ underlyingData E where
  hom i := (φ.hom i).torsorArrow
  comm _U q _i _j a b ha hb := congrArg (fun h => h.torsorArrow) (φ.comm q a b ha hb)

omit [J.Subcanonical] in
lemma value_vertical {X : Sheaf J (Type u)} (P : Object act X) {U : Cᵒᵖ}
    {x y : X.obj.obj U} (h : x = y)
    (p : P.torsor.family.family.obj (X.obj.elementsMk U x)) :
    P.value (X.obj.elementsMk U y) (P.torsor.family.family.map (ElementFamilies.vertical _ h) p) =
      P.value (X.obj.elementsMk U x) p := by
  simpa [ElementFamilies.vertical] using (P.natural (ElementFamilies.vertical _ h) p).symm

lemma evaluate_preserves {V W U : C} {P : Object act (J.yoneda.obj V)}
    {Q : Object act (J.yoneda.obj W)} {a : U ⟶ V} {b : U ⟶ W}
    (h : reindex P (J.yoneda.map a) ⟶ reindex Q (J.yoneda.map b))
    (p : TorsorExtension.fiber P.torsor a) :
    Q.value ((J.yoneda.obj W).obj.elementsMk (op U) b) (TorsorExtension.evaluate h.torsorArrow p) =
      P.value ((J.yoneda.obj V).obj.elementsMk (op U) a) p := by
  dsimp only [TorsorExtension.evaluate]
  rw [value_vertical]
  change (reindex Q (J.yoneda.map b)).value ((J.yoneda.obj U).obj.elementsMk (op U) (𝟙 U))
      (h.torsorArrow.iso.hom.app _ _) = _
  rw [h.preserves]
  change P.value _ (P.torsor.family.family.map _ p) = _
  rw [value_vertical]

/-- Quotient transitions retain the same target values during represented evaluation. -/
def extendHom (D : (quotientPseudofunctor act).DescentData f)
    {Z : Sheaf J (Type u)} (q : Z ⟶ J.yoneda.obj S) {i j : I}
    (a : Z ⟶ J.yoneda.obj (V i)) (b : Z ⟶ J.yoneda.obj (V j))
    (ha : a ≫ J.yoneda.map (f i) = q) (hb : b ≫ J.yoneda.map (f j) = q) :
    reindex (D.obj i) a ⟶ reindex (D.obj j) b where
  torsorArrow := TorsorExtension.extendHom (underlyingData D) q a b ha hb
  preserves x p := evaluate_preserves
    (D.hom (q.hom.app x.obj x.val) (a.hom.app x.obj x.val) (b.hom.app x.obj x.val)
      (congrArg (fun m : Z ⟶ J.yoneda.obj S => m.hom.app x.obj x.val) ha)
      (congrArg (fun m : Z ⟶ J.yoneda.obj S => m.hom.app x.obj x.val) hb)) p

/-- Extend original-site quotient descent data, including the target maps. -/
def extend (D : (quotientPseudofunctor act).DescentData f) :
    (SheafActionQuotient.Stack.pseudofunctor act).DescentData (fun i => J.yoneda.map (f i)) where
  obj := D.obj
  hom Z q i j a b ha hb := extendHom D q a b ha hb
  pullHom_hom Z' Z k q q' hq i j a b ha hb ka kb hka hkb := by
    subst q' ka kb
    change (extendHom D q a b ha hb).reindex k = extendHom D (k ≫ q) (k ≫ a) (k ≫ b) _ _
    apply SheafActionQuotient.Arrow.ext
    exact (TorsorExtension.extend (underlyingData D)).pullHom_hom k q (k ≫ q) rfl
      a b ha hb (k ≫ a) (k ≫ b) rfl rfl
  hom_self Z q i a ha := by
    apply SheafActionQuotient.Arrow.ext
    exact (TorsorExtension.extend (underlyingData D)).hom_self q a ha
  hom_comp Z q i j k a b c ha hb hc := by
    apply SheafActionQuotient.Arrow.ext
    exact (TorsorExtension.extend (underlyingData D)).hom_comp q a b c ha hb hc

lemma extendHom_yoneda (D : (quotientPseudofunctor act).DescentData f)
    {U : C} (q : U ⟶ S) {i j : I} (a : U ⟶ V i) (b : U ⟶ V j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    extendHom D (J.yoneda.map q) (J.yoneda.map a) (J.yoneda.map b)
      (by rw [← J.yoneda.map_comp, ha]) (by rw [← J.yoneda.map_comp, hb]) =
      D.hom q a b ha hb := by
  apply SheafActionQuotient.Arrow.ext
  exact TorsorExtension.extendHom_yoneda (underlyingData D) q a b ha hb

/-- Extension retains every compatible quotient arrow. -/
def extendFunctor : (quotientPseudofunctor act).DescentData f ⥤
    (SheafActionQuotient.Stack.pseudofunctor act).DescentData (fun i => J.yoneda.map (f i)) where
  obj := extend
  map {D E} φ :=
    { hom := φ.hom
      comm Z q i j a b ha hb := by
        apply SheafActionQuotient.Arrow.ext
        exact ((TorsorExtension.extendFunctor).map (underlyingHom φ)).comm q a b ha hb }

/-- Adding sheaf test objects does not identify or remove quotient arrows. -/
def extendFullyFaithful : (extendFunctor (act := act) (f := f)).FullyFaithful where
  preimage {D E} φ :=
    { hom := φ.hom
      comm U q i j a b ha hb := by
        have hc := φ.comm (J.yoneda.map q) (J.yoneda.map a) (J.yoneda.map b)
          (by rw [← J.yoneda.map_comp, ha]) (by rw [← J.yoneda.map_comp, hb])
        change (φ.hom i).reindex (J.yoneda.map a) ≫
          extendHom E (J.yoneda.map q) (J.yoneda.map a) (J.yoneda.map b) _ _ =
          extendHom D (J.yoneda.map q) (J.yoneda.map a) (J.yoneda.map b) _ _ ≫
          (φ.hom j).reindex (J.yoneda.map b) at hc
        rw [extendHom_yoneda, extendHom_yoneda] at hc
        exact hc }
  map_preimage _ := by apply Pseudofunctor.DescentData.hom_ext; intro i; rfl
  preimage_map _ := by apply Pseudofunctor.DescentData.hom_ext; intro i; rfl

lemma canonicalHom_eq (P : Object act (J.yoneda.obj S))
    {U : C} (q : U ⟶ S) {i j : I} (a : U ⟶ V i) (b : U ⟶ V j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (((quotientPseudofunctor act).toDescentData f).obj P).hom q a b ha hb =
      eqToHom (congrArg (reindex P)
        (show J.yoneda.map a ≫ J.yoneda.map (f i) =
          J.yoneda.map b ≫ J.yoneda.map (f j) by rw [← J.yoneda.map_comp,
            ← J.yoneda.map_comp, ha, hb])) := by
  simp only [Pseudofunctor.toDescentData_obj, Pseudofunctor.DescentData.ofObj_hom,
    Pseudofunctor.mapComp', quotientPseudofunctor, Functor.toPseudofunctor'_mapComp,
    PrelaxFunctor.map₂Iso_eqToIso, Iso.trans_hom, Iso.trans_inv, eqToIso.hom,
    eqToIso.inv, eqToHom_trans, Cat.eqToHom_app]

omit [J.Subcanonical] in
lemma sheafCanonicalHom_eq {X : Sheaf J (Type u)} {Y : I → Sheaf J (Type u)}
    (f : ∀ i, Y i ⟶ X) (P : Object act X)
    {Z : Sheaf J (Type u)} (q : Z ⟶ X) {i j : I} (a : Z ⟶ Y i) (b : Z ⟶ Y j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (((SheafActionQuotient.Stack.pseudofunctor act).toDescentData f).obj P).hom q a b ha hb =
      eqToHom (congrArg (reindex P) (ha.trans hb.symm)) := by
  simp only [Pseudofunctor.toDescentData_obj, Pseudofunctor.DescentData.ofObj_hom,
    Pseudofunctor.mapComp', SheafActionQuotient.Stack.pseudofunctor, Functor.toPseudofunctor'_mapComp,
    PrelaxFunctor.map₂Iso_eqToIso, Iso.trans_hom, Iso.trans_inv, eqToIso.hom,
    eqToIso.inv, eqToHom_trans, Cat.eqToHom_app]

lemma extendCanonicalHom (P : Object act (J.yoneda.obj S))
    {Z : Sheaf J (Type u)} (q : Z ⟶ J.yoneda.obj S) {i j : I}
    (a : Z ⟶ J.yoneda.obj (V i)) (b : Z ⟶ J.yoneda.obj (V j))
    (ha : a ≫ J.yoneda.map (f i) = q) (hb : b ≫ J.yoneda.map (f j) = q) :
    extendHom (((quotientPseudofunctor act).toDescentData f).obj P) q a b ha hb =
      (((SheafActionQuotient.Stack.pseudofunctor act).toDescentData
        (fun i => J.yoneda.map (f i))).obj P).hom q a b ha hb := by
  apply SheafActionQuotient.Arrow.ext
  apply SheafTorsor.Arrow.ext
  ext x p
  change TorsorExtension.evaluate
      (((((quotientPseudofunctor act).toDescentData f).obj P).hom
        (q.hom.app x.obj x.val) (a.hom.app x.obj x.val) (b.hom.app x.obj x.val)
        (congrArg (fun m : Z ⟶ J.yoneda.obj S => m.hom.app x.obj x.val) ha)
        (congrArg (fun m : Z ⟶ J.yoneda.obj S => m.hom.app x.obj x.val) hb)).torsorArrow) p = _
  rw [canonicalHom_eq, sheafCanonicalHom_eq, eqToHom_torsorArrow, eqToHom_torsorArrow]
  dsimp only [TorsorExtension.evaluate]
  have he : J.yoneda.map (a.hom.app x.obj x.val) ≫ J.yoneda.map (f i) =
      J.yoneda.map (b.hom.app x.obj x.val) ≫ J.yoneda.map (f j) := by
    rw [← J.yoneda.map_comp, ← J.yoneda.map_comp]
    exact congrArg J.yoneda.map ((congrArg (fun m : Z ⟶ J.yoneda.obj S =>
      m.hom.app x.obj x.val) ha).trans (congrArg (fun m : Z ⟶ J.yoneda.obj S =>
      m.hom.app x.obj x.val) hb).symm)
  rw [TorsorExtension.eqToHom_reindex_app P.torsor he,
    TorsorExtension.eqToHom_reindex_app P.torsor (ha.trans hb.symm)]
  change (P.torsor.family.family.map _ ≫ P.torsor.family.family.map _ ≫ P.torsor.family.family.map _) p =
    P.torsor.family.family.map _ p
  congr 1
  rw [← P.torsor.family.family.map_comp, ← P.torsor.family.family.map_comp]
  apply congrArg ConcreteCategory.hom
  apply congrArg P.torsor.family.family.map
  apply Functor.Elements.hom_ext
  simp [ElementFamilies.vertical]

/-- Quotient extension commutes with canonical descent, including target maps. -/
def canonicalIso : (quotientPseudofunctor act).toDescentData f ⋙ extendFunctor ≅
    (SheafActionQuotient.Stack.pseudofunctor act).toDescentData (fun i => J.yoneda.map (f i)) :=
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
      change (h.reindex (J.yoneda.map (f i)) :
        reindex P (J.yoneda.map (f i)) ⟶ reindex Q (J.yoneda.map (f i))) ≫
        𝟙 (reindex Q (J.yoneda.map (f i))) =
        𝟙 (reindex P (J.yoneda.map (f i))) ≫ (h.reindex (J.yoneda.map (f i)) :
          reindex P (J.yoneda.map (f i)) ⟶ reindex Q (J.yoneda.map (f i)))
      rw [Category.id_comp, Category.comp_id])

end QuotientExtension

private theorem isEquivalence_of_comparison
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
      (fun i => J.yoneda.map (f i))).IsEquivalence :=
    ((SheafTorsor.Stack.pseudofunctor G).isStackFor_ofArrows_iff _).mp
      (SheafFamilyDescent.torsor_isStackFor G _ (yoneda_jointlyLocallySurjective f hf))
  exact isEquivalence_of_comparison _ _ _ TorsorExtension.extendFullyFaithful
    TorsorExtension.canonicalIso

/-- Every original covering family has effective action-quotient descent. -/
theorem quotient_isEquivalence_toDescentData {G : Sheaf J GrpCat.{u}}
    {M : Sheaf J (Type u)} (act : SheafActionQuotient.Action G M)
    {I : Type u} {U : C} {V : I → C} (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ J U) :
    ((quotientPseudofunctor act).toDescentData f).IsEquivalence := by
  let : ((SheafActionQuotient.Stack.pseudofunctor act).toDescentData
      (fun i => J.yoneda.map (f i))).IsEquivalence :=
    ((SheafActionQuotient.Stack.pseudofunctor act).isStackFor_ofArrows_iff _).mp
      (SheafFamilyDescent.quotient_isStackFor act _ (yoneda_jointlyLocallySurjective f hf))
  exact isEquivalence_of_comparison _ _ _ QuotientExtension.extendFullyFaithful
    QuotientExtension.canonicalIso

instance torsor_isStack (G : Sheaf J GrpCat.{u}) : (torsorPseudofunctor G).IsStack J := by
  apply Pseudofunctor.IsStack.of_isStackFor
  intro U R hR
  rw [Pseudofunctor.isStackFor_iff]
  exact torsor_isEquivalence_toDescentData G (fun g : R.arrows.category => g.obj.hom)
    (by simpa only [Sieve.ofArrows_category] using hR)

instance quotient_isStack {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)}
    (act : SheafActionQuotient.Action G M) : (quotientPseudofunctor act).IsStack J := by
  apply Pseudofunctor.IsStack.of_isStackFor
  intro U R hR
  rw [Pseudofunctor.isStackFor_iff]
  exact quotient_isEquivalence_toDescentData act (fun g : R.arrows.category => g.obj.hom)
    (by simpa only [Sieve.ofArrows_category] using hR)

end SquareKit.SubcanonicalSheafStack
