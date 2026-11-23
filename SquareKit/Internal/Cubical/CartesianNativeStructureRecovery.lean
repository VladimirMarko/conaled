import SquareKit.Internal.Cubical.CartesianNativeStructureLaws

/-! Recovery of the existing law-bearing structures at explicitly presented
carriers. Native equality witnesses are decoded only after comparison with a
discrete family; the inverse reconstructs their complete path bodies. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.StructureIdentity.Native
open CategoryTheory SquareKit.StructureIdentity
variable {Γ Δ : Context.{1}} {A : Family Γ} {X : Type}

def reindexPresented (i : A ≅ constantFamily Γ (ULift.{1} X)) (σ : Δ ⟶ Γ) :
    reindex A σ ≅ constantFamily Δ (ULift.{1} X) :=
  Functor.isoWhiskerLeft σ.mapElements i

def decode (D : Description) (i : A ≅ constantFamily Γ (ULift.{1} X))
    (x : Γ.Elements) (a : (family D A).obj x) : D.Data X :=
  ((presentedIso D i).hom.app x a).down

theorem decode_injective (D : Description) (i : A ≅ constantFamily Γ (ULift.{1} X))
    (x : Γ.Elements) : Function.Injective (decode D i x) := by
  intro a b h
  have hh : (presentedIso D i).hom.app x a = (presentedIso D i).hom.app x b := ULift.ext h
  exact ((presentedIso D i).hom_inv_id_app_apply x a).symm.trans
    ((congrArg ((presentedIso D i).inv.app x) hh).trans
      ((presentedIso D i).hom_inv_id_app_apply x b))

theorem decode_natural (D : Description) (i : A ≅ constantFamily Γ (ULift.{1} X))
    {x y : Γ.Elements} (f : x ⟶ y) (a : (family D A).obj x) :
    decode D i y ((family D A).map f a) = decode D i x a :=
  congrArg ULift.down ((presentedIso D i).hom.naturality_apply f a)

set_option backward.isDefEq.respectTransparency false in
theorem decode_reindex (D : Description) (i : A ≅ constantFamily Γ (ULift.{1} X))
    (σ : Δ ⟶ Γ) (x : Δ.Elements) (a : (family D A).obj (σ.mapElements.obj x)) :
    decode D (reindexPresented i σ) x ((reindexIso D A σ).hom.app x a) =
      decode D i (σ.mapElements.obj x) a := by
  induction D with
  | carrier => rfl
  | fixed _ => rfl
  | product D E hD hE =>
    exact Prod.ext (hD a.1) (hE a.2)
  | function D E hD hE =>
    funext b
    let b' := (presentedIso D (reindexPresented i σ)).inv.app x (ULift.up b)
    have hb : (reindexIso D A σ).inv.app x b' =
        (presentedIso D i).inv.app (σ.mapElements.obj x) (ULift.up b) := by
      apply decode_injective D i
      change _ = ((presentedIso D i).hom.app _ ((presentedIso D i).inv.app _ (ULift.up b))).down
      rw [(presentedIso D i).inv_hom_id_app_apply]
      have h := hD ((reindexIso D A σ).inv.app x b')
      rw [(reindexIso D A σ).inv_hom_id_app_apply] at h
      exact h.symm.trans (congrArg (fun z : ULift.{1} (D.Data X) => z.down)
        ((presentedIso D (reindexPresented i σ)).inv_hom_id_app_apply x
          (show ULift.{1} (D.Data X) from ULift.up b)))
    change decode E (reindexPresented i σ) x
      ((reindexIso E A σ).hom.app x
        (a.val (σ.mapElements.map (𝟙 x)) ((reindexIso D A σ).inv.app x b'))) = _
    rw [hE, hb, CategoryTheory.Functor.map_id]
    rfl

theorem decode_term_natural (D : Description) (i : A ≅ constantFamily Γ (ULift.{1} X))
    (s : Term (family D A)) {x y : Γ.Elements} (f : x ⟶ y) :
    decode D i y (s.val y) = decode D i x (s.val x) := by
  rw [← s.property f]
  exact decode_natural D i f (s.val x)

set_option backward.isDefEq.respectTransparency false in
theorem decode_expression {D C E : Description}
    (i : A ≅ constantFamily Γ (ULift.{1} X))
    (s : Term (family D A)) (c : Term (family C A))
    (a : Expression D C E) (x : Γ.Elements) :
    decode E i x ((expression s c a).val x) =
      a.eval (decode D i x (s.val x)) (decode C i x (c.val x)) := by
  induction a with
  | data => rfl
  | var => rfl
  | fixed _ => rfl
  | pair a b ha hb => exact Prod.ext ha hb
  | first a ha => exact congrArg Prod.fst ha
  | second a ha => exact congrArg Prod.snd ha
  | @apply E F f a hf ha =>
    change decode F i x ((expression s c f).val x |>.val (𝟙 x)
      ((expression s c a).val x)) =
        f.eval (decode D i x (s.val x)) (decode C i x (c.val x))
          (a.eval (decode D i x (s.val x)) (decode C i x (c.val x)))
    rw [← hf, ← ha]
    change _ = decode F i x ((expression s c f).val x |>.val (𝟙 x)
      ((presentedIso E i).inv.app x ((presentedIso E i).hom.app x
        ((expression s c a).val x))))
    rw [(presentedIso E i).hom_inv_id_app_apply]

private theorem constant_path_value {S : Type 1}
    {a b : Term (constantFamily Γ S)} {x : Γ.Elements}
    (p : (homogeneousPath (constantFamily Γ S) a b).obj x)
    {y : Γ.Elements} (f : x ⟶ y) (r : (interval Γ).obj y) :
    p.val.val f r = a.val y := by
  let P := homogeneousPath (constantFamily Γ S) a b
  let τ := projection P
  let t := Term.map (EquivalenceFamilies.homogeneousReindexIso (constantFamily Γ S) a b τ).hom (generic P)
  let z := extendObj P y (P.map f p)
  have h := constant_section_interval (pathApp t) z r ((endpoint (total P) false).val z)
  have hz := congrArg (fun s => s.val z) (pathApp_zero t)
  have hh := h.trans hz
  change p.val.val (f ≫ 𝟙 y) r = a.val y at hh
  simpa only [Category.comp_id] using hh

/-- Discreteness determines every restriction and interval value of a path. -/
def constantPathEquiv {S : Type 1} (a b : Term (constantFamily Γ S)) (x : Γ.Elements) :
    (homogeneousPath (constantFamily Γ S) a b).obj x ≃
      ULift.{1} (PLift (a.val x = b.val x)) where
  toFun p := ⟨⟨(constant_path_value p (𝟙 x) ((endpoint Γ true).val x)).symm.trans
    (p.property (𝟙 x)).2⟩⟩
  invFun h := ⟨{
    val := fun {y} _ _ => a.val y
    naturality := fun _ g _ => a.property g }, fun {y} f =>
      ⟨rfl, (a.property f).symm.trans (h.down.down.trans (b.property f))⟩⟩
  left_inv p := by
    apply Subtype.ext
    apply PiElement.ext
    intro y f r
    exact (constant_path_value p f r).symm
  right_inv _ := Subsingleton.elim _ _

/-- A presented discrete carrier admits host equality recovery, with a proved
inverse on the full native path witness. -/
def presentedPathEquiv (i : A ≅ constantFamily Γ (ULift.{1} X))
    (a b : Term A) (x : Γ.Elements) :
    (homogeneousPath A a b).obj x ≃
      ULift.{1} (PLift ((i.hom.app x (a.val x)).down = (i.hom.app x (b.val x)).down)) :=
  let e := pathCongr i a b
  let q := constantPathEquiv (Term.map i.hom a) (Term.map i.hom b) x
  let r : (homogeneousPath A a b).obj x ≃
      (homogeneousPath (constantFamily Γ (ULift.{1} X)) (Term.map i.hom a) (Term.map i.hom b)).obj x := {
    toFun := e.hom.app x
    invFun := e.inv.app x
    left_inv := e.hom_inv_id_app_apply x
    right_inv := e.inv_hom_id_app_apply x }
  r.trans (q.trans {
    toFun := fun h => ⟨⟨congrArg ULift.down h.down.down⟩⟩
    invFun := fun h => ⟨⟨ULift.ext h.down.down⟩⟩
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun _ => Subsingleton.elim _ _ })

/-- This host subsingleton result uses an explicit discrete presentation. It is
stronger than, and does not follow merely from, native proposition data. -/
theorem lawFamily_obj_subsingleton_of_presented {D C : Description} (p : Formula D C)
    {Γ : Context.{1}} {A : Family Γ} {X : Type}
    (i : A ≅ constantFamily Γ (ULift.{1} X))
    (s : Term (family D A)) (c : Term (family C A)) (x : Γ.Elements) :
    Subsingleton ((lawFamily p s c).obj x) :=
  match p with
  | .truth => inferInstanceAs (Subsingleton (ULift.{1} Unit))
  | .equal (E := E) a b => ⟨fun _v _w =>
      (presentedPathEquiv (presentedIso E i) (expression s c a) (expression s c b) x).injective
        (Subsingleton.elim _ _)⟩
  | .holds _ => inferInstanceAs (Subsingleton (ULift.{1} (PLift _)))
  | .and p q => ⟨fun v w => Sigma.ext
      (@Subsingleton.elim _ (lawFamily_obj_subsingleton_of_presented p i s c x) v.1 w.1)
      (heq_of_eq (@Subsingleton.elim _ (lawFamily_obj_subsingleton_of_presented q i s c x) v.2 w.2))⟩
  | .implies _ q => ⟨fun v w => PiElement.ext (fun {y} f a =>
      @Subsingleton.elim _ (lawFamily_obj_subsingleton_of_presented q i s c y) (v.val f a) (w.val f a))⟩
  | .all E p =>
    let π := projection (family E A)
    let s' := reindexTerm D s π
    let c' := sigmaIntro (reindexTerm C c π)
      (Term.map (reindexIso E A π).hom (generic (family E A)))
    ⟨fun v w => PiElement.ext (fun {y} f a =>
      @Subsingleton.elim _
        (lawFamily_obj_subsingleton_of_presented p (reindexPresented i π) s' c' (extendObj (family E A) y a))
        (v.val f a) (w.val f a))⟩

theorem law_eval_natural {D C : Description} (p : Formula D C)
    (i : A ≅ constantFamily Γ (ULift.{1} X))
    (s : Term (family D A)) (c : Term (family C A))
    {x y : Γ.Elements} (f : x ⟶ y) :
    p.Eval (decode D i y (s.val y)) (decode C i y (c.val y)) =
      p.Eval (decode D i x (s.val x)) (decode C i x (c.val x)) :=
  congrArg₂ p.Eval (decode_term_natural D i s f) (decode_term_natural C i c f)

private def proofEquiv {S : Type 1} {P : Prop} (hS : Subsingleton S)
    (f : S → P) (g : P → S) : S ≃ ULift.{1} (PLift P) where
  toFun s := ⟨⟨f s⟩⟩
  invFun h := g h.down.down
  left_inv _ := @Subsingleton.elim _ hS _ _
  right_inv _ := Subsingleton.elim _ _

set_option backward.isDefEq.respectTransparency false in
/-- Native formula witnesses and the original satisfaction proofs agree at a
presented carrier, including quantified laws over function descriptions. -/
def presentedLawEquiv {D C : Description} (p : Formula D C)
    {Γ : Context.{1}} {A : Family Γ} {X : Type}
    (i : A ≅ constantFamily Γ (ULift.{1} X))
    (s : Term (family D A)) (c : Term (family C A)) (x : Γ.Elements) :
    (lawFamily p s c).obj x ≃
      ULift.{1} (PLift (p.Eval (decode D i x (s.val x)) (decode C i x (c.val x)))) :=
  match p with
  | .truth => proofEquiv (lawFamily_obj_subsingleton_of_presented .truth i s c x)
      (fun _ => True.intro) (fun _ => ⟨()⟩)
  | .equal (E := E) a b =>
    let e := presentedPathEquiv (presentedIso E i) (expression s c a) (expression s c b) x
    proofEquiv (lawFamily_obj_subsingleton_of_presented (.equal a b) i s c x)
      (fun w => by
        have h := (e w).down.down
        change decode E i x ((expression s c a).val x) =
          decode E i x ((expression s c b).val x) at h
        simpa only [decode_expression, Formula.Eval] using h)
      (fun h => e.symm ⟨⟨by
        change decode E i x ((expression s c a).val x) =
          decode E i x ((expression s c b).val x)
        simpa only [decode_expression, Formula.Eval] using h⟩⟩)
  | .holds a => proofEquiv (lawFamily_obj_subsingleton_of_presented (.holds a) i s c x)
      (fun w => Eq.mp (decode_expression i s c a x) w.down.down)
      (fun h => ⟨⟨Eq.mpr (decode_expression i s c a x) h⟩⟩)
  | .and p q => proofEquiv (lawFamily_obj_subsingleton_of_presented (.and p q) i s c x)
      (fun w => ⟨(presentedLawEquiv p i s c x w.1).down.down,
        (presentedLawEquiv q i s c x w.2).down.down⟩)
      (fun h => ⟨(presentedLawEquiv p i s c x).symm ⟨⟨h.1⟩⟩,
        (presentedLawEquiv q i s c x).symm ⟨⟨h.2⟩⟩⟩)
  | .implies p q => proofEquiv (lawFamily_obj_subsingleton_of_presented (.implies p q) i s c x)
      (fun w h => (presentedLawEquiv q i s c x
        (w.val (𝟙 x) ((presentedLawEquiv p i s c x).symm ⟨⟨h⟩⟩))).down.down)
      (fun h => {
        val := fun {y} f a => (presentedLawEquiv q i s c y).symm ⟨⟨
          ((law_eval_natural (.implies p q) i s c f).symm ▸ h)
            ((presentedLawEquiv p i s c y a).down.down)⟩⟩
        naturality := fun {_ z} _ _ _ =>
          @Subsingleton.elim _ (lawFamily_obj_subsingleton_of_presented q i s c z) _ _ })
  | .all E p =>
    let π := projection (family E A)
    let i' := reindexPresented i π
    let s' := reindexTerm D s π
    let c' := sigmaIntro (reindexTerm C c π)
      (Term.map (reindexIso E A π).hom (generic (family E A)))
    have eval_eq (y : Γ.Elements) (a : (family E A).obj y) :
        p.Eval (decode D i' (extendObj (family E A) y a) (s'.val _))
          (decode (.product C E) i' (extendObj (family E A) y a) (c'.val _)) =
        p.Eval (C := .product C E) (decode D i y (s.val y))
          (decode C i y (c.val y), decode E i y a) := by
      congr 1
      · exact decode_reindex D i π _ _
      · exact Prod.ext (decode_reindex C i π _ _) (decode_reindex E i π _ _)
    proofEquiv (lawFamily_obj_subsingleton_of_presented (.all E p) i s c x)
      (fun w a => by
        let b := (presentedIso E i).inv.app x (ULift.up a)
        have h := (presentedLawEquiv p i' s' c' (extendObj (family E A) x b)
          (w.val (𝟙 x) b)).down.down
        rw [eval_eq] at h
        have hb : decode E i x b = a := congrArg (fun z : ULift.{1} (E.Data X) => z.down)
          ((presentedIso E i).inv_hom_id_app_apply x (show ULift.{1} (E.Data X) from ⟨a⟩))
        simpa only [hb] using h)
      (fun h => {
        val := fun {y} f a =>
          (presentedLawEquiv p i' s' c' (extendObj (family E A) y a)).symm ⟨⟨
            (eval_eq y a).symm ▸
              (((law_eval_natural (.all E p) i s c f).symm ▸ h) (decode E i y a))⟩⟩
        naturality := fun {_ z} _ g a => @Subsingleton.elim _
          (lawFamily_obj_subsingleton_of_presented p i' s' c' (extendObj (family E A) z ((family E A).map g a))) _ _ })

def satisfactionFamily {D C : Description} (p : Formula D C)
    (i : A ≅ constantFamily Γ (ULift.{1} X))
    (s : Term (family D A)) (c : Term (family C A)) : Family Γ :=
  holdsFamily ⟨fun x => ⟨p.Eval (decode D i x (s.val x)) (decode C i x (c.val x))⟩,
    fun f => ULift.ext (law_eval_natural p i s c f).symm⟩

def presentedLawIso {D C : Description} (p : Formula D C)
    (i : A ≅ constantFamily Γ (ULift.{1} X))
    (s : Term (family D A)) (c : Term (family C A)) :
    lawFamily p s c ≅ satisfactionFamily p i s c :=
  NatIso.ofComponents (fun x => (presentedLawEquiv p i s c x).toIso) (by
    intro x y f
    apply ConcreteCategory.hom_ext
    intro w
    exact @Subsingleton.elim _
      (show Subsingleton (ULift.{1} (PLift (p.Eval
        (decode D i y (s.val y)) (decode C i y (c.val y))))) from inferInstance) _ _)

private def totalProofEquiv {S : Type 1} {T : Type} {B : S → Type 1} {P : T → Prop}
    (e : S ≃ T) (q : ∀ s, B s ≃ ULift.{1} (PLift (P (e s)))) :
    (Σ s, B s) ≃ ULift.{1} {t // P t} :=
  (Equiv.sigmaCongrRight q).trans
    ((Equiv.sigmaULiftPLiftEquivSubtype (fun s => P (e s))).trans
      ((Equiv.subtypeEquivOfSubtype e).trans Equiv.ulift.symm))

set_option backward.isDefEq.respectTransparency false in
/-- The complete native law-bearing package recovers the existing model type. -/
def presentedModelsEquiv (T : Specification)
    (i : A ≅ constantFamily Γ (ULift.{1} X)) (x : Γ.Elements) :
    (modelsFamily T A).obj x ≃ ULift.{1} (T.Model X) :=
  let S := family T.description A
  let π := projection S
  let s := Term.map (reindexIso T.description A π).hom (generic S)
  let e := ((presentedIso T.description i).app x).toEquiv.trans Equiv.ulift
  totalProofEquiv e (fun a =>
    (presentedLawEquiv T.law (reindexPresented i π) s unitContext (extendObj S x a)).trans
      (Equiv.cast (congrArg (fun P : Prop => ULift.{1} (PLift P)) (by
        exact congrArg (fun d => T.law.Eval (C := .fixed Unit) d ())
          (decode_reindex T.description i π (extendObj S x a) a)))))

theorem presentedModelsEquiv_data (T : Specification)
    (i : A ≅ constantFamily Γ (ULift.{1} X)) (x : Γ.Elements)
    (s : (modelsFamily T A).obj x) :
    (presentedModelsEquiv T i x s).down.val = decode T.description i x s.1 := rfl

def presentedModelsIso (T : Specification)
    (i : A ≅ constantFamily Γ (ULift.{1} X)) :
    modelsFamily T A ≅ constantFamily Γ (ULift.{1} (T.Model X)) :=
  NatIso.ofComponents (fun x => (presentedModelsEquiv T i x).toIso) (by
    intro x y f
    apply ConcreteCategory.hom_ext
    intro s
    apply ULift.ext
    apply Subtype.ext
    exact decode_natural T.description i f s.1)

/-- Context values satisfying a formula retain the native dependent law witness. -/
def solutionsFamily {D C : Description} (p : Formula D C)
    (s : Term (family D A)) : Family Γ :=
  let S := family C A
  let π := projection S
  sigma S (lawFamily p (reindexTerm D s π)
    (Term.map (reindexIso C A π).hom (generic S)))

set_option backward.isDefEq.respectTransparency false in
def presentedSolutionsEquiv {D C : Description} (p : Formula D C)
    (i : A ≅ constantFamily Γ (ULift.{1} X))
    (s : Term (family D A)) (x : Γ.Elements) :
    (solutionsFamily p s).obj x ≃ ULift.{1} (p.Solutions (decode D i x (s.val x))) :=
  let S := family C A
  let π := projection S
  let c := Term.map (reindexIso C A π).hom (generic S)
  let e := ((presentedIso C i).app x).toEquiv.trans Equiv.ulift
  totalProofEquiv e (fun a =>
    (presentedLawEquiv p (reindexPresented i π) (reindexTerm D s π) c (extendObj S x a)).trans
      (Equiv.cast (congrArg (fun P : Prop => ULift.{1} (PLift P))
        (congrArg₂ p.Eval (decode_reindex D i π (extendObj S x a) _)
          (decode_reindex C i π (extendObj S x a) a)))))

theorem presentedSolutionsEquiv_data {D C : Description} (p : Formula D C)
    (i : A ≅ constantFamily Γ (ULift.{1} X))
    (s : Term (family D A)) (x : Γ.Elements) (c : (solutionsFamily p s).obj x) :
    (presentedSolutionsEquiv p i s x c).down.val = decode C i x c.1 := rfl

theorem decode_presentedIso_inv (D : Description)
    (i : A ≅ constantFamily Γ (ULift.{1} X)) (x : Γ.Elements) (a : D.Data X) :
    decode D i x ((presentedIso D i).inv.app x (ULift.up a)) = a :=
  congrArg (fun z : ULift.{1} (D.Data X) => z.down)
    ((presentedIso D i).inv_hom_id_app_apply x (show ULift.{1} (D.Data X) from ⟨a⟩))

set_option backward.isDefEq.respectTransparency false in
/-- Both variances of the native field action recover the existing transport. -/
theorem decode_action (D : Description) {A B : Family Γ} {X Y : Type}
    (i : A ≅ constantFamily Γ (ULift.{1} X))
    (j : B ≅ constantFamily Γ (ULift.{1} Y)) (e : X ≃ Y) (k : A ≅ B)
    (hk : ∀ (x : Γ.Elements) (a : A.obj x),
      decode .carrier j x (k.hom.app x a) = e (decode .carrier i x a))
    (x : Γ.Elements) (a : (family D A).obj x) :
    decode D j x ((actionIso D k).hom.app x a) = D.transport e (decode D i x a) := by
  induction D generalizing A B X Y with
  | carrier => exact hk x a
  | fixed _ => rfl
  | product D E hD hE => exact Prod.ext (hD i j e k hk a.1) (hE i j e k hk a.2)
  | function D E hD hE =>
    have hk' (y : Γ.Elements) (b : B.obj y) :
        decode .carrier i y (k.inv.app y b) = e.symm (decode .carrier j y b) := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact (hk y (k.inv.app y b)).symm.trans
        (congrArg (decode .carrier j y) (k.inv_hom_id_app_apply y b))
    funext b
    let b' := (presentedIso D j).inv.app x (ULift.up b)
    have hb : (actionIso D k.symm).hom.app x b' =
        (presentedIso D i).inv.app x (ULift.up ((D.transport e).symm b)) := by
      apply decode_injective D i x
      rw [hD j i e.symm k.symm hk', decode_presentedIso_inv, Description.transport_symm]
      exact (decode_presentedIso_inv D i x ((D.transport e).symm b)).symm
    change decode E j x ((actionIso E k).hom.app x
      (a.val (𝟙 x) ((actionIso D k.symm).hom.app x b'))) = _
    rw [hE i j e k hk, hb]
    rfl

def presentedCarrierIso {B : Family Γ} {Y : Type}
    (i : A ≅ constantFamily Γ (ULift.{1} X))
    (j : B ≅ constantFamily Γ (ULift.{1} Y)) (e : X ≃ Y) : A ≅ B :=
  i ≪≫ constantIso (Equiv.ulift.trans (e.trans Equiv.ulift.symm)) ≪≫ j.symm

theorem decode_presentedCarrierIso {B : Family Γ} {Y : Type}
    (i : A ≅ constantFamily Γ (ULift.{1} X))
    (j : B ≅ constantFamily Γ (ULift.{1} Y)) (e : X ≃ Y)
    (x : Γ.Elements) (a : A.obj x) :
    decode .carrier j x ((presentedCarrierIso i j e).hom.app x a) =
      e (decode .carrier i x a) := by
  have h := j.inv_hom_id_app_apply x (ULift.up (e (decode .carrier i x a)) : ULift.{1} Y)
  exact congrArg (fun z : ULift.{1} Y => z.down) h

/-- Presented-carrier transport carries the whole native model, including its
law witness, through the proved comparison with the existing specification. -/
def presentedModelsTransport (T : Specification) {B : Family Γ} {Y : Type}
    (i : A ≅ constantFamily Γ (ULift.{1} X))
    (j : B ≅ constantFamily Γ (ULift.{1} Y)) (e : X ≃ Y) :
    modelsFamily T A ≅ modelsFamily T B :=
  presentedModelsIso T i ≪≫
    constantIso (Equiv.ulift.trans ((T.transport e).trans Equiv.ulift.symm)) ≪≫
      (presentedModelsIso T j).symm

theorem presentedModelsTransport_recovery (T : Specification) {B : Family Γ} {Y : Type}
    (i : A ≅ constantFamily Γ (ULift.{1} X))
    (j : B ≅ constantFamily Γ (ULift.{1} Y)) (e : X ≃ Y)
    (x : Γ.Elements) (s : (modelsFamily T A).obj x) :
    (presentedModelsEquiv T j x ((presentedModelsTransport T i j e).hom.app x s)).down =
      T.transport e (presentedModelsEquiv T i x s).down :=
  congrArg ULift.down ((presentedModelsEquiv T j x).apply_symm_apply _)

set_option backward.isDefEq.respectTransparency false in
theorem presentedModelsTransport_data (T : Specification) {B : Family Γ} {Y : Type}
    (i : A ≅ constantFamily Γ (ULift.{1} X))
    (j : B ≅ constantFamily Γ (ULift.{1} Y)) (e : X ≃ Y)
    (x : Γ.Elements) (s : (modelsFamily T A).obj x) :
    ((presentedModelsTransport T i j e).hom.app x s).1 =
      (actionIso T.description (presentedCarrierIso i j e)).hom.app x s.1 := by
  apply decode_injective T.description j x
  rw [decode_action T.description i j e _ (decode_presentedCarrierIso i j e)]
  exact congrArg Subtype.val (presentedModelsTransport_recovery T i j e x s)

def presentedSolutionsTransport {D C : Description} (p : Formula D C)
    {B : Family Γ} {Y : Type}
    (i : A ≅ constantFamily Γ (ULift.{1} X))
    (j : B ≅ constantFamily Γ (ULift.{1} Y)) (e : X ≃ Y)
    (s : Term (family D A)) (x : Γ.Elements) :
    (solutionsFamily p s).obj x ≃
      (solutionsFamily p (Term.map (actionIso D (presentedCarrierIso i j e)).hom s)).obj x :=
  let t := Term.map (actionIso D (presentedCarrierIso i j e)).hom s
  let hs := (D.preserves_iff e _ _).mpr
    (decode_action D i j e _ (decode_presentedCarrierIso i j e) x (s.val x)).symm
  (presentedSolutionsEquiv p i s x).trans
    ((Equiv.ulift.trans ((p.solutionEquiv e hs).trans Equiv.ulift.symm)).trans
      (presentedSolutionsEquiv p j t x).symm)

set_option backward.isDefEq.respectTransparency false in
theorem presentedSolutionsTransport_data {D C : Description} (p : Formula D C)
    {B : Family Γ} {Y : Type}
    (i : A ≅ constantFamily Γ (ULift.{1} X))
    (j : B ≅ constantFamily Γ (ULift.{1} Y)) (e : X ≃ Y)
    (s : Term (family D A)) (x : Γ.Elements) (c : (solutionsFamily p s).obj x) :
    (presentedSolutionsTransport p i j e s x c).1 =
      (actionIso C (presentedCarrierIso i j e)).hom.app x c.1 := by
  apply decode_injective C j x
  rw [decode_action C i j e _ (decode_presentedCarrierIso i j e)]
  let t := Term.map (actionIso D (presentedCarrierIso i j e)).hom s
  exact congrArg (fun z : ULift.{1} (p.Solutions (decode D j x (t.val x))) => z.down.val)
    ((presentedSolutionsEquiv p j t x).apply_symm_apply _)

variable {B : Family Γ} {Y : Type}

def presentedPreservationEquiv (D : Description)
    (i : A ≅ constantFamily Γ (ULift.{1} X))
    (j : B ≅ constantFamily Γ (ULift.{1} Y)) (e : X ≃ Y)
    (s : Term (family D A)) (t : Term (family D B)) (x : Γ.Elements) :
    (preserves D (presentedCarrierIso i j e).hom (presentedCarrierIso i j e).inv s t).obj x ≃
      ULift.{1} (PLift (D.Preserves e (decode D i x (s.val x)) (decode D j x (t.val x)))) := by
  let k := presentedCarrierIso i j e
  let q := preservesActionPathIso D k s t
  let qx : (preserves D k.hom k.inv s t).obj x ≃
      (homogeneousPath (family D B) (Term.map (actionIso D k).hom s) t).obj x := {
    toFun := q.hom.app x
    invFun := q.inv.app x
    left_inv := q.hom_inv_id_app_apply x
    right_inv := q.inv_hom_id_app_apply x }
  let h := decode_action D i j e k (decode_presentedCarrierIso i j e) x (s.val x)
  let r : (decode D j x ((actionIso D k).hom.app x (s.val x)) = decode D j x (t.val x)) ↔
      D.Preserves e (decode D i x (s.val x)) (decode D j x (t.val x)) :=
    (Iff.of_eq (congrArg (fun v => v = decode D j x (t.val x)) h)).trans (D.preserves_iff e _ _).symm
  exact qx.trans ((presentedPathEquiv (presentedIso D j) (Term.map (actionIso D k).hom s) t x).trans {
    toFun := fun h => ⟨⟨r.mp h.down.down⟩⟩
    invFun := fun h => ⟨⟨r.mpr h.down.down⟩⟩
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun _ => Subsingleton.elim _ _ })

def presentedModelPreservationEquiv (T : Specification)
    (i : A ≅ constantFamily Γ (ULift.{1} X))
    (j : B ≅ constantFamily Γ (ULift.{1} Y)) (e : X ≃ Y)
    (s : Term (modelsFamily T A)) (t : Term (modelsFamily T B)) (x : Γ.Elements) :
    (preserves T.description (presentedCarrierIso i j e).hom (presentedCarrierIso i j e).inv
      (sigmaFst s) (sigmaFst t)).obj x ≃
      ULift.{1} (PLift (T.Preserves e
        ((presentedModelsEquiv T i x) (s.val x)).down
        ((presentedModelsEquiv T j x) (t.val x)).down)) :=
  presentedPreservationEquiv T.description i j e (sigmaFst s) (sigmaFst t) x

theorem presented_model_preserves_iff (T : Specification)
    (i : A ≅ constantFamily Γ (ULift.{1} X))
    (j : B ≅ constantFamily Γ (ULift.{1} Y)) (e : X ≃ Y)
    (s : Term (modelsFamily T A)) (t : Term (modelsFamily T B)) (x : Γ.Elements) :
    Nonempty ((preserves T.description (presentedCarrierIso i j e).hom (presentedCarrierIso i j e).inv
      (sigmaFst s) (sigmaFst t)).obj x) ↔
      T.transport e ((presentedModelsEquiv T i x) (s.val x)).down =
        ((presentedModelsEquiv T j x) (t.val x)).down := by
  let q := presentedModelPreservationEquiv T i j e s t x
  constructor
  · rintro ⟨h⟩
    exact (T.preserves_iff e _ _).mp (q h).down.down
  · intro h
    exact ⟨q.symm ⟨⟨(T.preserves_iff e _ _).mpr h⟩⟩⟩


end SquareKit.Cubical.Cartesian.StructureIdentity.Native
