import SquareKit.Internal.Cubical.SmallFamilyDecoding

/-! Contextual coding is a natural map into the larger code presheaf. Lifting
context values changes only their Lean universe, not cube substitutions. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def raisedContext (Γ : Context.{u}) : Context.{u+1} where
  obj I := ULift.{u+1} (Γ.obj I)
  map f := TypeCat.ofHom (fun x => ⟨Γ.map f x.down⟩)
  map_id I := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.up (ConcreteCategory.congr_hom (Γ.map_id I) x.down)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.up (ConcreteCategory.congr_hom (Γ.map_comp f g) x.down)

def raisedSub {Γ Δ : Context.{u}} (σ : Δ ⟶ Γ) : raisedContext Δ ⟶ raisedContext Γ where
  app I := TypeCat.ofHom (fun x => ⟨σ.app I x.down⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    exact congrArg ULift.up (ConcreteCategory.congr_hom (σ.naturality f) x.down)

def LocalFamily.code {Γ : Context.{u}} (A : LocalFamily Γ) : raisedContext Γ ⟶ smallFamilyCodes.{u} where
  app I := TypeCat.ofHom (fun x => A.reindex (represented (Γ.elementsMk I x.down)))
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    let g : Γ.elementsMk I x.down ⟶ Γ.elementsMk J (Γ.map f x.down) :=
      Functor.Elements.homMk f rfl
    exact (congrArg A.reindex (represented_restrict g)).symm

theorem LocalFamily.code_reindex {Γ Δ : Context.{u}} (A : LocalFamily Γ) (σ : Δ ⟶ Γ) :
    (A.reindex σ).code = raisedSub σ ≫ A.code := by
  ext I x
  exact (congrArg A.reindex (represented_naturality σ (Δ.elementsMk I x.down))).symm

def raisedElements (Γ : Context.{u}) : Γ.Elements ⥤ (raisedContext Γ).Elements where
  obj x := (raisedContext Γ).elementsMk x.obj ⟨x.val⟩
  map f := Functor.Elements.homMk f.hom (congrArg ULift.up f.map_val)
  map_id _ := rfl
  map_comp _ _ := rfl

def decode {Γ : Context.{u}} (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) : Family Γ :=
  raisedElements Γ ⋙ a.mapElements ⋙ universalDecode

def LocalFamily.decodeCodeComponent {Γ : Context.{u}} (A : LocalFamily Γ) (x : Γ.Elements) :
    (decode A.code).obj x ≅ A.family.obj x :=
  A.family.mapIso (eqToIso (represented_generic_source x))

theorem LocalFamily.decodeCodeMap_heq {Γ : Context.{u}} (A : LocalFamily Γ)
    {x y : Γ.Elements} (f : x ⟶ y) (a : (decode A.code).obj x) :
    HEq ((decode A.code).map f a)
      (A.family.map ((represented x).mapElements.map (representableGenericHom f.hom.unop)) a) :=
  cast_heq _ _

def LocalFamily.decodeCodeIso {Γ : Context.{u}} (A : LocalFamily Γ) : decode A.code ≅ A.family :=
  NatIso.ofComponents A.decodeCodeComponent (by
    intro x y f
    apply ConcreteCategory.hom_ext
    intro a
    have ey := represented_generic_source y
    have hy := family_map_identity_heq A.family (eqToHom ey) ey
      (heq_of_eq (elements_eqToHom_hom ey)) ((decode A.code).map f a)
    have targetRel : (represented x).mapElements.obj
        ((representableMap f.hom.unop).mapElements.obj (representableGeneric.{u} y.obj.unop)) = y :=
      (congrArg (fun σ => σ.mapElements.obj (representableGeneric.{u} y.obj.unop))
        (represented_restrict f)).trans ey
    have hm := family_map_heq A.family
      (eqToHom (represented_generic_source x) ≫ f)
      ((represented x).mapElements.map (representableGenericHom f.hom.unop)) targetRel.symm
      (heq_of_eq (by
        change (eqToHom (represented_generic_source x) : _ ⟶ x).hom ≫ f.hom = f.hom
        rw [elements_eqToHom_hom]
        exact Category.id_comp f.hom)) a
    have hc := ConcreteCategory.congr_hom
      (A.family.map_comp (eqToHom (represented_generic_source x)) f) a
    exact eq_of_heq (hy.trans ((A.decodeCodeMap_heq f a).trans
      (hm.symm.trans (heq_of_eq hc)))))

theorem decode_reindex {Γ Δ : Context.{u}} (a : raisedContext Γ ⟶ smallFamilyCodes.{u})
    (σ : Δ ⟶ Γ) : decode (raisedSub σ ≫ a) = Presheaf.reindex (decode a) σ := rfl

theorem code_represented {Γ : Context.{u}} (a : raisedContext Γ ⟶ smallFamilyCodes.{u})
    (x : Γ.Elements) : raisedSub (represented x) ≫ a = (a.app x.obj ⟨x.val⟩).code := by
  ext J f
  exact (ConcreteCategory.congr_hom (a.naturality f.down.down.op) ⟨x.val⟩)

def decode_represented_iso {Γ : Context.{u}} (a : raisedContext Γ ⟶ smallFamilyCodes.{u})
    (x : Γ.Elements) : Presheaf.reindex (decode a) (represented x) ≅ (a.app x.obj ⟨x.val⟩).family :=
  eqToIso (decode_reindex a (represented x)).symm ≪≫
    eqToIso (congrArg decode (code_represented a x)) ≪≫ (a.app x.obj ⟨x.val⟩).decodeCodeIso

def chartElement {Γ : Context.{u}} {I : Cube}
    (p : total (interval (representable.{u} I)) ⟶ Γ) : Γ.Elements :=
  ((representableIntervalIso I).inv ≫ p).mapElements.obj (representableGeneric (Cube.extend I))

theorem chart_presentation {Γ : Context.{u}} {I : Cube}
    (p : total (interval (representable.{u} I)) ⟶ Γ) :
    (representableIntervalIso I).hom ≫ represented (chartElement p) = p := by
  unfold chartElement
  rw [represented_map_generic]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun q => q ≫ p) (representableIntervalIso I).hom_inv_id).trans (Category.id_comp p))

def chartCode {Γ : Context.{u}} (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) {I : Cube}
    (p : total (interval (representable.{u} I)) ⟶ Γ) : SmallFamilyCode.{u} (Cube.extend I) :=
  a.app (Opposite.op (Cube.extend I)) ⟨(chartElement p).val⟩

def chartDecodeIso {Γ : Context.{u}} (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) {I : Cube}
    (p : total (interval (representable.{u} I)) ⟶ Γ) :
    Presheaf.reindex (decode a) p ≅
      Presheaf.reindex (chartCode a p).family (representableIntervalIso I).hom :=
  eqToIso (congrArg (Presheaf.reindex (decode a)) (chart_presentation p).symm) ≪≫
    Functor.isoWhiskerLeft (representableIntervalIso I).hom.mapElements (decode_represented_iso a (chartElement p))

def decodedLocalFilling {Γ : Context.{u}} (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) :
    LocalFilling (decode a) where
  fill p φ b := Term.map (chartDecodeIso a p).inv
    ((chartCode a p).filling.fill (representableIntervalIso _).hom φ (b.map (chartDecodeIso a p).hom))

theorem decodedLocalFilling_fills {Γ : Context.{u}} (a : raisedContext Γ ⟶ smallFamilyCodes.{u})
    {I : Cube} (p : total (interval (representable.{u} I)) ⟶ Γ)
    (φ : Cofibration (representable.{u} I)) (b : OpenBox (Presheaf.reindex (decode a) p) φ) :
    b.Fills ((decodedLocalFilling a).fill p φ b) := by
  have h := (chartCode a p).lawful.fills (representableIntervalIso I).hom φ
    (b.map (chartDecodeIso a p).hom)
  constructor
  · apply Term.ext
    intro x
    exact (congrArg ((chartDecodeIso a p).inv.app ((endpointSub _ false).mapElements.obj x))
      (congrArg (fun t => t.val x) h.1)).trans
      (congrArg (fun q => q.app ((endpointSub _ false).mapElements.obj x) (b.base.val x))
        (chartDecodeIso a p).hom_inv_id)
  · intro x hx
    exact (congrArg ((chartDecodeIso a p).inv.app x) (h.2 x hx)).trans
      (congrArg (fun q => q.app x (b.tube.val x hx)) (chartDecodeIso a p).hom_inv_id)


theorem representableInterval_naturality {I J : Cube} (f : J ⟶ I) :
    liftSub (interval (representable.{u} I)) (representableMap f) ≫
      (representableIntervalIso I).hom =
    (representableIntervalIso J).hom ≫ representableMap (Cube.extensionMap f) := by
  ext K x
  apply congrArg ULift.up
  change Cube.pair (x.1.down ≫ f) x.2.down = Cube.pair x.1.down x.2.down ≫ Cube.extensionMap f
  apply Cube.pair_ext
  · simp only [Cube.pair_drop_cat, Category.assoc, Cube.extensionMap_drop]
    rw [← Category.assoc, Cube.pair_drop_cat]
  · simp [Category.assoc]

theorem representableInterval_inv_naturality {I J : Cube} (f : J ⟶ I) :
    (representableIntervalIso J).inv ≫
      liftSub (interval (representable.{u} I)) (representableMap f) =
    representableMap (Cube.extensionMap f) ≫ (representableIntervalIso I).inv := by
  ext K x
  apply Sigma.ext
  · exact congrArg ULift.up (by
      change (x.down ≫ Cube.drop J) ≫ f = (x.down ≫ Cube.extensionMap f) ≫ Cube.drop I
      simp [Category.assoc])
  · exact heq_of_eq (congrArg ULift.up (by
      change x.down ≫ Cube.fresh J = (x.down ≫ Cube.extensionMap f) ≫ Cube.fresh I
      simp [Category.assoc]))


theorem chartElement_reindex {Γ : Context.{u}} {I J : Cube}
    (p : total (interval (representable.{u} I)) ⟶ Γ) (f : J ⟶ I) :
    (chartElement (liftSub (interval (representable I)) (representableMap f) ≫ p)).val =
      Γ.map (Cube.extensionMap f).op (chartElement p).val := by
  have e := congrArg (fun σ => σ.app (Opposite.op (Cube.extend J))
    (ULift.up (𝟙 (Cube.extend J)))) (representableInterval_inv_naturality.{u} f)
  have n := ConcreteCategory.congr_hom
    (((representableIntervalIso I).inv ≫ p).naturality (Cube.extensionMap f).op)
    (representableGeneric.{u} (Cube.extend I)).val
  refine (congrArg (fun z => p.app (Opposite.op (Cube.extend J)) z) e).trans ?_
  change (((representableIntervalIso I).inv ≫ p).app _
    (ULift.up (𝟙 (Cube.extend J) ≫ Cube.extensionMap f))) = _
  change (((representableIntervalIso I).inv ≫ p).app _
    (ULift.up (Cube.extensionMap f ≫ 𝟙 (Cube.extend I)))) = _ at n
  exact (congrArg (((representableIntervalIso I).inv ≫ p).app _)
    (congrArg ULift.up ((Category.id_comp (Cube.extensionMap f)).trans
      (Category.comp_id (Cube.extensionMap f)).symm))).trans n

theorem chartCode_reindex {Γ : Context.{u}}
    (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) {I J : Cube}
    (p : total (interval (representable.{u} I)) ⟶ Γ) (f : J ⟶ I) :
    chartCode a (liftSub (interval (representable I)) (representableMap f) ≫ p) =
      (chartCode a p).reindex (representableMap (Cube.extensionMap f)) := by
  unfold chartCode
  rw [chartElement_reindex]
  exact ConcreteCategory.congr_hom (a.naturality (Cube.extensionMap f).op) ⟨(chartElement p).val⟩



theorem family_eqToIso_hom_heq {Γ : Context.{u}} {A B : Family Γ}
    (e : A = B) (x : Γ.Elements) (v : A.obj x) :
    HEq ((eqToIso e).hom.app x v) v := by
  cases e
  rfl

theorem LocalFamily.decodeCodeIso_hom_heq {Γ : Context.{u}} (A : LocalFamily Γ)
    (x : Γ.Elements) (v : (decode A.code).obj x) :
    HEq (A.decodeCodeIso.hom.app x v) v :=
  family_map_identity_heq A.family (eqToHom (represented_generic_source x))
    (represented_generic_source x) (heq_of_eq (elements_eqToHom_hom _)) v

theorem decode_represented_iso_hom_heq {Γ : Context.{u}}
    (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) (x : Γ.Elements)
    (y : (representable.{u} x.obj.unop).Elements)
    (v : (Presheaf.reindex (decode a) (represented x)).obj y) :
    HEq ((decode_represented_iso a x).hom.app y v) v := by
  let e₁ := (decode_reindex a (represented x)).symm
  let e₂ := congrArg decode (code_represented a x)
  exact ((a.app x.obj ⟨x.val⟩).decodeCodeIso_hom_heq y
    ((eqToIso e₂).hom.app y ((eqToIso e₁).hom.app y v))).trans
    ((family_eqToIso_hom_heq e₂ y _).trans (family_eqToIso_hom_heq e₁ y v))

theorem chartDecodeIso_hom_heq {Γ : Context.{u}}
    (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) {I : Cube}
    (p : total (interval (representable.{u} I)) ⟶ Γ)
    (x : (total (interval (representable.{u} I))).Elements)
    (v : (Presheaf.reindex (decode a) p).obj x) :
    HEq ((chartDecodeIso a p).hom.app x v) v := by
  let e := congrArg (Presheaf.reindex (decode a)) (chart_presentation p).symm
  exact (decode_represented_iso_hom_heq a (chartElement p)
    ((representableIntervalIso I).hom.mapElements.obj x)
    ((eqToIso e).hom.app x v)).trans (family_eqToIso_hom_heq e x v)


theorem chartDecodeIso_inv_heq {Γ : Context.{u}}
    (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) {I : Cube}
    (p : total (interval (representable.{u} I)) ⟶ Γ)
    (x : (total (interval (representable.{u} I))).Elements)
    (v : (Presheaf.reindex (chartCode a p).family (representableIntervalIso I).hom).obj x) :
    HEq ((chartDecodeIso a p).inv.app x v) v := by
  have h := chartDecodeIso_hom_heq a p x ((chartDecodeIso a p).inv.app x v)
  have e := congrArg (fun η => η.app x v) (chartDecodeIso a p).inv_hom_id
  exact h.symm.trans (heq_of_eq e)

theorem localFill_heq {Γ : Context.{u}} {A B : Family Γ}
    (F : LocalFilling A) (G : LocalFilling B) (e : A = B) (h : HEq F G)
    {I : Cube} {p q : total (interval (representable.{u} I)) ⟶ Γ} (ep : p = q)
    (φ : Cofibration (representable.{u} I))
    (b : OpenBox (Presheaf.reindex A p) φ) (c : OpenBox (Presheaf.reindex B q) φ)
    (hb : HEq b c) : HEq (F.fill p φ b) (G.fill q φ c) := by
  cases e
  cases h
  cases ep
  cases hb
  rfl

theorem openBox_hext {Γ : Context.{u}} {A B : Family (total (interval Γ))}
    (e : A = B) {φ : Cofibration Γ} (b : OpenBox A φ) (c : OpenBox B φ)
    (ht : ∀ x hx, HEq (b.tube.val x hx) (c.tube.val x hx))
    (hb : ∀ x, HEq (b.base.val x) (c.base.val x)) : HEq b c := by
  cases e
  apply heq_of_eq
  apply OpenBox.ext
  · apply PartialSection.ext
    intro x hx
    exact eq_of_heq (ht x hx)
  · apply Term.ext
    intro x
    exact eq_of_heq (hb x)


theorem localFamily_fill_reindex_heq {Γ Δ : Context.{u}}
    (C : LocalFamily Δ) (D : LocalFamily Γ) (σ : Δ ⟶ Γ) (e : C = D.reindex σ)
    {I : Cube} (p : total (interval (representable.{u} I)) ⟶ Δ)
    (q : total (interval (representable.{u} I)) ⟶ Γ) (ep : p ≫ σ = q)
    (φ : Cofibration (representable.{u} I))
    (b : OpenBox (Presheaf.reindex C.family p) φ)
    (c : OpenBox (Presheaf.reindex D.family q) φ) (hb : HEq b c) :
    HEq (C.filling.fill p φ b) (D.filling.fill q φ c) := by
  cases e
  change HEq (D.filling.fill (p ≫ σ) φ b) (D.filling.fill q φ c)
  cases ep
  cases hb
  rfl

theorem term_value_heq {Γ : Context.{u}} {A B : Family Γ} (e : A = B)
    (t : Term A) (s : Term B) (h : HEq t s) (x : Γ.Elements) : HEq (t.val x) (s.val x) := by
  cases e
  cases h
  rfl

theorem decodedLocalFilling_uniform {Γ : Context.{u}}
    (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) {I J : Cube}
    (p : total (interval (representable.{u} I)) ⟶ Γ)
    (φ : Cofibration (representable.{u} I)) (b : OpenBox (Presheaf.reindex (decode a) p) φ)
    (f : J ⟶ I) :
    (decodedLocalFilling a).fill (liftSub (interval (representable I)) (representableMap f) ≫ p)
      (φ.reindex (representableMap f)) (b.reindex (representableMap f)) =
    ((decodedLocalFilling a).fill p φ b).reindex
      (liftSub (interval (representable I)) (representableMap f)) := by
  let l := liftSub (interval (representable.{u} I)) (representableMap f)
  let C := chartCode a (l ≫ p)
  let D := chartCode a p
  let c := (b.reindex (representableMap f)).map (chartDecodeIso a (l ≫ p)).hom
  let d := (b.map (chartDecodeIso a p).hom).reindex (representableMap f)
  have eC : C = D.reindex (representableMap (Cube.extensionMap f)) := chartCode_reindex a p f
  have ep : (representableIntervalIso J).hom ≫ representableMap (Cube.extensionMap f) =
      l ≫ (representableIntervalIso I).hom := (representableInterval_naturality f).symm
  have eA : Presheaf.reindex C.family (representableIntervalIso J).hom =
      Presheaf.reindex D.family (l ≫ (representableIntervalIso I).hom) :=
    (congrArg (fun E : SmallFamilyCode.{u} (Cube.extend J) =>
      Presheaf.reindex E.family (representableIntervalIso J).hom) eC).trans
      (congrArg (Presheaf.reindex D.family) ep)
  have hb : HEq c d := by
    apply openBox_hext eA
    · intro x hx
      exact (chartDecodeIso_hom_heq a (l ≫ p) x _).trans
        (chartDecodeIso_hom_heq a p (l.mapElements.obj x) _).symm
    · intro x
      exact (chartDecodeIso_hom_heq a (l ≫ p) ((endpointSub _ false).mapElements.obj x) _).trans
        (chartDecodeIso_hom_heq a p (l.mapElements.obj ((endpointSub _ false).mapElements.obj x)) _).symm
  have hf := localFamily_fill_reindex_heq C D (representableMap (Cube.extensionMap f)) eC
    (representableIntervalIso J).hom (l ≫ (representableIntervalIso I).hom) ep
    (φ.reindex (representableMap f)) c d hb
  have hu := D.lawful.uniform (representableIntervalIso I).hom φ
    (b.map (chartDecodeIso a p).hom) f
  apply Term.ext
  intro x
  apply eq_of_heq
  exact (chartDecodeIso_inv_heq a (l ≫ p) x _).trans
    ((term_value_heq eA _ _ hf x).trans
      ((heq_of_eq (congrArg (fun t => t.val x) hu)).trans
        (chartDecodeIso_inv_heq a p (l.mapElements.obj x) _).symm))


theorem decodedLocalFilling_lawful {Γ : Context.{u}}
    (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) : (decodedLocalFilling a).Lawful where
  fills := decodedLocalFilling_fills a
  uniform := decodedLocalFilling_uniform a

def decodedLocalFamily {Γ : Context.{u}} (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) :
    LocalFamily Γ := ⟨decode a, decodedLocalFilling a, decodedLocalFilling_lawful a⟩

theorem decodedLocalFilling_reindex {Γ Δ : Context.{u}}
    (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) (σ : Δ ⟶ Γ) :
    decodedLocalFilling (raisedSub σ ≫ a) = (decodedLocalFilling a).reindex σ := by
  apply congrArg LocalFilling.mk
  funext I p φ b
  have hb : b.map (chartDecodeIso (raisedSub σ ≫ a) p).hom =
      b.map (chartDecodeIso a (p ≫ σ)).hom := by
    apply OpenBox.ext
    · apply PartialSection.ext
      intro x hx
      exact eq_of_heq ((chartDecodeIso_hom_heq (raisedSub σ ≫ a) p x _).trans
        (chartDecodeIso_hom_heq a (p ≫ σ) x _).symm)
    · apply Term.ext
      intro x
      exact eq_of_heq ((chartDecodeIso_hom_heq (raisedSub σ ≫ a) p
        ((endpointSub _ false).mapElements.obj x) _).trans
        (chartDecodeIso_hom_heq a (p ≫ σ) ((endpointSub _ false).mapElements.obj x) _).symm)
  apply Term.ext
  intro x
  exact eq_of_heq ((chartDecodeIso_inv_heq (raisedSub σ ≫ a) p x _).trans
    ((heq_of_eq (congrArg (fun box => ((chartCode a (p ≫ σ)).filling.fill
      (representableIntervalIso I).hom φ box).val x) hb)).trans
      (chartDecodeIso_inv_heq a (p ≫ σ) x _).symm))

theorem decodedLocalFamily_reindex {Γ Δ : Context.{u}}
    (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) (σ : Δ ⟶ Γ) :
    decodedLocalFamily (raisedSub σ ≫ a) = (decodedLocalFamily a).reindex σ := by
  unfold decodedLocalFamily LocalFamily.reindex
  congr 1
  exact decodedLocalFilling_reindex a σ


theorem LocalFamily.decodeCode_filling {Γ : Context.{u}} (A : LocalFamily Γ)
    {I : Cube} (p : total (interval (representable.{u} I)) ⟶ Γ)
    (φ : Cofibration (representable.{u} I)) (b : OpenBox (Presheaf.reindex (decode A.code) p) φ) :
    A.filling.fill p φ (b.map (Functor.whiskerLeft p.mapElements A.decodeCodeIso.hom)) =
      Term.map (Functor.whiskerLeft p.mapElements A.decodeCodeIso.hom)
        ((decodedLocalFilling A.code).fill p φ b) := by
  let q := (representableIntervalIso I).hom ≫ represented (chartElement p)
  let c := b.map (chartDecodeIso A.code p).hom
  let d := b.map (Functor.whiskerLeft p.mapElements A.decodeCodeIso.hom)
  have ep : q = p := chart_presentation p
  have eA : Presheaf.reindex A.family q = Presheaf.reindex A.family p :=
    congrArg (Presheaf.reindex A.family) ep
  have hb : HEq c d := by
    apply openBox_hext eA
    · intro x hx
      exact (chartDecodeIso_hom_heq A.code p x _).trans
        (A.decodeCodeIso_hom_heq (p.mapElements.obj x) _).symm
    · intro x
      exact (chartDecodeIso_hom_heq A.code p ((endpointSub _ false).mapElements.obj x) _).trans
        (A.decodeCodeIso_hom_heq (p.mapElements.obj ((endpointSub _ false).mapElements.obj x)) _).symm
  have hf := localFill_heq A.filling A.filling rfl HEq.rfl ep φ c d hb
  apply Term.ext
  intro x
  exact eq_of_heq ((term_value_heq eA _ _ hf x).symm.trans
    ((chartDecodeIso_inv_heq A.code p x _).symm.trans
      (A.decodeCodeIso_hom_heq (p.mapElements.obj x) _).symm))

/-- The code-of-decoding comparison is an isomorphism of the admitted fibers,
not a claim of source-language definitional conversion. -/
def codeDecodedComparison {Γ : Context.{u}}
    (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) (x : Γ.Elements) :
    ((decodedLocalFamily a).code.app x.obj ⟨x.val⟩).family ≅ (a.app x.obj ⟨x.val⟩).family :=
  decode_represented_iso a x

theorem decoded_represented_family {Γ : Context.{u}}
    (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) (x : Γ.Elements) :
    (decodedLocalFamily a).reindex (represented x) = decodedLocalFamily (a.app x.obj ⟨x.val⟩).code :=
  (decodedLocalFamily_reindex a (represented x)).symm.trans
    (congrArg decodedLocalFamily (code_represented a x))

end SquareKit.Cubical.Presheaf
