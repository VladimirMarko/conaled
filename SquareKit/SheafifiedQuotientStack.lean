import SquareKit.SheafifiedSheafStack

/-! Effective action-quotient descent on arbitrary sites via sheafified representables. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafifiedSheafStack
open CategoryTheory Limits Opposite
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
namespace QuotientExtension
open SheafActionQuotient
variable {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)}
variable {act : Action G M}

lemma eqToHom_torsorArrow {X : Sheaf J (Type u)} {P Q : Object act X} (h : P = Q) :
    (eqToHom h).torsorArrow = eqToHom (congrArg Object.torsor h) := by
  subst Q
  rfl

lemma pullHom_torsorArrow {V W U T : C} {P : Object act (represented V)}
    {Q : Object act (represented W)} {f : U ⟶ V} {g : U ⟶ W}
    (h : reindex P ((SheafifiedYoneda.functor J).map f) ⟶ reindex Q ((SheafifiedYoneda.functor J).map g)) (k : T ⟶ U)
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
  have hf : reindex P ((SheafifiedYoneda.functor J).map kf) =
      reindex (reindex P ((SheafifiedYoneda.functor J).map f)) ((SheafifiedYoneda.functor J).map k) := by
    rw [← hkf, (SheafifiedYoneda.functor J).map_comp]
    rfl
  have hg : reindex (reindex Q ((SheafifiedYoneda.functor J).map g)) ((SheafifiedYoneda.functor J).map k) =
      reindex Q ((SheafifiedYoneda.functor J).map kg) := by
    rw [← hkg, (SheafifiedYoneda.functor J).map_comp]
    rfl
  change (forget (a := act) (X := represented T)).map
    (eqToHom hf ≫ h.reindex ((SheafifiedYoneda.functor J).map k) ≫ eqToHom hg) = _
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

lemma value_vertical {X : Sheaf J (Type u)} (P : Object act X) {U : Cᵒᵖ}
    {x y : X.obj.obj U} (h : x = y)
    (p : P.torsor.family.family.obj (X.obj.elementsMk U x)) :
    P.value (X.obj.elementsMk U y) (P.torsor.family.family.map (ElementFamilies.vertical _ h) p) =
      P.value (X.obj.elementsMk U x) p := by
  simpa [ElementFamilies.vertical] using (P.natural (ElementFamilies.vertical _ h) p).symm

lemma evaluate_preserves {V W U : C} {P : Object act (represented V)}
    {Q : Object act (represented W)} {a : U ⟶ V} {b : U ⟶ W}
    (h : reindex P ((SheafifiedYoneda.functor J).map a) ⟶
      reindex Q ((SheafifiedYoneda.functor J).map b))
    (p : TorsorExtension.fiber P.torsor a) :
    Q.value ((represented W).obj.elementsMk (op U) (sectionOfArrow b))
      (TorsorExtension.evaluate h.torsorArrow p) =
      P.value ((represented V).obj.elementsMk (op U) (sectionOfArrow a)) p := by
  dsimp only [TorsorExtension.evaluate]
  rw [value_vertical]
  change (reindex Q ((SheafifiedYoneda.functor J).map b)).value
    ((represented U).obj.elementsMk (op U) (sectionOfArrow (𝟙 U)))
      (h.torsorArrow.iso.hom.app _ _) = _
  rw [h.preserves]
  change P.value _ (P.torsor.family.family.map _ p) = _
  rw [value_vertical]

/-- Target preservation is detected on any locally surjective presentation. -/
lemma preserves_of_restriction {X : Sheaf J (Type u)} {Z : Cᵒᵖ ⥤ Type u}
    (η : Z ⟶ X.obj) [Presheaf.IsLocallySurjective J η]
    {P Q : Object act X} (h : P.torsor ⟶ Q.torsor)
    (hh : ∀ (z : Z.Elements) (p),
      Q.value (η.mapElements.obj z) (h.iso.hom.app (η.mapElements.obj z) p) =
        P.value (η.mapElements.obj z) p) :
    ∀ x p, Q.value x (h.iso.hom.app x p) = P.value x p := by
  intro x p
  let T : Sheaf (ElementSite.topology X.obj J) (Type u) :=
    ((ElementSite.projection X.obj).sheafPushforwardContinuous (Type u)
      (ElementSite.topology X.obj J) J).obj M
  apply CategoryTheory.Functor.IsCoverDense.ext (ElementSite.mapSite η) T (op x)
  intro y k
  change M.obj.map k.unop.hom (Q.value x (h.iso.hom.app x p)) =
    M.obj.map k.unop.hom (P.value x p)
  rw [Q.natural, P.natural, ← NatTrans.naturality_apply]
  exact hh y.unop _

lemma familyComparison_preserves {Z : Cᵒᵖ ⥤ Type u} {X : Sheaf J (Type u)}
    (P : Object act X) {a b : Z ⟶ X.obj} (h : a = b) (x : Z.Elements) (p) :
    P.value (b.mapElements.obj x) ((TorsorExtension.familyComparison P.torsor h).hom.app x p) =
      P.value (a.mapElements.obj x) p := by
  subst b
  rfl

def sheafifyHom (D : (quotientPseudofunctor act).DescentData f)
    {Z : Cᵒᵖ ⥤ Type u} (q : Z ⟶ yoneda.obj S) {i j : I}
    (a : Z ⟶ yoneda.obj (V i)) (b : Z ⟶ yoneda.obj (V j))
    (ha : a ≫ yoneda.map (f i) = q) (hb : b ≫ yoneda.map (f j) = q) :
    reindex (D.obj i) ((presheafToSheaf J (Type u)).map a) ⟶
      reindex (D.obj j) ((presheafToSheaf J (Type u)).map b) where
  torsorArrow := TorsorExtension.sheafifyHom (underlyingData D) q a b ha hb
  preserves := by
    apply preserves_of_restriction (toSheafify J Z)
    intro x p
    have hr := congrArg (fun h => h.app x p)
      (TorsorExtension.sheafifyHom_restrict (underlyingData D) q a b ha hb)
    change (D.obj j).value _ ((TorsorExtension.sheafifyHom (underlyingData D) q a b ha hb).iso.hom.app ((toSheafify J Z).mapElements.obj x) p) = _
    apply (congrArg ((D.obj j).value _) hr).trans
    change (D.obj j).value _ ((TorsorExtension.comparisonToRaw (D.obj j).torsor b).inv.app x
      (TorsorExtension.evaluate (TorsorExtension.localHom (underlyingData D) q a b ha hb x)
        ((TorsorExtension.comparisonToRaw (D.obj i).torsor a).hom.app x p))) = _
    apply (familyComparison_preserves (D.obj j) (toSheafify_naturality J b) x _).trans
    have hv := evaluate_preserves
      (D.hom (q.app x.obj x.val) (a.app x.obj x.val) (b.app x.obj x.val)
        (congrArg (fun m => m.app x.obj x.val) ha)
        (congrArg (fun m => m.app x.obj x.val) hb))
      ((TorsorExtension.comparisonToRaw (D.obj i).torsor a).hom.app x p)
    exact hv.trans (familyComparison_preserves (D.obj i)
      (toSheafify_naturality J a).symm x p)

/-- Pullback preserves the target even when the base maps are propositionally equal. -/
def pullArrow {X Y A B : Sheaf J (Type u)} (P : Object act A) (Q : Object act B)
    {a : X ⟶ A} {b : X ⟶ B} (h : reindex P a ⟶ reindex Q b)
    (t : Y ⟶ X) (ta : Y ⟶ A) (tb : Y ⟶ B)
    (ha : t ≫ a = ta) (hb : t ≫ b = tb) : reindex P ta ⟶ reindex Q tb where
  torsorArrow := TorsorExtension.pullArrow P.torsor Q.torsor h.torsorArrow t ta tb ha hb
  preserves := by
    subst ta tb
    exact h.reindex t |>.preserves

def extendHom (D : (quotientPseudofunctor act).DescentData f)
    {Z : Sheaf J (Type u)} (q : Z ⟶ represented S) {i j : I}
    (a : Z ⟶ represented (V i)) (b : Z ⟶ represented (V j))
    (ha : a ≫ (SheafifiedYoneda.functor J).map (f i) = q)
    (hb : b ≫ (SheafifiedYoneda.functor J).map (f j) = q) :
    reindex (D.obj i) a ⟶ reindex (D.obj j) b :=
  pullArrow (D.obj i) (D.obj j)
    (sheafifyHom D (TorsorExtension.overlapFst i j ≫ yoneda.map (f i))
      (TorsorExtension.overlapFst i j) (TorsorExtension.overlapSnd i j)
      rfl pullback.condition.symm)
    (TorsorExtension.overlapLift q a b ha hb) a b
    (TorsorExtension.overlapLift_fst q a b ha hb) (TorsorExtension.overlapLift_snd q a b ha hb)

lemma extendHom_torsorArrow (D : (quotientPseudofunctor act).DescentData f)
    {Z : Sheaf J (Type u)} (q : Z ⟶ represented S) {i j : I}
    (a : Z ⟶ represented (V i)) (b : Z ⟶ represented (V j))
    (ha : a ≫ (SheafifiedYoneda.functor J).map (f i) = q)
    (hb : b ≫ (SheafifiedYoneda.functor J).map (f j) = q) :
    (extendHom D q a b ha hb).torsorArrow =
      TorsorExtension.extendHom (underlyingData D) q a b ha hb := rfl

/-- Extend original-site quotient descent data, including the target maps. -/
def extend (D : (quotientPseudofunctor act).DescentData f) :
    (SheafActionQuotient.Stack.pseudofunctor act).DescentData (fun i => (SheafifiedYoneda.functor J).map (f i)) where
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
    extendHom D ((SheafifiedYoneda.functor J).map q) ((SheafifiedYoneda.functor J).map a) ((SheafifiedYoneda.functor J).map b)
      (by rw [← (SheafifiedYoneda.functor J).map_comp, ha]) (by rw [← (SheafifiedYoneda.functor J).map_comp, hb]) =
      D.hom q a b ha hb := by
  apply SheafActionQuotient.Arrow.ext
  exact TorsorExtension.extendHom_yoneda (underlyingData D) q a b ha hb

/-- Extension retains every compatible quotient arrow. -/
def extendFunctor : (quotientPseudofunctor act).DescentData f ⥤
    (SheafActionQuotient.Stack.pseudofunctor act).DescentData (fun i => (SheafifiedYoneda.functor J).map (f i)) where
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
lemma canonicalHom_eq_of_functor (L : C ⥤ Sheaf J (Type u)) (P : Object act (L.obj S))
    {U : C} (q : U ⟶ S) {i j : I} (a : U ⟶ V i) (b : U ⟶ V j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    ((((L.op ⋙ SheafActionQuotient.Stack.functor act).toPseudofunctor').toDescentData f).obj P).hom q a b ha hb =
      eqToHom (congrArg (reindex P)
        (show L.map a ≫ L.map (f i) =
          L.map b ≫ L.map (f j) by rw [← L.map_comp,
            ← L.map_comp, ha, hb])) := by
  simp only [Pseudofunctor.toDescentData_obj, Pseudofunctor.DescentData.ofObj_hom,
    Pseudofunctor.mapComp', Functor.toPseudofunctor'_mapComp,
    PrelaxFunctor.map₂Iso_eqToIso, Iso.trans_hom, Iso.trans_inv, eqToIso.hom,
    eqToIso.inv, eqToHom_trans, Cat.eqToHom_app]

abbrev canonicalHom_eq (P : Object act (represented S))
    {U : C} (q : U ⟶ S) {i j : I} (a : U ⟶ V i) (b : U ⟶ V j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :=
  canonicalHom_eq_of_functor (SheafifiedYoneda.functor J) P q a b ha hb

set_option backward.defeqAttrib.useBackward true in
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

-- Kernel comparison of the canonical quotient transports exceeds the default 200000;
-- 400000 checks this statement without changing the construction or global budgets.
set_option backward.defeqAttrib.useBackward true in
set_option maxHeartbeats 400000 in
lemma underlyingCanonicalHom (P : Object act (represented S))
    {U : C} (q : U ⟶ S) {i j : I} (a : U ⟶ V i) (b : U ⟶ V j)
    (ha : a ≫ f i = q) (hb : b ≫ f j = q) :
    (underlyingData (((quotientPseudofunctor act).toDescentData f).obj P)).hom q a b ha hb =
      (((torsorPseudofunctor G).toDescentData f).obj P.torsor).hom q a b ha hb := by
  change ((((quotientPseudofunctor act).toDescentData f).obj P).hom q a b ha hb).torsorArrow = _
  rw [canonicalHom_eq, TorsorExtension.canonicalHom_eq, eqToHom_torsorArrow]

lemma underlyingCanonical (P : Object act (represented S)) :
    underlyingData (((quotientPseudofunctor act).toDescentData f).obj P) =
      ((torsorPseudofunctor G).toDescentData f).obj P.torsor := by
  unfold underlyingData Pseudofunctor.toDescentData Pseudofunctor.DescentData.ofObj
  congr 1
  funext U q i j a b ha hb
  exact underlyingCanonicalHom P q a b ha hb

set_option maxHeartbeats 400000 in
def underlyingCanonicalIso (P : Object act (represented S)) :
    underlyingData (((quotientPseudofunctor act).toDescentData f).obj P) ≅
      ((torsorPseudofunctor G).toDescentData f).obj P.torsor :=
  Pseudofunctor.DescentData.isoMk (fun _ => Iso.refl _) (by
    intro U q i j a b ha hb
    change 𝟙 _ ≫ _ = _ ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]
    exact (underlyingCanonicalHom P q a b ha hb).symm)

lemma underlyingCanonicalIso_hom_hom (P : Object act (represented S)) (i : I) :
    (underlyingCanonicalIso (f := f) P).hom.hom i = 𝟙 _ := rfl

lemma torsor_reindex_identity {X Y : Sheaf J (Type u)} (P : SheafTorsor.Torsor G X)
    (a : Y ⟶ X) : (𝟙 P : P ⟶ P).reindex a = 𝟙 (SheafTorsor.reindex P a) := rfl

lemma extendCanonicalHom (P : Object act (represented S))
    {Z : Sheaf J (Type u)} (q : Z ⟶ represented S) {i j : I}
    (a : Z ⟶ represented (V i)) (b : Z ⟶ represented (V j))
    (ha : a ≫ (SheafifiedYoneda.functor J).map (f i) = q)
    (hb : b ≫ (SheafifiedYoneda.functor J).map (f j) = q) :
    extendHom (((quotientPseudofunctor act).toDescentData f).obj P) q a b ha hb =
      (((SheafActionQuotient.Stack.pseudofunctor act).toDescentData
        (fun i => (SheafifiedYoneda.functor J).map (f i))).obj P).hom q a b ha hb := by
  apply SheafActionQuotient.Arrow.ext
  rw [extendHom_torsorArrow]
  have h := TorsorExtension.extendHom_comm (underlyingCanonicalIso P).hom q a b ha hb
  simp only [underlyingCanonicalIso_hom_hom] at h
  rw [torsor_reindex_identity _ a, torsor_reindex_identity _ b,
    Category.id_comp, Category.comp_id] at h
  apply h.symm.trans
  rw [TorsorExtension.extendCanonicalHom,
    TorsorExtension.sheafCanonicalHom_eq, sheafCanonicalHom_eq, eqToHom_torsorArrow]

/-- Quotient extension commutes with canonical descent, including target maps. -/
def canonicalIso : (quotientPseudofunctor act).toDescentData f ⋙ extendFunctor ≅
    (SheafActionQuotient.Stack.pseudofunctor act).toDescentData (fun i => (SheafifiedYoneda.functor J).map (f i)) :=
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

end QuotientExtension

/-- Every original covering family has effective action-quotient descent. -/
theorem quotient_isEquivalence_toDescentData {G : Sheaf J GrpCat.{u}}
    {M : Sheaf J (Type u)} (act : SheafActionQuotient.Action G M)
    {I : Type u} {U : C} {V : I → C} (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ J U) :
    ((quotientPseudofunctor act).toDescentData f).IsEquivalence := by
  let : ((SheafActionQuotient.Stack.pseudofunctor act).toDescentData
      (fun i => (SheafifiedYoneda.functor J).map (f i))).IsEquivalence :=
    ((SheafActionQuotient.Stack.pseudofunctor act).isStackFor_ofArrows_iff _).mp
      (SheafFamilyDescent.quotient_isStackFor act _ (SheafifiedYoneda.jointlyLocallySurjective J f hf))
  exact isEquivalence_of_comparison _ _ _ QuotientExtension.extendFullyFaithful
    QuotientExtension.canonicalIso

instance quotient_isStack {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)}
    (act : SheafActionQuotient.Action G M) : (quotientPseudofunctor act).IsStack J := by
  apply Pseudofunctor.IsStack.of_isStackFor
  intro U R hR
  rw [Pseudofunctor.isStackFor_iff]
  exact quotient_isEquivalence_toDescentData act (fun g : R.arrows.category => g.obj.hom)
    (by simpa only [Sieve.ofArrows_category] using hR)

/-- Effective descent for the original family, retaining all quotient arrows. -/
def quotientDescentEquivalence {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)}
    (act : SheafActionQuotient.Action G M)
    {I : Type u} {U : C} {V : I → C} (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ J U) :
    SheafActionQuotient.Object act (represented U) ≌
      (quotientPseudofunctor act).DescentData f := by
  letI := quotient_isEquivalence_toDescentData act f hf
  exact ((quotientPseudofunctor act).toDescentData f).asEquivalence

namespace QuotientRecovery
open SheafActionQuotient
variable {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)}
variable (act : Action G M)
variable {I : Type u} {U : C} {V : I → C} (f : ∀ i, V i ⟶ U)
variable (hf : Sieve.ofArrows V f ∈ J U)

abbrev glue (D : (quotientPseudofunctor act).DescentData f) :=
  (quotientDescentEquivalence act f hf).inverse.obj D

def localComparison (D : (quotientPseudofunctor act).DescentData f) :
    ((quotientPseudofunctor act).toDescentData f).obj (glue act f hf D) ≅ D :=
  (quotientDescentEquivalence act f hf).counitIso.app D

theorem localComparison_target (D : (quotientPseudofunctor act).DescentData f)
    (i : I) (x : (represented (J := J) (V i)).obj.Elements) (p) :
    (D.obj i).value x (((localComparison act f hf D).hom.hom i).torsorArrow.iso.hom.app x p) =
      (reindex (glue act f hf D) ((SheafifiedYoneda.functor J).map (f i))).value x p :=
  ((localComparison act f hf D).hom.hom i).preserves x p

theorem localComparison_action (D : (quotientPseudofunctor act).DescentData f)
    (i : I) (x : (represented (J := J) (V i)).obj.Elements) (g) (p) :
    ((localComparison act f hf D).hom.hom i).torsorArrow.iso.hom.app x
      ((reindex (glue act f hf D) ((SheafifiedYoneda.functor J).map (f i))).torsor.act x g p) =
      (D.obj i).torsor.act x g
        (((localComparison act f hf D).hom.hom i).torsorArrow.iso.hom.app x p) :=
  ((localComparison act f hf D).hom.hom i).torsorArrow.equivariant x g p

/-- Compatible local arrows, including automorphisms, are precisely global arrows. -/
def arrowEquiv (P Q : Object act (represented U)) :
    (P ⟶ Q) ≃ (((quotientPseudofunctor act).toDescentData f).obj P ⟶
      ((quotientPseudofunctor act).toDescentData f).obj Q) :=
  (quotientDescentEquivalence act f hf).fullyFaithfulFunctor.homEquiv

end QuotientRecovery

end SquareKit.SheafifiedSheafStack
