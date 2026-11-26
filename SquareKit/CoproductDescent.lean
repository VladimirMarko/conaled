import Mathlib.CategoryTheory.Limits.VanKampen
import Mathlib.CategoryTheory.Sites.Descent.DescentData
import Mathlib.CategoryTheory.Pi.Basic

/-!
# Descent and coproducts

`EffectiveCoproducts` requires product restriction to be an equivalence for every colimit
cofan. `restriction_isEquivalence_of_chosen_coproducts` transfers this property from chosen coproducts.
For a van Kampen cofan, `aggregateRestriction_isEquivalence` compares descent for a
family with singleton descent along its aggregate map. Its inverse objects are built
by gluing transition arrows over pairs of pullback coproduct charts; the identity and
cocycle laws are checked after restriction. `toDescentDataAggregateRestrictionIso`
identifies the canonical descent functors through this comparison.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.CoproductDescent
open CategoryTheory CategoryTheory.Limits Opposite
universe w u v u' v'
variable {C : Type u} [Category.{v} C]
variable (F : Pseudofunctor (LocallyDiscrete Cᵒᵖ) Cat.{v', u'})
variable {I : Type w} {S : C} {X : I → C} (f : ∀ i, X i ⟶ S)

/-- Restriction to all members of a family, retaining all component morphisms. -/
abbrev restriction : F.obj (.mk (op S)) ⥤ (∀ i, F.obj (.mk (op (X i)))) :=
  Functor.pi' (fun i => (F.map (f i).op.toLoc).toFunctor)

/-- Forget transition isomorphisms, keeping the family of objects and maps. -/
def forget : F.DescentData f ⥤ (∀ i, F.obj (.mk (op (X i)))) where
  obj D := D.obj
  map φ := φ.hom

instance forget_faithful : (forget F f).Faithful where
  map_injective h := Pseudofunctor.DescentData.hom_ext (fun i => congrFun h i)

/-- The comparison to descent data followed by forgetting is restriction. -/
theorem toDescentData_comp_forget : F.toDescentData f ⋙ forget F f = restriction F f := rfl

/-- Product restriction for every colimit cofan in the specified index universe. -/
abbrev EffectiveCoproducts : Prop :=
  ∀ {I : Type w} {X : I → C} (c : Cofan X), IsColimit c →
    (restriction F (Cofan.inj c)).IsEquivalence

/-- Restriction along an isomorphism is an equivalence for every pseudofunctor. -/
def mapEquivalence {S T : C} (e : S ≅ T) :
    F.obj (.mk (op T)) ≌ F.obj (.mk (op S)) :=
  CategoryTheory.Equivalence.mk (F.map e.hom.op.toLoc).toFunctor (F.map e.inv.op.toLoc).toFunctor
    (Cat.Hom.toNatIso ((F.mapId (.mk (op T))).symm ≪≫
      F.mapComp' e.hom.op.toLoc e.inv.op.toLoc (𝟙 _) (by
        change (e.inv ≫ e.hom).op.toLoc = _
        rw [e.inv_hom_id]
        rfl)))
    (Cat.Hom.toNatIso ((F.mapComp' e.inv.op.toLoc e.hom.op.toLoc (𝟙 _) (by
        change (e.hom ≫ e.inv).op.toLoc = _
        rw [e.hom_inv_id]
        rfl)).symm ≪≫
      F.mapId (.mk (op S))))

/-- Chosen coproduct restriction suffices for every isomorphic colimit cofan. -/
theorem restriction_isEquivalence_of_chosen_coproducts [HasCoproducts.{w} C]
    (hF : ∀ (X : I → C), (restriction F (Sigma.ι X)).IsEquivalence)
    (c : Cofan X) (hc : IsColimit c) :
    (restriction F (Cofan.inj c)).IsEquivalence := by
  let e := (coproductIsCoproduct X).coconePointUniqueUpToIso hc
  have he (i : I) : Sigma.ι X i ≫ e.hom = c.inj i :=
    (coproductIsCoproduct X).comp_coconePointUniqueUpToIso_hom hc ⟨i⟩
  have := (mapEquivalence F e).isEquivalence_functor
  have := hF X
  let iso : (mapEquivalence F e).functor ⋙ restriction F (Sigma.ι X) ≅
      restriction F (Cofan.inj c) := NatIso.pi' (fun i =>
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (Functor.pi'CompEval (fun i => (F.map (Sigma.ι X i).op.toLoc).toFunctor) i) ≪≫
      (Cat.Hom.toNatIso (F.mapComp' e.hom.op.toLoc (Sigma.ι X i).op.toLoc
        (c.inj i).op.toLoc (by simpa using congrArg (fun f => f.op.toLoc) (he i)))).symm ≪≫
      (Functor.pi'CompEval (fun i => (F.map (c.inj i).op.toLoc).toFunctor) i).symm)
  exact Functor.isEquivalence_of_iso iso

variable {F f}

/-- Empty coproduct restriction makes every hom-set over an initial object a singleton. -/
theorem hom_subsingleton_of_isInitial (hF : EffectiveCoproducts.{w} F)
    {Z : C} (hZ : IsInitial Z) (M N : F.obj (.mk (op Z))) : Subsingleton (M ⟶ N) := by
  let c : Cofan (fun i : PEmpty.{w+1} => PEmpty.elim i) := Cofan.mk Z (fun i => PEmpty.elim i)
  have hc : IsColimit c := Cofan.IsColimit.mk _ (fun s => hZ.to s.pt)
    (fun _ i => PEmpty.elim i) (fun _ _ _ => hZ.hom_ext _ _)
  have := hF c hc
  refine ⟨fun a b => (restriction F (Cofan.inj c)).map_injective ?_⟩
  funext i
  exact PEmpty.elim i

variable [HasInitial C] [HasStrictInitialObjects C]
variable {X : I → C} (c : Cofan X) (hC : IsVanKampenColimit c)
include hC

/-- Any compatible test object meeting distinct summands is initial. -/
def initialOfDistinctSummands {Z : C} {i j : I} (h : i ≠ j)
    (a : Z ⟶ X i) (b : Z ⟶ X j) (e : a ≫ c.inj i = b ≫ c.inj j) : IsInitial Z :=
  IsInitial.ofStrict
    ((isPullback_initial_to_of_cofan_isVanKampen hC ⟨i⟩ ⟨j⟩
      (fun e => h (Discrete.mk.inj e))).lift a b e) initialIsInitial

/-- On a coproduct, component maps automatically respect descent transitions. -/
theorem component_comm (hF : EffectiveCoproducts.{w} F)
    {D E : F.DescentData (Cofan.inj c)} (φ : ∀ i, D.obj i ⟶ E.obj i)
    {Z : C} (q : Z ⟶ c.pt) {i j : I} (a : Z ⟶ X i) (b : Z ⟶ X j)
    (ha : a ≫ c.inj i = q) (hb : b ≫ c.inj j = q) :
    (F.map a.op.toLoc).toFunctor.map (φ i) ≫ E.hom q a b =
      D.hom q a b ≫ (F.map b.op.toLoc).toFunctor.map (φ j) := by
  classical
  by_cases hij : i = j
  · subst j
    have : Mono (c.inj i) := mono_of_cofan_isVanKampen hC ⟨i⟩
    have hab : a = b := (cancel_mono (c.inj i)).mp (ha.trans hb.symm)
    subst b
    rw [D.hom_self q a ha, E.hom_self q a ha, Category.comp_id, Category.id_comp]
  · have := hom_subsingleton_of_isInitial hF
      (initialOfDistinctSummands c hC hij a b (ha.trans hb.symm))
      ((F.map a.op.toLoc).toFunctor.obj (D.obj i))
      ((F.map b.op.toLoc).toFunctor.obj (E.obj j))
    exact Subsingleton.elim _ _

/-- For a coproduct, forgetting descent transitions is fully faithful. -/
def fullyFaithfulForget (hC : IsVanKampenColimit c) (hF : EffectiveCoproducts.{w} F) :
    (forget F (Cofan.inj c)).FullyFaithful where
  preimage φ := { hom := φ, comm := fun {_Z} q {_i _j} a b ha hb => component_comm c hC hF φ q a b ha hb }
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- Effective product restriction gives effective Mathlib descent for coproduct injections. -/
theorem isEquivalence_toDescentData (hF : EffectiveCoproducts.{w} F) :
    (F.toDescentData (Cofan.inj c)).IsEquivalence := by
  have hR := hF c hC.isColimit
  have hff := fullyFaithfulForget c hC hF
  have := hff.full
  have : (F.toDescentData (Cofan.inj c) ⋙ forget F (Cofan.inj c)).IsEquivalence := hR
  have : (F.toDescentData (Cofan.inj c)).Faithful :=
    Functor.Faithful.of_comp _ (forget F (Cofan.inj c))
  have : (F.toDescentData (Cofan.inj c)).Full :=
    Functor.Full.of_comp_faithful _ (forget F (Cofan.inj c))
  have : (F.toDescentData (Cofan.inj c)).EssSurj := ⟨fun D =>
    ⟨(restriction F (Cofan.inj c)).objPreimage D.obj,
      ⟨hff.preimageIso ((restriction F (Cofan.inj c)).objObjPreimageIso D.obj)⟩⟩⟩
  exact {}

section Aggregate

variable [hPB : HasPullbacks C]

/-- Base change of a universal coproduct is again a coproduct. -/
abbrev baseChangeCofan {Z : C} (a : Z ⟶ c.pt) :
    Cofan (fun i => pullback (c.inj i) a) :=
  Cofan.mk Z (fun i => pullback.snd (c.inj i) a)

def baseChangeIsColimit {Z : C} (a : Z ⟶ c.pt) :
    IsColimit (baseChangeCofan c a) := by
  apply Nonempty.some
  refine hC.isUniversal _
    (Discrete.natTrans fun i => pullback.fst (c.inj i.as) a) a ?_ (.of_discrete _) ?_
  · apply NatTrans.ext
    funext ⟨i⟩
    exact pullback.condition
  · intro ⟨i⟩
    exact (IsPullback.of_hasPullback (c.inj i) a).flip

omit [HasInitial C] [HasStrictInitialObjects C] in
/-- Morphisms can be tested after any base change of the coproduct injections. -/
theorem baseChangeCofan_hom_ext (hF : EffectiveCoproducts.{w} F)
    {Z : C} (a : Z ⟶ c.pt) {M N : F.obj (.mk (op Z))} (φ ψ : M ⟶ N)
    (h : ∀ i, (F.map (pullback.snd (c.inj i) a).op.toLoc).toFunctor.map φ =
      (F.map (pullback.snd (c.inj i) a).op.toLoc).toFunctor.map ψ) : φ = ψ := by
  have := hF (baseChangeCofan c a) (baseChangeIsColimit c hC a)
  exact (restriction F (Cofan.inj (baseChangeCofan c a))).map_injective (funext h)

/-- Restrict an aggregate descent datum along its coproduct summands. -/
def aggregateRestriction {S : C} (p : c.pt ⟶ S) :
    F.DescentData (fun _ : Unit => p) ⥤ F.DescentData (fun i => c.inj i ≫ p) :=
  Pseudofunctor.DescentData.pullFunctor F (α := fun _ => ())
    (p := 𝟙 S) (p' := Cofan.inj c) (by intro i; simp)

omit [HasInitial C] [HasStrictInitialObjects C] hPB in
/-- Coproduct restriction detects all morphisms of aggregate descent data. -/
theorem aggregateRestriction_faithful (hF : EffectiveCoproducts.{w} F)
    {S : C} (p : c.pt ⟶ S) : (aggregateRestriction (F := F) c p).Faithful where
  map_injective {D E} {φ ψ} h := by
    have := hF c hC.isColimit
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    cases i
    apply (restriction F (Cofan.inj c)).map_injective
    exact congrArg (fun f => f.hom) h

open Pseudofunctor.LocallyDiscreteOpToCat
omit hC [HasInitial C] [HasStrictInitialObjects C] [HasPullbacks C]

lemma pullHom_map_comp {A B W V : C}
    {M M' : F.obj (.mk (op A))} {N : F.obj (.mk (op B))}
    {a : W ⟶ A} {b : W ⟶ B} (ψ : M ⟶ M')
    (θ : (F.map a.op.toLoc).toFunctor.obj M' ⟶ (F.map b.op.toLoc).toFunctor.obj N)
    (k : V ⟶ W) (ka : V ⟶ A) (kb : V ⟶ B)
    (ha : k ≫ a = ka) (hb : k ≫ b = kb) :
    pullHom ((F.map a.op.toLoc).toFunctor.map ψ ≫ θ) k ka kb ha hb =
      (F.map ka.op.toLoc).toFunctor.map ψ ≫ pullHom θ k ka kb ha hb := by
  dsimp [pullHom]
  rw [Functor.map_comp]
  simp only [← Category.assoc, ← Pseudofunctor.mapComp'_hom_naturality]

lemma pullHom_comp_map {A B W V : C}
    {M : F.obj (.mk (op A))} {N N' : F.obj (.mk (op B))}
    {a : W ⟶ A} {b : W ⟶ B}
    (θ : (F.map a.op.toLoc).toFunctor.obj M ⟶ (F.map b.op.toLoc).toFunctor.obj N)
    (ψ : N ⟶ N') (k : V ⟶ W) (ka : V ⟶ A) (kb : V ⟶ B)
    (ha : k ≫ a = ka) (hb : k ≫ b = kb) :
    pullHom (θ ≫ (F.map b.op.toLoc).toFunctor.map ψ) k ka kb ha hb =
      pullHom θ k ka kb ha hb ≫ (F.map kb.op.toLoc).toFunctor.map ψ := by
  simp only [pullHom, Functor.map_comp, Category.assoc,
    Pseudofunctor.mapComp'_inv_naturality]

/-- A compatibility equation can be checked after restricting its test object. -/
lemma map_comm_of_pull_comm {S Z V : C} {p : c.pt ⟶ S}
    {D E : F.DescentData (fun _ : Unit => p)} (ψ : D.obj () ⟶ E.obj ())
    (q : Z ⟶ S) (a b : Z ⟶ c.pt) (ha : a ≫ p = q) (hb : b ≫ p = q)
    (k : V ⟶ Z) (ka kb : V ⟶ c.pt) (hka : k ≫ a = ka) (hkb : k ≫ b = kb)
    (h : (F.map ka.op.toLoc).toFunctor.map ψ ≫ E.hom (k ≫ q) ka kb
      (by rw [← hka, Category.assoc, ha]) (by rw [← hkb, Category.assoc, hb]) =
      D.hom (k ≫ q) ka kb (by rw [← hka, Category.assoc, ha])
        (by rw [← hkb, Category.assoc, hb]) ≫ (F.map kb.op.toLoc).toFunctor.map ψ) :
    (F.map k.op.toLoc).toFunctor.map ((F.map a.op.toLoc).toFunctor.map ψ ≫ E.hom q a b ha hb) =
      (F.map k.op.toLoc).toFunctor.map (D.hom q a b ha hb ≫ (F.map b.op.toLoc).toFunctor.map ψ) := by
  rw [map_eq_pullHom _ k ka kb hka hkb, map_eq_pullHom _ k ka kb hka hkb,
    pullHom_map_comp, pullHom_comp_map,
    E.pullHom_hom k q (k ≫ q) rfl a b ha hb ka kb hka hkb,
    D.pullHom_hom k q (k ≫ q) rfl a b ha hb ka kb hka hkb, h]

/-- Compatible component maps commute with transitions on every pair of summands. -/
lemma aggregate_component_comm {S : C} (p : c.pt ⟶ S)
    {D E : F.DescentData (fun _ : Unit => p)}
    (φ : (aggregateRestriction (F := F) c p).obj D ⟶
      (aggregateRestriction (F := F) c p).obj E)
    (ψ : D.obj () ⟶ E.obj ())
    (hψ : ∀ i, (F.map (c.inj i).op.toLoc).toFunctor.map ψ = φ.hom i)
    {Z : C} (q : Z ⟶ S) {i j : I} (a : Z ⟶ X i) (b : Z ⟶ X j)
    (ha : a ≫ c.inj i ≫ p = q) (hb : b ≫ c.inj j ≫ p = q) :
    (F.map (a ≫ c.inj i).op.toLoc).toFunctor.map ψ ≫
        E.hom q (a ≫ c.inj i) (b ≫ c.inj j) (by simpa [Category.assoc] using ha)
          (by simpa [Category.assoc] using hb) =
      D.hom q (a ≫ c.inj i) (b ≫ c.inj j) (by simpa [Category.assoc] using ha)
        (by simpa [Category.assoc] using hb) ≫
        (F.map (b ≫ c.inj j).op.toLoc).toFunctor.map ψ := by
  have h := φ.comm q a b ha hb
  rw [← hψ i, ← hψ j] at h
  dsimp [aggregateRestriction, Pseudofunctor.DescentData.pullFunctor,
    Pseudofunctor.DescentData.pullFunctorObj] at h
  rw [Pseudofunctor.DescentData.pullFunctorObjHom_eq _ E _ a b q
      (a ≫ c.inj i) (b ≫ c.inj j) rfl (hb.trans ha.symm) (by simpa using ha) rfl rfl,
    Pseudofunctor.DescentData.pullFunctorObjHom_eq_assoc _ D _ a b q
      (a ≫ c.inj i) (b ≫ c.inj j) rfl (hb.trans ha.symm) (by simpa using ha) rfl rfl] at h
  dsimp at h
  rw [Pseudofunctor.mapComp'_inv_naturality_assoc,
    ← Pseudofunctor.mapComp'_hom_naturality] at h
  simp only [cancel_epi] at h
  simpa only [← Category.assoc, cancel_mono, ← Quiver.Hom.comp_toLoc, ← op_comp] using! h

include hC

/-- Every compatible family arrow comes from a unique aggregate arrow. -/
def aggregateRestrictionFullyFaithful (hF : EffectiveCoproducts.{w} F)
    {S : C} (p : c.pt ⟶ S) :
    (aggregateRestriction (F := F) c p).FullyFaithful := by
  have := hF c hC.isColimit
  have := aggregateRestriction_faithful c hC hF p
  have : (aggregateRestriction (F := F) c p).Full := by
    constructor
    intro D E φ
    let ψ : D.obj () ⟶ E.obj () := (restriction F (Cofan.inj c)).preimage φ.hom
    have hψ (i : I) : (F.map (c.inj i).op.toLoc).toFunctor.map ψ = φ.hom i :=
      congrFun ((restriction F (Cofan.inj c)).map_preimage φ.hom) i
    refine ⟨{ hom := fun _ => ψ, comm := ?_ }, ?_⟩
    · intro Z q i j a b ha hb
      cases i
      cases j
      apply baseChangeCofan_hom_ext c hC hF a
      intro i
      let r := pullback.snd (c.inj i) a
      let x := pullback.fst (c.inj i) a
      apply map_comm_of_pull_comm c ψ q a b ha hb r (x ≫ c.inj i) (r ≫ b)
        pullback.condition.symm rfl
      apply baseChangeCofan_hom_ext c hC hF (r ≫ b)
      intro j
      let t := pullback.snd (c.inj j) (r ≫ b)
      let y := pullback.fst (c.inj j) (r ≫ b)
      apply map_comm_of_pull_comm c ψ (r ≫ q) (x ≫ c.inj i) (r ≫ b)
        (by simp [r, x, Category.assoc, pullback.condition_assoc, ha])
        (by simp [Category.assoc, hb]) t ((t ≫ x) ≫ c.inj i) (y ≫ c.inj j)
        (Category.assoc _ _ _).symm pullback.condition.symm
      apply aggregate_component_comm c p φ ψ hψ
      · simp [r, x, Category.assoc, pullback.condition_assoc, ha]
      · simp [t, y, Category.assoc, pullback.condition_assoc, hb]
    · apply Pseudofunctor.DescentData.hom_ext
      exact hψ
  exact .ofFullyFaithful _

omit hC [HasInitial C] [HasStrictInitialObjects C] [HasPullbacks C] in
/-- The aggregate comparison commutes with canonical descent data. -/
def toDescentDataAggregateRestrictionIso {S : C} (p : c.pt ⟶ S) :
    F.toDescentData (fun _ : Unit => p) ⋙ aggregateRestriction (F := F) c p ≅
      F.toDescentData (fun i => c.inj i ≫ p) :=
  Pseudofunctor.DescentData.toDescentDataCompPullFunctorIso F
      (f := fun _ : Unit => p) (f' := fun i => c.inj i ≫ p)
      (p := 𝟙 S) (p' := Cofan.inj c) (α := fun _ => ()) (by intro i; simp) ≪≫
    Functor.isoWhiskerRight (Cat.Hom.toNatIso (F.mapId _)) _ ≪≫
    Functor.leftUnitor _

omit hC [HasInitial C] [HasStrictInitialObjects C] [HasPullbacks C]

/-- Full product restriction glues arrows with prescribed composite pullbacks. -/
def glueHom (hF : EffectiveCoproducts.{w} F) {J : Type w} {Y : J → C}
    (d : Cofan Y) (hd : IsColimit d) {A B : C}
    {M : F.obj (.mk (op A))} {N : F.obj (.mk (op B))}
    (a : d.pt ⟶ A) (b : d.pt ⟶ B) (da : ∀ i, Y i ⟶ A) (db : ∀ i, Y i ⟶ B)
    (ha : ∀ i, d.inj i ≫ a = da i) (hb : ∀ i, d.inj i ≫ b = db i)
    (θ : ∀ i, (F.map (da i).op.toLoc).toFunctor.obj M ⟶
      (F.map (db i).op.toLoc).toFunctor.obj N) :
    (F.map a.op.toLoc).toFunctor.obj M ⟶ (F.map b.op.toLoc).toFunctor.obj N := by
  have := hF d hd
  exact (restriction F (Cofan.inj d)).preimage (fun i =>
    (F.mapComp' a.op.toLoc (d.inj i).op.toLoc (da i).op.toLoc (by grind)).inv.toNatTrans.app _ ≫
      θ i ≫
    (F.mapComp' b.op.toLoc (d.inj i).op.toLoc (db i).op.toLoc (by grind)).hom.toNatTrans.app _)

lemma pullHom_glueHom (hF : EffectiveCoproducts.{w} F) {J : Type w} {Y : J → C}
    (d : Cofan Y) (hd : IsColimit d) {A B : C}
    {M : F.obj (.mk (op A))} {N : F.obj (.mk (op B))}
    (a : d.pt ⟶ A) (b : d.pt ⟶ B) (da : ∀ i, Y i ⟶ A) (db : ∀ i, Y i ⟶ B)
    (ha : ∀ i, d.inj i ≫ a = da i) (hb : ∀ i, d.inj i ≫ b = db i)
    (θ : ∀ i, (F.map (da i).op.toLoc).toFunctor.obj M ⟶
      (F.map (db i).op.toLoc).toFunctor.obj N) (i : J) :
    pullHom (glueHom hF d hd a b da db ha hb θ) (d.inj i) (da i) (db i) (ha i) (hb i) = θ i := by
  have := hF d hd
  have h := congrFun ((restriction F (Cofan.inj d)).map_preimage
    (fun i =>
      (F.mapComp' a.op.toLoc (d.inj i).op.toLoc (da i).op.toLoc (by grind)).inv.toNatTrans.app M ≫
        θ i ≫
      (F.mapComp' b.op.toLoc (d.inj i).op.toLoc (db i).op.toLoc (by grind)).hom.toNatTrans.app N)) i
  dsimp [glueHom, pullHom, restriction]
  dsimp [restriction] at h
  rw [h]
  simp

/-- Transport the objects of descent data through a family of isomorphisms. -/
def changeObjects {J : Type w} {Y : J → C} {S : C} {g : ∀ i, Y i ⟶ S}
    (D : F.DescentData g) (A : ∀ i, F.obj (.mk (op (Y i))))
    (e : ∀ i, A i ≅ D.obj i) : F.DescentData g where
  obj := A
  hom _ q i j a b ha hb :=
    (F.map a.op.toLoc).toFunctor.map (e i).hom ≫ D.hom q a b ha hb ≫
      (F.map b.op.toLoc).toFunctor.map (e j).inv
  pullHom_hom _ _ k q q' hq i j a b ha hb ka kb hka hkb := by
    rw [pullHom_map_comp, pullHom_comp_map, D.pullHom_hom k q q' hq a b ha hb ka kb hka hkb]
  hom_self _ q i a ha := by simp [D.hom_self q a ha, ← Functor.map_comp]
  hom_comp _ q i j k a b d ha hb hd := by
    simp [Category.assoc, ← Functor.map_comp_assoc]

/-- Changing objects retains the original datum up to its specified component isomorphisms. -/
def changeObjectsIso {J : Type w} {Y : J → C} {S : C} {g : ∀ i, Y i ⟶ S}
    (D : F.DescentData g) (A : ∀ i, F.obj (.mk (op (Y i))))
    (e : ∀ i, A i ≅ D.obj i) : changeObjects D A e ≅ D :=
  Pseudofunctor.DescentData.isoMk e (by
    intro Z q i j a b ha hb
    simp [changeObjects, Category.assoc, ← Functor.map_comp])

/-- Transition arrows expressed on composite maps into the coproduct. -/
structure ComponentData {S : C} (p : c.pt ⟶ S) (A : F.obj (.mk (op c.pt))) where
  hom : ∀ {Z : C} (q : Z ⟶ S) {i j : I} (a : Z ⟶ X i) (b : Z ⟶ X j)
    (_ : a ≫ c.inj i ≫ p = q) (_ : b ≫ c.inj j ≫ p = q),
    (F.map (a ≫ c.inj i).op.toLoc).toFunctor.obj A ⟶
      (F.map (b ≫ c.inj j).op.toLoc).toFunctor.obj A
  naturality : ∀ {Z W : C} (k : W ⟶ Z) (q : Z ⟶ S) {i j : I}
    (a : Z ⟶ X i) (b : Z ⟶ X j) (ha : a ≫ c.inj i ≫ p = q)
    (hb : b ≫ c.inj j ≫ p = q) (ka : W ⟶ X i) (kb : W ⟶ X j)
    (hka : k ≫ a = ka) (hkb : k ≫ b = kb),
    pullHom (hom q a b ha hb) k (ka ≫ c.inj i) (kb ≫ c.inj j)
      (by rw [← hka, Category.assoc]) (by rw [← hkb, Category.assoc]) =
      hom (k ≫ q) ka kb (by rw [← hka, Category.assoc, ha])
        (by rw [← hkb, Category.assoc, hb])
  identity : ∀ {Z : C} (q : Z ⟶ S) {i : I} (a : Z ⟶ X i)
    (ha : a ≫ c.inj i ≫ p = q), hom q a a ha ha = 𝟙 _
  cocycle : ∀ {Z : C} (q : Z ⟶ S) {i j k : I}
    (a : Z ⟶ X i) (b : Z ⟶ X j) (d : Z ⟶ X k)
    (ha : a ≫ c.inj i ≫ p = q) (hb : b ≫ c.inj j ≫ p = q)
    (hd : d ≫ c.inj k ≫ p = q),
    hom q a b ha hb ≫ hom q b d hb hd = hom q a d ha hd

/-- Reexpress a family datum using an object whose component restrictions are specified. -/
def componentData {S : C} (p : c.pt ⟶ S)
    (D : F.DescentData (fun i => c.inj i ≫ p))
    (A : F.obj (.mk (op c.pt)))
    (e : ∀ i, (F.map (c.inj i).op.toLoc).toFunctor.obj A ≅ D.obj i) :
    ComponentData (F := F) c p A := by
  let E := changeObjects D (fun i => (F.map (c.inj i).op.toLoc).toFunctor.obj A) e
  refine {
    hom := fun {_} q {i j} a b ha hb =>
      (F.mapComp' (c.inj i).op.toLoc a.op.toLoc (a ≫ c.inj i).op.toLoc rfl).hom.toNatTrans.app A ≫
      E.hom q a b ha hb ≫
      (F.mapComp' (c.inj j).op.toLoc b.op.toLoc (b ≫ c.inj j).op.toLoc rfl).inv.toNatTrans.app A
    naturality := ?_
    identity := ?_
    cocycle := ?_ }
  · intro Z W k q i j a b ha hb ka kb hka hkb
    rw [← E.pullHom_hom k q (k ≫ q) rfl a b ha hb ka kb hka hkb]
    dsimp only [pullHom]
    simp only [Functor.map_comp, Category.assoc]
    rw [F.mapComp'₀₂₃_hom_comp_mapComp'_hom_whiskerRight_app_assoc
      (c.inj i).op.toLoc a.op.toLoc k.op.toLoc (a ≫ c.inj i).op.toLoc
        ka.op.toLoc (ka ≫ c.inj i).op.toLoc rfl (by grind) (by grind),
      F.mapComp'_inv_whiskerRight_mapComp'₀₂₃_inv_app
        (c.inj j).op.toLoc b.op.toLoc k.op.toLoc (b ≫ c.inj j).op.toLoc
        kb.op.toLoc (kb ≫ c.inj j).op.toLoc rfl (by grind) (by grind)]
    rfl
  · intro Z q i a ha
    rw [E.hom_self q a ha]
    dsimp only [E, changeObjects]
    simp
  · intro Z q i j k a b d ha hb hd
    simp [Category.assoc]

lemma map_eq_of_pullHom_eq {B₁ B₂ Z W : C}
    {M : F.obj (.mk (op B₁))} {N : F.obj (.mk (op B₂))}
    {a : Z ⟶ B₁} {b : Z ⟶ B₂}
    (φ ψ : (F.map a.op.toLoc).toFunctor.obj M ⟶ (F.map b.op.toLoc).toFunctor.obj N)
    (k : W ⟶ Z) (ka : W ⟶ B₁) (kb : W ⟶ B₂)
    (hka : k ≫ a = ka) (hkb : k ≫ b = kb)
    (h : pullHom φ k ka kb hka hkb = pullHom ψ k ka kb hka hkb) :
    (F.map k.op.toLoc).toFunctor.map φ = (F.map k.op.toLoc).toFunctor.map ψ := by
  rw [map_eq_pullHom φ k ka kb hka hkb, map_eq_pullHom ψ k ka kb hka hkb, h]

lemma pullHom_comp {B₁ B₂ B₃ Z W : C}
    {M : F.obj (.mk (op B₁))} {N : F.obj (.mk (op B₂))} {P : F.obj (.mk (op B₃))}
    {a : Z ⟶ B₁} {b : Z ⟶ B₂} {d : Z ⟶ B₃}
    (φ : (F.map a.op.toLoc).toFunctor.obj M ⟶ (F.map b.op.toLoc).toFunctor.obj N)
    (ψ : (F.map b.op.toLoc).toFunctor.obj N ⟶ (F.map d.op.toLoc).toFunctor.obj P)
    (k : W ⟶ Z) (ka : W ⟶ B₁) (kb : W ⟶ B₂) (kd : W ⟶ B₃)
    (ha : k ≫ a = ka) (hb : k ≫ b = kb) (hd : k ≫ d = kd) :
    pullHom (φ ≫ ψ) k ka kd ha hd =
      pullHom φ k ka kb ha hb ≫ pullHom ψ k kb kd hb hd := by
  simp [pullHom, Functor.map_comp, Category.assoc]

include hC hPB
/-- Arrow gluing on the chosen pullbacks of a universal coproduct. -/
def baseChangeGlueHom (hF : EffectiveCoproducts.{w} F) {Z A B : C}
    {M : F.obj (.mk (op A))} {N : F.obj (.mk (op B))}
    (z : Z ⟶ c.pt) (a : Z ⟶ A) (b : Z ⟶ B)
    (da : ∀ i, pullback (c.inj i) z ⟶ A) (db : ∀ i, pullback (c.inj i) z ⟶ B)
    (ha : ∀ i, pullback.snd (c.inj i) z ≫ a = da i)
    (hb : ∀ i, pullback.snd (c.inj i) z ≫ b = db i)
    (θ : ∀ i, (F.map (da i).op.toLoc).toFunctor.obj M ⟶
      (F.map (db i).op.toLoc).toFunctor.obj N) :
    (F.map a.op.toLoc).toFunctor.obj M ⟶ (F.map b.op.toLoc).toFunctor.obj N :=
  glueHom hF (baseChangeCofan c z) (baseChangeIsColimit c hC z) a b da db ha hb θ

lemma pullHom_baseChangeGlueHom (hF : EffectiveCoproducts.{w} F) {Z A B : C}
    {M : F.obj (.mk (op A))} {N : F.obj (.mk (op B))}
    (z : Z ⟶ c.pt) (a : Z ⟶ A) (b : Z ⟶ B)
    (da : ∀ i, pullback (c.inj i) z ⟶ A) (db : ∀ i, pullback (c.inj i) z ⟶ B)
    (ha : ∀ i, pullback.snd (c.inj i) z ≫ a = da i)
    (hb : ∀ i, pullback.snd (c.inj i) z ≫ b = db i)
    (θ : ∀ i, (F.map (da i).op.toLoc).toFunctor.obj M ⟶
      (F.map (db i).op.toLoc).toFunctor.obj N) (i : I) :
    pullHom (baseChangeGlueHom c hC hF z a b da db ha hb θ)
      (pullback.snd (c.inj i) z) (da i) (db i) (ha i) (hb i) = θ i :=
  pullHom_glueHom hF (baseChangeCofan c z) (baseChangeIsColimit c hC z) a b da db ha hb θ i

/-- Arrows between pullbacks are detected on all pairs of summands. -/
lemma pair_hom_ext (hF : EffectiveCoproducts.{w} F) {Z : C}
    {M N : F.obj (.mk (op c.pt))} (a b : Z ⟶ c.pt)
    (φ ψ : (F.map a.op.toLoc).toFunctor.obj M ⟶ (F.map b.op.toLoc).toFunctor.obj N)
    (h : ∀ {W : C} (k : W ⟶ Z) {i j : I} (x : W ⟶ X i) (y : W ⟶ X j)
      (hx : k ≫ a = x ≫ c.inj i) (hy : k ≫ b = y ≫ c.inj j),
      pullHom φ k (x ≫ c.inj i) (y ≫ c.inj j) hx hy =
      pullHom ψ k (x ≫ c.inj i) (y ≫ c.inj j) hx hy) : φ = ψ := by
  apply baseChangeCofan_hom_ext c hC hF a
  intro i
  let r := pullback.snd (c.inj i) a
  let x := pullback.fst (c.inj i) a
  apply map_eq_of_pullHom_eq φ ψ r (x ≫ c.inj i) (r ≫ b) pullback.condition.symm rfl
  apply baseChangeCofan_hom_ext c hC hF (r ≫ b)
  intro j
  let t := pullback.snd (c.inj j) (r ≫ b)
  let y := pullback.fst (c.inj j) (r ≫ b)
  apply map_eq_of_pullHom_eq _ _ t ((t ≫ x) ≫ c.inj i) (y ≫ c.inj j)
    (Category.assoc _ _ _).symm pullback.condition.symm
  rw [pullHom_pullHom, pullHom_pullHom]
  exact h (t ≫ r) (t ≫ x) y (by simp [r, x, Category.assoc, pullback.condition])
    (by simpa only [Category.assoc] using (pullback.condition (f := c.inj j) (g := r ≫ b)).symm)

namespace ComponentData

variable {S : C} {p : c.pt ⟶ S} {A : F.obj (.mk (op c.pt))}
    (D : ComponentData (F := F) c p A)

/-- Glue transition maps first in the second summand and then in the first. -/
def aggregateHom (hF : EffectiveCoproducts.{w} F) {Z : C}
    (q : Z ⟶ S) (a b : Z ⟶ c.pt) (ha : a ≫ p = q) (hb : b ≫ p = q) :
    (F.map a.op.toLoc).toFunctor.obj A ⟶ (F.map b.op.toLoc).toFunctor.obj A :=
  baseChangeGlueHom c hC hF a a b
    (fun i => pullback.fst (c.inj i) a ≫ c.inj i)
    (fun i => pullback.snd (c.inj i) a ≫ b)
    (fun _ => pullback.condition.symm) (fun _ => rfl) (fun i =>
      let r := pullback.snd (c.inj i) a
      let x := pullback.fst (c.inj i) a
      baseChangeGlueHom c hC hF (r ≫ b)
        (x ≫ c.inj i) (r ≫ b)
        (fun j => (pullback.snd (c.inj j) (r ≫ b) ≫ x) ≫ c.inj i)
        (fun j => pullback.fst (c.inj j) (r ≫ b) ≫ c.inj j)
        (fun _ => (Category.assoc _ _ _).symm) (fun _ => pullback.condition.symm)
        (fun j => D.hom (pullback.snd (c.inj j) (r ≫ b) ≫ r ≫ q)
          (pullback.snd (c.inj j) (r ≫ b) ≫ x) (pullback.fst (c.inj j) (r ≫ b))
          (by simp [x, r, Category.assoc, pullback.condition_assoc, ha])
          (by simp [Category.assoc, pullback.condition_assoc, hb])))

lemma pullHom_aggregateHom_charts (hF : EffectiveCoproducts.{w} F) {Z : C}
    (q : Z ⟶ S) (a b : Z ⟶ c.pt) (ha : a ≫ p = q) (hb : b ≫ p = q) (i j : I) :
    let r := pullback.snd (c.inj i) a
    let x := pullback.fst (c.inj i) a
    let t := pullback.snd (c.inj j) (r ≫ b)
    let y := pullback.fst (c.inj j) (r ≫ b)
    pullHom (pullHom (D.aggregateHom c hC hF q a b ha hb) r (x ≫ c.inj i) (r ≫ b)
      pullback.condition.symm rfl) t ((t ≫ x) ≫ c.inj i) (y ≫ c.inj j)
      (Category.assoc _ _ _).symm pullback.condition.symm =
    D.hom (t ≫ r ≫ q) (t ≫ x) y
      (by simp [x, r, Category.assoc, pullback.condition_assoc, ha])
      (by simp [y, t, Category.assoc, pullback.condition_assoc, hb]) := by
  dsimp only
  unfold aggregateHom
  rw [pullHom_baseChangeGlueHom, pullHom_baseChangeGlueHom]

/-- The glued transition has its prescribed value on every map through two summands. -/
lemma pullHom_aggregateHom (hF : EffectiveCoproducts.{w} F) {Z W : C}
    (q : Z ⟶ S) (a b : Z ⟶ c.pt) (ha : a ≫ p = q) (hb : b ≫ p = q)
    (k : W ⟶ Z) {i j : I} (x : W ⟶ X i) (y : W ⟶ X j)
    (hx : k ≫ a = x ≫ c.inj i) (hy : k ≫ b = y ≫ c.inj j) :
    pullHom (D.aggregateHom c hC hF q a b ha hb) k (x ≫ c.inj i) (y ≫ c.inj j) hx hy =
      D.hom (k ≫ q) x y (by rw [← Category.assoc, ← hx, Category.assoc, ha])
        (by rw [← Category.assoc, ← hy, Category.assoc, hb]) := by
  let r := pullback.snd (c.inj i) a
  let z := pullback.fst (c.inj i) a
  let t := pullback.snd (c.inj j) (r ≫ b)
  let v := pullback.fst (c.inj j) (r ≫ b)
  let l := pullback.lift x k hx.symm
  have hl : l ≫ r = k := pullback.lift_snd _ _ _
  let m : W ⟶ pullback (c.inj j) (r ≫ b) :=
    pullback.lift y l (by rw [← Category.assoc, hl, hy])
  have hm : m ≫ t = l := pullback.lift_snd _ _ _
  have hz : m ≫ t ≫ z = x := by rw [← Category.assoc, hm]; exact pullback.lift_fst _ _ _
  have hv : m ≫ v = y := pullback.lift_fst _ _ _
  have hk : m ≫ t ≫ r = k := by rw [← Category.assoc, hm, hl]
  have H := congrArg (fun θ => pullHom θ m (x ≫ c.inj i) (y ≫ c.inj j)
    (by change m ≫ ((t ≫ z) ≫ c.inj i) = _
        simpa only [← Category.assoc] using congrArg (fun a => a ≫ c.inj i) hz)
      (by change m ≫ (v ≫ c.inj j) = _; rw [← Category.assoc, hv]))
    (D.pullHom_aggregateHom_charts c hC hF q a b ha hb i j)
  rw [pullHom_pullHom, pullHom_pullHom] at H
  rw [D.naturality m (t ≫ r ≫ q) (t ≫ z) v
    (by simp [t, r, z, Category.assoc, pullback.condition_assoc, ha])
    (by simp [v, t, Category.assoc, pullback.condition_assoc, hb]) x y hz hv] at H
  have hk' : (m ≫ t) ≫ r = k := by rw [hm, hl]
  dsimp only [t, r] at hk'
  simpa only [t, r, ← Category.assoc, hk'] using H

/-- Glued transitions commute with arbitrary pullback. -/
lemma aggregateHom_naturality (hF : EffectiveCoproducts.{w} F) {Z W : C}
    (k : W ⟶ Z) (q : Z ⟶ S) (q' : W ⟶ S) (hq : k ≫ q = q')
    (a b : Z ⟶ c.pt) (ha : a ≫ p = q) (hb : b ≫ p = q)
    (ka kb : W ⟶ c.pt) (hka : k ≫ a = ka) (hkb : k ≫ b = kb) :
    pullHom (D.aggregateHom c hC hF q a b ha hb) k ka kb hka hkb =
      D.aggregateHom c hC hF q' ka kb
        (by rw [← hka, Category.assoc, ha, hq]) (by rw [← hkb, Category.assoc, hb, hq]) := by
  subst q'
  apply pair_hom_ext c hC hF ka kb
  intro V l i j x y hx hy
  rw [pullHom_pullHom,
    D.pullHom_aggregateHom c hC hF q a b ha hb (l ≫ k) x y
      (by rw [Category.assoc, hka, hx]) (by rw [Category.assoc, hkb, hy]),
    D.pullHom_aggregateHom]
  simp only [Category.assoc]

/-- The aggregate transition along a repeated map is the identity. -/
lemma aggregateHom_identity (hF : EffectiveCoproducts.{w} F) {Z : C}
    (q : Z ⟶ S) (a : Z ⟶ c.pt) (ha : a ≫ p = q) :
    D.aggregateHom c hC hF q a a ha ha = 𝟙 _ := by
  apply baseChangeCofan_hom_ext c hC hF a
  intro i
  apply map_eq_of_pullHom_eq _ _ (pullback.snd (c.inj i) a)
    (pullback.fst (c.inj i) a ≫ c.inj i) (pullback.fst (c.inj i) a ≫ c.inj i)
    pullback.condition.symm pullback.condition.symm
  rw [D.pullHom_aggregateHom c hC hF q a a ha ha _ _ _
    pullback.condition.symm pullback.condition.symm, D.identity]
  simp [pullHom]

/-- The aggregate transitions satisfy the cocycle law. -/
lemma aggregateHom_cocycle (hF : EffectiveCoproducts.{w} F) {Z : C}
    (q : Z ⟶ S) (a b d : Z ⟶ c.pt)
    (ha : a ≫ p = q) (hb : b ≫ p = q) (hd : d ≫ p = q) :
    D.aggregateHom c hC hF q a b ha hb ≫ D.aggregateHom c hC hF q b d hb hd =
      D.aggregateHom c hC hF q a d ha hd := by
  apply pair_hom_ext c hC hF a d
  intro W k i l x z hx hz
  apply baseChangeCofan_hom_ext c hC hF (k ≫ b)
  intro j
  let t := pullback.snd (c.inj j) (k ≫ b)
  let y := pullback.fst (c.inj j) (k ≫ b)
  apply map_eq_of_pullHom_eq _ _ t ((t ≫ x) ≫ c.inj i) ((t ≫ z) ≫ c.inj l)
    (Category.assoc _ _ _).symm (Category.assoc _ _ _).symm
  rw [pullHom_pullHom, pullHom_pullHom]
  have hxa : (t ≫ k) ≫ a = (t ≫ x) ≫ c.inj i := by simp only [Category.assoc, hx]
  have hyb : (t ≫ k) ≫ b = y ≫ c.inj j := by
    simpa only [Category.assoc] using (pullback.condition (f := c.inj j) (g := k ≫ b)).symm
  have hzd : (t ≫ k) ≫ d = (t ≫ z) ≫ c.inj l := by simp only [Category.assoc, hz]
  rw [pullHom_comp _ _ (t ≫ k) ((t ≫ x) ≫ c.inj i) (y ≫ c.inj j) ((t ≫ z) ≫ c.inj l)
      hxa hyb hzd,
    D.pullHom_aggregateHom c hC hF q a b ha hb (t ≫ k) (t ≫ x) y hxa hyb,
    D.pullHom_aggregateHom c hC hF q b d hb hd (t ≫ k) y (t ≫ z) hyb hzd,
    D.pullHom_aggregateHom c hC hF q a d ha hd (t ≫ k) (t ≫ x) (t ≫ z) hxa hzd,
    D.cocycle]

/-- Effective coproduct restriction assembles component transitions into aggregate descent data. -/
def aggregateData (hF : EffectiveCoproducts.{w} F) : F.DescentData (fun _ : Unit => p) where
  obj _ := A
  hom _ q _ _ a b ha hb := D.aggregateHom c hC hF q a b ha hb
  pullHom_hom _ _ k q q' hq _ _ a b ha hb ka kb hka hkb :=
    D.aggregateHom_naturality c hC hF k q q' hq a b ha hb ka kb hka hkb
  hom_self _ q _ a ha := D.aggregateHom_identity c hC hF q a ha
  hom_comp _ q _ _ _ a b d ha hb hd := D.aggregateHom_cocycle c hC hF q a b d ha hb hd

/-- On two summands the assembled datum recovers the original transition. -/
lemma aggregateHom_summands (hF : EffectiveCoproducts.{w} F) {Z : C}
    (q : Z ⟶ S) {i j : I} (a : Z ⟶ X i) (b : Z ⟶ X j)
    (ha : a ≫ c.inj i ≫ p = q) (hb : b ≫ c.inj j ≫ p = q) :
    D.aggregateHom c hC hF q (a ≫ c.inj i) (b ≫ c.inj j)
      (by simpa only [Category.assoc] using ha) (by simpa only [Category.assoc] using hb) =
    D.hom q a b ha hb := by
  simpa only [pullHom_id, Category.id_comp] using
    D.pullHom_aggregateHom c hC hF q (a ≫ c.inj i) (b ≫ c.inj j)
      (by simpa only [Category.assoc] using ha) (by simpa only [Category.assoc] using hb)
      (𝟙 Z) a b (Category.id_comp _) (Category.id_comp _)

end ComponentData

/-- Restricting an assembled aggregate datum recovers the supplied family datum. -/
def aggregateRecoveryIso (hF : EffectiveCoproducts.{w} F) {S : C} (p : c.pt ⟶ S)
    (D : F.DescentData (fun i => c.inj i ≫ p))
    (A : F.obj (.mk (op c.pt)))
    (e : ∀ i, (F.map (c.inj i).op.toLoc).toFunctor.obj A ≅ D.obj i) :
    (aggregateRestriction (F := F) c p).obj
      ((componentData c p D A e).aggregateData c hC hF) ≅ D :=
  Pseudofunctor.DescentData.isoMk e (by
    intro Z q i j a b ha hb
    dsimp only [aggregateRestriction, Pseudofunctor.DescentData.pullFunctor,
      Pseudofunctor.DescentData.pullFunctorObj]
    rw [Pseudofunctor.DescentData.pullFunctorObjHom_eq_assoc _ _ _ a b q
      (a ≫ c.inj i) (b ≫ c.inj j) rfl (hb.trans ha.symm) (by simpa using ha) rfl rfl]
    dsimp only [ComponentData.aggregateData]
    rw [ComponentData.aggregateHom_summands _ _ _ _ q a b ha hb]
    dsimp only [componentData, changeObjects]
    simp [Category.assoc, ← Functor.map_comp])

/-- Family descent and singleton descent along its coproduct aggregate are equivalent. -/
theorem aggregateRestriction_isEquivalence (hF : EffectiveCoproducts.{w} F)
    {S : C} (p : c.pt ⟶ S) : (aggregateRestriction (F := F) c p).IsEquivalence := by
  have hff := aggregateRestrictionFullyFaithful c hC hF p
  have := hff.full
  have := hff.faithful
  have := hF c hC.isColimit
  have : (aggregateRestriction (F := F) c p).EssSurj := ⟨fun D => by
    let A := (restriction F (Cofan.inj c)).objPreimage D.obj
    let e (i : I) : (F.map (c.inj i).op.toLoc).toFunctor.obj A ≅ D.obj i :=
      (Pi.eval _ i).mapIso ((restriction F (Cofan.inj c)).objObjPreimageIso D.obj)
    exact ⟨(componentData c p D A e).aggregateData c hC hF,
      ⟨aggregateRecoveryIso c hC hF p D A e⟩⟩⟩
  exact {}

end Aggregate

end SquareKit.CoproductDescent
