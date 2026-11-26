import SquareKit.Internal.Cubical.DiscreteEquivalences
import SquareKit.Internal.Cubical.EquivalenceFamilySubstitution
import SquareKit.Internal.Cubical.CompositionalUnivalence
import SquareKit.Internal.Cubical.CartesianWitnesses

/-! Constant presentations classify complete native equivalence records.
The inverse laws retain generic fiber centers and every contraction argument. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u
namespace DiscreteRecords

theorem constant_path_value {Γ : Context.{u}} {S : Type u}
    {a b : Term (constantFamily Γ S)} {x : Γ.Elements}
    (p : (homogeneousPath (constantFamily Γ S) a b).obj x)
    {y : Γ.Elements} (f : x ⟶ y) (r : (interval Γ).obj y) :
    p.val.val f r = a.val y := by
  let P := homogeneousPath (constantFamily Γ S) a b
  let τ := projection P
  let t := Term.map (EquivalenceFamilies.homogeneousReindexIso
    (constantFamily Γ S) a b τ).hom (generic P)
  let z := extendObj P y (P.map f p)
  have h := constant_section_interval (pathApp t) z r ((endpoint (total P) false).val z)
  have hz := congrArg (fun s => s.val z) (pathApp_zero t)
  have hh := h.trans hz
  change p.val.val (f ≫ 𝟙 y) r = a.val y at hh
  simpa only [Category.comp_id] using hh

theorem constant_path_subsingleton {Γ : Context.{u}} {S : Type u}
    (a b : Term (constantFamily Γ S)) (x : Γ.Elements) :
    Subsingleton ((homogeneousPath (constantFamily Γ S) a b).obj x) := by
  constructor
  intro p q
  apply Subtype.ext
  apply PiElement.ext
  intro y f r
  exact (constant_path_value p f r).trans (constant_path_value q f r).symm


theorem presented_path_value {Γ : Context.{u}} {A : Family Γ} {S : Type u}
    (e : A ≅ constantFamily Γ S) {a b : Term A} {x : Γ.Elements}
    (p : (homogeneousPath A a b).obj x)
    {y : Γ.Elements} (f : x ⟶ y) (r : (interval Γ).obj y) :
    p.val.val f r = a.val y := by
  let P := homogeneousPath A a b
  let τ := projection P
  let t := Term.map (EquivalenceFamilies.homogeneousReindexIso A a b τ).hom (generic P)
  let q := homogeneousPathMap (Functor.whiskerLeft τ.mapElements e.hom) t
  let z := extendObj P y (P.map f p)
  have h := constant_section_interval (pathApp q) z r ((endpoint (total P) false).val z)
  have hz := congrArg (fun s => s.val z) (pathApp_zero q)
  have hh := h.trans hz
  change e.hom.app y (p.val.val (f ≫ 𝟙 y) r) = e.hom.app y (a.val y) at hh
  have hi : Function.Injective (e.hom.app y) := by
    intro v w hv
    have hl (v : A.obj y) : e.inv.app y (e.hom.app y v) = v :=
      congrArg (fun k => k.app y v) e.hom_inv_id
    exact (hl v).symm.trans ((congrArg (e.inv.app y) hv).trans (hl w))
  apply hi
  simpa only [Category.comp_id] using hh

theorem presented_path_subsingleton {Γ : Context.{u}} {A : Family Γ} {S : Type u}
    (e : A ≅ constantFamily Γ S) (a b : Term A) (x : Γ.Elements) :
    Subsingleton ((homogeneousPath A a b).obj x) := by
  constructor
  intro p q
  apply Subtype.ext
  apply PiElement.ext
  intro y f r
  exact (presented_path_value e p f r).trans (presented_path_value e q f r).symm

theorem presented_path_endpoints {Γ : Context.{u}} {A : Family Γ} {S : Type u}
    (e : A ≅ constantFamily Γ S) {a b : Term A} {x : Γ.Elements}
    (p : (homogeneousPath A a b).obj x) : a.val x = b.val x := by
  exact (presented_path_value e p (𝟙 x) ((endpoint Γ true).val x)).symm.trans
    (p.property (𝟙 x)).2

theorem fiber_subsingleton {Γ : Context.{u}} {A B : Family Γ} {T : Type u}
    (j : B ≅ constantFamily Γ T) (f : A ⟶ B)
    (hi : ∀ x, Function.Injective (f.app x)) (b : Term B) (x : Γ.Elements) :
    Subsingleton ((homotopyFiber f b).obj x) := by
  constructor
  rintro ⟨a,p⟩ ⟨a',q⟩
  have hp := presented_path_endpoints (Functor.isoWhiskerLeft (projection A).mapElements j) p
  have hq := presented_path_endpoints (Functor.isoWhiskerLeft (projection A).mapElements j) q
  have ha : a = a' := hi x (hp.trans hq.symm)
  subst a'
  have he := (presented_path_subsingleton
    (Functor.isoWhiskerLeft (projection A).mapElements j) _ _ _).elim p q
  cases he
  rfl

theorem contractible_subsingleton {Γ : Context.{u}} {A : Family Γ}
    (h : ∀ x, Subsingleton (A.obj x)) : Subsingleton (HomotopyContractible A) := by
  constructor
  rintro ⟨a,p⟩ ⟨b,q⟩
  have he : a = b := Term.ext (fun x => (h x).elim _ _)
  subst b
  congr 1
  apply Term.ext
  intro x
  apply Subtype.ext
  apply PiElement.ext
  intro y f r
  exact (h _).elim _ _

/-- Uniqueness is derived from singleton native fibers, including contraction bodies. -/
theorem equivalence_subsingleton {Γ : Context.{u}} {A B : Family Γ} {S T : Type u}
    (i : A ≅ constantFamily Γ S) (j : B ≅ constantFamily Γ T)
    (F : Filling A) (hF : F.Lawful) (f : A ⟶ B) :
    Subsingleton (HomotopyEquivalence f) := by
  constructor
  intro E H
  let k := E.discreteIso (PathDiscrete.of_iso (constant_pathDiscrete S) i) F hF
    (PathDiscrete.of_iso (constant_pathDiscrete T) j)
  have hi (x : Γ.Elements) : Function.Injective (f.app x) := by
    intro a b h
    have hl (a : A.obj x) : k.inv.app x (f.app x a) = a :=
      congrArg (fun m => m.app x a) k.hom_inv_id
    exact (hl a).symm.trans ((congrArg (k.inv.app x) h).trans (hl b))
  have hf := fiber_subsingleton
    (Functor.isoWhiskerLeft (projection B).mapElements j)
    (Functor.whiskerLeft (projection B).mapElements f)
    (fun x => hi ((projection B).mapElements.obj x)) (generic B)
  have he := (contractible_subsingleton hf).elim E.fibers H.fibers
  cases E
  cases H
  cases he
  rfl


def isoSection {Γ : Context.{u}} {S T : Type u}
    (k : constantFamily Γ S ≅ constantFamily Γ T) :
    Term (constantFamily Γ (S ≃ T)) where
  val x := (k.app x).toEquiv
  property f := by
    apply Equiv.ext
    intro s
    exact (k.hom.naturality_apply f s).symm

def sectionIso {Γ : Context.{u}} {S T : Type u}
    (t : Term (constantFamily Γ (S ≃ T))) :
    constantFamily Γ S ≅ constantFamily Γ T :=
  NatIso.ofComponents (fun x => (t.val x).toIso) (by
    intro x y f
    apply ConcreteCategory.hom_ext
    intro s
    exact congrArg (fun e : S ≃ T => e s) (t.property f).symm)

theorem record_ext {Γ : Context.{u}} {A B : Family Γ} {S T : Type u}
    (i : A ≅ constantFamily Γ S) (j : B ≅ constantFamily Γ T)
    (F : Filling A) (hF : F.Lawful)
    (p q : Σ f : A ⟶ B, HomotopyEquivalence f) (h : p.1 = q.1) : p = q := by
  rcases p with ⟨f,E⟩
  rcases q with ⟨g,H⟩
  dsimp at h
  subst g
  have he := (equivalence_subsingleton i j F hF f).elim E H
  cases he
  rfl

noncomputable def recordSections {Γ : Context.{u}} {A B : Family Γ} {S T : Type u}
    (i : A ≅ constantFamily Γ S) (j : B ≅ constantFamily Γ T)
    (F : Filling A) (hF : F.Lawful) :
    (Σ f : A ⟶ B, HomotopyEquivalence f) ≃ Term (constantFamily Γ (S ≃ T)) where
  toFun p := isoSection (i.symm ≪≫ p.2.discreteIso
    (PathDiscrete.of_iso (constant_pathDiscrete S) i) F hF
    (PathDiscrete.of_iso (constant_pathDiscrete T) j) ≪≫ j)
  invFun t := ⟨(i ≪≫ sectionIso t ≪≫ j.symm).hom,
    HomotopyEquivalence.ofIso (i ≪≫ sectionIso t ≪≫ j.symm)⟩
  left_inv p := by
    apply record_ext i j F hF
    ext x a
    change j.inv.app x (j.hom.app x (p.1.app x (i.inv.app x (i.hom.app x a)))) =
      p.1.app x a
    have hi := congrArg (fun k => k.app x a) i.hom_inv_id
    change i.inv.app x (i.hom.app x a) = a at hi
    rw [hi]
    exact congrArg (fun k => k.app x (p.1.app x a)) j.hom_inv_id
  right_inv t := by
    apply Term.ext
    intro x
    apply Equiv.ext
    intro s
    change j.hom.app x (j.inv.app x (Equiv.toFun (t.val x) (i.hom.app x (i.inv.app x s)))) =
      Equiv.toFun (t.val x) s
    have hi := congrArg (fun k => k.app x s) i.inv_hom_id
    change i.hom.app x (i.inv.app x s) = s at hi
    rw [hi]
    exact congrArg (fun k => k.app x (Equiv.toFun (t.val x) s)) j.inv_hom_id

/-- Classification after arbitrary substitution, with the complete encoded records. -/
noncomputable def presentedSections {Γ Δ : Context.{u}} {A B : Family Γ} {S T : Type u}
    (i : A ≅ constantFamily Γ S) (j : B ≅ constantFamily Γ T)
    (F : Filling A) (hF : F.Lawful) (σ : Δ ⟶ Γ) :
    Term (reindex (EquivalenceFamilies.equiv A B) σ) ≃
      Term (constantFamily Δ (S ≃ T)) :=
  (EquivalenceFamilies.equivReindexSections A B σ).symm.trans
    (recordSections (Functor.isoWhiskerLeft σ.mapElements i)
      (Functor.isoWhiskerLeft σ.mapElements j) (F.reindex σ) (hF.reindex σ))


theorem presentedSections_natural {Γ Δ Θ : Context.{u}} {A B : Family Γ} {S T : Type u}
    (i : A ≅ constantFamily Γ S) (j : B ≅ constantFamily Γ T)
    (F : Filling A) (hF : F.Lawful) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (z : Term (reindex (EquivalenceFamilies.equiv A B) σ)) :
    presentedSections i j F hF (τ ≫ σ) (z.reindex τ) =
      (presentedSections i j F hF σ z).reindex τ := by
  obtain ⟨⟨f,E⟩,rfl⟩ := (EquivalenceFamilies.equivReindexSections A B σ).surjective z
  rw [← EquivalenceFamilies.equivReindexSections_comp]
  simp only [presentedSections, Equiv.trans_apply, Equiv.symm_apply_apply]
  apply Term.ext
  intro x
  apply Equiv.ext
  intro s
  rfl

private def mapOfSections {Γ : Context.{u}} {A B : Family Γ}
    (Φ : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ), Term (reindex A σ) → Term (reindex B σ)) : A ⟶ B where
  app x := TypeCat.ofHom (fun a => (Φ (projection A) (generic A)).val (extendObj A x a))
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro a
    exact ((Φ (projection A) (generic A)).property (extendHom A f a)).symm

private theorem mapOfSections_apply {Γ : Context.{u}} {A B : Family Γ}
    (Φ : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ), Term (reindex A σ) → Term (reindex B σ))
    (hn : ∀ {Δ Θ : Context.{u}} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (z : Term (reindex A σ)),
      Φ (τ ≫ σ) (z.reindex τ) = (Φ σ z).reindex τ)
    {Δ : Context.{u}} (σ : Δ ⟶ Γ) (z : Term (reindex A σ)) :
    Term.map (Functor.whiskerLeft σ.mapElements (mapOfSections Φ)) z = Φ σ z :=
  (hn (projection A) (pair σ z) (generic A)).symm

noncomputable def isoOfSections {Γ : Context.{u}} {A B : Family Γ}
    (Φ : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ), Term (reindex A σ) ≃ Term (reindex B σ))
    (hn : ∀ {Δ Θ : Context.{u}} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (z : Term (reindex A σ)),
      Φ (τ ≫ σ) (z.reindex τ) = (Φ σ z).reindex τ) : A ≅ B := by
  have hm {Δ Θ : Context.{u}} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (z : Term (reindex B σ)) :
      (Φ (τ ≫ σ)).symm (z.reindex τ) = ((Φ σ).symm z).reindex τ := by
    apply (Φ (τ ≫ σ)).injective
    exact ((Φ (τ ≫ σ)).apply_symm_apply (z.reindex τ)).trans
      ((hn σ τ ((Φ σ).symm z)).trans
        (congrArg (fun t => t.reindex τ) ((Φ σ).apply_symm_apply z))).symm
  refine {
    hom := mapOfSections (fun σ => Φ σ)
    inv := mapOfSections (fun σ => (Φ σ).symm)
    hom_inv_id := ?_
    inv_hom_id := ?_ }
  · ext x a
    let σ := projection A
    let z := generic A
    have hf := mapOfSections_apply (fun σ => Φ σ) hn σ z
    have hb := mapOfSections_apply (fun σ => (Φ σ).symm) hm σ (Φ σ z)
    have he := (congrArg (Term.map (Functor.whiskerLeft σ.mapElements
      (mapOfSections (fun σ => (Φ σ).symm)))) hf).trans
      (hb.trans ((Φ σ).symm_apply_apply z))
    exact congrArg (fun t => t.val (extendObj A x a)) he
  · ext x b
    let σ := projection B
    let z := generic B
    have hb := mapOfSections_apply (fun σ => (Φ σ).symm) hm σ z
    have hf := mapOfSections_apply (fun σ => Φ σ) hn σ ((Φ σ).symm z)
    have he := (congrArg (Term.map (Functor.whiskerLeft σ.mapElements
      (mapOfSections (fun σ => Φ σ)))) hb).trans
      (hf.trans ((Φ σ).apply_symm_apply z))
    exact congrArg (fun t => t.val (extendObj B x b)) he

noncomputable def presentedEquivIso {Γ : Context.{u}} {A B : Family Γ} {S T : Type u}
    (i : A ≅ constantFamily Γ S) (j : B ≅ constantFamily Γ T)
    (F : Filling A) (hF : F.Lawful) :
    EquivalenceFamilies.equiv A B ≅ constantFamily Γ (S ≃ T) :=
  isoOfSections (fun σ => presentedSections i j F hF σ)
    (presentedSections_natural i j F hF)


theorem presentedEquivIso_hom_reindex {Γ Δ : Context.{u}} {A B : Family Γ} {S T : Type u}
    (i : A ≅ constantFamily Γ S) (j : B ≅ constantFamily Γ T)
    (F : Filling A) (hF : F.Lawful) (σ : Δ ⟶ Γ)
    (z : Term (reindex (EquivalenceFamilies.equiv A B) σ)) :
    Term.map (Functor.whiskerLeft σ.mapElements (presentedEquivIso i j F hF).hom) z =
      presentedSections i j F hF σ z :=
  @mapOfSections_apply Γ (EquivalenceFamilies.equiv A B) (constantFamily Γ (S ≃ T))
    (fun {_} σ => presentedSections i j F hF σ)
    (fun {_ _} σ τ z => presentedSections_natural i j F hF σ τ z) Δ σ z

theorem presentedSections_encoded_apply {Γ Δ : Context.{u}} {A B : Family Γ} {S T : Type u}
    (i : A ≅ constantFamily Γ S) (j : B ≅ constantFamily Γ T)
    (F : Filling A) (hF : F.Lawful) (σ : Δ ⟶ Γ)
    (f : reindex A σ ⟶ reindex B σ) (E : HomotopyEquivalence f)
    (x : Δ.Elements) (s : S) :
    Equiv.toFun ((presentedSections i j F hF σ
      (EquivalenceFamilies.equivReindexSections A B σ ⟨f,E⟩)).val x) s =
      j.hom.app (σ.mapElements.obj x) (f.app x (i.inv.app (σ.mapElements.obj x) s)) := by
  simp only [presentedSections, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl

def constantFilling (Γ : Context.{u}) (S : Type u) : Filling (constantFamily Γ S) :=
  discreteFilling (DiscreteEquivalences.constant (PUnit.unit : PUnit)) (fun _ => S)

theorem constantFilling_lawful (Γ : Context.{u}) (S : Type u) :
    (constantFilling Γ S).Lawful :=
  discreteFilling_lawful (DiscreteEquivalences.constant (PUnit.unit : PUnit)) (fun _ => S)

/-- Constant presentations suffice: the required lawful filler is constructed. -/
noncomputable def constantPresentationIso {Γ : Context.{u}} {A B : Family Γ} {S T : Type u}
    (i : A ≅ constantFamily Γ S) (j : B ≅ constantFamily Γ T) :
    EquivalenceFamilies.equiv A B ≅ constantFamily Γ (S ≃ T) :=
  presentedEquivIso i j ((constantFilling Γ S).transport i.symm)
    (Filling.transport_lawful i.symm _ (constantFilling_lawful Γ S))

-- This specialization compares every native record over every context to a
-- finite permutation, including all generalized contraction arguments.
noncomputable def finThreeIso (Γ : Context) :
    EquivalenceFamilies.equiv (constantFamily Γ (Fin 3)) (constantFamily Γ (Fin 3)) ≅
      constantFamily Γ (Fin 3 ≃ Fin 3) :=
  constantPresentationIso (Iso.refl _) (Iso.refl _)

theorem finThreeIso_encoded_apply {Γ Δ : Context} (σ : Δ ⟶ Γ)
    (e : Fin 3 ≃ Fin 3) (x : Δ.Elements) (s : Fin 3) :
    Equiv.toFun ((Term.map (Functor.whiskerLeft σ.mapElements (finThreeIso Γ).hom)
      (EquivalenceFamilies.equivReindexSections
        (constantFamily Γ (Fin 3)) (constantFamily Γ (Fin 3)) σ
        ⟨(sectionIso (DiscreteEquivalences.constant e)).hom,
          HomotopyEquivalence.ofIso (sectionIso (DiscreteEquivalences.constant e))⟩)).val x) s = e s := by
  rw [show finThreeIso Γ = constantPresentationIso (Iso.refl _) (Iso.refl _) from rfl]
  unfold constantPresentationIso
  rw [presentedEquivIso_hom_reindex]
  exact presentedSections_encoded_apply _ _ _ _ _ _ _ _ _

/-- The fiber-center recipe selects the inverse of the actual presented map. -/
theorem discreteInverse_eq_inv {Γ : Context.{u}} {A B : Family Γ} {T : Type u}
    (j : B ≅ constantFamily Γ T) (k : A ≅ B) (E : HomotopyEquivalence k.hom) :
    E.discreteInverse = k.inv := by
  have h := E.discrete_right (PathDiscrete.of_iso (constant_pathDiscrete T) j)
  calc
    E.discreteInverse = (E.discreteInverse ≫ k.hom) ≫ k.inv := by simp
    _ = k.inv := by rw [h]; exact Category.id_comp _

section SelectedUniverseRecords
open SmallUniverse SmallUniverse.NativeUnivalence
variable {Γ : Context.{u+1}} (a b : Γ ⟶ smallFamilyCodes.{u})
  {S T : Type (u+1)}
  (i : liftedDecode a ≅ constantFamily Γ S) (j : liftedDecode b ≅ constantFamily Γ T)
  (k : liftedDecode a ≅ liftedDecode b) (E : HomotopyEquivalence k.hom)

include i in
/-- The universe-selected inverse retains its reversed-ua transport recipe. Its
left homotopy at the generic element proves equality of all map components. -/
theorem inverseMap_eq_inv : inverseMap a b k.hom E = k.inv := by
  let σ := projection (liftedDecode a)
  have h := inverseLeft (σ ≫ a) (σ ≫ b)
    (Functor.whiskerLeft σ.mapElements k.hom) (E.reindex σ) (generic (liftedDecode a))
  have he := (PathDiscrete.of_iso (constant_pathDiscrete S) i) σ h
  have hn := inverseMap_reindex a b k.hom E σ
  have hc : k.hom ≫ inverseMap a b k.hom E = 𝟙 (liftedDecode a) := by
    ext x t
    have ht := congrArg (fun s => s.val (extendObj (liftedDecode a) x t)) he
    have hm := congrArg (fun f => f.app (extendObj (liftedDecode a) x t)
      (k.hom.app x t)) hn
    exact hm.trans ht
  calc
    inverseMap a b k.hom E = k.inv ≫ (k.hom ≫ inverseMap a b k.hom E) := by simp
    _ = k.inv := by rw [hc]; exact Category.comp_id _

include i j in
/-- Equality includes the chosen inverse's entire native fiber contraction. -/
theorem inverseEquivalence_record :
    (⟨inverseMap a b k.hom E, inverseEquivalence a b k.hom E⟩ :
      Σ f : liftedDecode b ⟶ liftedDecode a, HomotopyEquivalence f) =
    ⟨k.inv, HomotopyEquivalence.ofIso k.symm⟩ := by
  apply record_ext j i ((constantFilling Γ T).transport j.symm)
    (Filling.transport_lawful j.symm _ (constantFilling_lawful Γ T))
  exact inverseMap_eq_inv a b i k E

include i j in
/-- Both chosen inverse recipes agree as maps, without replacing either recipe. -/
theorem discreteInverse_eq_inverseMap : E.discreteInverse = inverseMap a b k.hom E :=
  (discreteInverse_eq_inv j k E).trans (inverseMap_eq_inv a b i k E).symm

include i in
/-- Every generalized argument of the selected left-inverse witness is retained. -/
theorem inverseLeft_value (t : Term (liftedDecode a))
    {x y : Γ.Elements} (f : x ⟶ y) (r : (interval Γ).obj y) :
    ((inverseLeft a b k.hom E t).val x).val.val f r = t.val y :=
  (presented_path_value i _ f r).trans
    (presented_path_endpoints i ((inverseLeft a b k.hom E t).val y))

include j in
/-- The right-inverse witness has the same full generalized-value guarantee. -/
theorem inverseRight_value (t : Term (liftedDecode b))
    {x y : Γ.Elements} (f : x ⟶ y) (r : (interval Γ).obj y) :
    ((inverseRight a b k.hom E t).val x).val.val f r = t.val y :=
  (presented_path_value j _ f r).trans
    (presented_path_endpoints j ((inverseRight a b k.hom E t).val y))

end SelectedUniverseRecords

/-- The actual source composite, including its fiber contractions, agrees with
recomputation from the composed isomorphism. -/
theorem compositeEquivalence_record {Γ : Context.{u+1}}
    (a b c : Γ ⟶ smallFamilyCodes.{u}) {S T : Type (u+1)}
    (i : SmallUniverse.liftedDecode a ≅ constantFamily Γ S)
    (j : SmallUniverse.liftedDecode c ≅ constantFamily Γ T)
    (k : SmallUniverse.liftedDecode a ≅ SmallUniverse.liftedDecode b)
    (l : SmallUniverse.liftedDecode b ≅ SmallUniverse.liftedDecode c)
    (E : HomotopyEquivalence k.hom) (D : HomotopyEquivalence l.hom) :
    (⟨k.hom ≫ l.hom,
      SmallUniverse.NativeUnivalence.compositeEquivalence a b c k.hom E l.hom D⟩ :
      Σ f : SmallUniverse.liftedDecode a ⟶ SmallUniverse.liftedDecode c, HomotopyEquivalence f) =
    ⟨(k ≪≫ l).hom, HomotopyEquivalence.ofIso (k ≪≫ l)⟩ := by
  apply record_ext i j ((constantFilling Γ S).transport i.symm)
    (Filling.transport_lawful i.symm _ (constantFilling_lawful Γ S))
  rfl

/-- Any actual section computes chosen transport into a discrete endpoint. -/
theorem mapTo_section {Γ : Context.{u}} {B : Family (total (interval Γ))}
    (F : Filling B) (hF : F.Lawful) (s : Term B) {C D : Family Γ}
    (h₀ : reindex B (endpointSub Γ false) = C)
    (h₁ : reindex B (endpointSub Γ true) = D)
    (hD : PathDiscrete D) (c : Term C) (d : Term D)
    (hc : HEq (s.reindex (endpointSub Γ false)) c)
    (hd : HEq (s.reindex (endpointSub Γ true)) d) :
    Term.map (IntervalTransport.mapTo F C D h₀ h₁) c = d := by
  subst C
  subst D
  cases eq_of_heq hc
  cases eq_of_heq hd
  exact hD (𝟙 Γ) (NativeTransportComposition.sectionComparison F hF s)

end DiscreteRecords
end SquareKit.Cubical.Presheaf

namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u

def Contractible.ofSingleton {Γ : Context.{u}} {A : Family Γ}
    (h : ∀ x, Subsingleton (A.obj x)) (a : Term A) : Contractible A where
  center := a
  contraction _ b := ⟨{
    val := fun f _ => A.map f b
    naturality := fun _ _ _ => (h _).elim _ _ },
    fun _ => ⟨(h _).elim _ _, rfl⟩⟩
  naturality _ _ _ _ := (h _).elim _ _

theorem Contractible.singleton_unique {Γ : Context.{u}} {A : Family Γ}
    (h : ∀ x, Subsingleton (A.obj x)) (c d : Contractible A) : c = d := by
  apply Contractible.ext
  · exact Term.ext (fun x => (h x).elim _ _)
  · intros
    exact (h _).elim _ _

theorem genericFiber_singleton {Γ : Presheaf.Context.{u}} {A B : Presheaf.Family Γ}
    {S : Type u} (j : B ≅ Presheaf.constantFamily Γ S) (k : A ≅ B)
    (x : (restrict (Presheaf.total B)).Elements) : Subsingleton ((genericFiber k.hom).obj x) := by
  have h := Presheaf.DiscreteRecords.fiber_subsingleton
    (Functor.isoWhiskerLeft (Presheaf.projection B).mapElements j)
    (Functor.whiskerLeft (Presheaf.projection B).mapElements k.hom)
    (fun y => (k.app ((Presheaf.projection B).mapElements.obj y)).toEquiv.injective)
    (Presheaf.generic B)
  let e := fiberIso (Functor.whiskerLeft (Presheaf.projection B).mapElements k.hom)
    (Presheaf.generic B)
  constructor
  intro a b
  have he := congrArg (e.hom.app x)
    ((h ((elements _).obj x)).elim (e.inv.app x a) (e.inv.app x b))
  exact (e.inv_hom_id_app_apply x a).symm.trans (he.trans (e.inv_hom_id_app_apply x b))

/-- Recompute the full target contraction from an inverse isomorphism and
singleton generic fibers, independently of any supplied equivalence witness. -/
def recomputeEquivalence {Γ : Presheaf.Context.{u}} {A B : Presheaf.Family Γ}
    {S : Type u} (j : B ≅ Presheaf.constantFamily Γ S) (k : A ≅ B) : Equivalence k.hom where
  fibers := Contractible.ofSingleton (genericFiber_singleton j k)
    (Term.map (fiberIso _ _).hom
      (restrictTerm (Presheaf.isoFiberCenter k)))

theorem recomputeEquivalence_eq {Γ : Presheaf.Context.{u}} {A B : Presheaf.Family Γ}
    {S : Type u} (j : B ≅ Presheaf.constantFamily Γ S) (k : A ≅ B)
    (E : Equivalence k.hom) : recomputeEquivalence j k = E := by
  cases E with
  | mk c =>
    apply congrArg Equivalence.mk
    exact Contractible.singleton_unique (genericFiber_singleton j k) _ _

theorem recomputeEquivalence_inverse {Γ : Presheaf.Context.{u}} {A B : Presheaf.Family Γ}
    {S : Type u} (j : B ≅ Presheaf.constantFamily Γ S) (k : A ≅ B) :
    (recomputeEquivalence j k).selectedInverse = restrictFamilyMap k.inv := rfl

end SquareKit.Cubical.Cartesian
