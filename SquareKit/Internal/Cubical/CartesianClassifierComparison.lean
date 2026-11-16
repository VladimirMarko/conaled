import SquareKit.Internal.Cubical.CartesianUnivalenceCompletion
import SquareKit.Internal.Cubical.CartesianTransportConcatenation
import SquareKit.Internal.Cubical.CartesianSelectedComparison
import SquareKit.Internal.Cubical.CartesianRelativeExtension
import SquareKit.Internal.Cubical.CartesianNerve
import SquareKit.Internal.Cubical.CartesianSmallFamilyClassification
import SquareKit.Internal.Cubical.CartesianGlueFilling
import SquareKit.Internal.Cubical.CartesianUniverseComposition
import SquareKit.Internal.Cubical.CartesianUniverse
import SquareKit.Internal.Cubical.CartesianUnivalence
import SquareKit.Internal.Cubical.CartesianEquivalenceComposition

/-! Classification of the finite tuple decoder with complete chosen operations.
Full equivalence records have discrete presentations; actual fiber contractions
supply independent comparisons and boundary-alignment cubes. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u
namespace ClassifierComparison
/-- Assemble a family from an objectwise presentation; restriction is conjugation. -/
def familyFromPresentation {Γ : Context.{u}} (P : Γ.Elements → Type u) {S : Type u}
    (e : ∀ x, P x ≃ S) : Family Γ where
  obj := P
  map {x y} _ := TypeCat.ofHom (fun a => (e y).symm (e x a))
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (e x).symm_apply_apply a
  map_comp {x y z} _ _ := by
    apply ConcreteCategory.hom_ext
    intro a
    exact congrArg (e z).symm ((e y).apply_symm_apply (e x a)).symm

def familyPresentation {Γ : Context.{u}} (P : Γ.Elements → Type u) {S : Type u}
    (e : ∀ x, P x ≃ S) : familyFromPresentation P e ≅ constantFamily Γ S where
  hom := {
    app := fun x => TypeCat.ofHom (e x)
    naturality := fun x y _ => by
      apply ConcreteCategory.hom_ext
      intro a
      exact (e y).apply_symm_apply (e x a) }
  inv := {
    app := fun x => TypeCat.ofHom (e x).symm
    naturality := fun x y _ => by
      apply ConcreteCategory.hom_ext
      intro a
      exact (congrArg (e y).symm ((e x).apply_symm_apply a)).symm }
  hom_inv_id := by ext x a; exact (e x).symm_apply_apply a
  inv_hom_id := by ext x a; exact (e x).apply_symm_apply a

/-- Every represented chart has small tuple fibers, without lifting its base. -/
def fiber {I : Cube} (T : VertexSystem.{u} (Vertex I.dimension))
    (x : (representable.{u} I).Elements) : Type u :=
  (T.reindex (Cube.vertices x.val.down)).Tuple

def presentationEquiv {I : Cube} (T : VertexSystem.{u} (Vertex I.dimension))
    (x : (representable.{u} I).Elements) :
    fiber T x ≃ (T.obj (fun _ => false)).carrier :=
  T.tupleGlobalEquiv (Cube.vertices x.val.down) (fun _ => false) (fun _ => false)

def family {I : Cube} (T : VertexSystem.{u} (Vertex I.dimension)) :
    Family (representable.{u} I) :=
  familyFromPresentation (fiber T) (presentationEquiv T)

/-- Conjugation is exactly tuple restriction, not a different decoding action. -/
theorem family_map_coordinate {I : Cube} (T : VertexSystem.{u} (Vertex I.dimension))
    {x y : (representable.{u} I).Elements} (f : x ⟶ y)
    (a : (family T).obj x) (w : Vertex y.obj.unop.dimension) :
    HEq (((family T).map f a).val w) (a.val (Cube.vertices f.hom.unop w)) := by
  change HEq (((presentationEquiv T y).symm (presentationEquiv T x a)).val w) _
  apply (heq_of_eq (T.tupleGlobalEquiv_symm_apply (Cube.vertices y.val.down)
    (fun _ => false) w (fun _ => false) (presentationEquiv T x a))).trans
  change HEq (T.arrow (fun _ => false) (Cube.vertices y.val.down w)
    (T.arrow (Cube.vertices x.val.down (fun _ => false)) (fun _ => false) (a.val (fun _ => false)))) _
  apply (heq_of_eq (T.arrow_comp_apply (Cube.vertices x.val.down (fun _ => false))
    (fun _ => false) (Cube.vertices y.val.down w) (a.val (fun _ => false)))).trans
  have hm : Cube.vertices y.val.down w = Cube.vertices x.val.down (Cube.vertices f.hom.unop w) := by
    have hv := congrArg ULift.down f.map_val
    change f.hom.unop ≫ x.val.down = y.val.down at hv
    rw [← hv]
    exact Cube.vertices_comp f.hom.unop x.val.down w
  have ha : ∀ z z' : Vertex I.dimension, z = z' →
      HEq (T.arrow (Cube.vertices x.val.down (fun _ => false)) z (a.val (fun _ => false)))
        (T.arrow (Cube.vertices x.val.down (fun _ => false)) z' (a.val (fun _ => false))) := by
    intro z z' h
    cases h
    rfl
  exact (ha _ _ hm).trans (heq_of_eq (a.property (fun _ => false) (Cube.vertices f.hom.unop w)))

theorem system_reindex {I J : Cube} (T : VertexSystem.{u} (Vertex I.dimension))
    (h : J ⟶ I) (x : (representable.{u} J).Elements) :
    (T.reindex (Cube.vertices h)).reindex (Cube.vertices x.val.down) =
      T.reindex (Cube.vertices ((representableMap h).mapElements.obj x).val.down) := by
  change T.reindex (fun v => Cube.vertices h (Cube.vertices x.val.down v)) =
    T.reindex (Cube.vertices (x.val.down ≫ h))
  exact congrArg T.reindex (funext (Cube.vertices_comp x.val.down h)).symm

private theorem typeHom_heq {A B C D : Type u} {f : A → B} {g : C → D}
    (ha : A = C) (hb : B = D) (h : HEq f g) : HEq (TypeCat.ofHom f) (TypeCat.ofHom g) := by
  subst C
  subst D
  cases h
  rfl

theorem family_reindex {I J : Cube} (T : VertexSystem.{u} (Vertex I.dimension))
    (h : J ⟶ I) : family (T.reindex (Cube.vertices h)) =
      reindex (family T) (representableMap h) := by
  have hobj : ∀ x : (representable.{u} J).Elements,
      (family (T.reindex (Cube.vertices h))).obj x =
      (reindex (family T) (representableMap h)).obj x :=
    fun x => congrArg VertexSystem.Tuple (system_reindex T h x)
  apply Functor.hext hobj
  intro x y f
  apply typeHom_heq (hobj x) (hobj y)
  apply Function.hfunext (hobj x)
  intro a b hab
  apply VertexSystem.Tuple.hext (system_reindex T h y)
  intro w
  have h₁ := family_map_coordinate (T.reindex (Cube.vertices h)) f a w
  have h₂ := family_map_coordinate T ((representableMap h).mapElements.map f) b w
  exact h₁.trans ((VertexSystem.Tuple.val_heq (system_reindex T h x) hab
    (Cube.vertices f.hom.unop w)).trans h₂.symm)

def presentation {I : Cube} (T : VertexSystem.{u} (Vertex I.dimension)) :
    family T ≅ constantFamily (representable.{u} I)
      (T.obj (fun _ => false)).carrier :=
  familyPresentation (fiber T) (presentationEquiv T)

def filling {I : Cube} (T : VertexSystem.{u} (Vertex I.dimension)) :
    Filling (family T) := presentedFilling (presentation T)

theorem filling_lawful {I : Cube} (T : VertexSystem.{u} (Vertex I.dimension)) :
    (filling T).Lawful := presentedFilling_lawful (presentation T)

def localFamily {I : Cube} (T : VertexSystem.{u} (Vertex I.dimension)) :
    SmallFamilyCode.{u} I :=
  ⟨family T, (filling T).toLocal,
    Filling.toLocal_lawful (filling_lawful T)⟩


/-- Discrete presented carriers determine the whole lawful selected operation. -/
theorem localFamily_eq_of_presented {Γ : Context.{u}} (A B : LocalFamily Γ)
    (h : A.family = B.family) {S : Type u} (e : A.family ≅ constantFamily Γ S) : A = B := by
  cases A with
  | mk af fa ha =>
    cases B with
    | mk bf fb hb =>
      dsimp at h e
      subst bf
      have he : fa = fb := by
        cases fa with
        | mk fillA =>
          cases fb with
          | mk fillB =>
            congr
            funext I p φ r b
            exact (b.presentedFill_unique (Functor.isoWhiskerLeft p.mapElements e) _
              (ha.fills p φ r b).1).trans
                (b.presentedFill_unique (Functor.isoWhiskerLeft p.mapElements e) _
                  (hb.fills p φ r b).1).symm
      cases he
      rfl

/-- Substitution preserves the entire classified tuple family. -/
theorem localFamily_reindex {I J : Cube} (T : VertexSystem.{u} (Vertex I.dimension))
    (h : J ⟶ I) : localFamily (T.reindex (Cube.vertices h)) =
      (localFamily T).reindex (representableMap h) :=
  localFamily_eq_of_presented _ _ (family_reindex T h)
    (presentation (T.reindex (Cube.vertices h)))

/-- The finite nerve embeds in the arbitrary-family classifier without resizing. -/
def classifyFinite : finiteNerve.{u} ⟶ smallFamilyCodes.{u} where
  app _ := TypeCat.ofHom localFamily
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro T
    exact localFamily_reindex T f.unop

def decodedFinite : finiteNerve.{u}.Elements ⥤ Type u :=
  classifyFinite.mapElements ⋙ universalDecode

/-- Decoding retains the entire tuple restriction, not only its vertices' types. -/
theorem decodedFinite_map_coordinate {x y : finiteNerve.{u}.Elements}
    (f : x ⟶ y) (a : decodedFinite.obj x) (w : Vertex y.obj.unop.dimension) :
    HEq ((decodedFinite.map f a).val w) (a.val (Cube.vertices f.hom.unop w)) := by
  have hc := cast_heq
    (congrArg (fun A : SmallFamilyCode.{u} y.obj.unop => codeFiber A)
      ((classifyFinite.mapElements.map f).map_val))
    ((localFamily x.val).family.map (representableGenericHom f.hom.unop) a)
  have ht : y.val.reindex (Cube.vertices (𝟙 y.obj.unop)) =
      (x.val.reindex (Cube.vertices f.hom.unop)).reindex (Cube.vertices (𝟙 y.obj.unop)) :=
    congrArg (fun T : VertexSystem.{u} (Vertex y.obj.unop.dimension) =>
      T.reindex (Cube.vertices (𝟙 y.obj.unop))) f.map_val.symm
  have hs := ht.trans (system_reindex x.val f.hom.unop (representableGeneric y.obj.unop))
  exact (VertexSystem.Tuple.val_heq hs hc w).trans
    (family_map_coordinate x.val (representableGenericHom f.hom.unop) a w)

def liftedDecodedFinite : Family finiteNerve.{u} := decodedFinite ⋙ uliftFunctor.{u+1, u}

/-- The old exact decoder is recovered, including its restriction action. -/
def tupleDecoderIso : liftedDecodedFinite.{u} ≅ TupleDecoder.family.{u} where
  hom := {
    app := fun _ => TypeCat.ofHom (fun a => a)
    naturality := by
      intro x y f
      apply ConcreteCategory.hom_ext
      intro a
      apply ULift.ext
      apply VertexSystem.Tuple.ext
      intro w
      exact eq_of_heq ((decodedFinite_map_coordinate f a.down w).trans
        (TupleDecoder.mapEquiv_coordinate f a.down w).symm) }
  inv := {
    app := fun _ => TypeCat.ofHom (fun a => a)
    naturality := by
      intro x y f
      apply ConcreteCategory.hom_ext
      intro a
      apply ULift.ext
      apply VertexSystem.Tuple.ext
      intro w
      exact eq_of_heq ((TupleDecoder.mapEquiv_coordinate f a.down w).trans
        (decodedFinite_map_coordinate f a.down w).symm) }

/-- Any lawful operation on the recovered decoder agrees as a complete record
with the original tuple selection, rather than merely on observed transport. -/
theorem tupleDecoder_filling_unique (F : Filling TupleDecoder.family.{u}) (hF : F.Lawful) :
    F = TupleDecoder.filling := by
  cases F with
  | mk fill =>
    congr
    funext Δ p φ r b
    exact (TupleDecoder.fill_eq p φ r b _ (hF.fills p φ r b).1).symm

/-- An independently built decoded operation recovers the old exact chosen filler. -/
theorem tupleDecoder_filling_recovery (F : Filling liftedDecodedFinite.{u}) (hF : F.Lawful) :
    F.transport tupleDecoderIso = TupleDecoder.filling :=
  tupleDecoder_filling_unique _ (Filling.transport_lawful tupleDecoderIso F hF)

/-- The actual classifier-selected decoder operation, obtained independently
by reconstructing the small represented operations. -/
def classifiedFilling : Filling liftedDecodedFinite.{u} :=
  SmallUniverse.NativeDecode.filling classifyFinite

theorem classifiedFilling_lawful : classifiedFilling.{u}.Lawful :=
  SmallUniverse.NativeDecode.filling_lawful classifyFinite

/-- Recover the old whole filling record from the actual new decoder operation. -/
theorem classifiedFilling_recovers_tuple :
    classifiedFilling.{u}.transport tupleDecoderIso = TupleDecoder.filling :=
  tupleDecoder_filling_recovery classifiedFilling classifiedFilling_lawful

namespace DiscreteRecords
theorem constant_path_value {Γ : Context.{u}} {S : Type u}
    {a b : Term (constantFamily Γ S)} {x : Γ.Elements}
    (p : (homogeneousPath (constantFamily Γ S) a b).obj x)
    {y : Γ.Elements} (f : x ⟶ y) (r : (interval Γ).obj y) :
    p.val.val f r = a.val y := by
  let P := homogeneousPath (constantFamily Γ S) a b
  let τ := projection P
  let t := Term.map (pathReindexIso (intervalCoefficient (constantFamily Γ S)) a b τ).hom (generic P)
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
  let t := Term.map (pathReindexIso (intervalCoefficient A) a b τ).hom (generic P)
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
    Subsingleton ((Homotopy.fiber f b).obj x) := by
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
    (h : ∀ x, Subsingleton (A.obj x)) : Subsingleton (Contractible A) := by
  constructor
  intro c d
  apply Contractible.ext (Term.ext (fun x => (h x).elim _ _))
  intro x a y f r
  exact (h y).elim _ _

theorem equivalence_subsingleton {Γ : Context.{u}} {A B : Family Γ} {T : Type u}
    (j : B ≅ constantFamily Γ T) (f : A ⟶ B)
    (hi : ∀ x, Function.Injective (f.app x)) : Subsingleton (HomotopyEquivalence f) := by
  constructor
  intro E H
  have hf := fiber_subsingleton (Functor.isoWhiskerLeft (projection B).mapElements j)
    (Functor.whiskerLeft (projection B).mapElements f)
    (fun x => hi ((projection B).mapElements.obj x)) (generic B)
  exact congrArg HomotopyEquivalence.mk ((contractible_subsingleton hf).elim E.fibers H.fibers)

theorem iso_witness_unique {Γ : Context.{u}} {A B : Family Γ} {T : Type u}
    (j : B ≅ constantFamily Γ T) (e : A ≅ B) (E H : HomotopyEquivalence e.hom) : E = H :=
  (equivalence_subsingleton j e.hom (fun x => (e.app x).toEquiv.injective)).elim E H

/-- On presented discrete fibers, equality of maps recovers complete equivalence records. -/
theorem record_eq_iso {Γ : Context.{u}} {A B : Family Γ} {T : Type u}
    (j : B ≅ constantFamily Γ T) (e : A ≅ B) (F : Filling B) (hF : F.Lawful)
    (r : Σ f : A ⟶ B, HomotopyEquivalence f) (h : r.1 = e.hom) :
    r = EquivalenceFamilies.isoPair e F hF := by
  rcases r with ⟨f,E⟩
  dsimp at h
  subst f
  exact congrArg (Sigma.mk e.hom) (iso_witness_unique j e E _)

def firstMap {Γ : Context.{u}} (A : Family Γ) (B : Family (total A)) : sigma A B ⟶ A where
  app _ := TypeCat.ofHom Sigma.fst
  naturality _ _ _ := rfl

def discreteInverse {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (E : HomotopyEquivalence f) : B ⟶ A :=
  EquivalenceFamilies.decodeMap (lam (Glue.genericFiberFst f (𝟙 (total B)) E.fibers.center))

theorem discrete_right {Γ : Context.{u}} {A B : Family Γ} {T : Type u}
    (j : B ≅ constantFamily Γ T) (f : A ⟶ B) (E : HomotopyEquivalence f) :
    discreteInverse E ≫ f = 𝟙 B := by
  let p := Glue.genericFiberPath f (𝟙 (total B)) E.fibers.center
  ext x b
  exact presented_path_endpoints (Functor.isoWhiskerLeft (projection B).mapElements j)
    (p.val (extendObj B x b))

theorem discrete_left {Γ : Context.{u}} {A B : Family Γ} {S : Type u}
    (i : A ≅ constantFamily Γ S) (f : A ⟶ B) (E : HomotopyEquivalence f) :
    f ≫ discreteInverse E = 𝟙 A := by
  let π := projection A
  let a := generic A
  let fa := Term.map (Functor.whiskerLeft π.mapElements f) a
  let τ := pair π fa
  let c := E.fibers.reindex τ
  let z := Glue.genericFiberIntro f τ a (homogeneousRefl fa)
  let q := homogeneousPathMap
    (firstMap (reindex A π) (reindex (Glue.genericFiberPathFamily f) (liftSub (reindex A (projection B)) τ)))
    (c.pathTo z)
  ext x a
  exact presented_path_endpoints (Functor.isoWhiskerLeft π.mapElements i) (q.val (extendObj A x a))

noncomputable def discreteIso {Γ : Context.{u}} {A B : Family Γ} {S T : Type u}
    (i : A ≅ constantFamily Γ S) (j : B ≅ constantFamily Γ T)
    (f : A ⟶ B) (E : HomotopyEquivalence f) : A ≅ B where
  hom := f
  inv := discreteInverse E
  hom_inv_id := discrete_left i f E
  inv_hom_id := discrete_right j f E
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
    (p q : Σ f : A ⟶ B, HomotopyEquivalence f) (h : p.1 = q.1) : p = q := by
  rcases p with ⟨f,E⟩
  rcases q with ⟨g,H⟩
  dsimp at h
  subst g
  have he := (equivalence_subsingleton j f (fun x => ((discreteIso i j f E).app x).toEquiv.injective)).elim E H
  cases he
  rfl

noncomputable def recordSections {Γ : Context.{u}} {A B : Family Γ} {S T : Type u}
    (i : A ≅ constantFamily Γ S) (j : B ≅ constantFamily Γ T)
    :
    (Σ f : A ⟶ B, HomotopyEquivalence f) ≃ Term (constantFamily Γ (S ≃ T)) where
  toFun p := isoSection (i.symm ≪≫ discreteIso i j p.1 p.2 ≪≫ j)
  invFun t := ⟨(i ≪≫ sectionIso t ≪≫ j.symm).hom,
    HomotopyEquivalence.ofIso (i ≪≫ sectionIso t ≪≫ j.symm)
      (presentedFilling j) (presentedFilling_lawful j)⟩
  left_inv p := by
    apply record_ext i j
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
    (σ : Δ ⟶ Γ) :
    Term (reindex (EquivalenceFamilies.equiv A B) σ) ≃
      Term (constantFamily Δ (S ≃ T)) :=
  (EquivalenceFamilies.equivReindexSections A B σ).symm.trans
    (recordSections (Functor.isoWhiskerLeft σ.mapElements i)
      (Functor.isoWhiskerLeft σ.mapElements j))


theorem presentedSections_natural {Γ Δ Θ : Context.{u}} {A B : Family Γ} {S T : Type u}
    (i : A ≅ constantFamily Γ S) (j : B ≅ constantFamily Γ T)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (z : Term (reindex (EquivalenceFamilies.equiv A B) σ)) :
    presentedSections i j (τ ≫ σ) (Term.reindex z τ) =
      Term.reindex (presentedSections i j σ z) τ := by
  obtain ⟨⟨f,E⟩,rfl⟩ := (EquivalenceFamilies.equivReindexSections A B σ).surjective z
  rw [EquivalenceFamilies.equivReindexSections_comp]
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
      Φ (τ ≫ σ) (Term.reindex z τ) = Term.reindex (Φ σ z) τ)
    {Δ : Context.{u}} (σ : Δ ⟶ Γ) (z : Term (reindex A σ)) :
    Term.map (Functor.whiskerLeft σ.mapElements (mapOfSections Φ)) z = Φ σ z :=
  (hn (projection A) (pair σ z) (generic A)).symm

noncomputable def isoOfSections {Γ : Context.{u}} {A B : Family Γ}
    (Φ : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ), Term (reindex A σ) ≃ Term (reindex B σ))
    (hn : ∀ {Δ Θ : Context.{u}} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (z : Term (reindex A σ)),
      Φ (τ ≫ σ) (Term.reindex z τ) = Term.reindex (Φ σ z) τ) : A ≅ B := by
  have hm {Δ Θ : Context.{u}} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (z : Term (reindex B σ)) :
      (Φ (τ ≫ σ)).symm (Term.reindex z τ) = Term.reindex ((Φ σ).symm z) τ := by
    apply (Φ (τ ≫ σ)).injective
    exact ((Φ (τ ≫ σ)).apply_symm_apply (Term.reindex z τ)).trans
      ((hn σ τ ((Φ σ).symm z)).trans
        (congrArg (fun t => Term.reindex t τ) ((Φ σ).apply_symm_apply z))).symm
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
    : EquivalenceFamilies.equiv A B ≅ constantFamily Γ (S ≃ T) :=
  isoOfSections (fun σ => presentedSections i j σ)
    (presentedSections_natural i j)


theorem presentedEquivIso_hom_reindex {Γ Δ : Context.{u}} {A B : Family Γ} {S T : Type u}
    (i : A ≅ constantFamily Γ S) (j : B ≅ constantFamily Γ T)
    (σ : Δ ⟶ Γ)
    (z : Term (reindex (EquivalenceFamilies.equiv A B) σ)) :
    Term.map (Functor.whiskerLeft σ.mapElements (presentedEquivIso i j).hom) z =
      presentedSections i j σ z :=
  @mapOfSections_apply Γ (EquivalenceFamilies.equiv A B) (constantFamily Γ (S ≃ T))
    (fun {_} σ => presentedSections i j σ)
    (fun {_ _} σ τ z => presentedSections_natural i j σ τ z) Δ σ z

theorem presentedSections_encoded_apply {Γ Δ : Context.{u}} {A B : Family Γ} {S T : Type u}
    (i : A ≅ constantFamily Γ S) (j : B ≅ constantFamily Γ T)
    (σ : Δ ⟶ Γ)
    (f : reindex A σ ⟶ reindex B σ) (E : HomotopyEquivalence f)
    (x : Δ.Elements) (s : S) :
    Equiv.toFun ((presentedSections i j σ
      (EquivalenceFamilies.equivReindexSections A B σ ⟨f,E⟩)).val x) s =
      j.hom.app (σ.mapElements.obj x) (f.app x (i.inv.app (σ.mapElements.obj x) s)) := by
  simp only [presentedSections, Equiv.trans_apply, Equiv.symm_apply_apply]
  rfl



end DiscreteRecords

namespace Selected
noncomputable def filling : Filling TupleDecoder.family.{u} :=
  classifiedFilling.transport tupleDecoderIso
noncomputable def line (Γ : Context.{u+1}) (S : FiniteCode.{u})
    (e : S.carrier ≃ S.carrier) (s : S.carrier) :=
  filling.fill (TargetTransport.intervalChart Γ ≫ TupleDecoder.chart (VertexSystem.loopSystem S e))
    (TargetTransport.emptyTube Γ) (TargetTransport.endpointTerm Γ false) (TargetTransport.box Γ S e s)

theorem line_eq (Γ : Context.{u+1}) (S : FiniteCode.{u})
    (e : S.carrier ≃ S.carrier) (s : S.carrier) : line Γ S e s = TargetTransport.selected Γ S e s := by
  unfold line filling
  rw [classifiedFilling_recovers_tuple]
  rfl

noncomputable def action (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) (s : S.carrier) : S.carrier :=
  ((line (representable.{u+1} ⟨0⟩) S e s).val
    (extendObj (interval (representable.{u+1} ⟨0⟩))
      ((representable.{u+1} ⟨0⟩).elementsMk (.op ⟨0⟩) ⟨𝟙 _⟩)
      ⟨Cube.endpoint ⟨0⟩ true⟩)).down.val (fun i => Fin.elim0 i)

theorem action_eq (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) (s : S.carrier) : action S e s = e s := by
  unfold action
  rw [line_eq]
  exact TargetTransport.action_eq S e s

theorem action_composite (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier) (s : S.carrier) :
    action S (e.trans d) s = action S d (action S e s) := by
  simp only [action_eq, Equiv.trans_apply]
noncomputable def arrow (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) : S.carrier ≃ S.carrier :=
  Equiv.ofBijective (action S e) (by
    have h : action S e = e := funext (action_eq S e)
    rw [h]
    exact e.bijective)
theorem arrow_eq (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) : arrow S e = e :=
  Equiv.ext (action_eq S e)

theorem arrow_eq_tuple_selected (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) :
    arrow S e = TargetTransport.arrow S e :=
  (arrow_eq S e).trans (TargetTransport.arrow_eq S e).symm

noncomputable def record {Γ : Context.{u}} {A B : Family Γ} {S T : Type u}
    (i : A ≅ constantFamily Γ S) (j : B ≅ constantFamily Γ T)
    (e : S ≃ T) : Σ f : A ⟶ B, HomotopyEquivalence f :=
  (DiscreteRecords.recordSections i j).symm ⟨fun _ => e, fun _ => rfl⟩

theorem record_complete {Γ : Context.{u}} {A B : Family Γ} {S T : Type u}
    (i : A ≅ constantFamily Γ S) (j : B ≅ constantFamily Γ T)
    (e : S ≃ T) (f : A ⟶ B) (E : HomotopyEquivalence f)
    (h : ∀ x a, f.app x a = j.inv.app x (e (i.hom.app x a))) :
    (⟨f,E⟩ : Σ g : A ⟶ B, HomotopyEquivalence g) = record i j e := by
  apply DiscreteRecords.record_ext i j
  ext x a
  exact h x a

def reindexRecord {Γ Δ : Context.{u}} {A B : Family Γ}
    (p : Σ f : A ⟶ B, HomotopyEquivalence f) (σ : Δ ⟶ Γ) :
    Σ f : reindex A σ ⟶ reindex B σ, HomotopyEquivalence f :=
  ⟨Functor.whiskerLeft σ.mapElements p.1, p.2.reindex σ⟩

theorem record_reindex {Γ Δ : Context.{u}} {A B : Family Γ} {S T : Type u}
    (i : A ≅ constantFamily Γ S) (j : B ≅ constantFamily Γ T)
    (e : S ≃ T) (σ : Δ ⟶ Γ) :
    reindexRecord (record i j e) σ =
      record (Functor.isoWhiskerLeft σ.mapElements i) (Functor.isoWhiskerLeft σ.mapElements j) e := by
  apply DiscreteRecords.record_ext (Functor.isoWhiskerLeft σ.mapElements i)
    (Functor.isoWhiskerLeft σ.mapElements j)
  rfl

theorem reindexRecord_comp {Γ Δ Θ : Context.{u}} {A B : Family Γ} {S T : Type u}
    (i : A ≅ constantFamily Γ S) (j : B ≅ constantFamily Γ T)
    (p : Σ f : A ⟶ B, HomotopyEquivalence f) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    reindexRecord (reindexRecord p σ) τ = reindexRecord p (τ ≫ σ) := by
  apply DiscreteRecords.record_ext (Functor.isoWhiskerLeft (τ ≫ σ).mapElements i)
    (Functor.isoWhiskerLeft (τ ≫ σ).mapElements j)
  rfl

theorem reindexRecord_id {Γ : Context.{u}} {A B : Family Γ} {S T : Type u}
    (i : A ≅ constantFamily Γ S) (j : B ≅ constantFamily Γ T)
    (p : Σ f : A ⟶ B, HomotopyEquivalence f) : reindexRecord p (𝟙 Γ) = p := by
  apply DiscreteRecords.record_ext i j
  rfl

end Selected

namespace RelativeComparison

section SquareBody
variable {Γ : Context.{u}} {X : Family Γ} {p q : Term X}
  {H K : Term (homogeneousPath X p q)}
  (Ω : Term (homogeneousPath (homogeneousPath X p q) H K))

/-- The entire two-interval body of an arbitrary native path between paths. -/
noncomputable def squareBody : Term (reindex X
    (projection (interval (total (interval Γ))) ≫ projection (interval Γ))) :=
  pathApp (Term.map (EquivalenceFamilies.homogeneousReindexIso X p q
    (projection (interval Γ))).hom (pathApp Ω))

theorem squareBody_start :
    (Term.reindex (squareBody Ω) (endpointSub (total (interval Γ)) false)) =
      (Term.reindex p (projection (interval Γ))) := pathApp_zero _

theorem squareBody_finish :
    (Term.reindex (squareBody Ω) (endpointSub (total (interval Γ)) true)) =
      (Term.reindex q (projection (interval Γ))) := pathApp_one _

theorem squareBody_zero :
    (Term.reindex (squareBody Ω) (liftSub (interval (total (interval Γ))) (endpointSub Γ false))) =
      pathApp H := by
  apply Term.ext
  intro x
  let y := (projection (interval Γ)).mapElements.obj x
  exact congrArg (fun t : Term (homogeneousPath X p q) => (t.val y).val.val (𝟙 y) x.val.2)
    (pathApp_zero Ω)

theorem squareBody_one :
    (Term.reindex (squareBody Ω) (liftSub (interval (total (interval Γ))) (endpointSub Γ true))) =
      pathApp K := by
  apply Term.ext
  intro x
  let y := (projection (interval Γ)).mapElements.obj x
  exact congrArg (fun t : Term (homogeneousPath X p q) => (t.val y).val.val (𝟙 y) x.val.2)
    (pathApp_one Ω)
end SquareBody

namespace Contractible
variable {Γ : Context.{u}} {A : Family Γ}
  (c : Contractible A) (F : Filling A) (hF : F.Lawful)
  {a b : Term A} (H K : Term (homogeneousPath A a b))

abbrev P := homogeneousPath A a b
abbrev π := projection (interval Γ)
noncomputable abbrev boundary := endpointBoundary (reindex (P (a := a) (b := b)) (π (Γ := Γ))) H K

noncomputable def line : Term (reindex (P (a := a) (b := b)) (π (Γ := Γ))) :=
  Term.map (EquivalenceFamilies.homogeneousReindexIso A a b (π (Γ := Γ))).inv
    (EquivalenceFamilies.ContractiblePaths.extend (c.reindex (π (Γ := Γ)))
      (F.reindex (π (Γ := Γ))) (hF.reindex _)
      ((boundary H K).map
        (EquivalenceFamilies.homogeneousReindexIso A a b (π (Γ := Γ))).hom))

theorem line_boundary (x : (total (interval Γ)).Elements)
    (hx : ((intervalFace Γ false).join (intervalFace Γ true)).holds x) :
    (line c F hF H K).val x = (boundary H K).val x hx := by
  let e := EquivalenceFamilies.homogeneousReindexIso A a b (π (Γ := Γ))
  have h := EquivalenceFamilies.ContractiblePaths.extend_boundary
    (c.reindex (π (Γ := Γ))) (F.reindex (π (Γ := Γ))) (hF.reindex _)
    ((boundary H K).map e.hom) x hx
  exact (congrArg (e.inv.app x) h).trans
    (congrArg (fun f => f.app x ((boundary H K).val x hx)) e.hom_inv_id)

theorem line_zero : (Term.reindex (line c F hF H K) (endpointSub Γ false)) = H := by
  apply Term.ext
  intro x
  let y := (endpointSub Γ false).mapElements.obj x
  have hy : (intervalFace Γ false).holds y :=
    (intervalFace_iff false y).mpr rfl
  have hj : ((intervalFace Γ false).join (intervalFace Γ true)).holds y :=
    Or.inl hy
  exact (line_boundary c F hF H K y hj).trans
    ((endpointBoundary_zero (reindex (homogeneousPath A a b) (projection (interval Γ))) H K y hj hy).trans
      (eq_of_heq (endpointSection_val (reindex (homogeneousPath A a b) (projection (interval Γ))) false H y hy)))

theorem line_one : (Term.reindex (line c F hF H K) (endpointSub Γ true)) = K := by
  apply Term.ext
  intro x
  let y := (endpointSub Γ true).mapElements.obj x
  have hy : (intervalFace Γ true).holds y :=
    (intervalFace_iff true y).mpr rfl
  have hj : ((intervalFace Γ false).join (intervalFace Γ true)).holds y :=
    Or.inr hy
  exact (line_boundary c F hF H K y hj).trans
    ((endpointBoundary_one (reindex (homogeneousPath A a b) (projection (interval Γ))) H K y hj hy).trans
      (eq_of_heq (endpointSection_val (reindex (homogeneousPath A a b) (projection (interval Γ))) true K y hy)))

noncomputable def compare : Term (homogeneousPath (homogeneousPath A a b) H K) :=
  pathLam (line c F hF H K) (line_zero c F hF H K) (line_one c F hF H K)

end Contractible

def homogeneousMap {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (a b : Term A) :
    homogeneousPath A a b ⟶ homogeneousPath B (Term.map f a) (Term.map f b) where
  app _x := TypeCat.ofHom (fun p => ⟨{
    val := fun {y} g r => f.app y (p.val.val g r)
    naturality := fun {_y z} g k r => (f.naturality_apply k _).symm.trans
      (congrArg (f.app z) (p.val.naturality g k r)) },
    fun g => ⟨congrArg (f.app _) (p.property g).1, congrArg (f.app _) (p.property g).2⟩⟩)
  naturality _ _ _ := rfl

namespace Fiber
variable {Γ : Context.{u}} {X D : Family Γ} {S : Type u}
  (f : X ⟶ D) (e : D ≅ constantFamily Γ S) (p : Term X)

abbrev target := Term.map f p
abbrev targetSub := pair (𝟙 Γ) (target f p)
abbrev family := reindex
  (Homotopy.fiber (Functor.whiskerLeft (projection D).mapElements f) (generic D))
  (targetSub f p)

def projectionMap : family f p ⟶ X where
  app _ := TypeCat.ofHom Sigma.fst
  naturality _ _ _ := rfl

def lift {Δ : Context.{u}} (σ : Δ ⟶ Γ) (z : Term (reindex X σ))
    (h : Term.map (Functor.whiskerLeft σ.mapElements f) z = (Term.reindex (target f p) σ)) :
    Term (reindex (family f p) σ) :=
  Glue.genericFiberIntro f (σ ≫ targetSub f p) z
    (pathLam (Term.reindex (Term.reindex (target f p) σ) (Cartesian.projection (interval Δ))) h.symm rfl)

include e in
theorem ext {Δ : Context.{u}} (σ : Δ ⟶ Γ)
    (z w : Term (reindex (family f p) σ))
    (h : Term.map (Functor.whiskerLeft σ.mapElements (projectionMap f p)) z =
      Term.map (Functor.whiskerLeft σ.mapElements (projectionMap f p)) w) : z = w := by
  rw [← Homotopy.fiberIntroOver_eta (Functor.whiskerLeft (projection D).mapElements f)
    (generic D) (σ ≫ targetSub f p) z,
    ← Homotopy.fiberIntroOver_eta (Functor.whiskerLeft (projection D).mapElements f)
    (generic D) (σ ≫ targetSub f p) w]
  apply Homotopy.fiberIntroOver_congr
  · exact h
  apply heq_of_eq
  apply Term.ext
  intro x
  let y := (Cartesian.projection (interval Δ)).mapElements.obj x
  let r := x.val.2
  let P := Glue.genericFiberPath f (σ ≫ targetSub f p) z
  let Q := Glue.genericFiberPath f (σ ≫ targetSub f p) w
  have hp := DiscreteRecords.presented_path_value
    (Functor.isoWhiskerLeft σ.mapElements e) (P.val y) (𝟙 y) r
  have hq := DiscreteRecords.presented_path_value
    (Functor.isoWhiskerLeft σ.mapElements e) (Q.val y) (𝟙 y) r
  exact hp.trans ((congrArg (fun t => f.app (σ.mapElements.obj y) (t.val y)) h).trans hq.symm)

include e in
theorem path_image {q : Term X} (H : Term (homogeneousPath X p q)) :
    Term.map (Functor.whiskerLeft (Cartesian.projection (interval Γ)).mapElements f) (pathApp H) =
      (Term.reindex (target f p) (Cartesian.projection (interval Γ))) := by
  apply Term.ext
  intro x
  let y := (Cartesian.projection (interval Γ)).mapElements.obj x
  exact DiscreteRecords.presented_path_value e ((homogeneousPathMap f H).val y) (𝟙 y) x.val.2

def start : Term (family f p) := lift f p (𝟙 Γ) p rfl

def finish {q : Term X} (H : Term (homogeneousPath X p q)) : Term (family f p) :=
  lift f p (𝟙 Γ) q
    (by
      apply Term.ext
      intro x
      exact (DiscreteRecords.presented_path_endpoints e ((homogeneousPathMap f H).val x)).symm)


def liftedLine {q : Term X} (H : Term (homogeneousPath X p q)) :
    Term (reindex (family f p) (Cartesian.projection (interval Γ))) :=
  lift f p (Cartesian.projection (interval Γ)) (pathApp H) (path_image f e p H)

theorem liftedLine_zero {q : Term X} (H : Term (homogeneousPath X p q)) :
    (Term.reindex (liftedLine f e p H) (endpointSub Γ false)) = start f p := by
  apply ext f e p (𝟙 Γ)
  exact pathApp_zero H

theorem liftedLine_one {q : Term X} (H : Term (homogeneousPath X p q)) :
    (Term.reindex (liftedLine f e p H) (endpointSub Γ true)) = finish f e p H := by
  apply ext f e p (𝟙 Γ)
  exact pathApp_one H

def liftedPath {q : Term X} (H : Term (homogeneousPath X p q)) :
    Term (homogeneousPath (family f p) (start f p) (finish f e p H)) :=
  pathLam (liftedLine f e p H) (liftedLine_zero f e p H) (liftedLine_one f e p H)

theorem liftedPath_projection {q : Term X} (H : Term (homogeneousPath X p q)) :
    Term.map (homogeneousMap (projectionMap f p) (start f p) (finish f e p H))
      (liftedPath f e p H) = H := by
  apply pathApp_injective
  rfl

end Fiber


/-- Reindex both dimensions of a native square, retaining its endpoint paths. -/
def squareReindex {Γ Δ : Context.{u}} {X : Family Γ} {p q : Term X}
    {H K : Term (homogeneousPath X p q)}
    (C : Term (homogeneousPath (homogeneousPath X p q) H K)) (σ : Δ ⟶ Γ) :
    Term (homogeneousPath
      (homogeneousPath (reindex X σ) ((Term.reindex p σ)) ((Term.reindex q σ)))
      (homogeneousReindex H σ) (homogeneousReindex K σ)) :=
  homogeneousPathMap (EquivalenceFamilies.homogeneousReindexIso X p q σ).hom
    (homogeneousReindex C σ)

theorem squareReindex_comp {Γ Δ Θ : Context.{u}} {X : Family Γ} {p q : Term X}
    {H K : Term (homogeneousPath X p q)}
    (C : Term (homogeneousPath (homogeneousPath X p q) H K))
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    squareReindex (squareReindex C σ) τ = squareReindex C (τ ≫ σ) := rfl

theorem squareReindex_id {Γ : Context.{u}} {X : Family Γ} {p q : Term X}
    {H K : Term (homogeneousPath X p q)}
    (C : Term (homogeneousPath (homogeneousPath X p q) H K)) :
    squareReindex C (𝟙 Γ) = C := by
  apply pathApp_injective
  rfl

/-- The full composition equation, named so concrete witnesses need not be
normalized again merely to elaborate the dependent equality's type. -/
def SquareSubstitutionLaw {Γ Δ Θ : Context.{u}} {X : Family Γ} {p q : Term X}
    {H K : Term (homogeneousPath X p q)}
    (C : Term (homogeneousPath (homogeneousPath X p q) H K))
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) : Prop :=
  squareReindex (squareReindex C σ) τ = squareReindex C (τ ≫ σ)

theorem squareSubstitutionLaw {Γ Δ Θ : Context.{u}} {X : Family Γ} {p q : Term X}
    {H K : Term (homogeneousPath X p q)}
    (C : Term (homogeneousPath (homogeneousPath X p q) H K))
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) : SquareSubstitutionLaw C σ τ :=
  squareReindex_comp C σ τ

/-- The corresponding full identity equation for the same chosen witness. -/
def SquareIdentityLaw {Γ : Context.{u}} {X : Family Γ} {p q : Term X}
    {H K : Term (homogeneousPath X p q)}
    (C : Term (homogeneousPath (homogeneousPath X p q) H K)) : Prop :=
  squareReindex C (𝟙 Γ) = C

theorem squareIdentityLaw {Γ : Context.{u}} {X : Family Γ} {p q : Term X}
    {H K : Term (homogeneousPath X p q)}
    (C : Term (homogeneousPath (homogeneousPath X p q) H K)) : SquareIdentityLaw C :=
  squareReindex_id C

variable {Γ : Context.{u}} {X D : Family Γ} {S : Type u}
  (f : X ⟶ D) (E : HomotopyEquivalence f) (e : D ≅ constantFamily Γ S)
  (FX : Filling X) (hFX : FX.Lawful) (FD : Filling D) (hFD : FD.Lawful)
  {p q : Term X} (H K : Term (homogeneousPath X p q))

noncomputable def fiberComparison :
    Term (homogeneousPath
      (homogeneousPath (Fiber.family f p) (Fiber.start f p) (Fiber.finish f e p H))
      (Fiber.liftedPath f e p H) (Fiber.liftedPath f e p K)) :=
  Contractible.compare (E.fibers.reindex (Fiber.targetSub f p))
    ((genericFiberFilling f FX hFX FD hFD).reindex (Fiber.targetSub f p))
    ((genericFiberFilling_lawful f FX hFX FD hFD).reindex _)
    (Fiber.liftedPath f e p H) (Fiber.liftedPath f e p K)

/-- The prescribed paths are retained as exact faces of a native relative square. -/
noncomputable def compare : Term (homogeneousPath (homogeneousPath X p q) H K) := by
  let P := homogeneousMap (Fiber.projectionMap f p) (Fiber.start f p) (Fiber.finish f e p H)
  let C := homogeneousPathMap P (fiberComparison f E e FX hFX FD hFD H K)
  exact pathLam (pathApp C)
    ((pathApp_zero C).trans (Fiber.liftedPath_projection f e p H))
    ((pathApp_one C).trans (Fiber.liftedPath_projection f e p K))

theorem compare_zero :
    (Term.reindex (pathApp (compare f E e FX hFX FD hFD H K)) (endpointSub Γ false)) = H :=
  pathApp_zero _

theorem compare_one :
    (Term.reindex (pathApp (compare f E e FX hFX FD hFD H K)) (endpointSub Γ true)) = K :=
  pathApp_one _


noncomputable def body := squareBody (compare f E e FX hFX FD hFD H K)

theorem body_start :
    (Term.reindex (body f E e FX hFX FD hFD H K) (endpointSub (total (interval Γ)) false)) =
      (Term.reindex p (projection (interval Γ))) := squareBody_start _

theorem body_finish :
    (Term.reindex (body f E e FX hFX FD hFD H K) (endpointSub (total (interval Γ)) true)) =
      (Term.reindex q (projection (interval Γ))) := squareBody_finish _

theorem body_zero :
    (Term.reindex (body f E e FX hFX FD hFD H K) (liftSub (interval (total (interval Γ))) (endpointSub Γ false))) = pathApp H :=
  squareBody_zero _

theorem body_one :
    (Term.reindex (body f E e FX hFX FD hFD H K) (liftSub (interval (total (interval Γ))) (endpointSub Γ true))) = pathApp K :=
  squareBody_one _

/-- Pull back the fixed chosen comparison rather than rerunning its choices. -/
noncomputable def compareAt {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    Term (homogeneousPath
      (homogeneousPath (reindex X σ) ((Term.reindex p σ)) ((Term.reindex q σ)))
      (homogeneousReindex H σ) (homogeneousReindex K σ)) :=
  squareReindex (compare f E e FX hFX FD hFD H K) σ

theorem compareAt_zero {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    (Term.reindex (pathApp (compareAt f E e FX hFX FD hFD H K σ)) (endpointSub Δ false)) =
      homogeneousReindex H σ := pathApp_zero _

theorem compareAt_one {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    (Term.reindex (pathApp (compareAt f E e FX hFX FD hFD H K σ)) (endpointSub Δ true)) =
      homogeneousReindex K σ := pathApp_one _


theorem compareAt_comp {Δ Θ : Context.{u}} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    squareReindex (compareAt f E e FX hFX FD hFD H K σ) τ =
      compareAt f E e FX hFX FD hFD H K (τ ≫ σ) :=
  squareReindex_comp _ σ τ

theorem compareAt_id :
    compareAt f E e FX hFX FD hFD H K (𝟙 Γ) = compare f E e FX hFX FD hFD H K :=
  squareReindex_id _


end RelativeComparison

namespace RelativeComparison
variable {Γ : Context.{u}} {X D : Family Γ}
  (f : X ⟶ D) (E : HomotopyEquivalence f)
  (FX : Filling X) (hFX : FX.Lawful) (FD : Filling D) (hFD : FD.Lawful)
  (p q : Term X) (h : Term.map f q = Term.map f p)

/-- Choose a path from the equivalence's actual fiber contraction. Neither an
input path nor a nerve square is used in this construction. -/
noncomputable def connect : Term (homogeneousPath X p q) := by
  let c := E.fibers.reindex (Fiber.targetSub f p)
  let F := (genericFiberFilling f FX hFX FD hFD).reindex (Fiber.targetSub f p)
  have hF := (genericFiberFilling_lawful f FX hFX FD hFD).reindex (Fiber.targetSub f p)
  let z := Fiber.start f p
  let w := Fiber.lift f p (𝟙 Γ) q h
  let path := homogeneousConcat F hF (homogeneousReverse F hF (c.pathTo z)) (c.pathTo w)
  exact homogeneousPathMap (Fiber.projectionMap f p) path
end RelativeComparison

namespace BoundaryAlignment
variable {Γ : Context.{u}} {X : Family Γ} (F : Filling X) (hF : F.Lawful)
  {p q P Q : Term X} (δp : Term (homogeneousPath X p P))
  (δq : Term (homogeneousPath X q Q)) (K : Term (homogeneousPath X P Q))

noncomputable def left := homogeneousReverse F hF δp
noncomputable def right := homogeneousReverse F hF δq
noncomputable def square : Term (reindex X (NativeSquare.squareBase Γ)) :=
  NativeSquare.fill F false (pathApp (left F hF δp)) (pathApp (right F hF δq)) (pathApp K)
    ((pathApp_zero K).trans (pathApp_zero (left F hF δp)).symm)
    ((pathApp_one K).trans (pathApp_zero (right F hF δq)).symm)

theorem square_original :
    Term.reindex (square F hF δp δq K) (endpointSub (total (interval Γ)) false) = pathApp K :=
  NativeSquare.fill_source F hF _ _ _ _ _ _
theorem square_left :
    Term.reindex (square F hF δp δq K) (intervalSub (endpointSub Γ false)) = pathApp (left F hF δp) :=
  NativeSquare.fill_left F hF _ _ _ _ _ _
theorem square_right :
    Term.reindex (square F hF δp δq K) (intervalSub (endpointSub Γ true)) = pathApp (right F hF δq) :=
  NativeSquare.fill_right F hF _ _ _ _ _ _

noncomputable def aligned : Term (homogeneousPath X p q) :=
  pathLam (NativeSquare.slice (square F hF δp δq K) true)
    ((NativeSquare.slice_left F hF false _ _ _ _ _ true).trans (pathApp_one (left F hF δp)))
    ((NativeSquare.slice_right F hF false _ _ _ _ _ true).trans (pathApp_one (right F hF δq)))
theorem square_aligned :
    Term.reindex (square F hF δp δq K) (endpointSub (total (interval Γ)) true) = pathApp (aligned F hF δp δq K) := by
  apply Term.ext
  intro x
  rfl
/-- Substitute the fixed alignment, retaining its selected filler. -/
noncomputable def squareAt {Δ : Context.{u}} (σ : Δ ⟶ Γ) :=
  Term.reindex (square F hF δp δq K) (intervalSub (intervalSub σ))

theorem squareAt_comp {Δ Θ : Context.{u}} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    Term.reindex (squareAt F hF δp δq K σ) (intervalSub (intervalSub τ)) =
      squareAt F hF δp δq K (τ ≫ σ) := rfl

theorem squareAt_id : squareAt F hF δp δq K (𝟙 Γ) = square F hF δp δq K := rfl

theorem squareAt_original {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    Term.reindex (squareAt F hF δp δq K σ) (endpointSub (total (interval Δ)) false) =
      pathApp (homogeneousReindex K σ) :=
  congrArg (fun t => Term.reindex t (intervalSub σ)) (square_original F hF δp δq K)

theorem squareAt_left {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    Term.reindex (squareAt F hF δp δq K σ) (intervalSub (endpointSub Δ false)) =
      pathApp (homogeneousReindex (left F hF δp) σ) :=
  congrArg (fun t => Term.reindex t (intervalSub σ)) (square_left F hF δp δq K)

theorem squareAt_right {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    Term.reindex (squareAt F hF δp δq K σ) (intervalSub (endpointSub Δ true)) =
      pathApp (homogeneousReindex (right F hF δq) σ) :=
  congrArg (fun t => Term.reindex t (intervalSub σ)) (square_right F hF δp δq K)

theorem squareAt_aligned {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    Term.reindex (squareAt F hF δp δq K σ) (endpointSub (total (interval Δ)) true) =
      pathApp (homogeneousReindex (aligned F hF δp δq K) σ) :=
  congrArg (fun t => Term.reindex t (intervalSub σ)) (square_aligned F hF δp δq K)

end BoundaryAlignment

namespace NativeNerve
abbrev point : Context.{u} := representable ⟨0⟩
def constantNerve (Γ : Context.{u+1}) (S : FiniteCode.{u}) : Γ ⟶ finiteNerve.{u} where
  app I := TypeCat.ofHom (fun _ => VertexSystem.constant S (Vertex I.unop.dimension))
  naturality _ _ _ := rfl

def realizedConstant (S : FiniteCode.{u}) : raisedContext point.{u} ⟶
    smallFamilyCodes.{u} := constantNerve _ S ≫ classifyFinite

def loopNerve (Γ : Context.{u+1}) (S : FiniteCode.{u})
    (e : S.carrier ≃ S.carrier) : total (interval Γ) ⟶ finiteNerve.{u} where
  app I := TypeCat.ofHom (fun x => (VertexSystem.loopSystem S e).reindex (Cube.vertices x.2.down))
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    change (VertexSystem.loopSystem S e).reindex (Cube.vertices (f.unop ≫ x.2.down)) =
      (VertexSystem.loopSystem S e).reindex (fun v => Cube.vertices x.2.down (Cube.vertices f.unop v))
    exact congrArg (VertexSystem.reindex _) (funext (Cube.vertices_comp f.unop x.2.down))

theorem loopNerve_endpoint (Γ : Context.{u+1}) (S : FiniteCode.{u})
    (e : S.carrier ≃ S.carrier) (b : Bool) :
    endpointSub Γ b ≫ loopNerve Γ S e = constantNerve Γ S := by
  ext I x
  change (VertexSystem.loopSystem S e).reindex (Cube.vertices (Cube.endpoint I.unop b)) = _
  have h : Cube.vertices (Cube.endpoint I.unop b) = fun _ _ => b := by
    cases b <;> rfl
  rw [h]
  exact VertexSystem.loopSystem_endpoint S e _ b

def realizedLoopCode (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) :
    total (interval (raisedContext point.{u})) ⟶
      smallFamilyCodes.{u} := loopNerve _ S e ≫ classifyFinite

def compositionNerve (Γ : Context.{u+1}) (S : FiniteCode.{u})
    (e d : S.carrier ≃ S.carrier) :
    total (interval (total (interval Γ))) ⟶ finiteNerve.{u} where
  app I := TypeCat.ofHom (fun x => (VertexSystem.compositionSquare S e d).reindex
    (Cube.vertices (Cube.pair x.2.down x.1.2.down)))
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro x
    apply congrArg (VertexSystem.reindex (VertexSystem.compositionSquare S e d))
    funext v i
    have h := Cube.vertices_comp f.unop (Cube.pair x.2.down x.1.2.down) v
    have hc := Cube.comp_pair f.unop x.2.down x.1.2.down
    exact congrArg (fun z => z i) ((congrArg (fun z => Cube.vertices z v) hc.symm).trans h)


noncomputable def constantDecodePresentation (S : FiniteCode.{u}) :
    decode (realizedConstant S) ≅ constantFamily point S.carrier where
  hom := {
    app := fun x => TypeCat.ofHom (fun a => a.val (fun _ => false))
    naturality := fun x y f => by
      apply ConcreteCategory.hom_ext
      intro a
      change (decodeMap ((realizedConstant S).mapElements.map
        ((raisedElements point).map f)) a).val (fun _ => false) = a.val (fun _ => false)
      have h : decodeMap ((realizedConstant S).mapElements.map
          ((raisedElements point).map f)) a =
          (⟨fun _ => a.val (fun _ => false), by intros; rfl⟩ :
            (VertexSystem.constant S (Vertex y.obj.unop.dimension)).Tuple) := by
        exact eq_of_heq (_root_.cast_heq _ _)
      exact congrArg (fun a => a.val (fun _ => false)) h }
  inv := {
    app := fun x => TypeCat.ofHom (fun s => ⟨fun _ => s, by intros; rfl⟩)
    naturality := fun x y f => by
      apply ConcreteCategory.hom_ext
      intro s
      apply Eq.symm
      change decodeMap ((realizedConstant S).mapElements.map
        ((raisedElements point).map f)) ⟨fun _ => s, _⟩ = ⟨fun _ => s, _⟩
      exact eq_of_heq (_root_.cast_heq _ _) }
  hom_inv_id := by
    ext x a
    apply VertexSystem.Tuple.ext
    intro v
    exact a.property (fun _ => false) v
  inv_hom_id := by ext x s; rfl



abbrev loops (S : FiniteCode.{u}) := homogeneousPath
  (SmallUniverse.family (raisedContext point.{u}))
  (SmallUniverse.term (realizedConstant S)) (SmallUniverse.term (realizedConstant S))
def realizedLoop (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) : Term (loops S) :=
  SmallUniverse.pathOfCode _ _ (realizedLoopCode S e)
    ((Category.assoc _ _ _).symm.trans (congrArg (fun p => p ≫ classifyFinite) (loopNerve_endpoint _ S e false)))
    ((Category.assoc _ _ _).symm.trans (congrArg (fun p => p ≫ classifyFinite) (loopNerve_endpoint _ S e true)))

noncomputable def realizedComposition (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier) :
    Term (homogeneousPath (loops S) (realizedLoop S (e.trans d)) (realizedLoop S (e.trans d))) :=
  homogeneousRefl (realizedLoop S (e.trans d))

theorem realizedComposition_body (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier) :
    RelativeComparison.squareBody (realizedComposition S e d) =
      SmallUniverse.term (compositionNerve _ S e d ≫ classifyFinite) := by
  apply Term.ext
  intro x
  change localFamily ((VertexSystem.loopSystem S (e.trans d)).reindex (Cube.vertices x.val.2.down)) = _
  apply congrArg localFamily
  apply congrArg (VertexSystem.reindex (VertexSystem.loopSystem S (e.trans d)))
  funext v i
  rw [Fin.eq_zero i]
  rfl

def raisedConstantIso (Γ : Context.{u}) (S : Type u) :
    Raising.family (constantFamily Γ S) ≅ constantFamily (raisedContext Γ) (ULift.{u+1} S) where
  hom := { app := fun _ => 𝟙 _, naturality := fun _ _ _ => rfl }
  inv := { app := fun _ => 𝟙 _, naturality := fun _ _ _ => rfl }

noncomputable def decoderPresentation (S : FiniteCode.{u}) :
    SmallUniverse.liftedDecode (realizedConstant S) ≅
      constantFamily (raisedContext point) (ULift.{u+1} S.carrier) :=
  Raising.iso (constantDecodePresentation S) ≪≫ raisedConstantIso _ _

noncomputable def nativeRecordPresentation (S : FiniteCode.{u}) :
    EquivalenceFamilies.equiv (SmallUniverse.liftedDecode (realizedConstant S))
      (SmallUniverse.liftedDecode (realizedConstant S)) ≅
    constantFamily (raisedContext point) (ULift.{u+1} S.carrier ≃ ULift.{u+1} S.carrier) :=
  DiscreteRecords.presentedEquivIso (decoderPresentation S) (decoderPresentation S)

noncomputable def nativeIso (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) :
    SmallUniverse.liftedDecode (realizedConstant S) ≅ SmallUniverse.liftedDecode (realizedConstant S) :=
  decoderPresentation S ≪≫ DiscreteRecords.sectionIso
    ⟨fun _ => Equiv.ulift.trans (e.trans Equiv.ulift.symm), fun _ => rfl⟩ ≪≫ (decoderPresentation S).symm

noncomputable def nativeEquivalence (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) :
    HomotopyEquivalence (nativeIso S e).hom :=
  HomotopyEquivalence.ofIso (nativeIso S e)
    (SmallUniverse.NativeDecode.filling (realizedConstant S))
    (SmallUniverse.NativeDecode.filling_lawful (realizedConstant S))

noncomputable def compositeEquivalence (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier) :
    HomotopyEquivalence ((nativeIso S e).hom ≫ (nativeIso S d).hom) :=
  (nativeEquivalence S e).comp (nativeEquivalence S d)
    (SmallUniverse.NativeDecode.filling (realizedConstant S))
    (SmallUniverse.NativeDecode.filling_lawful (realizedConstant S))
    (SmallUniverse.NativeDecode.filling (realizedConstant S))
    (SmallUniverse.NativeDecode.filling_lawful (realizedConstant S))
    (SmallUniverse.NativeDecode.filling (realizedConstant S))
    (SmallUniverse.NativeDecode.filling_lawful (realizedConstant S))

theorem composite_complete (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier) :
    (⟨(nativeIso S e).hom ≫ (nativeIso S d).hom, compositeEquivalence S e d⟩ :
      Σ f : SmallUniverse.liftedDecode (realizedConstant S) ⟶ _, HomotopyEquivalence f) =
      ⟨(nativeIso S (e.trans d)).hom, nativeEquivalence S (e.trans d)⟩ := by
  apply DiscreteRecords.record_ext (decoderPresentation S) (decoderPresentation S)
  ext x a
  change (decoderPresentation S).inv.app x
    ⟨d (((decoderPresentation S).hom.app x
      ((decoderPresentation S).inv.app x ⟨e (((decoderPresentation S).hom.app x a).down)⟩)).down)⟩ = _
  rw [(decoderPresentation S).inv_hom_id_app_apply]
  rfl

noncomputable def inverseIso (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) :=
  (DiscreteRecords.discreteIso (decoderPresentation S) (decoderPresentation S)
    (nativeIso S e).hom (nativeEquivalence S e)).symm

noncomputable def inverseEquivalence (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) :
    HomotopyEquivalence (inverseIso S e).hom :=
  HomotopyEquivalence.ofIso (inverseIso S e)
    (SmallUniverse.NativeDecode.filling (realizedConstant S))
    (SmallUniverse.NativeDecode.filling_lawful (realizedConstant S))

theorem inverse_map (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) :
    (inverseIso S e).hom = (nativeIso S e).inv := by
  have h := DiscreteRecords.discrete_right (decoderPresentation S) (nativeIso S e).hom
    (nativeEquivalence S e)
  change (inverseIso S e).hom ≫ (nativeIso S e).hom = 𝟙 _ at h
  calc
    (inverseIso S e).hom = ((inverseIso S e).hom ≫ (nativeIso S e).hom) ≫ (nativeIso S e).inv := by simp
    _ = (nativeIso S e).inv := by rw [h]; exact Category.id_comp _

theorem inverse_complete (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) :
    (⟨(inverseIso S e).hom, inverseEquivalence S e⟩ :
      Σ f : SmallUniverse.liftedDecode (realizedConstant S) ⟶ _, HomotopyEquivalence f) =
      ⟨(nativeIso S e.symm).hom, nativeEquivalence S e.symm⟩ := by
  apply DiscreteRecords.record_ext (decoderPresentation S) (decoderPresentation S)
  exact (inverse_map S e).trans rfl

end NativeNerve

namespace SelectedSpan
variable {Γ : Context.{u}} {X D : Family Γ} {S : Type u}
  (f : X ⟶ D) (E : HomotopyEquivalence f) (e : D ≅ constantFamily Γ S)
  (F : Filling X) (hF : F.Lawful) (G : Filling D) (hG : G.Lawful)
  (p q : Term X) (h : Term.map f q = Term.map f p)

/-- The target-selected comparison is constructed before a nerve square or
its endpoints are supplied. -/
noncomputable def H : Term (homogeneousPath X p q) :=
  RelativeComparison.connect f E F hF G hG p q h

variable {P Q : Term X} (hp : Term.map f P = Term.map f p)
  (hq : Term.map f Q = Term.map f q) (K : Term (homogeneousPath X P Q))
noncomputable def deltaP := RelativeComparison.connect f E F hF G hG p P hp
noncomputable def deltaQ := RelativeComparison.connect f E F hF G hG q Q hq
noncomputable def alignmentL := BoundaryAlignment.square F hF
  (deltaP f E F hF G hG p hp) (deltaQ f E F hF G hG q hq) K
noncomputable def aligned := BoundaryAlignment.aligned F hF
  (deltaP f E F hF G hG p hp) (deltaQ f E F hF G hG q hq) K

noncomputable def omega : Term (homogeneousPath (homogeneousPath X p q)
    (H f E F hF G hG p q h) (aligned f E F hF G hG p q hp hq K)) :=
  RelativeComparison.compare f E e F hF G hG (H f E F hF G hG p q h)
    (aligned f E F hF G hG p q hp hq K)

theorem alignment_original :
    Term.reindex (alignmentL f E F hF G hG p q hp hq K)
      (endpointSub (total (interval Γ)) false) = pathApp K :=
  BoundaryAlignment.square_original _ _ _ _ _
theorem alignment_target :
    Term.reindex (alignmentL f E F hF G hG p q hp hq K)
      (endpointSub (total (interval Γ)) true) = pathApp (aligned f E F hF G hG p q hp hq K) :=
  BoundaryAlignment.square_aligned _ _ _ _ _
theorem alignment_left :
    Term.reindex (alignmentL f E F hF G hG p q hp hq K) (intervalSub (endpointSub Γ false)) =
      pathApp (homogeneousReverse F hF (deltaP f E F hF G hG p hp)) :=
  BoundaryAlignment.square_left _ _ _ _ _
theorem alignment_right :
    Term.reindex (alignmentL f E F hF G hG p q hp hq K) (intervalSub (endpointSub Γ true)) =
      pathApp (homogeneousReverse F hF (deltaQ f E F hF G hG q hq)) :=
  BoundaryAlignment.square_right _ _ _ _ _

theorem omega_independent : Term.reindex (pathApp (omega f E e F hF G hG p q h hp hq K))
    (endpointSub Γ false) = H f E F hF G hG p q h := pathApp_zero _
theorem omega_aligned : Term.reindex (pathApp (omega f E e F hF G hG p q h hp hq K))
    (endpointSub Γ true) = aligned f E F hF G hG p q hp hq K := pathApp_one _

theorem omega_start : Term.reindex (RelativeComparison.squareBody (omega f E e F hF G hG p q h hp hq K))
    (endpointSub (total (interval Γ)) false) = Term.reindex p (projection (interval Γ)) :=
  RelativeComparison.squareBody_start _
theorem omega_finish : Term.reindex (RelativeComparison.squareBody (omega f E e F hF G hG p q h hp hq K))
    (endpointSub (total (interval Γ)) true) = Term.reindex q (projection (interval Γ)) :=
  RelativeComparison.squareBody_finish _

noncomputable def omegaAt {Δ : Context.{u}} (σ : Δ ⟶ Γ) :=
  RelativeComparison.squareReindex (omega f E e F hF G hG p q h hp hq K) σ

theorem omegaAt_comp {Δ Θ : Context.{u}} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    RelativeComparison.squareReindex (omegaAt f E e F hF G hG p q h hp hq K σ) τ =
      omegaAt f E e F hF G hG p q h hp hq K (τ ≫ σ) :=
  RelativeComparison.squareReindex_comp _ _ _
theorem omegaAt_id : omegaAt f E e F hF G hG p q h hp hq K (𝟙 Γ) =
    omega f E e F hF G hG p q h hp hq K := RelativeComparison.squareReindex_id _

end SelectedSpan

namespace PathSection
variable {Γ Δ : Context.{u}} (A : Family Γ) (a b : Term A) (σ : Δ ⟶ Γ)
  (z : Term (reindex (homogeneousPath A a b) σ))
def body : Term (reindex A (projection (interval Δ) ≫ σ)) :=
  pathApp (Term.map (EquivalenceFamilies.homogeneousReindexIso A a b σ).hom z)
theorem body_zero : Term.reindex (body A a b σ z) (endpointSub Δ false) = Term.reindex a σ :=
  pathApp_zero _
theorem body_one : Term.reindex (body A a b σ z) (endpointSub Δ true) = Term.reindex b σ :=
  pathApp_one _
theorem body_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    Term.reindex (body A a b σ z) (intervalSub τ) = body A a b (τ ≫ σ) (Term.reindex z τ) := rfl
end PathSection

namespace NativeNerve
noncomputable def loopTuple (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) (s : S.carrier) :
    Term (SmallUniverse.liftedDecode (realizedLoopCode S e)) :=
  Term.map (Functor.whiskerLeft (loopNerve (raisedContext point) S e).mapElements tupleDecoderIso.inv)
    (TargetTransport.tupleSection (raisedContext point) S e s)
noncomputable def loopBase (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) (s : S.carrier) :=
  Term.reindex (loopTuple S e s) (endpointSub (raisedContext point) false)
theorem transport_line_of_presentation {Γ : Context.{u}} {A B : Family (total (interval Γ))}
    (i : A ≅ B) (hB : BijectiveRestrictions B) (F : Filling A) (hF : F.Lawful)
    (r : Term (interval Γ)) (t : Term A) :
    IntervalTransport.line F r (𝟙 _) (Term.reindex t (graph r)) = t := by
  have h := sections_equal_source hB r
    (Term.map i.hom (IntervalTransport.line F r (𝟙 _) (Term.reindex t (graph r))))
    (Term.map i.hom t) (by
      exact congrArg (Term.map (Functor.whiskerLeft (graph r).mapElements i.hom))
        (IntervalTransport.line_source F hF r (𝟙 _) (Term.reindex t (graph r))))
  exact (Term.map_iso_roundtrip i _).symm.trans ((congrArg (Term.map i.inv) h).trans (Term.map_iso_roundtrip i _))
theorem transport_line (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) (s : S.carrier) :
  IntervalTransport.line (SmallUniverse.NativeDecode.filling (realizedLoopCode S e))
    (endpoint (raisedContext point) false) (𝟙 _) (loopBase S e s) = loopTuple S e s :=
  transport_line_of_presentation
    (Functor.isoWhiskerLeft (loopNerve (raisedContext point) S e).mapElements tupleDecoderIso)
    (fun f => TupleDecoder.bijective ((loopNerve (raisedContext point) S e).mapElements.map f))
    _ (SmallUniverse.NativeDecode.filling_lawful _) _ _
theorem selected_transport_section (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) (s : S.carrier) :
    Term.map (UniversalTransport.selectedMap (realizedLoopCode S e)
      (endpoint (raisedContext point) false) (endpoint (raisedContext point) true)) (loopBase S e s) =
      Term.reindex (loopTuple S e s) (endpointSub (raisedContext point) true) := by
  exact (congrArg (fun f => Term.map f (loopBase S e s))
    (UniversalTransport.selectedMap_eq (realizedLoopCode S e)
      (endpoint (raisedContext point) false) (endpoint (raisedContext point) true))).trans
    ((IntervalTransport.map_section (SmallUniverse.NativeDecode.filling (realizedLoopCode S e))
      (SmallUniverse.NativeDecode.filling_lawful (realizedLoopCode S e))
      (endpoint (raisedContext point) false) (endpoint (raisedContext point) true) (loopBase S e s)).trans
      (congrArg (fun t => Term.reindex t (endpointSub (raisedContext point) true)) (transport_line S e s)))

noncomputable def constantElement (S : FiniteCode.{u}) (s : S.carrier) :
    Term (SmallUniverse.liftedDecode (realizedConstant S)) :=
  Term.map (decoderPresentation S).inv ⟨fun _ => ⟨s⟩, fun _ => rfl⟩
theorem cast_section {Γ : Context.{u}} {A B A' B' : Family Γ}
    (f : A ⟶ B) (hA : A = A') (hB : B = B') (t : Term A) :
    Term.map (HomotopyEquivalence.castMap f A' B' hA hB) (Term.map (eqToHom hA) t) =
      Term.map (eqToHom hB) (Term.map f t) := by
  subst A'; subst B'; rfl

theorem cast_component_heq {Γ : Context.{u}} {A B : Family Γ} (h : A = B)
    (x : Γ.Elements) (a : A.obj x) : HEq ((eqToHom h).app x a) a := by
  subst B; rfl

theorem loopCode_endpoint (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) (b : Bool) :
    endpointSub (raisedContext point) b ≫ realizedLoopCode S e = realizedConstant S := by
  cases b
  · exact SmallUniverse.codeOfPath_zero (realizedLoop S e)
  · exact SmallUniverse.codeOfPath_one (realizedLoop S e)
theorem ulift_heq {A B : Type u} {a : A} {b : B} (h : HEq a b) :
    HEq (ULift.up.{u+1} a) (ULift.up.{u+1} b) := by cases h; rfl
theorem loop_endpoint (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) (s : S.carrier)
    (b : Bool) :
    Term.map (eqToHom (congrArg SmallUniverse.liftedDecode
      (loopCode_endpoint S e b)))
      (Term.reindex (loopTuple S e s) (endpointSub (raisedContext point) b)) =
        constantElement S (if b then e s else s) := by
  cases b
  · apply Term.ext
    intro x
    apply eq_of_heq
    apply (cast_component_heq _ x _).trans
    apply ulift_heq
    apply VertexSystem.Tuple.hext (VertexSystem.loopSystem_endpoint S e _ false)
    intro v
    rfl
  · apply Term.ext
    intro x
    apply eq_of_heq
    apply (cast_component_heq _ x _).trans
    apply ulift_heq
    apply VertexSystem.Tuple.hext (VertexSystem.loopSystem_endpoint S e _ true)
    intro v
    rfl

theorem native_coe_section (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) (s : S.carrier) :
    Term.map (SmallUniverse.NativeUnivalence.pathToMap (realizedLoop S e)) (constantElement S s) =
      constantElement S (e s) := by
  have h := cast_section
    (UniversalTransport.selectedMap (realizedLoopCode S e)
      (endpoint (raisedContext point) false) (endpoint (raisedContext point) true))
    (congrArg SmallUniverse.liftedDecode (loopCode_endpoint S e false))
    (congrArg SmallUniverse.liftedDecode (loopCode_endpoint S e true)) (loopBase S e s)
  have hs := loop_endpoint S e s false
  have ht := loop_endpoint S e s true
  change Term.map _ (loopBase S e s) = constantElement S s at hs
  change Term.map _ (Term.reindex (loopTuple S e s) (endpointSub (raisedContext point) true)) =
    constantElement S (e s) at ht
  exact ((congrArg (Term.map (SmallUniverse.NativeUnivalence.pathToMap (realizedLoop S e))) hs.symm).trans h).trans ((congrArg (Term.map (eqToHom
    (congrArg SmallUniverse.liftedDecode (loopCode_endpoint S e true))))
      (selected_transport_section S e s)).trans ht)

theorem native_coe_map (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) :
    SmallUniverse.NativeUnivalence.pathToMap (realizedLoop S e) = (nativeIso S e).hom := by
  ext x a
  let s := ((decoderPresentation S).hom.app x a).down
  have hs : (constantElement S s).val x = a :=
    (decoderPresentation S).hom_inv_id_app_apply x a
  have h := congrArg (fun t => t.val x) (native_coe_section S e s)
  exact (congrArg ((SmallUniverse.NativeUnivalence.pathToMap (realizedLoop S e)).app x) hs.symm).trans h

theorem native_coe_complete (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) :
    (⟨SmallUniverse.NativeUnivalence.pathToMap (realizedLoop S e),
      SmallUniverse.NativeUnivalence.pathToEquivalence (realizedLoop S e)⟩ :
      Σ f : SmallUniverse.liftedDecode (realizedConstant S) ⟶ _, HomotopyEquivalence f) =
      ⟨(nativeIso S e).hom, nativeEquivalence S e⟩ := by
  apply DiscreteRecords.record_ext (decoderPresentation S) (decoderPresentation S)
  exact native_coe_map S e

end NativeNerve

end ClassifierComparison
end SquareKit.Cubical.Cartesian

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.ClassifierComparison.NativeNerve
open CategoryTheory
universe u
theorem native_coe_encoded (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) :
    Term.map (SmallUniverse.NativeUnivalence.pathToEquiv (realizedConstant S) (realizedConstant S))
      (realizedLoop S e) =
      EquivalenceFamilies.equivSections (SmallUniverse.liftedDecode (realizedConstant S))
        (SmallUniverse.liftedDecode (realizedConstant S))
        ⟨(nativeIso S e).hom, nativeEquivalence S e⟩ :=
  (SmallUniverse.NativeUnivalence.pathToEquiv_beta (realizedLoop S e)).symm.trans
    (congrArg (EquivalenceFamilies.equivSections _ _) (native_coe_complete S e))
end SquareKit.Cubical.Cartesian.ClassifierComparison.NativeNerve

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.ClassifierComparison.NativeNerve
open CategoryTheory SmallUniverse.NativeUnivalence
universe u
noncomputable def uaLoop (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) : Term (loops S) :=
  ua (realizedConstant S) (realizedConstant S) (nativeIso S e).hom (nativeEquivalence S e)
noncomputable def uaComposite (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier) : Term (loops S) :=
  ua (realizedConstant S) (realizedConstant S)
    ((nativeIso S e).hom ≫ (nativeIso S d).hom) (compositeEquivalence S e d)
noncomputable def uaConcatenation (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier) : Term (loops S) :=
  homogeneousConcat (SmallUniverse.filling (raisedContext point))
    (SmallUniverse.filling_lawful _) (uaLoop S e) (uaLoop S d)

theorem coe_ua_encoded (S : FiniteCode.{u})
    (f : SmallUniverse.liftedDecode (realizedConstant S) ⟶ SmallUniverse.liftedDecode (realizedConstant S))
    (E : HomotopyEquivalence f) :
    Term.map (pathToEquiv (realizedConstant S) (realizedConstant S))
      (ua (realizedConstant S) (realizedConstant S) f E) =
      EquivalenceFamilies.equivSections _ _ ⟨f,E⟩ := by
  apply Term.ext
  intro x
  have h := DiscreteRecords.presented_path_endpoints (nativeRecordPresentation S)
    ((uaEquivalenceComparison (realizedConstant S) (realizedConstant S) f E).val x)
  exact (congrArg (fun t => t.val x) (pathToEquiv_beta
    (ua (realizedConstant S) (realizedConstant S) f E))).symm.trans h.symm

theorem uaComposite_observation (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier) :
    Term.map (pathToEquiv (realizedConstant S) (realizedConstant S)) (uaComposite S e d) =
      Term.map (pathToEquiv (realizedConstant S) (realizedConstant S)) (realizedLoop S (e.trans d)) :=
  (coe_ua_encoded S _ _).trans
    ((congrArg (EquivalenceFamilies.equivSections _ _) (composite_complete S e d)).trans
      (native_coe_encoded S (e.trans d)).symm)

theorem ua_complete (S : FiniteCode.{u})
    (f : SmallUniverse.liftedDecode (realizedConstant S) ⟶ SmallUniverse.liftedDecode (realizedConstant S))
    (E : HomotopyEquivalence f) :
    (⟨pathToMap (ua (realizedConstant S) (realizedConstant S) f E),
      pathToEquivalence (ua (realizedConstant S) (realizedConstant S) f E)⟩ :
      Σ g, HomotopyEquivalence g) = ⟨f,E⟩ :=
  (EquivalenceFamilies.equivSections _ _).injective
    ((pathToEquiv_beta _).trans (coe_ua_encoded S f E))
theorem uaLoop_map (S : FiniteCode.{u}) (e : S.carrier ≃ S.carrier) :
    pathToMap (uaLoop S e) = (nativeIso S e).hom :=
  congrArg Sigma.fst (ua_complete S _ _)

theorem maps_equal_of_homotopy {Γ : Context.{u}} {A B : Family Γ} {T : Type u}
    (j : B ≅ constantFamily Γ T) (f g : A ⟶ B)
    (H : Term (homogeneousPath (reindex B (projection A))
      (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
      (Term.map (Functor.whiskerLeft (projection A).mapElements g) (generic A)))) : f = g := by
  ext x a
  exact DiscreteRecords.presented_path_endpoints
    (Functor.isoWhiskerLeft (projection A).mapElements j) (H.val (extendObj A x a))

theorem uaConcatenation_map (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier) :
    pathToMap (uaConcatenation S e d) = (nativeIso S e).hom ≫ (nativeIso S d).hom :=
  (maps_equal_of_homotopy (decoderPresentation S) _ _
    (concatMapHomotopy (SmallUniverse.filling (raisedContext point)) (SmallUniverse.filling_lawful _)
      (uaLoop S e) (uaLoop S d))).trans
    (congrArg₂ (fun f g => f ≫ g) (uaLoop_map S e) (uaLoop_map S d))

theorem uaConcatenation_complete (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier) :
    (⟨pathToMap (uaConcatenation S e d), pathToEquivalence (uaConcatenation S e d)⟩ :
      Σ g, HomotopyEquivalence g) =
      ⟨(nativeIso S (e.trans d)).hom, nativeEquivalence S (e.trans d)⟩ := by
  apply DiscreteRecords.record_ext (decoderPresentation S) (decoderPresentation S)
  exact (uaConcatenation_map S e d).trans (congrArg Sigma.fst (composite_complete S e d))

theorem uaConcatenation_observation (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier) :
    Term.map (pathToEquiv (realizedConstant S) (realizedConstant S)) (uaConcatenation S e d) =
      Term.map (pathToEquiv (realizedConstant S) (realizedConstant S)) (realizedLoop S (e.trans d)) :=
  (pathToEquiv_beta _).symm.trans
    ((congrArg (EquivalenceFamilies.equivSections _ _) (uaConcatenation_complete S e d)).trans
      (native_coe_encoded S (e.trans d)).symm)

theorem nativeIso_injective (S : FiniteCode.{u}) {e d : S.carrier ≃ S.carrier}
    (h : (nativeIso S e).hom = (nativeIso S d).hom) : e = d := by
  apply Equiv.ext
  intro s
  let x := (raisedElements point).obj (representableGeneric ⟨0⟩)
  have hh := congrArg (fun f => ((decoderPresentation S).hom.app x
    (f.app x ((decoderPresentation S).inv.app x ⟨s⟩))).down) h
  change ((decoderPresentation S).hom.app x ((decoderPresentation S).inv.app x
    ⟨e (((decoderPresentation S).hom.app x ((decoderPresentation S).inv.app x ⟨s⟩)).down)⟩)).down =
    ((decoderPresentation S).hom.app x ((decoderPresentation S).inv.app x
    ⟨d (((decoderPresentation S).hom.app x ((decoderPresentation S).inv.app x ⟨s⟩)).down)⟩)).down at hh
  simpa only [(decoderPresentation S).inv_hom_id_app_apply] using hh

theorem uaLoop_injective (S : FiniteCode.{u}) {e d : S.carrier ≃ S.carrier}
    (h : uaLoop S e = uaLoop S d) : e = d :=
  nativeIso_injective S ((uaLoop_map S e).symm.trans
    ((congrArg pathToMap h).trans (uaLoop_map S d)))

theorem uaConcatenation_order (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier)
    (h : uaConcatenation S e d = uaConcatenation S d e) : e.trans d = d.trans e := by
  apply nativeIso_injective S
  have h₀ := (uaConcatenation_map S e d).symm.trans
    ((congrArg pathToMap h).trans (uaConcatenation_map S d e))
  exact (congrArg Sigma.fst (composite_complete S e d)).symm.trans
    (h₀.trans (congrArg Sigma.fst (composite_complete S d e)))

end SquareKit.Cubical.Cartesian.ClassifierComparison.NativeNerve

namespace SquareKit.Cubical.Cartesian.ClassifierComparison.NativeComparison
open CategoryTheory SmallUniverse.NativeUnivalence NativeNerve
universe u
noncomputable abbrev coe (S : FiniteCode.{u}) := pathToEquiv (NativeNerve.realizedConstant S) (NativeNerve.realizedConstant S)
noncomputable abbrev coeEquivalence (S : FiniteCode.{u}) := univalence (NativeNerve.realizedConstant S) (NativeNerve.realizedConstant S)
noncomputable abbrev loopFilling (S : FiniteCode.{u}) := pathsFilling (NativeNerve.realizedConstant S) (NativeNerve.realizedConstant S)
theorem loopFilling_lawful (S : FiniteCode.{u}) : (loopFilling S).Lawful := pathsFilling_lawful _ _
noncomputable def recordFilling (S : FiniteCode.{u}) :=
  EquivalenceFamilies.equivFilling (SmallUniverse.NativeDecode.filling (NativeNerve.realizedConstant S))
    (SmallUniverse.NativeDecode.filling_lawful _) (SmallUniverse.NativeDecode.filling (NativeNerve.realizedConstant S))
    (SmallUniverse.NativeDecode.filling_lawful _)
theorem recordFilling_lawful (S : FiniteCode.{u}) : (recordFilling S).Lawful :=
  EquivalenceFamilies.equivFilling_lawful _ (SmallUniverse.NativeDecode.filling_lawful _)
    _ (SmallUniverse.NativeDecode.filling_lawful _)

variable (S : FiniteCode.{u}) (e d : S.carrier ≃ S.carrier)
theorem observed_endpoints : Term.map (coe S) (uaConcatenation S e d) = Term.map (coe S) (uaComposite S e d) :=
  (uaConcatenation_observation S e d).trans (uaComposite_observation S e d).symm

/-- Chosen from the actual univalence fiber before the common nerve square is used. -/
noncomputable def H := SelectedSpan.H (coe S) (coeEquivalence S)
  (loopFilling S) (loopFilling_lawful S) (recordFilling S) (recordFilling_lawful S)
  (uaComposite S e d) (uaConcatenation S e d) (observed_endpoints S e d)
noncomputable def deltaP := SelectedSpan.deltaP (coe S) (coeEquivalence S)
  (loopFilling S) (loopFilling_lawful S) (recordFilling S) (recordFilling_lawful S)
  (uaComposite S e d) (uaComposite_observation S e d).symm
noncomputable def deltaQ := SelectedSpan.deltaQ (coe S) (coeEquivalence S)
  (loopFilling S) (loopFilling_lawful S) (recordFilling S) (recordFilling_lawful S)
  (uaConcatenation S e d) (uaConcatenation_observation S e d).symm
noncomputable def alignmentL := BoundaryAlignment.square (loopFilling S) (loopFilling_lawful S)
  (deltaP S e d) (deltaQ S e d) (NativeNerve.realizedComposition S e d)
noncomputable def aligned := BoundaryAlignment.aligned (loopFilling S) (loopFilling_lawful S)
  (deltaP S e d) (deltaQ S e d) (NativeNerve.realizedComposition S e d)
noncomputable def omegaU := RelativeComparison.compare (coe S) (coeEquivalence S) (nativeRecordPresentation S)
  (loopFilling S) (loopFilling_lawful S) (recordFilling S) (recordFilling_lawful S)
  (H S e d) (aligned S e d)

theorem alignment_original : Term.reindex (alignmentL S e d)
    (endpointSub (total (interval (raisedContext point))) false) = pathApp (NativeNerve.realizedComposition S e d) :=
  BoundaryAlignment.square_original _ _ _ _ _
theorem alignment_target : Term.reindex (alignmentL S e d)
    (endpointSub (total (interval (raisedContext point))) true) = pathApp (aligned S e d) :=
  BoundaryAlignment.square_aligned _ _ _ _ _
theorem alignment_left : Term.reindex (alignmentL S e d)
    (intervalSub (endpointSub (raisedContext point) false)) =
      pathApp (homogeneousReverse (loopFilling S) (loopFilling_lawful S) (deltaP S e d)) :=
  BoundaryAlignment.square_left _ _ _ _ _
theorem alignment_right : Term.reindex (alignmentL S e d)
    (intervalSub (endpointSub (raisedContext point) true)) =
      pathApp (homogeneousReverse (loopFilling S) (loopFilling_lawful S) (deltaQ S e d)) :=
  BoundaryAlignment.square_right _ _ _ _ _

theorem omega_independent : Term.reindex (pathApp (omegaU S e d))
    (endpointSub (raisedContext point) false) = H S e d := pathApp_zero _
theorem omega_aligned : Term.reindex (pathApp (omegaU S e d))
    (endpointSub (raisedContext point) true) = aligned S e d := pathApp_one _
theorem omega_start : Term.reindex (RelativeComparison.squareBody (omegaU S e d))
    (endpointSub (total (interval (raisedContext point))) false) =
      Term.reindex (uaComposite S e d) (projection (interval (raisedContext point))) :=
  RelativeComparison.squareBody_start _
theorem omega_finish : Term.reindex (RelativeComparison.squareBody (omegaU S e d))
    (endpointSub (total (interval (raisedContext point))) true) =
      Term.reindex (uaConcatenation S e d) (projection (interval (raisedContext point))) :=
  RelativeComparison.squareBody_finish _
noncomputable def omegaAt {Δ : Context.{u+1}} (σ : Δ ⟶ raisedContext point) :=
  RelativeComparison.squareReindex (omegaU S e d) σ
theorem omegaAt_comp {Δ Θ : Context.{u+1}} (σ : Δ ⟶ raisedContext point) (τ : Θ ⟶ Δ) :
    RelativeComparison.squareReindex (omegaAt S e d σ) τ = omegaAt S e d (τ ≫ σ) :=
  RelativeComparison.squareReindex_comp _ _ _
theorem omegaAt_id : omegaAt S e d (𝟙 (raisedContext point)) = omegaU S e d :=
  RelativeComparison.squareReindex_id _
noncomputable def alignmentAt {Δ : Context.{u+1}} (σ : Δ ⟶ raisedContext point) :=
  Term.reindex (alignmentL S e d) (intervalSub (intervalSub σ))
theorem alignmentAt_comp {Δ Θ : Context.{u+1}} (σ : Δ ⟶ raisedContext point) (τ : Θ ⟶ Δ) :
    Term.reindex (alignmentAt S e d σ) (intervalSub (intervalSub τ)) = alignmentAt S e d (τ ≫ σ) := rfl
theorem alignmentAt_id : alignmentAt S e d (𝟙 (raisedContext point)) = alignmentL S e d := rfl

theorem omegaAt_independent {Δ : Context.{u+1}} (σ : Δ ⟶ raisedContext point) :
    Term.reindex (pathApp (omegaAt S e d σ)) (endpointSub Δ false) = homogeneousReindex (H S e d) σ :=
  pathApp_zero _
theorem omegaAt_aligned {Δ : Context.{u+1}} (σ : Δ ⟶ raisedContext point) :
    Term.reindex (pathApp (omegaAt S e d σ)) (endpointSub Δ true) = homogeneousReindex (aligned S e d) σ :=
  pathApp_one _
theorem alignmentAt_original {Δ : Context.{u+1}} (σ : Δ ⟶ raisedContext point) :
    Term.reindex (alignmentAt S e d σ) (endpointSub (total (interval Δ)) false) =
      pathApp (homogeneousReindex (NativeNerve.realizedComposition S e d) σ) :=
  congrArg (fun t => Term.reindex t (intervalSub σ)) (alignment_original S e d)
theorem alignmentAt_target {Δ : Context.{u+1}} (σ : Δ ⟶ raisedContext point) :
    Term.reindex (alignmentAt S e d σ) (endpointSub (total (interval Δ)) true) =
      pathApp (homogeneousReindex (aligned S e d) σ) :=
  congrArg (fun t => Term.reindex t (intervalSub σ)) (alignment_target S e d)
theorem alignmentAt_left {Δ : Context.{u+1}} (σ : Δ ⟶ raisedContext point) :
    Term.reindex (alignmentAt S e d σ) (intervalSub (endpointSub Δ false)) =
      pathApp (homogeneousReindex (homogeneousReverse (loopFilling S) (loopFilling_lawful S) (deltaP S e d)) σ) :=
  congrArg (fun t => Term.reindex t (intervalSub σ)) (alignment_left S e d)
theorem alignmentAt_right {Δ : Context.{u+1}} (σ : Δ ⟶ raisedContext point) :
    Term.reindex (alignmentAt S e d σ) (intervalSub (endpointSub Δ true)) =
      pathApp (homogeneousReindex (homogeneousReverse (loopFilling S) (loopFilling_lawful S) (deltaQ S e d)) σ) :=
  congrArg (fun t => Term.reindex t (intervalSub σ)) (alignment_right S e d)

noncomputable def alignmentCube := PathSection.body (SmallUniverse.family (raisedContext point))
  (SmallUniverse.term (NativeNerve.realizedConstant S)) (SmallUniverse.term (NativeNerve.realizedConstant S))
  (NativeSquare.squareBase (raisedContext point)) (alignmentL S e d)
noncomputable def omegaCube := PathSection.body (SmallUniverse.family (raisedContext point))
  (SmallUniverse.term (NativeNerve.realizedConstant S)) (SmallUniverse.term (NativeNerve.realizedConstant S))
  (NativeSquare.squareBase (raisedContext point)) (RelativeComparison.squareBody (omegaU S e d))
theorem alignment_loop_zero : Term.reindex (alignmentCube S e d)
    (endpointSub (total (interval (total (interval (raisedContext point))))) false) =
      Term.reindex (SmallUniverse.term (NativeNerve.realizedConstant S)) (NativeSquare.squareBase (raisedContext point)) :=
  PathSection.body_zero _ _ _ _ _
theorem alignment_loop_one : Term.reindex (alignmentCube S e d)
    (endpointSub (total (interval (total (interval (raisedContext point))))) true) =
      Term.reindex (SmallUniverse.term (NativeNerve.realizedConstant S)) (NativeSquare.squareBase (raisedContext point)) :=
  PathSection.body_one _ _ _ _ _
theorem omega_loop_zero : Term.reindex (omegaCube S e d)
    (endpointSub (total (interval (total (interval (raisedContext point))))) false) =
      Term.reindex (SmallUniverse.term (NativeNerve.realizedConstant S)) (NativeSquare.squareBase (raisedContext point)) :=
  PathSection.body_zero _ _ _ _ _
theorem omega_loop_one : Term.reindex (omegaCube S e d)
    (endpointSub (total (interval (total (interval (raisedContext point))))) true) =
      Term.reindex (SmallUniverse.term (NativeNerve.realizedConstant S)) (NativeSquare.squareBase (raisedContext point)) :=
  PathSection.body_one _ _ _ _ _

end SquareKit.Cubical.Cartesian.ClassifierComparison.NativeComparison
