import SquareKit.Internal.Cubical.CartesianNerve
import SquareKit.Internal.Cubical.CartesianSourceVertices
import SquareKit.Internal.Cubical.SmallFamilyClassification
import SquareKit.Internal.Cubical.FillingTransport
import SquareKit.Internal.Cubical.CartesianDiscreteRecords

/-! Small represented tuple families and their complete selected fillers. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

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

def presentedConstantFilling (Γ : Context.{u}) (S : Type u) : Filling (constantFamily Γ S) where
  fill _ _ b := b.base.reindex (projection (interval _))

theorem presentedConstantFilling_lawful (Γ : Context.{u}) (S : Type u) :
    (presentedConstantFilling Γ S).Lawful where
  fills {Δ} _ _ b := by
    constructor
    · rfl
    · intro x h
      rcases x with @⟨I, γ, r⟩
      exact ((constant_partial_interval b.tube (Functor.elementsMk _ I γ) h r
        ((endpoint _ false).val _)).trans (b.boundary (Δ.elementsMk I γ) h)).symm
  uniform _ _ _ _ := rfl

def presentationFilling {Γ : Context.{u}} {A : Family Γ} {S : Type u}
    (e : A ≅ constantFamily Γ S) : Filling A :=
  (presentedConstantFilling Γ S).transport e.symm

theorem presentationFilling_lawful {Γ : Context.{u}} {A : Family Γ} {S : Type u}
    (e : A ≅ constantFamily Γ S) : (presentationFilling e).Lawful :=
  Filling.transport_lawful e.symm _ (presentedConstantFilling_lawful Γ S)

/-- The whole section is determined by its source boundary in a presented family. -/
theorem presented_section_unique {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {S : Type u} (e : A ≅ constantFamily (total (interval Γ)) S) (s t : Term A)
    (h : s.reindex (endpointSub Γ false) = t.reindex (endpointSub Γ false)) : s = t := by
  apply Term.ext
  intro x
  rcases x with @⟨I, γ, r⟩
  let y := Γ.elementsMk I γ
  have hs := constant_section_interval (Term.map e.hom s) y r ((endpoint Γ false).val y)
  have ht := constant_section_interval (Term.map e.hom t) y r ((endpoint Γ false).val y)
  have hb := congrArg (fun a => e.hom.app (extendObj (interval Γ) y ((endpoint Γ false).val y))
    (a.val y)) h
  have he := hs.trans (hb.trans ht.symm)
  have hh := congrArg (e.inv.app (extendObj (interval Γ) y r)) he
  dsimp only [Term.map] at hh
  rw [e.hom_inv_id_app_apply, e.hom_inv_id_app_apply] at hh
  exact hh

theorem presented_filling_unique {Γ : Context.{u}} {A : Family Γ} {S : Type u}
    (e : A ≅ constantFamily Γ S) (F G : Filling A) (hF : F.Lawful) (hG : G.Lawful) : F = G := by
  cases F with | mk ff =>
    cases G with | mk gg =>
      congr
      funext Δ p φ b
      exact presented_section_unique (Functor.isoWhiskerLeft p.mapElements e) _ _
        ((hF.fills p φ b).1.trans (hG.fills p φ b).1.symm)

/-- Equality here includes the entire chosen local filling operation. -/
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
            funext I p φ b
            exact presented_section_unique (Functor.isoWhiskerLeft p.mapElements e) _ _
              ((ha.fills p φ b).1.trans (hb.fills p φ b).1.symm)
      cases he
      rfl

end SquareKit.Cubical.Presheaf

namespace SquareKit.Cubical.Cartesian.VertexChart
open CategoryTheory
open Presheaf
universe u
variable (V : SquareKit.Cubical.Cube ⥤ Type) (zero : ∀ I, V.obj I)

/-- Every represented chart has small tuple fibers, without lifting its base. -/
def Fiber {I : SquareKit.Cubical.Cube} (T : VertexSystem.{u} (V.obj I))
    (x : (Presheaf.representable.{u} I).Elements) : Type u :=
  (T.reindex (V.map x.val.down)).Tuple

def presentationEquiv {I : SquareKit.Cubical.Cube} (T : VertexSystem.{u} (V.obj I))
    (x : (Presheaf.representable.{u} I).Elements) :
    Fiber V T x ≃ (T.obj (zero I)).Carrier :=
  T.tupleGlobalEquiv (V.map x.val.down) (zero x.obj.unop) (zero I)

def family {I : SquareKit.Cubical.Cube} (T : VertexSystem.{u} (V.obj I)) :
    Presheaf.Family (Presheaf.representable.{u} I) :=
  familyFromPresentation (Fiber V T) (presentationEquiv V zero T)

/-- Conjugation is exactly tuple restriction, not a different decoding action. -/
theorem family_map_coordinate {I : SquareKit.Cubical.Cube} (T : VertexSystem.{u} (V.obj I))
    {x y : (Presheaf.representable.{u} I).Elements} (f : x ⟶ y)
    (a : (family V zero T).obj x) (w : V.obj y.obj.unop) :
    HEq (((family V zero T).map f a).val w) (a.val (V.map f.hom.unop w)) := by
  change HEq (((presentationEquiv V zero T y).symm (presentationEquiv V zero T x a)).val w) _
  apply (heq_of_eq (T.tupleGlobalEquiv_symm_apply (V.map y.val.down)
    (zero y.obj.unop) w (zero I) (presentationEquiv V zero T x a))).trans
  change HEq (T.arrow (zero I) (V.map y.val.down w)
    (T.arrow (V.map x.val.down (zero x.obj.unop)) (zero I) (a.val (zero x.obj.unop)))) _
  apply (heq_of_eq (T.arrow_comp_apply (V.map x.val.down (zero x.obj.unop))
    (zero I) (V.map y.val.down w) (a.val (zero x.obj.unop)))).trans
  have hm : V.map y.val.down w = V.map x.val.down (V.map f.hom.unop w) := by
    have hv := congrArg ULift.down f.map_val
    change f.hom.unop ≫ x.val.down = y.val.down at hv
    rw [← hv, V.map_comp]
    rfl
  have ha : ∀ z z' : V.obj I, z = z' →
      HEq (T.arrow (V.map x.val.down (zero x.obj.unop)) z (a.val (zero x.obj.unop)))
        (T.arrow (V.map x.val.down (zero x.obj.unop)) z' (a.val (zero x.obj.unop))) := by
    intro z z' h
    cases h
    rfl
  exact (ha _ _ hm).trans (heq_of_eq (a.property (zero x.obj.unop) (V.map f.hom.unop w)))

theorem system_reindex {I J : SquareKit.Cubical.Cube} (T : VertexSystem.{u} (V.obj I))
    (h : J ⟶ I) (x : (Presheaf.representable.{u} J).Elements) :
    (T.reindex (V.map h)).reindex (V.map x.val.down) =
      T.reindex (V.map ((Presheaf.representableMap h).mapElements.obj x).val.down) := by
  change T.reindex (fun v => V.map h (V.map x.val.down v)) =
    T.reindex (V.map (x.val.down ≫ h))
  rw [V.map_comp]
  rfl

private theorem typeHom_heq {A B C D : Type u} {f : A → B} {g : C → D}
    (ha : A = C) (hb : B = D) (h : HEq f g) : HEq (TypeCat.ofHom f) (TypeCat.ofHom g) := by
  subst C
  subst D
  cases h
  rfl

theorem family_reindex {I J : SquareKit.Cubical.Cube} (T : VertexSystem.{u} (V.obj I))
    (h : J ⟶ I) : family V zero (T.reindex (V.map h)) =
      Presheaf.reindex (family V zero T) (Presheaf.representableMap h) := by
  have hobj : ∀ x : (Presheaf.representable.{u} J).Elements,
      (family V zero (T.reindex (V.map h))).obj x =
      (Presheaf.reindex (family V zero T) (Presheaf.representableMap h)).obj x :=
    fun x => congrArg VertexSystem.Tuple (system_reindex V T h x)
  apply Functor.hext hobj
  intro x y f
  apply typeHom_heq (hobj x) (hobj y)
  apply Function.hfunext (hobj x)
  intro a b hab
  apply VertexSystem.Tuple.hext (system_reindex V T h y)
  intro w
  have h₁ := family_map_coordinate V zero (T.reindex (V.map h)) f a w
  have h₂ := family_map_coordinate V zero T ((Presheaf.representableMap h).mapElements.map f) b w
  exact h₁.trans ((VertexSystem.Tuple.val_heq (system_reindex V T h x) hab
    (V.map f.hom.unop w)).trans h₂.symm)

def presentation {I : SquareKit.Cubical.Cube} (T : VertexSystem.{u} (V.obj I)) :
    family V zero T ≅ Presheaf.constantFamily (Presheaf.representable.{u} I)
      (T.obj (zero I)).Carrier :=
  familyPresentation (Fiber V T) (presentationEquiv V zero T)

def filling {I : SquareKit.Cubical.Cube} (T : VertexSystem.{u} (V.obj I)) :
    Presheaf.Filling (family V zero T) := presentationFilling (presentation V zero T)

theorem filling_lawful {I : SquareKit.Cubical.Cube} (T : VertexSystem.{u} (V.obj I)) :
    (filling V zero T).Lawful := presentationFilling_lawful (presentation V zero T)

def localFamily {I : SquareKit.Cubical.Cube} (T : VertexSystem.{u} (V.obj I)) :
    SmallFamilyCode.{u} I :=
  ⟨family V zero T, (filling V zero T).toLocal,
    Presheaf.Filling.toLocal_lawful (filling_lawful V zero T)⟩

/-- Reindexing preserves the small family and its complete selected filler record. -/
theorem localFamily_reindex {I J : SquareKit.Cubical.Cube} (T : VertexSystem.{u} (V.obj I))
    (h : J ⟶ I) : localFamily V zero (T.reindex (V.map h)) =
      (localFamily V zero T).reindex (Presheaf.representableMap h) :=
  localFamily_eq_of_presented _ _ (family_reindex V zero T h)
    (presentation V zero (T.reindex (V.map h)))

end SquareKit.Cubical.Cartesian.VertexChart

namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u

/-- The same finite-set nerve on De Morgan substitutions, evaluated at Boolean vertices. -/
def dmVertexFunctor : SquareKit.Cubical.Cube ⥤ Type where
  obj I := Vertex I.dimension
  map f := TypeCat.ofHom (dmVertices f)
  map_id _ := rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro v
    exact dmVertices_comp f g v

def dmFiniteNerve : Presheaf.Context.{u+1} where
  obj I := VertexSystem.{u} (Vertex I.unop.dimension)
  map f := TypeCat.ofHom (fun T => T.reindex (dmVertices f.unop))
  map_id _ := rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro T
    have h : dmVertices (f ≫ g).unop = dmVertices f.unop ∘ dmVertices g.unop :=
      funext (dmVertices_comp g.unop f.unop)
    change T.reindex (dmVertices (f ≫ g).unop) = _
    rw [h]
    rfl

/-- Realization lands in the original small-family universe; each chart base stays small. -/
def realizeDM : dmFiniteNerve.{u} ⟶ Presheaf.smallFamilyCodes.{u} where
  app I := TypeCat.ofHom (fun T => VertexChart.localFamily dmVertexFunctor (fun _ _ => false) T)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro T
    exact VertexChart.localFamily_reindex dmVertexFunctor (fun _ _ => false) T f.unop

@[simp] theorem dmVertices_inclusion {I J : Cube} (f : I ⟶ J) (v : Vertex I.dimension) :
    dmVertices (inclusion.map f) v = Cube.vertices f v := by
  funext i
  change SourceVertexExpr.eval v (Dim.expr (f i)) = Dim.eval (f i) v
  cases f i with
  | endpoint b => cases b <;> rfl
  | var _ => rfl

def nerveRestriction : restrict dmFiniteNerve.{u} ≅ finiteNerve.{u} where
  hom := {
    app := fun _ => TypeCat.ofHom (fun T => T)
    naturality := fun I J f => by
      apply ConcreteCategory.hom_ext
      intro T
      change T.reindex (dmVertices (inclusion.map f.unop)) = T.reindex (Cube.vertices f.unop)
      exact congrArg T.reindex (funext (dmVertices_inclusion f.unop)) }
  inv := {
    app := fun _ => TypeCat.ofHom (fun T => T)
    naturality := fun I J f => by
      apply ConcreteCategory.hom_ext
      intro T
      change T.reindex (Cube.vertices f.unop) = T.reindex (dmVertices (inclusion.map f.unop))
      exact congrArg T.reindex (funext (dmVertices_inclusion f.unop)).symm }

def realizeCartesian : finiteNerve.{u} ⟶ restrict Presheaf.smallFamilyCodes.{u} :=
  nerveRestriction.inv ≫ restrictMap realizeDM

/-- Decoding a realized nerve preserves the complete tuple restriction action. -/
theorem realizedDecode_map_coordinate {x y : dmFiniteNerve.{u}.Elements}
    (f : x ⟶ y) (a : ((Presheaf.SmallUniverse.decode realizeDM).obj x))
    (w : Vertex y.obj.unop.dimension) :
    HEq (((Presheaf.SmallUniverse.decode realizeDM).map f a).val w)
      (a.val (dmVertices f.hom.unop w)) := by
  have hc := cast_heq
    (congrArg (fun A : Presheaf.SmallFamilyCode.{u} y.obj.unop => Presheaf.CodeFiber A)
      ((realizeDM.mapElements.map f).map_val))
    ((VertexChart.localFamily dmVertexFunctor (fun _ _ => false) x.val).family.map
      (Presheaf.representableGenericHom f.hom.unop) a)
  have ht : y.val.reindex (dmVertices (𝟙 y.obj.unop)) =
      (x.val.reindex (dmVertices f.hom.unop)).reindex (dmVertices (𝟙 y.obj.unop)) :=
    congrArg (fun T : VertexSystem.{u} (Vertex y.obj.unop.dimension) =>
      T.reindex (dmVertices (𝟙 y.obj.unop))) f.map_val.symm
  have hs := ht.trans (VertexChart.system_reindex dmVertexFunctor x.val f.hom.unop
    (Presheaf.representableGeneric y.obj.unop))
  exact (VertexSystem.Tuple.val_heq hs hc w).trans
    (VertexChart.family_map_coordinate dmVertexFunctor (fun _ _ => false) x.val
      (Presheaf.representableGenericHom f.hom.unop) a w)

theorem decodedTuple_map_coordinate {Γ : Presheaf.Context.{u}}
    (c : Presheaf.raisedContext Γ ⟶ dmFiniteNerve.{u}) {x y : Γ.Elements}
    (f : x ⟶ y) (a : (Presheaf.decode (c ≫ realizeDM)).obj x)
    (w : Vertex y.obj.unop.dimension) :
    HEq (((Presheaf.decode (c ≫ realizeDM)).map f a).val w)
      (a.val (dmVertices f.hom.unop w)) :=
  realizedDecode_map_coordinate (c.mapElements.map ((Presheaf.raisedElements Γ).map f)) a w

private theorem tupleValue_heq {V : Type} {T : VertexSystem.{u} V}
    (a : T.Tuple) {v w : V} (h : v = w) : HEq (a.val v) (a.val w) := by
  subst w
  rfl

/-- Realization and Cartesian decoding have the same raised tuples and restriction maps. -/
def realizedDecoderIso :
    restrictFamily (Presheaf.SmallUniverse.liftedDecode realizeDM.{u}) ≅
      reindex TupleDecoder.family nerveRestriction.hom where
  hom := {
    app := fun _ => TypeCat.ofHom (fun a => a)
    naturality := by
      intro x y f
      apply ConcreteCategory.hom_ext
      intro a
      apply ULift.ext
      apply VertexSystem.Tuple.ext
      intro w
      have hs := realizedDecode_map_coordinate ((elements dmFiniteNerve).map f) a.down w
      have ht := TupleDecoder.mapEquiv_coordinate (nerveRestriction.hom.mapElements.map f) a.down w
      have hi : HEq (a.down.val (dmVertices (inclusion.map f.hom.unop) w))
          (a.down.val (Cube.vertices f.hom.unop w)) :=
        tupleValue_heq a.down (dmVertices_inclusion f.hom.unop w)
      exact eq_of_heq (hs.trans (hi.trans ht.symm)) }
  inv := {
    app := fun _ => TypeCat.ofHom (fun a => a)
    naturality := by
      intro x y f
      apply ConcreteCategory.hom_ext
      intro a
      apply ULift.ext
      apply VertexSystem.Tuple.ext
      intro w
      have hs := realizedDecode_map_coordinate ((elements dmFiniteNerve).map f) a.down w
      have ht := TupleDecoder.mapEquiv_coordinate (nerveRestriction.hom.mapElements.map f) a.down w
      have hi : HEq (a.down.val (dmVertices (inclusion.map f.hom.unop) w))
          (a.down.val (Cube.vertices f.hom.unop w)) :=
        tupleValue_heq a.down (dmVertices_inclusion f.hom.unop w)
      exact eq_of_heq (ht.trans (hi.symm.trans hs.symm)) }

/-- Any realized decoded section with the box's source is the complete selected
Cartesian filler, after the explicit decoder identification. -/
theorem realizedDecoder_fill_eq {Γ : Context.{u+1}}
    (p : total (interval Γ) ⟶ restrict dmFiniteNerve.{u})
    (φ : Subcontext Γ) (r : Term (interval Γ))
    (b : OpenBox (reindex TupleDecoder.family (p ≫ nerveRestriction.hom)) φ r)
    (s : Term (reindex (restrictFamily (Presheaf.SmallUniverse.liftedDecode realizeDM)) p))
    (h : Term.reindex (Term.map (Functor.whiskerLeft p.mapElements realizedDecoderIso.hom) s)
      (graph r) = b.base) :
    TupleDecoder.filling.fill (p ≫ nerveRestriction.hom) φ r b =
      Term.map (Functor.whiskerLeft p.mapElements realizedDecoderIso.hom) s :=
  TupleDecoder.fill_eq _ φ r b _ h


end SquareKit.Cubical.Cartesian

namespace SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u
variable {Γ : Context.{u}} {a b : raisedContext Γ ⟶ smallFamilyCodes.{u}}
  (p : Term (paths a b))

/-- Raise a small decoded line section without changing its actual values. -/
def raiseLineSection (s : Term (Presheaf.decode ((raisedIntervalIso Γ).hom ≫ codeOfPath p))) :
    Term (liftedDecode (codeOfPath p)) :=
  (Raising.raiseTerm s).reindex (raisedIntervalIso Γ).inv

private theorem raiseTerm_heq {B C : Family Γ} (h : B = C)
    {s : Term B} {t : Term C} (ht : HEq s t) : HEq (Raising.raiseTerm s) (Raising.raiseTerm t) := by
  subst C
  cases ht
  rfl

/-- An actual small decoded section computes universal native transport when
the endpoint is discrete; no equality of selected filling recipes is required. -/
theorem pathToMap_of_smallSection (hB : PathDiscrete (liftedDecode b))
    (s : Term (Presheaf.decode ((raisedIntervalIso Γ).hom ≫ codeOfPath p)))
    (c : Term (Presheaf.decode a)) (d : Term (Presheaf.decode b))
    (hc : HEq (s.reindex (endpointSub Γ false)) c)
    (hd : HEq (s.reindex (endpointSub Γ true)) d) :
    Term.map (pathToMap p) (Raising.raiseTerm c) = Raising.raiseTerm d := by
  apply DiscreteRecords.mapTo_section (NativeDecode.filling (codeOfPath p))
    (NativeDecode.filling_lawful _) (raiseLineSection p s) (decode_zero p) (decode_one p) hB
  · have h₀ : reindex (Presheaf.decode ((raisedIntervalIso Γ).hom ≫ codeOfPath p))
        (endpointSub Γ false) = Presheaf.decode a :=
      congrArg Presheaf.decode (codeOfPath_zero p)
    change HEq (Raising.raiseTerm (s.reindex (endpointSub Γ false))) (Raising.raiseTerm c)
    exact raiseTerm_heq h₀ hc
  · have h₁ : reindex (Presheaf.decode ((raisedIntervalIso Γ).hom ≫ codeOfPath p))
        (endpointSub Γ true) = Presheaf.decode b :=
      congrArg Presheaf.decode (codeOfPath_one p)
    change HEq (Raising.raiseTerm (s.reindex (endpointSub Γ true))) (Raising.raiseTerm d)
    exact raiseTerm_heq h₁ hd
end SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
