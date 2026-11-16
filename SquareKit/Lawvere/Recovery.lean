import SquareKit.Lawvere.Action
import Mathlib.CategoryTheory.Equivalence

/-! Equivalence between operation algebras and finite-product-preserving type-valued models. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SquareKit.Lawvere.Operations
open CategoryTheory CategoryTheory.Limits
universe u w
variable {O : Operations.{u}}
namespace Algebra
/-- A function preserving every operation, including constants. -/
structure Hom (A B : O.Algebra.{u,w}) where
  toFun : A.Carrier → B.Carrier
  map_act : ∀ {n} (t : O.Op n) (x : Fin n → A.Carrier),
    toFun (A.act t x) = B.act t (fun i => toFun (x i))

@[ext] theorem Hom.ext {A B : O.Algebra.{u,w}} {f g : Hom A B}
    (h : f.toFun = g.toFun) : f = g := by cases f; cases g; cases h; rfl

instance : Category O.Algebra.{u,w} where
  Hom := Hom
  id _ := ⟨id, fun _ _ => rfl⟩
  comp f g := ⟨g.toFun ∘ f.toFun, fun t x => by
    change g.toFun (f.toFun (Algebra.act _ t x)) = _
    rw [f.map_act, g.map_act]
    rfl⟩

/-- Algebra homomorphisms act on every coordinate. -/
def Hom.toNatTrans {A B : O.Algebra.{u,w}} (h : A ⟶ B) : A.toFunctor ⟶ B.toFunctor where
  app _ := TypeCat.ofHom (fun x i => h.toFun (x i))
  naturality _ _ f := by ext x; funext i; exact h.map_act (f i) x

def modelFunctor : O.Algebra.{u,w} ⥤ Model O.theory (Type w) where
  obj A := A.model
  map h := h.toNatTrans

/-- Naturality at projections forces every component to be coordinatewise. -/
theorem naturality_coordinate {A B : O.Algebra.{u,w}} (η : A.model ⟶ B.model)
    {n} (x : Fin n → A.Carrier) (i : Fin n) :
    η.app ⟨n⟩ x i = η.app ⟨1⟩ (fun _ => x i) 0 := by
  have h := congrArg (fun f => f x 0) (η.naturality
    (show (⟨n⟩ : O.Context) ⟶ ⟨1⟩ from fun _ => O.var i))
  change η.app ⟨1⟩ (fun _ => A.act (O.var i) x) 0 = B.act (O.var i) (η.app ⟨n⟩ x) at h
  simpa only [A.var_act, B.var_act] using h.symm

def homOfNatTrans {A B : O.Algebra.{u,w}} (η : A.model ⟶ B.model) : A ⟶ B where
  toFun x := η.app ⟨1⟩ (fun _ => x) 0
  map_act t x := by
    have h := congrArg (fun f => f x 0) (η.naturality
      (show (⟨_⟩ : O.Context) ⟶ ⟨1⟩ from fun _ => t))
    change η.app ⟨1⟩ (fun _ => A.act t x) 0 = B.act t (fun i => η.app ⟨1⟩ (fun _ => x i) 0)
    change η.app ⟨1⟩ (fun _ => A.act t x) 0 = B.act t (η.app ⟨_⟩ x) at h
    rw [h]
    congr 1
    funext i
    exact naturality_coordinate η x i

def modelFullyFaithful : (modelFunctor.{u,w} (O := O)).FullyFaithful where
  preimage := homOfNatTrans
  map_preimage η := by
    apply NatTrans.ext
    funext n
    ext x
    funext i
    exact (naturality_coordinate η x i).symm
  preimage_map h := by
    apply Hom.ext
    rfl
end Algebra

namespace Recovery
variable (M : Model O.theory (Type w))
abbrev carrier := M.toFunctor.obj ⟨1⟩
def powerLimit (n : Nat) : IsLimit (Fan.mk (M.toFunctor.obj ⟨n⟩)
    (fun i : Fin n => M.toFunctor.map (fun _ : Fin 1 => O.var i))) :=
  isLimitOfPreserves M.toFunctor (O.powerLimit n) |>
    isLimitMapConeFanMkEquiv M.toFunctor _ _
def coordinates (n : Nat) : M.toFunctor.obj ⟨n⟩ ≅ (Fin n → carrier M) :=
  (powerLimit M n).conePointUniqueUpToIso (Types.productLimitCone _).isLimit
@[simp] theorem coordinates_apply {n} (x : M.toFunctor.obj ⟨n⟩) (i : Fin n) :
    (coordinates M n).hom x i = M.toFunctor.map (fun _ : Fin 1 => O.var i) x := by
  exact congrArg (fun f => f x) ((powerLimit M n).conePointUniqueUpToIso_hom_comp
    (Types.productLimitCone _).isLimit ⟨i⟩)
@[simp] theorem coordinates_inv_apply {n} (x : Fin n → carrier M) (i : Fin n) :
    M.toFunctor.map (fun _ : Fin 1 => O.var i) ((coordinates M n).inv x) = x i := by
  exact congrArg (fun f => f x) ((powerLimit M n).conePointUniqueUpToIso_inv_comp
    (Types.productLimitCone _).isLimit ⟨i⟩)
def act {n} (t : O.Op n) (x : Fin n → carrier M) : carrier M :=
  M.toFunctor.map (fun _ : Fin 1 => t) ((coordinates M n).inv x)

theorem tuple_map {m n} (f : (⟨m⟩ : O.Context) ⟶ ⟨n⟩) (x : Fin m → carrier M) :
    (coordinates M n).hom (M.toFunctor.map f ((coordinates M m).inv x)) =
      fun i => act M (f i) x := by
  funext i
  rw [coordinates_apply]
  change (M.toFunctor.map f ≫ M.toFunctor.map (fun _ : Fin 1 => O.var i)) _ = _
  rw [← M.toFunctor.map_comp]
  have h : f ≫ (fun _ : Fin 1 => O.var i) = (fun _ : Fin 1 => f i) :=
    funext (fun _ => O.var_subst i f)
  rw [h]
  rfl

def algebra : O.Algebra.{u,w} where
  Carrier := carrier M
  act := act M
  var_act i x := coordinates_inv_apply M x i
  subst_act {m n} t σ x := by
    change M.toFunctor.map (fun _ : Fin 1 => O.subst t σ) _ = _
    have h : ((fun _ : Fin 1 => O.subst t σ) : (⟨m⟩ : O.Context) ⟶ ⟨1⟩) =
        (show (⟨m⟩ : O.Context) ⟶ ⟨1⟩ from σ ≫ (fun _ : Fin 1 => t)) := rfl
    rw [h, M.toFunctor.map_comp]
    change M.toFunctor.map (fun _ : Fin 1 => t) (M.toFunctor.map σ _) = _
    unfold act
    congr 1
    apply (coordinates M n).toEquiv.injective
    exact (tuple_map M σ x).trans ((coordinates M n).toEquiv.apply_symm_apply _).symm

/-- The finite-power comparisons are natural in the context. -/
def functorIso : (algebra M).toFunctor ≅ M.toFunctor :=
  NatIso.ofComponents (fun n => (coordinates M n.size).symm) (by
    intro m n f
    ext x
    apply (coordinates M n.size).toEquiv.injective
    exact ((coordinates M n.size).toEquiv.apply_symm_apply _).trans (tuple_map M f x).symm)

/-- Every model is isomorphic to the tuple model of its recovered algebra. -/
def modelIso : (algebra M).model ≅ M :=
  ⟨(functorIso M).hom, (functorIso M).inv,
    (functorIso M).hom_inv_id, (functorIso M).inv_hom_id⟩

/-- Recovery on natural transformations, transported through the power comparisons. -/
def functor : Model O.theory (Type w) ⥤ O.Algebra.{u,w} where
  obj := algebra
  map {M N} η := Algebra.modelFullyFaithful.preimage
    ((modelIso M).hom ≫ η ≫ (modelIso N).inv)
  map_id M := by
    apply Algebra.modelFullyFaithful.map_injective
    rw [Algebra.modelFullyFaithful.map_preimage, CategoryTheory.Functor.map_id]
    simp
  map_comp {M N P} η θ := by
    apply Algebra.modelFullyFaithful.map_injective
    rw [Functor.map_comp]
    simp only [Algebra.modelFullyFaithful.map_preimage, Category.assoc,
      Iso.inv_hom_id_assoc]

/-- The model round trip is natural in model homomorphisms. -/
def counitIso : functor (O := O) ⋙ Algebra.modelFunctor ≅ 𝟭 (Model O.theory (Type w)) :=
  NatIso.ofComponents modelIso (by
    intro M N η
    change Algebra.modelFunctor.map (Algebra.modelFullyFaithful.preimage _) ≫ _ = _
    rw [Algebra.modelFullyFaithful.map_preimage]
    simp)
end Recovery

namespace Algebra
instance : modelFunctor.{u,w} (O := O) |>.IsEquivalence where
  faithful := modelFullyFaithful.faithful
  full := modelFullyFaithful.full
  essSurj := ⟨fun M => ⟨Recovery.algebra M, ⟨Recovery.modelIso M⟩⟩⟩

/-- The algebra round trip is natural in algebra homomorphisms. -/
def recoveryUnitIso : 𝟭 O.Algebra.{u,w} ≅ modelFunctor ⋙ Recovery.functor :=
  NatIso.ofComponents (fun A => (modelFullyFaithful.preimageIso (Recovery.modelIso A.model)).symm)
    (by
      intro A B h
      apply modelFullyFaithful.map_injective
      simp only [Functor.map_comp]
      change modelFunctor.map h ≫ modelFunctor.map (modelFullyFaithful.preimage _) =
        modelFunctor.map (modelFullyFaithful.preimage _) ≫
          modelFunctor.map (modelFullyFaithful.preimage _)
      simp only [modelFullyFaithful.map_preimage]
      change modelFunctor.map h ≫ (Recovery.modelIso B.model).inv =
        (Recovery.modelIso A.model).inv ≫
          (Recovery.modelIso A.model).hom ≫ modelFunctor.map h ≫ (Recovery.modelIso B.model).inv
      rw [Iso.inv_hom_id_assoc])

/-- Equivalence includes the explicit generator recovery functor and natural round trips. -/
def modelEquivalence : O.Algebra.{u,w} ≌ Model O.theory (Type w) :=
  CategoryTheory.Equivalence.mk modelFunctor Recovery.functor recoveryUnitIso Recovery.counitIso

/-- Transport all operations along an equivalence of carriers. -/
def transport (A : O.Algebra.{u,w}) {X : Type w} (e : A.Carrier ≃ X) : O.Algebra.{u,w} where
  Carrier := X
  act t x := e (A.act t (fun i => e.symm (x i)))
  var_act i x := by rw [A.var_act, e.apply_symm_apply]
  subst_act t σ x := by simp only [A.subst_act, e.symm_apply_apply]

@[simp] theorem transport_refl (A : O.Algebra.{u,w}) : A.transport (Equiv.refl _) = A := rfl

theorem transport_trans (A : O.Algebra.{u,w}) {X Y : Type w}
    (e : A.Carrier ≃ X) (f : X ≃ Y) :
    (A.transport e).transport f = A.transport (e.trans f) := rfl

/-- Carrier transport gives an algebra isomorphism, with the supplied equivalence as its function. -/
def transportIso (A : O.Algebra.{u,w}) {X : Type w} (e : A.Carrier ≃ X) : A ≅ A.transport e where
  hom := ⟨e, fun t x => by change e (A.act t x) = e (A.act t _); simp only [e.symm_apply_apply]⟩
  inv := ⟨e.symm, fun t x => e.symm_apply_apply _⟩
  hom_inv_id := by apply Hom.ext; funext x; exact e.symm_apply_apply x
  inv_hom_id := by apply Hom.ext; funext x; exact e.apply_symm_apply x

/-- The recovered action on a tuple model agrees with the original scalar action. -/
theorem recovered_act (A : O.Algebra.{u,w}) {n} (t : O.Op n)
    (x : Fin n → Recovery.carrier A.model) :
    (Recovery.algebra A.model).act t x 0 = A.act t (fun i => x i 0) := by
  change A.act t ((Recovery.coordinates A.model n).inv x) = _
  congr 1
  funext i
  have h := congrArg (fun f => f 0) (Recovery.coordinates_inv_apply A.model x i)
  change A.act (O.var i) ((Recovery.coordinates A.model n).inv x) = x i 0 at h
  rw [A.var_act] at h
  exact h

/-- Recovering the generator of a tuple model returns an isomorphic algebra. -/
def recoveryIso (A : O.Algebra.{u,w}) : Recovery.algebra A.model ≅ A :=
  modelFullyFaithful.preimageIso (Recovery.modelIso A.model)
end Algebra
end SquareKit.Lawvere.Operations
