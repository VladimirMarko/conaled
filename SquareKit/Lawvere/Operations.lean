import SquareKit.Lawvere
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sigma
import Mathlib.CategoryTheory.Limits.Types.Products

/-! Construct a Lawvere theory from operations, projections and substitution. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SquareKit.Lawvere
open CategoryTheory CategoryTheory.Limits
universe u w

/-- A clone, with all finite arities including zero. -/
structure Operations where
  Op : Nat → Type u
  var : ∀ {n}, Fin n → Op n
  subst : ∀ {m n}, Op n → (Fin n → Op m) → Op m
  var_subst : ∀ {m n} (i : Fin n) (σ : Fin n → Op m), subst (var i) σ = σ i
  subst_var : ∀ {n} (t : Op n), subst t var = t
  subst_assoc : ∀ {l m n} (t : Op n) (σ : Fin n → Op m) (τ : Fin m → Op l),
    subst (subst t σ) τ = subst t (fun i => subst (σ i) τ)

namespace Operations
variable (O : Operations.{u})

/-- A wrapper keeps each theory's category instance local to its own objects. -/
structure Context (O : Operations.{u}) where
  size : Nat

instance : Category O.Context where
  Hom a b := Fin b.size → O.Op a.size
  id _ := O.var
  comp f g i := O.subst (g i) f
  id_comp f := funext (fun i => O.subst_var (f i))
  comp_id f := funext (fun i => O.var_subst i f)
  assoc f g h := funext (fun i => (O.subst_assoc (h i) g f).symm)

noncomputable def indexEquiv {k : Nat} (f : Fin k → O.Context) :
    (Σ i, Fin (f i).size) ≃ Fin (Fintype.card (Σ i, Fin (f i).size)) :=
  Fintype.equivFin _

noncomputable def productFan {k : Nat} (f : Fin k → O.Context) : Fan f :=
  Fan.mk ⟨Fintype.card (Σ i, Fin (f i).size)⟩
    (fun i j => O.var (O.indexEquiv f ⟨i,j⟩))

noncomputable def productLimit {k : Nat} (f : Fin k → O.Context) :
    IsLimit (O.productFan f) :=
  Fan.IsLimit.mk _
    (fun s j => s.proj ((O.indexEquiv f).symm j).1 ((O.indexEquiv f).symm j).2)
    (by
      intro s i; funext j
      change O.subst (O.var _) _ = _
      rw [O.var_subst]
      exact congrArg (fun p : Σ i, Fin (f i).size => s.proj p.1 p.2)
        ((O.indexEquiv f).symm_apply_apply ⟨i,j⟩))
    (by
      intro s m h
      funext j
      have hi := congrFun (h ((O.indexEquiv f).symm j).1) ((O.indexEquiv f).symm j).2
      change O.subst (O.var _) m = _ at hi
      rw [O.var_subst] at hi
      simpa only [Sigma.eta, Equiv.apply_symm_apply] using hi)

noncomputable instance : HasFiniteProducts O.Context where
  out _k := { has_limit := fun F =>
    HasLimit.mk ⟨(Cone.postcompose Discrete.natIsoFunctor.inv).obj
      (O.productFan (fun i => F.obj ⟨i⟩)),
      (IsLimit.postcomposeInvEquiv _ _).symm (O.productLimit _)⟩ }

/-- The designated context `n` is the power of the one-variable context. -/
def powerFan (n : Nat) : Fan (fun _ : Fin n => (⟨1⟩ : O.Context)) :=
  Fan.mk ⟨n⟩ (fun i _ => O.var i)

def powerLimit (n : Nat) : IsLimit (O.powerFan n) :=
  Fan.IsLimit.mk _ (fun s i => s.proj i 0)
    (by intro s i; funext j; have : j = 0 := Fin.eq_zero j; subst j; exact O.var_subst _ _)
    (by intro s m h; funext i; exact (O.var_subst i m).symm.trans (congrFun (h i) 0))

noncomputable def theory : Theory.{0,u} where
  Obj := O.Context
  category := inferInstance
  products := inferInstance
  generator := ⟨1⟩
  generated X := ⟨X.size, ⟨(O.powerLimit X.size).conePointUniqueUpToIso (limit.isLimit _)⟩⟩

/-- Maps of operations preserve variables and simultaneous substitution. -/
structure Map (P : Operations) where
  map : ∀ {n}, O.Op n → P.Op n
  map_var : ∀ {n} (i : Fin n), map (O.var i) = P.var i
  map_subst : ∀ {m n} (t : O.Op n) (σ : Fin n → O.Op m),
    map (O.subst t σ) = P.subst (map t) (fun i => map (σ i))

namespace Map
variable {O} {P : Operations} (F : O.Map P)
def toFunctor : O.Context ⥤ P.Context where
  obj X := ⟨X.size⟩
  map f i := F.map (f i)
  map_id _X := funext (fun i => F.map_var i)
  map_comp f g := funext (fun i => F.map_subst (g i) f)

noncomputable def mappedProductLimit {k} (f : Fin k → O.Context) :
    IsLimit (Fan.mk (F.toFunctor.obj (O.productFan f).pt)
      (fun i => F.toFunctor.map ((O.productFan f).proj i))) := by
  have hp := P.productLimit (fun i => F.toFunctor.obj (f i))
  convert hp using 1
  congr 1
  funext i j
  exact F.map_var _

noncomputable instance : PreservesFiniteProducts F.toFunctor where
  preserves _k := by
    refine ⟨?_⟩
    intro K
    let f := K.obj ∘ Discrete.mk
    let : PreservesLimit (Discrete.functor (K.obj ∘ Discrete.mk)) F.toFunctor :=
      preservesLimit_of_preserves_limit_cone (O.productLimit f)
        ((isLimitMapConeFanMkEquiv F.toFunctor f _).symm (F.mappedProductLimit f))
    exact preservesLimit_of_iso_diagram F.toFunctor (Discrete.natIsoFunctor (F := K)).symm

noncomputable def theoryHom : Hom O.theory P.theory :=
  ⟨F.toFunctor, (inferInstance : PreservesFiniteProducts F.toFunctor), Iso.refl _⟩
end Map

/-- An algebra of operations. The laws express projection and substitution,
not the desired categorical conclusion. -/
structure Algebra where
  Carrier : Type w
  act : ∀ {n}, O.Op n → (Fin n → Carrier) → Carrier
  var_act : ∀ {n} (i : Fin n) (x : Fin n → Carrier), act (O.var i) x = x i
  subst_act : ∀ {m n} (t : O.Op n) (σ : Fin n → O.Op m) (x : Fin m → Carrier),
    act (O.subst t σ) x = act t (fun i => act (σ i) x)

namespace Algebra
variable {O} (A : O.Algebra.{u,w})

def toFunctor : O.Context ⥤ Type w where
  obj n := Fin n.size → A.Carrier
  map f := TypeCat.ofHom (fun x i => A.act (f i) x)
  map_id n := by ext x i; exact A.var_act i x
  map_comp f g := by ext x i; exact A.subst_act (g i) f x

noncomputable def mappedProductLimit {k : Nat} (f : Fin k → O.Context) :
    IsLimit (Fan.mk (A.toFunctor.obj (O.productFan f).pt)
      (fun i => A.toFunctor.map ((O.productFan f).proj i))) :=
  Fan.IsLimit.mk _
    (fun s => TypeCat.ofHom (fun x j => s.proj ((O.indexEquiv f).symm j).1 x
      ((O.indexEquiv f).symm j).2))
    (by
      intro s i; ext x; funext j
      change A.act (O.var _) _ = _
      rw [A.var_act]
      exact congrArg (fun p : Σ i, Fin (f i).size => s.proj p.1 x p.2)
        ((O.indexEquiv f).symm_apply_apply ⟨i,j⟩))
    (by
      intro s m h
      ext x
      funext j
      have hi := congrFun (congrArg (fun q => q x) (h ((O.indexEquiv f).symm j).1))
        ((O.indexEquiv f).symm j).2
      change A.act (O.var _) (m x) = _ at hi
      rw [A.var_act] at hi
      change m x j = s.proj ((O.indexEquiv f).symm j).1 x ((O.indexEquiv f).symm j).2
      simpa only [Sigma.eta, Equiv.apply_symm_apply] using hi)

noncomputable instance : PreservesFiniteProducts A.toFunctor where
  preserves k := by
    refine ⟨?_⟩
    intro K
    let f : Fin k → O.Context := fun i => K.obj ⟨i⟩
    let : PreservesLimit (Discrete.functor (K.obj ∘ Discrete.mk)) A.toFunctor :=
      preservesLimit_of_preserves_limit_cone (O.productLimit f)
        ((isLimitMapConeFanMkEquiv A.toFunctor f _).symm (A.mappedProductLimit f))
    exact preservesLimit_of_iso_diagram A.toFunctor (Discrete.natIsoFunctor (F := K)).symm

noncomputable def model : Model O.theory (Type w) := ⟨A.toFunctor, (inferInstance : PreservesFiniteProducts A.toFunctor)⟩
end Algebra
end Operations
end SquareKit.Lawvere
