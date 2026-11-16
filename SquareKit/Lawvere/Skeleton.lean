import SquareKit.Lawvere.Recovery
import Mathlib.CategoryTheory.Adjunction.Limits

/-! Recover operations from any Lawvere theory, without choosing object equalities. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SquareKit.Lawvere
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe u v w z
namespace Model
variable {T : Theory.{u,v}} {U : Theory} {C : Type w} [Category.{z} C]
/-- Precomposition needs finite-product preservation, but no chosen generator comparison. -/
def precompose (F : T.Obj ⥤ U.Obj) [PreservesFiniteProducts F] : Model U C ⥤ Model T C where
  obj M := ⟨F ⋙ M.toFunctor, inferInstance⟩
  map η := whiskerLeft F η

@[simp] theorem precompose_hom (F : Hom T U) :
    precompose (C := C) F.toFunctor = restrict F := rfl

def isoMk {M N : Model T C} (e : M.toFunctor ≅ N.toFunctor) : M ≅ N :=
  ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩

/-- Changing to an equivalent theory transports models in any target category. -/
def precomposeEquivalence (e : T.Obj ≌ U.Obj) : Model U C ≌ Model T C :=
  CategoryTheory.Equivalence.mk (precompose e.functor) (precompose e.inverse)
    (NatIso.ofComponents (fun M => isoMk
      (M.toFunctor.leftUnitor.symm ≪≫ isoWhiskerRight e.counitIso.symm M.toFunctor)) (by
        intro M N η
        apply NatTrans.ext
        funext X
        change η.app X ≫ (𝟙 _ ≫ N.toFunctor.map (e.counitIso.inv.app X)) =
          (𝟙 _ ≫ M.toFunctor.map (e.counitIso.inv.app X)) ≫ η.app _
        simpa only [Category.id_comp, Functor.id_obj] using (η.naturality (e.counitIso.inv.app X)).symm))
    (NatIso.ofComponents (fun M => isoMk
      (isoWhiskerRight e.unitIso.symm M.toFunctor ≪≫ M.toFunctor.leftUnitor)) (by
        intro M N η
        apply NatTrans.ext
        funext X
        change η.app _ ≫ (N.toFunctor.map (e.unitIso.inv.app X) ≫ 𝟙 _) =
          (M.toFunctor.map (e.unitIso.inv.app X) ≫ 𝟙 _) ≫ η.app X
        simpa only [Category.comp_id, Functor.id_obj] using (η.naturality (e.unitIso.inv.app X)).symm))
end Model

namespace Theory
variable (T : Theory.{u,v})
abbrev power (n : Nat) := ∏ᶜ (fun _ : Fin n => T.generator)

/-- Operations of a nonskeletal theory are maps from a finite power to the generator. -/
def operations : Operations.{v} where
  Op n := T.power n ⟶ T.generator
  var i := Pi.π _ i
  subst t σ := Pi.lift σ ≫ t
  var_subst i σ := Pi.lift_comp_π σ i
  subst_var t := by simp
  subst_assoc t σ τ := by
    rw [← Category.assoc]
    congr 1
    apply Pi.hom_ext
    intro i
    simp

def skeletonFunctor : T.operations.Context ⥤ T.Obj where
  obj n := T.power n.size
  map f := Pi.lift f
  map_id _ := Pi.lift_π
  map_comp f g := by
    apply Pi.hom_ext
    intro i
    simp only [Category.assoc, Pi.lift_comp_π]
    rfl

def skeletonFullyFaithful : T.skeletonFunctor.FullyFaithful where
  preimage f i := f ≫ Pi.π _ i
  map_preimage f := by apply Pi.hom_ext; intro i; simp [skeletonFunctor]
  preimage_map f := by funext i; exact Pi.lift_comp_π f i

instance : T.skeletonFunctor.IsEquivalence where
  full := T.skeletonFullyFaithful.full
  faithful := T.skeletonFullyFaithful.faithful
  essSurj := ⟨fun X => by
    obtain ⟨n, ⟨e⟩⟩ := T.generated X
    exact ⟨⟨n⟩, ⟨e.symm⟩⟩⟩

/-- Every object is compared by an isomorphism; no skeletal equality is assumed. -/
def skeletonEquivalence : T.operations.Context ≌ T.Obj := T.skeletonFunctor.asEquivalence
/-- The one-fold power is compared with the original distinguished generator. -/
def generatorIso : T.skeletonFunctor.obj ⟨1⟩ ≅ T.generator where
  hom := Pi.π _ 0
  inv := Pi.lift (fun _ : Fin 1 => 𝟙 T.generator)
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    have : i = 0 := Fin.eq_zero i
    subst i
    simp
  inv_hom_id := by simp

def skeletonHom : Hom T.operations.theory T :=
  ⟨T.skeletonFunctor, (inferInstance : PreservesFiniteProducts T.skeletonFunctor), T.generatorIso⟩

/-- The algebra–model equivalence for the original, possibly nonskeletal theory. -/
def algebraModelEquivalence : T.operations.Algebra.{v,w} ≌ Model T (Type w) :=
  Operations.Algebra.modelEquivalence.trans
    (Model.precomposeEquivalence (T := T.operations.theory) (U := T) T.skeletonEquivalence).symm
end Theory

namespace Model
variable {T : Theory.{u,v}} (M : Model T (Type w))
/-- Recover on the original generator, transporting across its one-power comparison. -/
def algebra : T.operations.Algebra.{v,w} :=
  (Operations.Recovery.algebra ((restrict T.skeletonHom).obj M)).transport
    (M.toFunctor.mapIso T.generatorIso).toEquiv

/-- The original generator carrier is retained literally by this adapter. -/
theorem algebra_carrier : M.algebra.Carrier = M.toFunctor.obj T.generator := rfl

/-- The canonical interpretation of the recovered algebra returns the entire model. -/
def algebraModelIso : T.algebraModelEquivalence.functor.obj M.algebra ≅ M := by
  let E := precomposeEquivalence (T := T.operations.theory) (U := T) (C := Type w)
    T.skeletonEquivalence
  let R := Operations.Recovery.algebra (E.functor.obj M)
  let e := (M.toFunctor.mapIso T.generatorIso).toEquiv
  exact E.inverse.mapIso
    ((Operations.Algebra.modelFunctor.mapIso (R.transportIso e)).symm ≪≫
      Operations.Recovery.modelIso (E.functor.obj M)) ≪≫ (E.unitIso.app M).symm
end Model
end SquareKit.Lawvere
