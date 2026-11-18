import SquareKit.Lawvere.Comparison
import Mathlib.CategoryTheory.Category.Cat

/-! # Functorial model restriction and compatibility with algebra recovery

Restriction is a strict contravariant functor on theories. Algebra recovery
commutes through natural comparisons, retaining the chosen generator maps.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SquareKit.Lawvere
open CategoryTheory CategoryTheory.Functor
universe u v w z
namespace Model
variable {T U V : Theory.{u,v}} {C : Type w} [Category.{z} C]
@[simp] theorem restrict_id : restrict (C := C) (Hom.id T) = 𝟭 (Model T C) := rfl
@[simp] theorem restrict_comp (F : Hom T U) (G : Hom U V) :
    restrict (C := C) (Hom.comp F G) = restrict G ⋙ restrict F := rfl

def semantics (C : Type w) [Category.{z} C] :
    Theory.{u,v}ᵒᵖ ⥤ Cat.{max u z, max u v w z} where
  obj T := Cat.of (Model T.unop C)
  map F := (restrict F.unop).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl
/-- Isomorphic precomposition functors induce naturally isomorphic restrictions. -/
def precomposeIso {T : Theory} {U : Theory} {F G : T.Obj ⥤ U.Obj}
    [Limits.PreservesFiniteProducts F] [Limits.PreservesFiniteProducts G] (e : F ≅ G) :
    precompose (C := C) F ≅ precompose G :=
  NatIso.ofComponents (fun M => isoMk (isoWhiskerRight e M.toFunctor)) (by
    intro M N η
    apply NatTrans.ext
    funext X
    exact (η.naturality (e.hom.app X)).symm)

end Model

namespace Operations
namespace Algebra
variable {O : Operations.{u}} {P : Operations.{v}}
def restrict (F : O.Map P) : P.Algebra.{v,w} ⥤ O.Algebra.{u,w} where
  obj A := (A.action.restrict F).algebra
  map h := ⟨h.toFun, fun t x => h.map_act (F.map t) x⟩
@[simp] theorem restrict_id : restrict (Map.id O) = 𝟭 O.Algebra.{u,w} := rfl
@[simp] theorem restrict_comp {Q : Operations} (F : O.Map P) (G : P.Map Q) :
    restrict.{u, _, w} (F.comp G) = restrict G ⋙ restrict F := rfl

theorem restrict_modelFunctor (F : O.Map P) :
    restrict.{u,v,w} F ⋙ modelFunctor = modelFunctor ⋙ Model.restrict F.theoryHom := rfl
end Algebra

namespace Recovery
variable {O : Operations.{u}} {P : Operations.{v}} (F : O.Map P)
    (M : Model P.theory (Type w))

theorem coordinates_inv_restrict {n} (x : Fin n → carrier M) :
    (coordinates ((Model.restrict F.theoryHom).obj M) n).inv x = (coordinates M n).inv x := by
  apply (coordinates M n).toEquiv.injective
  funext i
  change (coordinates M n).hom ((coordinates ((Model.restrict F.theoryHom).obj M) n).inv x) i =
    (coordinates M n).hom ((coordinates M n).inv x) i
  rw [coordinates_apply, coordinates_apply, coordinates_inv_apply]
  have h := coordinates_inv_apply ((Model.restrict F.theoryHom).obj M) x i
  change M.toFunctor.map (fun _ : Fin 1 => F.map (O.var i)) _ = _ at h
  simpa only [F.map_var] using h

theorem act_restrict {n} (t : O.Op n) (x : Fin n → carrier M) :
    (algebra ((Model.restrict F.theoryHom).obj M)).act t x =
      (algebra M).act (F.map t) x := by
  change M.toFunctor.map (fun _ : Fin 1 => F.map t) _ = _
  rw [coordinates_inv_restrict]
  rfl

/-- For operation maps the generator carrier is unchanged; the comparison is identity there. -/
def restrictionIso : (Algebra.restrict F).obj (algebra M) ≅
    algebra ((Model.restrict F.theoryHom).obj M) where
  hom := ⟨id, fun t x => (act_restrict F M t x).symm⟩
  inv := ⟨id, fun t x => act_restrict F M t x⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

theorem coordinates_inv_one (x : carrier M) :
    (coordinates M 1).inv (fun _ => x) = x := by
  have h := coordinates_inv_apply M (fun _ : Fin 1 => x) 0
  have hp : (fun _ : Fin 1 => P.var (0 : Fin 1)) = (𝟙 (⟨1⟩ : P.Context)) := by
    funext i
    exact congrArg P.var (Fin.eq_zero i).symm
  rw [hp, M.toFunctor.map_id] at h
  exact h

theorem functor_map_apply {M N : Model P.theory (Type w)} (η : M ⟶ N) (x : carrier M) :
    (functor.map η).toFun x = η.app ⟨1⟩ x := by
  change (coordinates N 1).hom (η.app ⟨1⟩ ((coordinates M 1).inv (fun _ => x))) 0 = _
  rw [coordinates_inv_one, coordinates_apply]
  have hp : (fun _ : Fin 1 => P.var (0 : Fin 1)) = (𝟙 (⟨1⟩ : P.Context)) := by
    funext i
    exact congrArg P.var (Fin.eq_zero i).symm
  rw [hp, N.toFunctor.map_id]
  rfl

def restrictionComparison : functor.{v,w} (O := P) ⋙ Algebra.restrict F ≅
    Model.restrict F.theoryHom ⋙ functor (O := O) :=
  NatIso.ofComponents (restrictionIso F) (by
    intro M N η
    apply Algebra.Hom.ext
    funext x
    change (functor.map η).toFun x = (functor.map ((Model.restrict F.theoryHom).map η)).toFun x
    rw [functor_map_apply, functor_map_apply]
    rfl)

@[simp] theorem restrictionIso_id (M : Model P.theory (Type w)) :
    restrictionIso (Map.id P) M = Iso.refl (algebra M) := rfl

theorem restrictionIso_comp {Q : Operations} (G : P.Map Q) (M : Model Q.theory (Type w)) :
    restrictionIso (F.comp G) M =
      (Algebra.restrict F).mapIso (restrictionIso G M) ≪≫
        restrictionIso F ((Model.restrict G.theoryHom).obj M) := rfl

end Recovery
end Operations
namespace Hom
variable {T U : Theory.{u,v}}
def operations (F : Hom T U) : T.operations.Map U.operations :=
  Operations.operationMap (Hom.comp T.skeletonHom F)

/-- Normalization compares both ways of restricting to the chosen context categories. -/
def skeletonRestrictionIso (F : Hom T U) (C : Type w) [Category.{z} C] :
    Model.restrict (C := C) F ⋙ Model.restrict T.skeletonHom ≅
      Model.restrict U.skeletonHom ⋙ Model.restrict F.operations.theoryHom := by
  letI : Limits.PreservesFiniteProducts (T.skeletonFunctor ⋙ F.toFunctor) :=
    (Hom.comp T.skeletonHom F).preserves
  letI : Limits.PreservesFiniteProducts (F.operations.toFunctor ⋙ U.skeletonFunctor) :=
    (Hom.comp F.operations.theoryHom U.skeletonHom).preserves
  exact Model.precomposeIso (T := T.operations.theory) (U := U) (C := C)
    (F := T.skeletonFunctor ⋙ F.toFunctor) (G := F.operations.toFunctor ⋙ U.skeletonFunctor)
    (Operations.normalizationIso (Hom.comp T.skeletonHom F))
end Hom

namespace Model
variable (T : Theory.{u,v})
/-- Recovery on the original distinguished generator, including natural transformations. -/
def originalRecovery : Model T (Type w) ⥤ T.operations.Algebra.{v,w} where
  obj M := M.algebra
  map {M N} η :=
    ((Operations.Recovery.algebra ((restrict T.skeletonHom).obj M)).transportIso
      (M.toFunctor.mapIso T.generatorIso).toEquiv).inv ≫
    Operations.Recovery.functor.map ((restrict T.skeletonHom).map η) ≫
    ((Operations.Recovery.algebra ((restrict T.skeletonHom).obj N)).transportIso
      (N.toFunctor.mapIso T.generatorIso).toEquiv).hom
  map_id M := by
    simp only [CategoryTheory.Functor.map_id]
    apply Operations.Algebra.Hom.ext
    funext x
    exact (M.toFunctor.mapIso T.generatorIso).toEquiv.apply_symm_apply x
  map_comp η θ := by
    simp only [CategoryTheory.Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

def originalRecoveryIso : restrict T.skeletonHom ⋙ Operations.Recovery.functor ≅
    originalRecovery.{u,v,w} T :=
  NatIso.ofComponents (fun M =>
    (Operations.Recovery.algebra ((restrict T.skeletonHom).obj M)).transportIso
      (M.toFunctor.mapIso T.generatorIso).toEquiv) (by
    intro M N η
    simp only [originalRecovery, Iso.hom_inv_id_assoc]
    rfl)
/-- Recovery on the original generator commutes with an arbitrary theory change. -/
def originalRestrictionComparison {U : Theory.{u,v}} (F : Hom T U) :
    originalRecovery.{u,v,w} U ⋙ Operations.Algebra.restrict F.operations ≅
      restrict F ⋙ originalRecovery T :=
  isoWhiskerRight (originalRecoveryIso U).symm (Operations.Algebra.restrict F.operations) ≪≫
    isoWhiskerLeft (restrict U.skeletonHom) (Operations.Recovery.restrictionComparison F.operations) ≪≫
    isoWhiskerRight (F.skeletonRestrictionIso (Type w)).symm Operations.Recovery.functor ≪≫
    isoWhiskerLeft (restrict F) (originalRecoveryIso T)

/-- On the original carrier, recovery of a model map is its generator component. -/
theorem originalRecovery_map_apply {M N : Model T (Type w)} (η : M ⟶ N)
    (x : M.toFunctor.obj T.generator) :
    ((originalRecovery T).map η).toFun x = η.app T.generator x := by
  change N.toFunctor.map T.generatorIso.hom
    ((Operations.Recovery.functor.map ((restrict T.skeletonHom).map η)).toFun
      (M.toFunctor.map T.generatorIso.inv x)) = _
  rw [Operations.Recovery.functor_map_apply]
  have h := congrArg (fun f => f (M.toFunctor.map T.generatorIso.inv x))
    (η.naturality T.generatorIso.hom)
  change η.app T.generator
    (M.toFunctor.map T.generatorIso.hom (M.toFunctor.map T.generatorIso.inv x)) =
      N.toFunctor.map T.generatorIso.hom
        (η.app (T.power 1) (M.toFunctor.map T.generatorIso.inv x)) at h
  change N.toFunctor.map T.generatorIso.hom
    (η.app (T.power 1) (M.toFunctor.map T.generatorIso.inv x)) = _
  rw [← h]
  change η.app T.generator ((M.toFunctor.map T.generatorIso.inv ≫
    M.toFunctor.map T.generatorIso.hom) x) = _
  rw [← M.toFunctor.map_comp, Iso.inv_hom_id, M.toFunctor.map_id]
  rfl

theorem originalRestrictionComparison_apply {U : Theory.{u,v}} (F : Hom T U)
    (M : Model U (Type w)) (x : M.toFunctor.obj U.generator) :
    ((originalRestrictionComparison T F).hom.app M).toFun x =
      M.toFunctor.map F.generatorIso.inv x := by
  change M.toFunctor.map (F.toFunctor.map T.generatorIso.hom)
    ((Operations.Recovery.functor.map ((F.skeletonRestrictionIso (Type w)).inv.app M)).toFun
      (M.toFunctor.map U.generatorIso.inv x)) = _
  rw [Operations.Recovery.functor_map_apply]
  change M.toFunctor.map (F.toFunctor.map T.generatorIso.hom)
    (M.toFunctor.map (Operations.powerComparison (Hom.comp T.skeletonHom F) 1).inv
      (M.toFunctor.map U.generatorIso.inv x)) = _
  have he : U.generatorIso.inv ≫ (Operations.powerComparison (Hom.comp T.skeletonHom F) 1).inv ≫
      F.toFunctor.map T.generatorIso.hom = F.generatorIso.inv := by
    apply (cancel_mono F.generatorIso.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id]
    have hn := Operations.normalization_generator (Hom.comp T.skeletonHom F)
    change (Operations.powerComparison (Hom.comp T.skeletonHom F) 1).hom ≫ U.generatorIso.hom =
      F.toFunctor.map T.generatorIso.hom ≫ F.generatorIso.hom at hn
    rw [← hn, Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  change (M.toFunctor.map U.generatorIso.inv ≫
    M.toFunctor.map (Operations.powerComparison (Hom.comp T.skeletonHom F) 1).inv ≫
      M.toFunctor.map (F.toFunctor.map T.generatorIso.hom)) x = _
  rw [← M.toFunctor.map_comp, ← M.toFunctor.map_comp, he]

@[simp] theorem originalRestrictionComparison_id_apply (M : Model T (Type w))
    (x : M.toFunctor.obj T.generator) :
    ((originalRestrictionComparison T (Hom.id T)).hom.app M).toFun x = x := by
  rw [originalRestrictionComparison_apply]
  change M.toFunctor.map (𝟙 _) x = x
  rw [M.toFunctor.map_id]
  rfl

/-- Comparison maps compose in the same order as contravariant restriction. -/
theorem originalRestrictionComparison_comp_apply {U V : Theory.{u,v}}
    (F : Hom T U) (G : Hom U V) (M : Model V (Type w))
    (x : M.toFunctor.obj V.generator) :
    ((originalRestrictionComparison T (Hom.comp F G)).hom.app M).toFun x =
      ((originalRestrictionComparison T F).hom.app ((restrict G).obj M)).toFun
        (((originalRestrictionComparison U G).hom.app M).toFun x) := by
  rw [originalRestrictionComparison_apply, originalRestrictionComparison_apply,
    originalRestrictionComparison_apply]
  change M.toFunctor.map (G.generatorIso.inv ≫ G.toFunctor.map F.generatorIso.inv) x =
    M.toFunctor.map (G.toFunctor.map F.generatorIso.inv) (M.toFunctor.map G.generatorIso.inv x)
  rw [M.toFunctor.map_comp]
  rfl

/-- The algebra restrictions induced by a composite theory change are coherently compared. -/
def originalCompositeIso {U V : Theory.{u,v}} (F : Hom T U) (G : Hom U V) :
    originalRecovery.{u,v,w} V ⋙ Operations.Algebra.restrict G.operations ⋙
        Operations.Algebra.restrict F.operations ≅
      originalRecovery V ⋙ Operations.Algebra.restrict (Hom.comp F G).operations :=
  isoWhiskerRight (originalRestrictionComparison U G) (Operations.Algebra.restrict F.operations) ≪≫
    isoWhiskerLeft (restrict G) (originalRestrictionComparison T F) ≪≫
    (originalRestrictionComparison T (Hom.comp F G)).symm

/-- The composite comparison commutes with the recovery comparison as natural transformations. -/
theorem originalCompositeIso_coherence {U V : Theory.{u,v}} (F : Hom T U) (G : Hom U V) :
    originalCompositeIso.{u,v,w} T F G ≪≫ originalRestrictionComparison T (Hom.comp F G) =
      isoWhiskerRight (originalRestrictionComparison U G) (Operations.Algebra.restrict F.operations) ≪≫
        isoWhiskerLeft (restrict G) (originalRestrictionComparison T F) := by
  simp [originalCompositeIso]

/-- The comparison between the two algebra restrictions changes no carrier elements. -/
theorem originalCompositeIso_apply {U V : Theory.{u,v}} (F : Hom T U) (G : Hom U V)
    (M : Model V (Type w)) (x : M.toFunctor.obj V.generator) :
    ((originalCompositeIso T F G).hom.app M).toFun x = x := by
  change ((originalRestrictionComparison T (Hom.comp F G)).inv.app M).toFun
    (((originalRestrictionComparison T F).hom.app ((restrict G).obj M)).toFun
      (((originalRestrictionComparison U G).hom.app M).toFun x)) = x
  rw [← originalRestrictionComparison_comp_apply]
  exact congrArg (fun h => h.toFun x)
    ((originalRestrictionComparison T (Hom.comp F G)).app M).hom_inv_id

end Model

end SquareKit.Lawvere
