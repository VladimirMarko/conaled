import SquareKit.Lawvere.Skeleton

/-! # Normalize categorical interpretations by finite powers

The generator comparison and preserved product limits determine an operation
map and a natural isomorphism recovering the original interpretation.
-/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SquareKit.Lawvere
open CategoryTheory CategoryTheory.Limits
universe u v w
namespace Operations
namespace Map
@[ext] theorem ext {O : Operations.{u}} {P : Operations.{w}} {F G : O.Map P}
    (h : ∀ n (t : O.Op n), F.map t = G.map t) : F = G := by
  cases F; cases G
  congr
  funext n t
  exact h n t
end Map
variable {O : Operations.{u}} {T : Theory.{v,w}} (F : Hom O.theory T)

def mappedPowerLimit (n : Nat) : IsLimit (Fan.mk (F.toFunctor.obj ⟨n⟩)
    (fun i : Fin n => F.toFunctor.map (fun _ : Fin 1 => O.var i) ≫ F.generatorIso.hom)) := by
  let h := (isLimitMapConeFanMkEquiv F.toFunctor _ _)
    (isLimitOfPreserves F.toFunctor (O.powerLimit n))
  refine Fan.IsLimit.mk (Fan.mk (F.toFunctor.obj ⟨n⟩)
    (fun i : Fin n => F.toFunctor.map (fun _ : Fin 1 => O.var i) ≫ F.generatorIso.hom))
    (fun s => h.lift (Fan.mk s.pt (fun i => s.proj i ≫ F.generatorIso.inv))) ?_ ?_
  · intro s i
    have hf := h.fac (Fan.mk s.pt (fun i => s.proj i ≫ F.generatorIso.inv)) ⟨i⟩
    have hg := congrArg (fun k => k ≫ F.generatorIso.hom) hf
    change (h.lift (Fan.mk s.pt (fun i => s.proj i ≫ F.generatorIso.inv)) ≫
      F.toFunctor.map (fun _ : Fin 1 => O.var i)) ≫ F.generatorIso.hom =
        (s.proj i ≫ F.generatorIso.inv) ≫ F.generatorIso.hom at hg
    dsimp only [Fan.mk, Fan.proj, Discrete.natTrans] at hg ⊢
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hg
  · intro s m hm
    apply h.hom_ext
    intro i
    rw [h.fac]
    apply (cancel_mono F.generatorIso.hom).mp
    simpa using hm i.as

def powerComparison (n : Nat) : F.toFunctor.obj ⟨n⟩ ≅ T.power n :=
  (mappedPowerLimit F n).conePointUniqueUpToIso (limit.isLimit _)

@[reassoc (attr := simp)] theorem powerComparison_hom_π (n : Nat) (i : Fin n) :
    (powerComparison F n).hom ≫ Pi.π _ i =
      F.toFunctor.map (fun _ : Fin 1 => O.var i) ≫ F.generatorIso.hom :=
  (mappedPowerLimit F n).conePointUniqueUpToIso_hom_comp (limit.isLimit _) ⟨i⟩

@[reassoc (attr := simp)] theorem powerComparison_inv_projection (n : Nat) (i : Fin n) :
    (powerComparison F n).inv ≫ F.toFunctor.map (fun _ : Fin 1 => O.var i) ≫
      F.generatorIso.hom = Pi.π _ i := by
  rw [← powerComparison_hom_π, Iso.inv_hom_id_assoc]

def operationMap : O.Map T.operations where
  map {n} t := (powerComparison F n).inv ≫ F.toFunctor.map (fun _ : Fin 1 => t) ≫ F.generatorIso.hom
  map_var i := powerComparison_inv_projection F _ i
  map_subst {m n} t σ := by
    change (powerComparison F m).inv ≫ F.toFunctor.map (_ ≫ _) ≫ _ = _
    rw [F.toFunctor.map_comp]
    have h : Pi.lift (fun i => (powerComparison F m).inv ≫
        F.toFunctor.map (fun _ : Fin 1 => σ i) ≫ F.generatorIso.hom) =
        (powerComparison F m).inv ≫ F.toFunctor.map σ ≫ (powerComparison F n).hom := by
      apply Pi.hom_ext
      intro i
      simp only [Pi.lift_comp_π, Category.assoc, powerComparison_hom_π,
        ← F.toFunctor.map_comp_assoc]
      congr 2
      exact congrArg F.toFunctor.map (funext fun _ => O.var_subst i σ).symm
    change _ = Pi.lift _ ≫ _
    rw [h]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- A categorical interpretation is naturally isomorphic to its normalized operation map. -/
def normalizationIso : F.toFunctor ≅ (operationMap F).toFunctor ⋙ T.skeletonFunctor :=
  NatIso.ofComponents (fun X => powerComparison F X.size) (by
    intro X Y f
    apply Pi.hom_ext
    intro i
    simp only [Functor.comp_map, Map.toFunctor, Theory.skeletonFunctor,
      Category.assoc, Pi.lift_comp_π, powerComparison_hom_π]
    change _ = (powerComparison F X.size).hom ≫ (powerComparison F X.size).inv ≫ _
    rw [Iso.hom_inv_id_assoc, ← F.toFunctor.map_comp_assoc]
    congr 2
    exact funext fun _ => O.var_subst i f)

/-- The normalization respects the supplied comparison at the generator. -/
theorem normalization_generator :
    (normalizationIso F).hom.app ⟨1⟩ ≫ T.generatorIso.hom = F.generatorIso.hom := by
  change (powerComparison F 1).hom ≫ Pi.π _ 0 = _
  rw [powerComparison_hom_π]
  have h : (fun _ : Fin 1 => O.var (0 : Fin 1)) = (𝟙 (⟨1⟩ : O.Context)) := by
    funext i
    exact congrArg O.var (Fin.eq_zero i).symm
  rw [h, F.toFunctor.map_id, Category.id_comp]

variable (φ : O.Map T.operations)

@[simp] theorem canonical_generator :
    (Hom.comp φ.theoryHom T.skeletonHom).generatorIso.hom = T.generatorIso.hom := by
  change T.skeletonFunctor.map (𝟙 _) ≫ T.generatorIso.hom = _
  rw [T.skeletonFunctor.map_id, Category.id_comp]

theorem canonical_powerComparison (n : Nat) :
    powerComparison (Hom.comp φ.theoryHom T.skeletonHom) n = Iso.refl (T.power n) := by
  apply Iso.ext
  apply Pi.hom_ext
  intro i
  rw [powerComparison_hom_π, canonical_generator]
  change Pi.lift (fun _ : Fin 1 => φ.map (O.var i)) ≫ Pi.π _ 0 = _
  rw [Pi.lift_comp_π, φ.map_var]
  change Pi.π _ i = 𝟙 _ ≫ Pi.π _ i
  simp

@[simp] theorem operationMap_canonical :
    operationMap (Hom.comp φ.theoryHom T.skeletonHom) = φ := by
  apply Map.ext
  intro n t
  change (powerComparison _ n).inv ≫ _ ≫ _ = _
  rw [canonical_powerComparison, canonical_generator]
  change (𝟙 _) ≫ Pi.lift (fun _ : Fin 1 => φ.map t) ≫ Pi.π _ 0 = φ.map t
  simp

end Operations
end SquareKit.Lawvere
