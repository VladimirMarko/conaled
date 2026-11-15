import Mathlib.CategoryTheory.Action
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Topology.Maps.Proper.Basic

/-! External action presentations. Finite discrete labels give proper étale
presentations on arbitrary Hausdorff smooth manifolds, including noncompact
manifolds and ineffective actions. Properness is Mathlib's `IsProperMap`;
no internal properness predicate or quotient comparison is asserted. -/
noncomputable section
open CategoryTheory
open scoped Manifold ContDiff
namespace Orbifolds.FiniteActionPresentation

abbrev Arrow (G M : Type*) := G × M

variable {G M : Type*} [Group G] [MulAction G M]

def source (a : Arrow G M) : M := a.2
def target (a : Arrow G M) : M := a.1 • a.2
def unit (x : M) : Arrow G M := (1, x)
def inverse (a : Arrow G M) : Arrow G M := (a.1⁻¹, target a)
/-- Coordinates on the composable pairs: `g`, then `h`, based at `x`. -/
def compose (g h : G) (x : M) : Arrow G M := (h * g, x)
def anchor (a : Arrow G M) : M × M := (source a, target a)

omit [MulAction G M] in
@[simp] theorem source_unit (x : M) : source (unit (G := G) x) = x := rfl
@[simp] theorem target_unit (x : M) : target (unit (G := G) x) = x := one_smul _ _
@[simp] theorem source_inverse (a : Arrow G M) : source (inverse a) = target a := rfl
@[simp] theorem target_inverse (a : Arrow G M) : target (inverse a) = source a := inv_smul_smul _ _
@[simp] theorem inverse_inverse (a : Arrow G M) : inverse (inverse a) = a := by
  ext <;> simp [inverse, target]
theorem target_compose (g h : G) (x : M) :
    target (compose g h x) = h • (g • x) := mul_smul _ _ _

/-- These coordinates identify exactly the composable pairs, including their labels. -/
def composableEquiv : (G × G) × M ≃
    {p : Arrow G M × Arrow G M // target p.1 = source p.2} where
  toFun p := ⟨((p.1.1, p.2), (p.1.2, p.1.1 • p.2)), rfl⟩
  invFun p := ((p.val.1.1, p.val.2.1), p.val.1.2)
  left_inv _ := rfl
  right_inv p := by
    apply Subtype.ext
    exact Prod.ext rfl (Prod.ext rfl p.property)

/-- Coordinate arrows are the arrows of Mathlib's existing action groupoid. -/
def asHom (a : Arrow G M) :
    (show CategoryTheory.ActionCategory G M from (source a : M)) ⟶
      (show CategoryTheory.ActionCategory G M from (target a : M)) :=
  CategoryTheory.Functor.Elements.homMk a.1 rfl

/-- Every categorical arrow has these coordinates, with its source remembered. -/
def ofHom {x y : ActionCategory G M} (f : x ⟶ y) : Arrow G M := (f.hom, x.back)

@[simp] theorem ofHom_ident (x : ActionCategory G M) : ofHom (𝟙 x) = unit x.back := rfl

theorem ofHom_comp {x y z : ActionCategory G M} (f : x ⟶ y) (g : y ⟶ z) :
    ofHom (f ≫ g) = compose f.hom g.hom x.back := rfl

theorem ofHom_inverse {x y : ActionCategory G M} (f : x ⟶ y) :
    ofHom (Groupoid.inv f) = inverse (ofHom f) := by
  change ((show G from f.hom)⁻¹, y.back) = ((show G from f.hom)⁻¹, (show G from f.hom) • x.back)
  exact Prod.ext rfl f.map_val.symm

/-- The fiber of the geometric anchor is the existing category's hom type. -/
def homEquiv (x y : M) :
    ((show ActionCategory G M from x) ⟶ (show ActionCategory G M from y)) ≃
      {a : Arrow G M // source a = x ∧ target a = y} where
  toFun f := ⟨ofHom f, rfl, f.map_val⟩
  invFun a := Functor.Elements.homMk a.val.1 (by
    change a.val.1 • x = y
    exact (congrArg (fun z => a.val.1 • z) a.property.1.symm).trans a.property.2)
  left_inv _ := Functor.Elements.Hom.ext rfl
  right_inv a := by
    apply Subtype.ext
    exact Prod.ext rfl a.property.1.symm

section Topology
variable [TopologicalSpace G] [TopologicalSpace M] [T2Space M]

/-- Compact labels suffice: no discreteness, finiteness, or manifold hypothesis
is used for this topological theorem. -/
theorem anchor_proper_of_compact [CompactSpace G]
    (continuousAction : Continuous (fun a : G × M => a.1 • a.2)) :
    IsProperMap (anchor (G := G) (M := M)) := by
  apply isProperMap_of_comp_of_t2
    (continuous_snd.prodMk continuousAction) continuous_fst
  exact isProperMap_snd_of_compactSpace
end Topology

section Smooth
variable [TopologicalSpace G] [DiscreteTopology G]
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
variable [TopologicalSpace M] [ChartedSpace H M]

scoped instance labelCharts : ChartedSpace (Fin 0 → ℝ) G :=
  ChartedSpace.ofDiscreteTopology
scoped instance labelManifold : IsManifold 𝓘(ℝ, Fin 0 → ℝ) ∞ G :=
  IsManifold.of_discreteTopology ∞

abbrev arrowModel := (𝓘(ℝ, Fin 0 → ℝ)).prod I

/-- Every fixed-label component has the whole base as its source image. -/
def sourceChart (g : G) : PartialDiffeomorph (arrowModel I) I (Arrow G M) M ∞ where
  toFun := source
  invFun x := (g, x)
  source := {a | a.1 = g}
  target := Set.univ
  map_source' _ _ := Set.mem_univ _
  map_target' _ _ := rfl
  left_inv' _a ha := Prod.ext ha.symm rfl
  right_inv' _ _ := rfl
  open_source := (isOpen_discrete {g}).preimage continuous_fst
  open_target := isOpen_univ
  contMDiffOn_toFun := contMDiff_snd.contMDiffOn
  contMDiffOn_invFun := (contMDiff_const.prodMk contMDiff_id).contMDiffOn

/-- Every label acts by a diffeomorphism; smoothness of inverse labels supplies its inverse. -/
def actionDiffeomorph
    (smoothAction : ∀ g : G, ContMDiff I I ∞ (fun x : M => g • x)) (g : G) :
    Diffeomorph I I M M ∞ where
  toFun x := g • x
  invFun x := g⁻¹ • x
  left_inv := inv_smul_smul g
  right_inv := smul_inv_smul g
  contMDiff_toFun := smoothAction g
  contMDiff_invFun := smoothAction g⁻¹

/-- The target chart on the component `g` applies the action to the source chart. -/
def targetChart
    (smoothAction : ∀ g : G, ContMDiff I I ∞ (fun x : M => g • x)) (g : G) : PartialDiffeomorph (arrowModel I) I (Arrow G M) M ∞ :=
  (sourceChart I g).trans (actionDiffeomorph I smoothAction g).toPartialDiffeomorph

omit [Group G] [MulAction G M] in
theorem source_etale : IsLocalDiffeomorph (arrowModel I) I ∞ (source (G := G) (M := M)) := by
  intro a
  exact ⟨sourceChart I a.1, rfl, fun _ _ => rfl⟩

theorem target_etale
    (smoothAction : ∀ g : G, ContMDiff I I ∞ (fun x : M => g • x)) :
    IsLocalDiffeomorph (arrowModel I) I ∞ (target (G := G) (M := M)) := by
  intro a
  refine ⟨targetChart I smoothAction a.1, ⟨rfl, Set.mem_univ _⟩, ?_⟩
  intro b hb
  change b.1 • b.2 = a.1 • b.2
  rw [hb.1]

omit [MulAction G M] in
theorem unit_smooth : ContMDiff I (arrowModel I) ∞ (unit (G := G) (M := M)) :=
  contMDiff_const.prodMk contMDiff_id

theorem inverse_smooth
    (smoothAction : ∀ g : G, ContMDiff I I ∞ (fun x : M => g • x)) :
    ContMDiff (arrowModel I) (arrowModel I) ∞ (inverse (G := G) (M := M)) :=
  ((contMDiff_of_discreteTopology (I := 𝓘(ℝ, Fin 0 → ℝ))
    (I' := 𝓘(ℝ, Fin 0 → ℝ)) (f := fun g : G => g⁻¹)).comp
    contMDiff_fst).prodMk (target_etale I smoothAction).contMDiff

omit [MulAction G M] in
/-- Composition is smooth in the coordinates `(g,h,x)` on composable pairs. -/
theorem compose_smooth :
    ContMDiff (((𝓘(ℝ, Fin 0 → ℝ)).prod 𝓘(ℝ, Fin 0 → ℝ)).prod I)
      (arrowModel I) ∞ (fun p : (G × G) × M => compose p.1.1 p.1.2 p.2) :=
  ((contMDiff_of_discreteTopology
    (I := (𝓘(ℝ, Fin 0 → ℝ)).prod 𝓘(ℝ, Fin 0 → ℝ))
    (I' := 𝓘(ℝ, Fin 0 → ℝ)) (f := fun p : G × G => p.2 * p.1)).comp
    contMDiff_fst).prodMk contMDiff_snd

/-- Finite-action specialization with explicit finite data. Neither compactness
of the base, effectiveness, nor anchor injectivity is required. -/
theorem proper_etale
    (smoothAction : ∀ g : G, ContMDiff I I ∞ (fun x : M => g • x))
    [Fintype G] [DecidableEq G] [T2Space M]
    [IsManifold I ∞ M] [SecondCountableTopology M] :
    IsProperMap (anchor (G := G) (M := M)) ∧
    IsLocalDiffeomorph (arrowModel I) I ∞ (source (G := G) (M := M)) ∧
    IsLocalDiffeomorph (arrowModel I) I ∞ (target (G := G) (M := M)) :=
  ⟨anchor_proper_of_compact (target_etale I smoothAction).contMDiff.continuous,
    source_etale I, target_etale I smoothAction⟩
end Smooth
end Orbifolds.FiniteActionPresentation
