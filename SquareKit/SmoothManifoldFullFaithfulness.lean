import SquareKit.SmoothChartReconstruction
import SquareKit.SmoothManifoldPrincipalMaps

/-! Full faithfulness for Type-sized, finite-dimensional real boundaryless
Mathlib manifolds. Neither separation nor countability is assumed. -/
noncomputable section
open CategoryTheory
open scoped Manifold ContDiff
namespace SquareKit.ManifoldRealization
variable {n m p : ℕ} {M N P : Type}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
    [ChartedSpace (Space n) M] [ChartedSpace (Space m) N] [ChartedSpace (Space p) P]

namespace ChartFamily
variable (A : ChartFamily n M) (B : ChartFamily m N) (C : ChartFamily p P)

/-- The underlying function is extracted from the arrow's action at the real
stage using the proved point/section equivalence. -/
def reconstruct (h : A.realization ⟶ B.realization) : M → N :=
  A.charts.realMap B.charts A.atlas.covers B.atlas.covers h

theorem reconstruct_smooth (h : A.realization ⟶ B.realization) :
    ContMDiff (Model n) (Model m) ∞ (A.reconstruct B h) :=
  A.contMDiff_of_localMap B
    (A.charts.reconstructLocalMap B.charts A.atlas.covers B.atlas.covers h)

theorem reconstruct_interpret (f : M → N) (hf : ContMDiff (Model n) (Model m) ∞ f) :
    A.reconstruct B (A.interpret B f hf) = f :=
  A.charts.realMap_realize B.charts A.atlas.covers B.atlas.covers (A.localMap B f hf)

/-- The inverse law is equality of sheaf arrows at all stages. -/
theorem interpret_reconstruct (h : A.realization ⟶ B.realization) :
    A.interpret B (A.reconstruct B h) (A.reconstruct_smooth B h) = h :=
  (A.interpret_choice B _ _
    (A.charts.reconstructLocalMap B.charts A.atlas.covers B.atlas.covers h)).trans
      (A.charts.reconstruct_realize B.charts A.atlas.covers B.atlas.covers h)

def homEquiv :
    {f : M → N // ContMDiff (Model n) (Model m) ∞ f} ≃ (A.realization ⟶ B.realization) where
  toFun f := A.interpret B f.val f.property
  invFun h := ⟨A.reconstruct B h, A.reconstruct_smooth B h⟩
  left_inv f := Subtype.ext (A.reconstruct_interpret B f.val f.property)
  right_inv h := A.interpret_reconstruct B h

theorem reconstruct_id : A.reconstruct A (𝟙 A.realization) = id := by
  rw [← A.interpret_id]
  exact A.reconstruct_interpret A id contMDiff_id

theorem reconstruct_comp (h : A.realization ⟶ B.realization) (k : B.realization ⟶ C.realization) :
    A.reconstruct C (h ≫ k) = B.reconstruct C k ∘ A.reconstruct B h := by
  conv_lhs => rw [← A.interpret_reconstruct B h, ← B.interpret_reconstruct C k,
    ← A.interpret_comp B C]
  exact A.reconstruct_interpret C _ _

theorem reconstruct_comparison (A' : ChartFamily n M) (B' : ChartFamily m N)
    (h : A.realization ⟶ B.realization) :
    A'.reconstruct B' ((A.comparison A').inv ≫ h ≫ (B.comparison B').hom) =
      A.reconstruct B h := by
  have hn := A.comparison_naturality B A' B' (A.reconstruct B h) (A.reconstruct_smooth B h)
  rw [A.interpret_reconstruct B h] at hn
  have he : (A.comparison A').inv ≫ h ≫ (B.comparison B').hom =
      A'.interpret B' (A.reconstruct B h) (A.reconstruct_smooth B h) := by
    rw [← hn, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  rw [he]
  exact A'.reconstruct_interpret B' _ _

end ChartFamily

variable [IsManifold (Model n) ∞ M] [IsManifold (Model m) ∞ N] [IsManifold (Model p) ∞ P]

def reconstruct (h : object n M ⟶ object m N) : M → N :=
  ChartFamily.reconstruct .preferred .preferred h

theorem reconstruct_smooth (h : object n M ⟶ object m N) :
    ContMDiff (Model n) (Model m) ∞ (reconstruct h) :=
  ChartFamily.reconstruct_smooth .preferred .preferred h

def homEquiv : {f : M → N // ContMDiff (Model n) (Model m) ∞ f} ≃ (object n M ⟶ object m N) :=
  ChartFamily.homEquiv .preferred .preferred

theorem homEquiv_apply (f : {f : M → N // ContMDiff (Model n) (Model m) ∞ f}) :
    homEquiv f = map f.val f.property := rfl

theorem reconstruct_map (f : M → N) (hf : ContMDiff (Model n) (Model m) ∞ f) :
    reconstruct (map f hf) = f :=
  ChartFamily.reconstruct_interpret .preferred .preferred f hf

theorem map_reconstruct (h : object n M ⟶ object m N) :
    map (reconstruct h) (reconstruct_smooth h) = h :=
  ChartFamily.interpret_reconstruct .preferred .preferred h

theorem map_injective {f g : M → N}
    (hf : ContMDiff (Model n) (Model m) ∞ f) (hg : ContMDiff (Model n) (Model m) ∞ g)
    (h : map f hf = map g hg) : f = g :=
  (reconstruct_map f hf).symm.trans ((congrArg reconstruct h).trans (reconstruct_map g hg))

theorem reconstruct_id : reconstruct (𝟙 (object n M)) = id :=
  ChartFamily.reconstruct_id .preferred

theorem reconstruct_comp (h : object n M ⟶ object m N) (k : object m N ⟶ object p P) :
    reconstruct (h ≫ k) = reconstruct k ∘ reconstruct h :=
  ChartFamily.reconstruct_comp .preferred .preferred .preferred h k

theorem reconstruct_atlas (A : ChartFamily n M) (B : ChartFamily m N)
    (h : object n M ⟶ object m N) :
    A.reconstruct B ((atlasIso A).inv ≫ h ≫ (atlasIso B).hom) = reconstruct h :=
  ChartFamily.reconstruct_comparison .preferred .preferred A B h

theorem homEquiv_principal (U V : EuclideanOpen.Domain) :
    (homEquiv (n := U.dimension) (M := ordinaryOpen U) (m := V.dimension) (N := ordinaryOpen V)) =
      principalHomEquiv U V := by
  apply Equiv.ext
  intro f
  exact (principalHomEquiv_apply U V f).symm

end SquareKit.ManifoldRealization
