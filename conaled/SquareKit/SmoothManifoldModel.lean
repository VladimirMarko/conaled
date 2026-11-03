import SquareKit.SmoothManifoldRefinement

/-! Experimental interpretation of Mathlib smooth manifolds and all smooth maps.
The indexed construction admits different finite dimensions in each argument. -/
noncomputable section
open CategoryTheory
open scoped Manifold ContDiff
namespace SquareKit.ManifoldRealization
variable (n : ℕ) (M : Type) [TopologicalSpace M] [ChartedSpace (Space n) M]
    [IsManifold (Model n) ∞ M]

/-- The sheaf assigned to the actual preferred Mathlib atlas. -/
abbrev object : Sheaf SmoothOpenSite.topology (Type) :=
  (ChartFamily.preferred (n := n) (M := M)).realization

variable {n M} {m p : ℕ} {N P : Type}
    [TopologicalSpace N] [TopologicalSpace P]
    [ChartedSpace (Space m) N] [ChartedSpace (Space p) P]
    [IsManifold (Model m) ∞ N] [IsManifold (Model p) ∞ P]

def map (f : M → N) (hf : ContMDiff (Model n) (Model m) ∞ f) : object n M ⟶ object m N :=
  ChartFamily.interpret _ _ f hf

theorem map_id : map (id : M → M) contMDiff_id = 𝟙 (object n M) :=
  ChartFamily.interpret_id _

theorem map_comp (f : M → N) (g : N → P)
    (hf : ContMDiff (Model n) (Model m) ∞ f) (hg : ContMDiff (Model m) (Model p) ∞ g) :
    map (g ∘ f) (hg.comp hf) = map f hf ≫ map g hg :=
  ChartFamily.interpret_comp _ _ _ f g hf hg

/-- Any covering family of smooth manifold charts gives the same object. -/
def atlasIso (A : ChartFamily n M) : object n M ≅ A.realization :=
  ChartFamily.comparison _ A

theorem atlas_naturality (A : ChartFamily n M) (B : ChartFamily m N)
    (f : M → N) (hf : ContMDiff (Model n) (Model m) ∞ f) :
    (atlasIso A).hom ≫ A.interpret B f hf = map f hf ≫ (atlasIso B).hom :=
  ChartFamily.comparison_naturality _ _ A B f hf

theorem atlas_common (A : ChartFamily n M) : atlasIso A =
    EuclideanOpen.Charts.commonRefinementIso
      ((ChartFamily.preferred (n := n) (M := M)).commonLeft A)
      ((ChartFamily.preferred (n := n) (M := M)).commonRight A) :=
  ChartFamily.comparison_common _ A

end SquareKit.ManifoldRealization
