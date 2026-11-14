import SquareKit.Internal.Cubical.NativeUnivalence
import SquareKit.Internal.Cubical.NativePathComposition

/-! Native two-path substitution and its actual code-valued square. The inner
path-family reindexing is explicit before evaluating the second interval. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u
variable {Γ Δ Θ : Context.{u+1}} {a b : Γ ⟶ smallFamilyCodes.{u}}
  {p q : Term (paths a b)}

def nativePathReindex (a b : Γ ⟶ smallFamilyCodes.{u}) (σ : Δ ⟶ Γ) :
    reindex (paths a b) σ ⟶ paths (σ ≫ a) (σ ≫ b) :=
  pathReindex (reindex (family Γ) (projection (interval Γ))) (term a) (term b) σ

/-- Substitute a native two-path using the actual inner path-family map. -/
def reindexComparison (H : Term (homogeneousPath (paths a b) p q)) (σ : Δ ⟶ Γ) :
    Term (homogeneousPath (paths (σ ≫ a) (σ ≫ b)) (reindexPath p σ) (reindexPath q σ)) :=
  homogeneousPathMap (nativePathReindex a b σ) (homogeneousReindex H σ)

theorem reindexComparison_comp (H : Term (homogeneousPath (paths a b) p q))
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    reindexComparison (reindexComparison H σ) τ = reindexComparison H (τ ≫ σ) := rfl

/-- The square retains both interval coordinates and the actual code values. -/
def comparisonSquare (H : Term (homogeneousPath (paths a b) p q)) :
    Term (family (total (interval (total (interval Γ))))) :=
  pathApp (Term.map (nativePathReindex a b (projection (interval Γ))) (pathApp H))

/-- Evaluating both interval coordinates loses no native two-path data. -/
theorem comparisonSquare_injective :
    Function.Injective (comparisonSquare (p := p) (q := q)) := by
  intro H K h
  apply pathApp_injective
  apply Term.map_injective_of_iso (pathReindexIso
    (reindex (family Γ) (projection (interval Γ))) (term a) (term b) (projection (interval Γ)))
  exact pathApp_injective h

theorem comparisonSquare_reindex (H : Term (homogeneousPath (paths a b) p q)) (σ : Δ ⟶ Γ) :
    comparisonSquare (reindexComparison H σ) =
      (comparisonSquare H).reindex
        (liftSub (interval (total (interval Γ))) (liftSub (interval Γ) σ)) := rfl

theorem comparisonSquare_left (H : Term (homogeneousPath (paths a b) p q)) :
    (comparisonSquare H).reindex (endpointSub (total (interval Γ)) false) =
      term (projection (interval Γ) ≫ a) :=
  pathApp_zero (Term.map (nativePathReindex a b (projection (interval Γ))) (pathApp H))

theorem comparisonSquare_right (H : Term (homogeneousPath (paths a b) p q)) :
    (comparisonSquare H).reindex (endpointSub (total (interval Γ)) true) =
      term (projection (interval Γ) ≫ b) :=
  pathApp_one (Term.map (nativePathReindex a b (projection (interval Γ))) (pathApp H))

theorem comparisonSquare_zero (H : Term (homogeneousPath (paths a b) p q)) :
    (comparisonSquare H).reindex
      (liftSub (interval (total (interval Γ))) (endpointSub Γ false)) = pathApp p := by
  exact congrArg pathApp (pathApp_zero H)

theorem comparisonSquare_one (H : Term (homogeneousPath (paths a b) p q)) :
    (comparisonSquare H).reindex
      (liftSub (interval (total (interval Γ))) (endpointSub Γ true)) = pathApp q := by
  exact congrArg pathApp (pathApp_one H)

end SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
