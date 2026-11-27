import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
import Mathlib.CategoryTheory.FiberedCategory.Cartesian

/-! Cartesian preservation can be checked on any chosen lift of a base arrow. -/
set_option autoImplicit false

namespace CategoryTheory.BasedFunctor
open CategoryTheory.Functor

universe u v a b c d
variable {S : Type u} [Category.{v} S]
variable {X : BasedCategory.{b,a} S} {Y : BasedCategory.{d,c} S}

/-- If a based functor preserves one cartesian lift, it preserves every cartesian
lift of the same base arrow with the same codomain. -/
theorem map_isCartesian_of_map_isCartesian (T : BasedFunctor X Y)
    {r s : S} (f : r ⟶ s) {x x' y : X.obj} (φ : x ⟶ y) (ψ : x' ⟶ y)
    [hφ : X.p.IsCartesian f φ] [hψ : X.p.IsCartesian f ψ]
    [hT : Y.p.IsCartesian f (T.map φ)] : Y.p.IsCartesian f (T.map ψ) := by
  let e := IsCartesian.domainUniqueUpToIso X.p f φ ψ
  have he : e.hom ≫ φ = ψ := IsCartesian.fac X.p f φ ψ
  have : X.p.IsHomLift (𝟙 r) e.hom := inferInstance
  have : Y.p.IsHomLift (𝟙 r) (T.toFunctor.mapIso e).hom :=
    preserves_isHomLift T (𝟙 r) e.hom
  have h := IsCartesian.of_iso_comp Y.p f (T.map φ) (T.toFunctor.mapIso e)
  simpa only [Functor.mapIso_hom, ← T.toFunctor.map_comp, he] using h

end CategoryTheory.BasedFunctor
