import SquareKit.SmoothRepresentedCover
import SquareKit.SmoothCechRefinement

/-! Represented Čech geometry derived from an ordinary principal-open cover.
All pullbacks are in sheaves on the full finite-presentation site. -/
noncomputable section
namespace SquareKit.EuclideanOpen.PrincipalAtlas
open CategoryTheory CategoryTheory.Limits Opposite SmoothAlgebra SmoothOpenSite

variable (U : Domain)

def left (f g : freeAlgebra U.dimension) : subdomain U (f * g) ⟶ subdomain U f :=
  domainInclusion _ _ (fun _ h => mul_ne_zero (left_ne_zero_of_mul h)
    (left_ne_zero_of_mul (right_ne_zero_of_mul h)))

def right (f g : freeAlgebra U.dimension) : subdomain U (f * g) ⟶ subdomain U g :=
  domainInclusion _ _ (fun _ h => mul_ne_zero (left_ne_zero_of_mul h)
    (right_ne_zero_of_mul (right_ne_zero_of_mul h)))

theorem square (f g : freeAlgebra U.dimension) :
    IsPullback (embedding.map (left U f g)) (embedding.map (right U f g))
      (embedding.map (subInclusion U f)) (embedding.map (subInclusion U g)) := by
  let e : overlap U f g ≅ subdomain U (f * g) :=
    { hom := domainInclusion _ _ (fun x h => by simpa only [subdomain, mul_assoc] using h)
      inv := domainInclusion _ _ (fun x h => by simpa only [subdomain, mul_assoc] using h)
      hom_inv_id := OpenFunctions.Map.ext (fun _ => rfl)
      inv_hom_id := OpenFunctions.Map.ext (fun _ => rfl) }
  apply (overlap_sheaf_pullback U f g).of_iso (embedding.mapIso e)
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp only [Functor.mapIso_hom, Iso.refl_hom, Category.comp_id]
    rw [← Functor.map_comp]
    exact congrArg embedding.map (OpenFunctions.Map.ext (fun _ => rfl))
  · simp only [Functor.mapIso_hom, Iso.refl_hom, Category.comp_id]
    rw [← Functor.map_comp]
    exact congrArg embedding.map (OpenFunctions.Map.ext (fun _ => rfl))
  · simp
  · simp

theorem covering {I : Type} (f : I → freeAlgebra U.dimension) (hf : Covers U f)
    (V : SmoothPresentationSite.Site) (x : (embedding.obj U).obj.obj (op V)) :
    SheafCoproductLocal.liftSieve (fun i => embedding.obj (subdomain U (f i)))
      (fun i => embedding.map (subInclusion U (f i))) x ∈ topology V := by
  apply topology.superset_covering _ (topology.pullback_stable x (EuclideanOpen.covering U f hf))
  intro W r hr
  rcases hr with ⟨Z, t, a, ⟨i⟩, he⟩
  exact ⟨i, t, he⟩

/-- The atlas is constructed from functions and ordinary pointwise coverage;
neither intersections nor sheaf covering witnesses are caller inputs. -/
def atlas {I : Type} (f : I → freeAlgebra U.dimension) (hf : Covers U f) :
    SmoothRepresentedCover.Atlas (embedding.obj U) I where
  domain i := subdomain U (f i)
  chart i := embedding.map (subInclusion U (f i))
  covering := covering U f hf
  pair i j := subdomain U (f i * f j)
  left i j := left U (f i) (f j)
  right i j := right U (f i) (f j)
  square i j := square U (f i) (f j)
  triple i j k := subdomain U ((f i * f j) * f k)
  firstSecond i j k := left U (f i * f j) (f k)
  third i j k := right U (f i * f j) (f k)
  tripleSquare i j k := by
    have h : left U (f i) (f j) ≫ subInclusion U (f i) =
        subInclusion U (f i * f j) := OpenFunctions.Map.ext (fun _ => rfl)
    rw [← Functor.map_comp, h]
    exact square U (f i * f j) (f k)

def commonFunctions {I J : Type} (f : I → freeAlgebra U.dimension) (g : J → freeAlgebra U.dimension)
    (ij : I × J) : freeAlgebra U.dimension := f ij.1 * g ij.2

theorem common_covers {I J : Type} (f : I → freeAlgebra U.dimension) (g : J → freeAlgebra U.dimension)
    (hf : Covers U f) (hg : Covers U g) : Covers U (commonFunctions U f g) := by
  intro x
  obtain ⟨i, hi⟩ := hf x
  obtain ⟨j, hj⟩ := hg x
  exact ⟨(i,j), mul_ne_zero hi hj⟩

def commonLeft {I J : Type} (f : I → freeAlgebra U.dimension) (g : J → freeAlgebra U.dimension)
    (hf : Covers U f) (hg : Covers U g) :
    SmoothRepresentedCover.AtlasMap (atlas U f hf)
      (atlas U (commonFunctions U f g) (common_covers U f g hf hg)) (𝟙 _) where
  index := Prod.fst
  chart ij := left U (f ij.1) (g ij.2)
  commutes ij := by
    simp only [Category.comp_id]
    dsimp only [atlas, commonFunctions]
    rw [← Functor.map_comp]
    exact congrArg embedding.map (OpenFunctions.Map.ext (fun _ => rfl))

def commonRight {I J : Type} (f : I → freeAlgebra U.dimension) (g : J → freeAlgebra U.dimension)
    (hf : Covers U f) (hg : Covers U g) :
    SmoothRepresentedCover.AtlasMap (atlas U g hg)
      (atlas U (commonFunctions U f g) (common_covers U f g hf hg)) (𝟙 _) where
  index := Prod.snd
  chart ij := right U (f ij.1) (g ij.2)
  commutes ij := by
    simp only [Category.comp_id]
    dsimp only [atlas, commonFunctions]
    rw [← Functor.map_comp]
    exact congrArg embedding.map (OpenFunctions.Map.ext (fun _ => rfl))

end SquareKit.EuclideanOpen.PrincipalAtlas
