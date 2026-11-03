import SquareKit.SmoothChartRefinement

/-! Experimental independence of chart presentations under ordinary principal
covers and common refinements. All comparison arrows retain their chart maps. -/
noncomputable section
open CategoryTheory SquareKit.SmoothAlgebra
namespace SquareKit.EuclideanOpen.Charts
variable {M : Type} (A : Charts M)

def subdivision (K : A.Index → Type) (g : ∀ i, K i → Free (A.domain i).dimension) : Charts M where
  Index := Σ i, K i
  domain p := subdomain (A.domain p.1) (g p.1 p.2)
  coordinate p x := A.coordinate p.1 ((show EuclideanOpen.Map _ _ from subInclusion _ _) x)

def subdivisionRefinement (K : A.Index → Type) (g : ∀ i, K i → Free (A.domain i).dimension)
    (hc : ∀ i, Covers (A.domain i) (g i)) : Refinement (A.subdivision K g) A where
  map := ⟨id, Sigma.fst, fun _p => subInclusion _ _, fun _ _ => rfl⟩
  point_identity := rfl
  Cover := K
  defining := g
  covers := hc
  index i k := ⟨i,k⟩
  lift _ _ := 𝟙 _
  agreement _ _ _ := rfl

def subdivisionIso (K : A.Index → Type) (g : ∀ i, K i → Free (A.domain i).dimension)
    (hc : ∀ i, Covers (A.domain i) (g i)) : (A.subdivision K g).realization ≅ A.realization :=
  (A.subdivisionRefinement K g hc).iso

theorem subdivision_chart (K : A.Index → Type) (g : ∀ i, K i → Free (A.domain i).dimension)
    (hc : ∀ i, Covers (A.domain i) (g i)) (i : A.Index) (k : K i) :
    (A.subdivision K g).chart ⟨i,k⟩ ≫ (A.subdivisionIso K g hc).hom =
      embedding.map (subInclusion (A.domain i) (g i k)) ≫ A.chart i :=
  Map.chart_realize _ _

variable {A} {B C D : Charts M}

/-- Comparison through a common ordinary refinement. -/
def commonRefinementIso (r : Refinement C A) (s : Refinement C B) :
    A.realization ≅ B.realization := r.iso.symm ≪≫ s.iso

theorem commonRefinement_commutes (r : Refinement C A) (s : Refinement C B) :
    r.map.realize ≫ (commonRefinementIso r s).hom = s.map.realize := by
  change r.iso.hom ≫ (r.iso.inv ≫ s.iso.hom) = s.iso.hom
  simp

theorem commonRefinement_refl (r : Refinement C A) : commonRefinementIso r r = Iso.refl _ := by
  apply Iso.ext
  simp [commonRefinementIso]

theorem commonRefinement_trans (r : Refinement D A) (s : Refinement D B) (t : Refinement D C) :
    commonRefinementIso r s ≪≫ commonRefinementIso s t = commonRefinementIso r t := by
  apply Iso.ext
  simp [commonRefinementIso]

/-- Refinement choices do not change the realized map of an ordinary function. -/
theorem refinement_naturality {N : Type} {E F : Charts N}
    (r : Refinement B A) (s : Refinement F E) (f : Map A E) (g : Map B F)
    (h : f.point = g.point) :
    r.iso.hom ≫ f.realize = g.realize ≫ s.iso.hom := by
  change r.map.realize ≫ f.realize = g.realize ≫ s.map.realize
  rw [← Map.realize_comp, ← Map.realize_comp]
  apply Map.realize_eq
  funext x
  change f.point (r.map.point x) = s.map.point (g.point x)
  rw [r.point_identity, s.point_identity, h]
  rfl

/-- The comparison does not depend on the chosen cover lifts. -/
theorem refinementIso_eq (r s : Refinement B A) : r.iso = s.iso := by
  apply Iso.ext
  exact Map.realize_eq r.map s.map (r.point_identity.trans s.point_identity.symm)

/-- A further common refinement leaves the comparison unchanged. -/
theorem commonRefinement_further (r : Refinement C A) (s : Refinement C B)
    (r' : Refinement D A) (s' : Refinement D B) (t : Refinement D C) :
    commonRefinementIso r s = commonRefinementIso r' s' := by
  have hr : t.map.realize ≫ r.map.realize = r'.map.realize := by
    rw [← Map.realize_comp]
    apply Map.realize_eq
    funext x
    change r.map.point (t.map.point x) = r'.map.point x
    rw [r.point_identity, t.point_identity, r'.point_identity]
    rfl
  have hs : t.map.realize ≫ s.map.realize = s'.map.realize := by
    rw [← Map.realize_comp]
    apply Map.realize_eq
    funext x
    change s.map.point (t.map.point x) = s'.map.point x
    rw [s.point_identity, t.point_identity, s'.point_identity]
    rfl
  apply Iso.ext
  apply (cancel_epi r'.iso.hom).mp
  change r'.map.realize ≫ _ = r'.map.realize ≫ _
  rw [commonRefinement_commutes, ← hr, Category.assoc, commonRefinement_commutes, hs]

end SquareKit.EuclideanOpen.Charts
