import SquareKit.SmoothChartOpenAtlas

/-! Experimental closure of ordinary atlases under principal-cover subdivision. -/
noncomputable section
open CategoryTheory SquareKit.SmoothAlgebra
namespace SquareKit.EuclideanOpen

/-- The smooth coordinate identity for an inclusion of ordinary open domains. -/
def domainInclusion {n : ℕ} (f g : Free n) (h : Localization.locus f ⊆ Localization.locus g) :
    (⟨n,f⟩ : Domain) ⟶ (⟨n,g⟩ : Domain) where
  toFun x := ⟨x.val,h x.property⟩
  smooth i := (OpenFunctions.representative_iff _ (fun x => x i) (fun _ => rfl)).mpr
    (contDiff_apply ℝ (fun _ : Fin n => ℝ) i).contDiffOn

namespace Atlas
variable {M : Type} [TopologicalSpace M] (A : Atlas M)
    (K : A.Index → Type) (g : ∀ i, K i → Free (A.domain i).dimension)
    (hc : ∀ i, Covers (A.domain i) (g i))

def subdivision : Atlas M where
  toCharts := A.toCharts.subdivision K g
  openEmbedding p := (A.openEmbedding p.1).comp (subInclusion_openEmbedding _ _)
  covers x := by
    obtain ⟨i,y,hy⟩ := A.covers x
    obtain ⟨k,hk⟩ := hc i y
    exact ⟨⟨i,k⟩,localPoint _ (g i) y hk,hy⟩
  transition p q x y he := by
    let xi : Points (A.domain p.1) := (show Map _ _ from subInclusion _ _) x
    let yj : Points (A.domain q.1) := (show Map _ _ from subInclusion _ _) y
    obtain ⟨s,hs,t,ht⟩ := A.transition p.1 q.1 xi yj he
    let z : Points (subdomain (A.domain p.1) s) := ⟨x.val,mul_ne_zero xi.property hs⟩
    have hz : (show Map _ _ from t) z = yj :=
      (A.openEmbedding q.1).injective ((ht z).symm.trans he)
    let v := inverseDefining t (g q.1 q.2)
    have hv : v.val x.val ≠ 0 := by
      apply (inverseDefining_iff t (g q.1 q.2) z).mpr
      rw [hz]
      exact right_ne_zero_of_mul y.property
    let D := subdomain (subdomain (A.domain p.1) (g p.1 p.2)) (s*v)
    let inc : D ⟶ subdomain (subdomain (A.domain p.1) s) v :=
      domainInclusion _ _ (fun w hw =>
        mul_ne_zero (mul_ne_zero (left_ne_zero_of_mul (left_ne_zero_of_mul hw))
          (left_ne_zero_of_mul (right_ne_zero_of_mul hw)))
          (right_ne_zero_of_mul (right_ne_zero_of_mul hw)))
    refine ⟨s*v,mul_ne_zero hs hv,inc ≫ inverseRestriction t (g q.1 q.2),?_⟩
    intro w
    exact ht ⟨w.val,mul_ne_zero (left_ne_zero_of_mul (left_ne_zero_of_mul w.property))
      (left_ne_zero_of_mul (right_ne_zero_of_mul w.property))⟩

end Atlas
end SquareKit.EuclideanOpen
