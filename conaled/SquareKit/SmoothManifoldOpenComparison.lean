import SquareKit.SmoothManifoldModel

/-! Experimental comparison between the Mathlib open-submanifold interpretation
and the existing principal-open embedding, including empty open domains. -/
noncomputable section
open CategoryTheory Set
open scoped Manifold ContDiff
namespace SquareKit.ManifoldRealization
open EuclideanOpen SmoothAlgebra

abbrev ordinaryOpen (U : Domain) : TopologicalSpace.Opens (Space U.dimension) :=
  ⟨Points U,domain_open U⟩

theorem open_chart_target (U : Domain) (i : ordinaryOpen U) :
    (chartAt (Space U.dimension) i).target = Points U := by
  simp [TopologicalSpace.Opens.chartAt_eq,chartAt_self_eq,OpenPartialHomeomorph.subtypeRestr]

theorem open_chart_value (U : Domain) (i : ordinaryOpen U)
    (x : Points (chartDomain (chartAt (Space U.dimension) i))) :
    (chartPoint (chartAt (Space U.dimension) i) x).val = x.val := by
  have hx : x.val ∈ (chartAt (Space U.dimension) i).target := by
    exact (Set.ext_iff.mp (chartDomain_locus (chartAt (Space U.dimension) i)) x.val).mp x.property
  have h := (chartAt (Space U.dimension) i).right_inv hx
  simpa [chartPoint,TopologicalSpace.Opens.chartAt_eq,chartAt_self_eq] using h

abbrev openFamily (U : Domain) := ChartFamily.preferred (n := U.dimension) (M := ordinaryOpen U)

/-- The usual manifold charts cover the single existing principal-open chart. -/
def fromSingle (U : Domain) : Charts.LocalMap (singleAtlas U).toCharts (openFamily U).charts id where
  Cover _ := ordinaryOpen U
  defining _ _ := 1
  covers _ x := ⟨x,by simp⟩
  index _ i := i
  coordinate _ i := domainInclusion _ _ (fun x hx => by
    change x ∈ Points (chartDomain (chartAt (Space U.dimension) i))
    rw [chartDomain_locus,open_chart_target]
    exact Localization.locus_product_subset _ _ hx)
  agreement _ i x := by
    apply Subtype.ext
    change x.val = (chartPoint (chartAt (Space U.dimension) i) _).val
    have hx : x.val ∈ Points (chartDomain (chartAt (Space U.dimension) i)) := by
      rw [chartDomain_locus,open_chart_target]
      exact Localization.locus_product_subset _ _ x.property
    exact (open_chart_value U i ⟨x.val,hx⟩).symm

/-- The ordinary point function of each inherited chart is the coordinate identity. -/
def toSingle (U : Domain) : Charts.LocalMap (openFamily U).charts (singleAtlas U).toCharts id where
  Cover _ := Unit
  defining _ _ := 1
  covers _ _ := ⟨(),by simp⟩
  index _ _ := ()
  coordinate i _ := domainInclusion _ _ (fun x hx => by
    have hp := Localization.locus_product_subset _ _ hx
    change x ∈ Points (chartDomain (chartAt (Space U.dimension) i)) at hp
    rw [chartDomain_locus,open_chart_target] at hp
    exact hp)
  agreement i _ x := by
    apply Subtype.ext
    change (chartPoint (chartAt (Space U.dimension) i) _).val = x.val
    exact open_chart_value U i _

/-- A local identity description works without choosing a point of the domain. -/
private def localIdentity {X : Type} (A : Charts X) : Charts.LocalMap A A id where
  Cover _ := Unit
  defining _ _ := 1
  covers _ _ := ⟨(),by simp⟩
  index i _ := i
  coordinate i _ := subInclusion (A.domain i) 1
  agreement _ _ _ := rfl

def openSingleIso (U : Domain) : object U.dimension (ordinaryOpen U) ≅ (singleAtlas U).toCharts.realization where
  hom := (toSingle U).realize
  inv := (fromSingle U).realize
  hom_inv_id :=
    (Charts.LocalMap.realize_comp (toSingle U) (fromSingle U)
      (localIdentity (openFamily U).charts)).symm.trans (Charts.LocalMap.realize_id _)
  inv_hom_id :=
    (Charts.LocalMap.realize_comp (fromSingle U) (toSingle U)
      (localIdentity (singleAtlas U).toCharts)).symm.trans (Charts.LocalMap.realize_id _)

/-- The manifold bridge recovers the prior open-domain object, also when empty. -/
def principalIso (U : Domain) : object U.dimension (ordinaryOpen U) ≅ embedding.obj U :=
  openSingleIso U ≪≫ Charts.singleIso U

end SquareKit.ManifoldRealization
