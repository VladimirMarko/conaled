import SquareKit.SmoothCechComparison
import SquareKit.SmoothClutchingPrincipal

/-! The two genuine represented charts of the doubled-origin parameter sheaf. -/
noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace SquareKit.SmoothClutching
open EuclideanOpen SmoothOpenSite SmoothRepresentedCover SmoothAlgebra
namespace Represented

def chart : Bool → (lineSheaf ⟶ base)
  | false => left
  | true => right

def pair : Bool → Bool → Domain
  | false, false => line
  | true, true => line
  | _, _ => punctured

def projection : (i j : Bool) → pair i j ⟶ line
  | false, false => 𝟙 _
  | true, true => 𝟙 _
  | false, true => subInclusion line (generator 0)
  | true, false => subInclusion line (generator 0)

theorem square (i j : Bool) : IsPullback (embedding.map (projection i j))
    (embedding.map (projection i j)) (chart i) (chart j) := by
  cases i <;> cases j
  · simpa [projection, chart, pair, embedding.map_id] using
      (IsPullback.of_horiz_isIso_mono (fst := 𝟙 lineSheaf) (snd := 𝟙 lineSheaf)
        (f := left) (g := left) ⟨by simp⟩)
  · exact overlap
  · exact overlap.flip
  · simpa [projection, chart, pair, embedding.map_id] using
      (IsPullback.of_horiz_isIso_mono (fst := 𝟙 lineSheaf) (snd := 𝟙 lineSheaf)
        (f := right) (g := right) ⟨by simp⟩)

def triple : Bool → Bool → Bool → Domain
  | false, false, false => line
  | true, true, true => line
  | _, _, _ => punctured

def firstSecond : (i j k : Bool) → triple i j k ⟶ pair i j
  | false, false, false => 𝟙 _
  | false, false, true => subInclusion line (generator 0)
  | true, true, false => subInclusion line (generator 0)
  | true, true, true => 𝟙 _
  | false, true, _ => 𝟙 _
  | true, false, _ => 𝟙 _

def third : (i j k : Bool) → triple i j k ⟶ line
  | false, false, false => 𝟙 _
  | true, true, true => 𝟙 _
  | false, false, true => subInclusion line (generator 0)
  | false, true, _ => subInclusion line (generator 0)
  | true, false, _ => subInclusion line (generator 0)
  | true, true, false => subInclusion line (generator 0)

theorem tripleSquare (i j k : Bool) : IsPullback (embedding.map (firstSecond i j k))
    (embedding.map (third i j k)) (embedding.map (projection i j) ≫ chart i) (chart k) := by
  cases i <;> cases j <;> cases k
  · simpa [firstSecond, third, projection, chart, pair, triple, embedding.map_id] using square false false
  · simpa [firstSecond, third, projection, chart, pair, triple, embedding.map_id] using overlap
  · simp only [firstSecond, third, projection, chart, pair, triple, embedding.map_id]
    apply IsPullback.of_horiz_isIso_mono
    exact ⟨by simp⟩
  · simp only [firstSecond, third, projection, chart, pair, triple, embedding.map_id]
    apply IsPullback.of_horiz_isIso_mono
    exact ⟨by simpa [firstSecond, third, projection, chart, pair, triple, embedding.map_id] using overlap.w⟩
  · simp only [firstSecond, third, projection, chart, pair, triple, embedding.map_id]
    apply IsPullback.of_horiz_isIso_mono
    exact ⟨by simpa [firstSecond, third, projection, chart, pair, triple, embedding.map_id] using overlap.w.symm⟩
  · simp only [firstSecond, third, projection, chart, pair, triple, embedding.map_id]
    apply IsPullback.of_horiz_isIso_mono
    exact ⟨by simp⟩
  · simpa [firstSecond, third, projection, chart, pair, triple, embedding.map_id] using overlap.flip
  · simpa [firstSecond, third, projection, chart, pair, triple, embedding.map_id] using square true true

def atlas : Atlas base Bool where
  domain _ := line
  chart := chart
  covering V x := by
    apply topology.superset_covering _ (SheafPushoutLocal.chartSieve_cover inclusion inclusion x)
    intro W r hr
    rcases hr with ⟨y,hy⟩ | ⟨y,hy⟩
    · exact ⟨false,y,hy⟩
    · exact ⟨true,y,hy⟩
  pair := pair
  left := projection
  right := projection
  square := square
  triple := triple
  firstSecond := firstSecond
  third := third
  tripleSquare := tripleSquare

variable (G : Type) [Group G] (c : G)

/-- The displayed identity point of either chart supplies a local section;
it does not supply a section on the doubled-origin parameter. -/
def chartSection (j : lineSheaf ⟶ base) (k : totalLine G ⟶ total G c)
    (hk : k ≫ SmoothClutching.projection G c = lineProjection G ≫ j) :
    SplitSheaf.Tm (SheafTorsor.reindex (torsor G c) j).family where
  val x := ⟨k.hom.app x.obj (pairSection _ _ x.obj x.val (1 : (locallyConstantGroup G).obj.obj x.obj)),
    projection_chart G c j k hk x.obj x.val 1⟩
  natural {x y} f := by
    apply Subtype.ext
    change (total G c).obj.map f.hom (k.hom.app x.obj (pairSection _ _ x.obj x.val (1 : (locallyConstantGroup G).obj.obj x.obj))) =
      k.hom.app y.obj (pairSection _ _ y.obj y.val (1 : (locallyConstantGroup G).obj.obj y.obj))
    rw [← NatTrans.naturality_apply]
    erw [pairSection_natural]
    congr 2
    · exact f.map_val
    · exact ((locallyConstantGroup G).obj.map f.hom).hom.map_one

/-- Genuine equivariant trivializations of the existing nontrivial clutching torsor. -/
def localTrivialization (i : Bool) :
    SheafTorsor.Arrow (SheafTorsor.trivial (locallyConstantGroup G) lineSheaf)
      (SheafTorsor.reindex (torsor G c) (chart i)) :=
  match i with
  | false => SheafTorsor.ofSection _
      (chartSection G c left (totalChartLeft G c) (localTrivial G c).1.w)
  | true => SheafTorsor.ofSection _
      (chartSection G c right (totalChartRight G c) (localTrivial G c).2.w)

theorem localTrivialization_left_apply (x : lineSheaf.obj.Elements)
    (g : (locallyConstantGroup G).obj.obj x.obj) :
    ((localTrivialization G c false).iso.hom.app x g).val =
      (totalChartLeft G c).hom.app x.obj (pairSection _ _ x.obj x.val g) := by
  change sectionAction G c x.obj g
    ((totalChartLeft G c).hom.app x.obj (pairSection _ _ x.obj x.val (1 : (locallyConstantGroup G).obj.obj x.obj))) = _
  rw [sectionAction_chart G c _ (actionMap_left G c)]
  erw [pairSection_fst, pairSection_snd, mul_one]
theorem localTrivialization_right_apply (x : lineSheaf.obj.Elements)
    (g : (locallyConstantGroup G).obj.obj x.obj) :
    ((localTrivialization G c true).iso.hom.app x g).val =
      (totalChartRight G c).hom.app x.obj (pairSection _ _ x.obj x.val g) := by
  change sectionAction G c x.obj g
    ((totalChartRight G c).hom.app x.obj (pairSection _ _ x.obj x.val (1 : (locallyConstantGroup G).obj.obj x.obj))) = _
  rw [sectionAction_chart G c _ (actionMap_right G c)]
  erw [pairSection_fst, pairSection_snd, mul_one]
theorem chart_gluing (U : SmoothPresentationSite.Siteᵒᵖ)
    (x : puncturedSheaf.obj.obj U) (g : (locallyConstantGroup G).obj.obj U) :
    (totalChartLeft G c).hom.app U
      (pairSection _ _ U (inclusion.hom.app U x) g) =
    (totalChartRight G c).hom.app U
      (pairSection _ _ U (inclusion.hom.app U x)
        (g * (show (locallyConstantGroup G).obj.obj U from (transition G c).hom.app U x))) := by
  have h := congrArg (fun f : totalOverlap G ⟶ total G c =>
    f.hom.app U (pairSection _ _ U x g))
    (pushout.condition (f := totalLeft G) (g := totalRight G c))
  change (totalChartLeft G c).hom.app U ((totalLeft G).hom.app U _) =
    (totalChartRight G c).hom.app U ((totalRight G c).hom.app U _) at h
  change (totalChartLeft G c).hom.app U
    ((prod.map inclusion (𝟙 (locallyConstantGroupSheaf G))).hom.app U (pairSection _ _ U x g)) =
    (totalChartRight G c).hom.app U
    ((prod.lift (overlapProjection G ≫ inclusion)
      (multiply G prod.snd (overlapProjection G ≫ transition G c))).hom.app U
        (pairSection _ _ U x g)) at h
  erw [pairSection_map, pairSection_lift] at h
  change (totalChartLeft G c).hom.app U (pairSection _ _ U (inclusion.hom.app U x) g) =
    (totalChartRight G c).hom.app U (pairSection _ _ U
      (inclusion.hom.app U ((prod.fst : totalOverlap G ⟶ puncturedSheaf).hom.app U (pairSection _ _ U x g)))
      ((show (locallyConstantGroup G).obj.obj U from
        (prod.snd : totalOverlap G ⟶ _).hom.app U (pairSection _ _ U x g)) *
       (show (locallyConstantGroup G).obj.obj U from (transition G c).hom.app U
        ((prod.fst : totalOverlap G ⟶ puncturedSheaf).hom.app U (pairSection _ _ U x g))))) at h
  erw [pairSection_fst, pairSection_snd] at h
  exact h

end Represented
end SquareKit.SmoothClutching
