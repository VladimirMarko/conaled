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
    exact ⟨by simp [firstSecond, third, projection, chart, pair, triple, embedding.map_id]⟩
  · simp only [firstSecond, third, projection, chart, pair, triple, embedding.map_id]
    apply IsPullback.of_horiz_isIso_mono
    exact ⟨by simpa [firstSecond, third, projection, chart, pair, triple, embedding.map_id] using overlap.w⟩
  · simp only [firstSecond, third, projection, chart, pair, triple, embedding.map_id]
    apply IsPullback.of_horiz_isIso_mono
    exact ⟨by simpa [firstSecond, third, projection, chart, pair, triple, embedding.map_id] using overlap.w.symm⟩
  · simp only [firstSecond, third, projection, chart, pair, triple, embedding.map_id]
    apply IsPullback.of_horiz_isIso_mono
    exact ⟨by simp [firstSecond, third, projection, chart, pair, triple, embedding.map_id]⟩
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

end Represented
end SquareKit.SmoothClutching
