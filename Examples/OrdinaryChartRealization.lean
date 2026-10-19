import SquareKit.SmoothAtlasSubdivision
import Examples.OrdinaryOpenDescent

/-! Experimental ordinary atlases: infinite covers, a nonidentity transition,
induced maps, and the empty boundary. -/
noncomputable section
open CategoryTheory SquareKit SquareKit.EuclideanOpen SquareKit.SmoothAlgebra
namespace Examples.OrdinaryChartRealization

abbrev line := full 1

def negate : line ⟶ line where
  toFun x := ⟨-x.val, by simp [Localization.locus]⟩
  smooth i := (OpenFunctions.representative_iff _ (fun x => -x i) (fun _ => rfl)).mpr
    (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) i).neg.contDiffOn

theorem negate_twice (x : Points line) :
    (show Map _ _ from negate) ((show Map _ _ from negate) x) = x := by
  apply Subtype.ext
  simp [negate]

def negHomeomorph : Points line ≃ₜ Points line where
  toFun := (show Map _ _ from negate)
  invFun := (show Map _ _ from negate)
  left_inv := negate_twice
  right_inv := negate_twice
  continuous_toFun := map_continuous negate
  continuous_invFun := map_continuous negate

def coordinate : Bool → (line ⟶ line)
  | false => 𝟙 _
  | true => negate

theorem coordinate_twice (i : Bool) (x : Points line) :
    (show Map _ _ from coordinate i) ((show Map _ _ from coordinate i) x) = x := by
  cases i
  · rfl
  · exact negate_twice x

def reversedAtlas : Atlas (Points line) where
  Index := Bool
  domain _ := line
  coordinate i := (show Map _ _ from coordinate i)
  openEmbedding i := by
    cases i
    · exact Topology.IsOpenEmbedding.id
    · exact negHomeomorph.isOpenEmbedding
  covers x := ⟨false,x,rfl⟩
  transition i j x _ _ :=
    ⟨1, by simp, subInclusion line 1 ≫ coordinate i ≫ coordinate j,
      fun z => (coordinate_twice j ((show Map _ _ from coordinate i)
        ((show Map _ _ from subInclusion line 1) z))).symm⟩

/-- The chart transition reverses sign, and is not the identity. -/
theorem transition_nonidentity : coordinate true ≠ coordinate false := by
  intro h
  have e := congrArg (fun f : line ⟶ line => ((show Map _ _ from f)
    ⟨fun _ => 1,by simp [Localization.locus]⟩).val 0) h
  change (-1 : ℝ) = 1 at e
  norm_num at e

def reflection : Charts.Map reversedAtlas.toCharts reversedAtlas.toCharts where
  point := (show Map _ _ from negate)
  index := id
  coordinate _ := negate
  agreement i x := by
    cases i
    · rfl
    · rfl

def reflected : reversedAtlas.toCharts.realization ⟶ reversedAtlas.toCharts.realization :=
  reflection.realize

theorem reflected_chart (i : Bool) :
    reversedAtlas.toCharts.chart i ≫ reflected = embedding.map negate ≫ reversedAtlas.toCharts.chart i :=
  Charts.Map.chart_realize reflection i

theorem reflected_involution : reflected ≫ reflected = 𝟙 _ := by
  change reflection.realize ≫ reflection.realize = _
  rw [← Charts.Map.realize_comp]
  rw [Charts.Map.realize_eq (reflection.comp reflection) (Charts.Map.ident _) (by
    funext x
    exact negate_twice x)]
  exact Charts.Map.realize_ident

def reversedRefinement : Charts.Refinement reversedAtlas.toCharts (singleAtlas line).toCharts where
  map := ⟨id, fun _ => (), coordinate, fun _ _ => rfl⟩
  point_identity := rfl
  Cover _ := Unit
  defining _ _ := 1
  covers _ _ := ⟨(),by simp⟩
  index _ _ := false
  lift _ _ := subInclusion line 1
  agreement _ _ _ := rfl

def reversedIso : reversedAtlas.toCharts.realization ≅ embedding.obj line :=
  reversedRefinement.iso ≪≫ Charts.singleIso line

abbrev infiniteAtlas := coverAtlas OrdinaryOpenDescent.line OrdinaryOpenDescent.defining OrdinaryOpenDescent.covers

def infiniteIso : infiniteAtlas.toCharts.realization ≅ embedding.obj OrdinaryOpenDescent.line :=
  coverAtlasIso _ _ OrdinaryOpenDescent.covers

theorem infinite_not_finite (S : Finset ℕ) :
    ¬ Covers OrdinaryOpenDescent.line (fun i : S => OrdinaryOpenDescent.defining i.val) :=
  OrdinaryOpenDescent.no_finite_subcover S

/-- Descent on the same genuinely infinite atlas tests every sheaf target. -/
example (F : Sheaf SmoothOpenSite.topology (Type)) :
    (infiniteAtlas.toCharts.realization ⟶ F) ≃
      {a : ∀ i, embedding.obj (infiniteAtlas.domain i) ⟶ F // infiniteAtlas.toCharts.Compatible a} :=
  infiniteAtlas.toCharts.homEquiv F

def emptyAtlas : Atlas Empty where
  Index := Empty
  domain := Empty.elim
  coordinate i := i.elim
  openEmbedding i := i.elim
  covers x := x.elim
  transition i := i.elim

theorem empty_initial (F : Sheaf SmoothOpenSite.topology (Type)) :
    ∃! _f : emptyAtlas.toCharts.realization ⟶ F, True := by
  refine ⟨emptyAtlas.toCharts.descend (fun i => i.elim) (fun r => r.first.elim), trivial, ?_⟩
  intro f _
  apply Charts.hom_ext
  intro i
  exact i.elim

end Examples.OrdinaryChartRealization
