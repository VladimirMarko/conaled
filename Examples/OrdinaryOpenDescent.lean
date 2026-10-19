import SquareKit.SmoothOpenSheafDescent
import SquareKit.SmoothOpenRestriction
import Examples.ArbitrarySmoothCovers
import Examples.EuclideanOpenEmbedding

/-! Experimental ordinary/sheaf descent on the established countable cover,
with a nonpolynomial glued map, proper overlap and empty-cover boundaries. -/
noncomputable section
namespace Examples.OrdinaryOpenDescent
open CategoryTheory Opposite SquareKit SmoothAlgebra EuclideanOpen
open SmoothPresentationSite
abbrev line := EuclideanOpen.full 1
abbrev defining := ArbitrarySmoothCovers.defining

theorem covers : EuclideanOpen.Covers line defining := by
  intro x
  exact (OpenCover.covers_iff_zero_locus ArbitrarySmoothCovers.relations defining).mp
    ArbitrarySmoothCovers.covers x.val (fun j => Fin.elim0 j)

theorem no_finite_subcover (S : Finset ℕ) :
    ¬ EuclideanOpen.Covers line (fun i : S => defining i.val) := by
  intro hc
  apply ArbitrarySmoothCovers.no_finite_subcover S
  apply (OpenCover.covers_iff_zero_locus ArbitrarySmoothCovers.relations (fun i : S => defining i.val)).mpr
  intro x _
  exact hc ⟨x,one_ne_zero⟩

theorem covering : coverSieve line defining ∈ SmoothOpenSite.topology (toSite.obj line) :=
  EuclideanOpen.covering line defining covers

abbrev expMap := EuclideanOpenEmbedding.exponential
abbrev localExp (i : ℕ) : subdomain line (defining i) ⟶ line := subInclusion line (defining i) ≫ expMap

theorem localExp_compatible : Compatible line line defining localExp := restriction_compatible _ _ _ expMap

def gluedExp : line ⟶ line := glue line line defining covers localExp localExp_compatible

theorem gluedExp_eq : gluedExp = expMap :=
  (glue_unique line line defining covers localExp localExp_compatible expMap (fun _ => rfl)).symm

theorem gluedExp_value (x : Points line) : (show Map line line from gluedExp) x =
    ⟨fun _ => Real.exp (x.val 0),one_ne_zero⟩ := by
  rw [gluedExp_eq]
  rfl

/-- The ordinary reconstruction is precisely the unique descent in the sheaf model. -/
theorem model_descent (b : embedding.obj line ⟶ embedding.obj line) :
    (∀ i, embedding.map (subInclusion line (defining i)) ≫ b = embedding.map (localExp i)) ↔
      b = embedding.map gluedExp := glue_sheaf_comparison line defining line covers localExp localExp_compatible b

abbrev g : Free 1 := generator 0
abbrev h : Free 1 := generator 0 - 1

theorem proper_overlap : ¬ Function.Surjective
    (show Map (overlap line g h) (subdomain line g) from overlapLeft line g h) := by
  intro hs
  have hx : (fun _ : Fin 1 => (1 : ℝ)) ∈ Points (subdomain line g) := by change (1 : ℝ)*1 ≠ 0; norm_num
  obtain ⟨x,he⟩ := hs ⟨fun _ => 1,hx⟩
  have he' : x.val 0 = 1 := congrArg (fun y : Points (subdomain line g) => y.val 0) he
  have hn : x.val 0 - 1 ≠ 0 := right_ne_zero_of_mul x.property
  exact hn (by rw [he']; ring)

theorem overlap_nonempty : Nonempty (Points (overlap line g h)) := by
  refine ⟨⟨fun _ => 2,?_⟩⟩
  change (1 : ℝ)*2*(2-1) ≠ 0
  norm_num

theorem model_overlap : IsPullback (embedding.map (overlapLeft line g h))
    (embedding.map (overlapRight line g h)) (embedding.map (subInclusion line g))
      (embedding.map (subInclusion line h)) := overlap_sheaf_pullback line g h

/-- Actual base change also handles the reciprocal map without an ambient extension. -/
theorem reciprocal_baseChange :
    (show code line ⟶ code (subdomain line g) from Localization.pullback (subInclusion line g)) ≫
        baseChangeMap EuclideanOpenEmbedding.reciprocal g =
      (show code line ⟶ code EuclideanOpenEmbedding.punctured from Localization.pullback EuclideanOpenEmbedding.reciprocal) ≫
        localizationBase (code EuclideanOpenEmbedding.punctured)
          (Localization.pullback EuclideanOpenEmbedding.reciprocal (element line g)) :=
  baseChange_square EuclideanOpenEmbedding.reciprocal g

abbrev emptyDomain := EuclideanOpenEmbedding.emptyDomain
abbrev emptyFamily : Fin 0 → Free emptyDomain.dimension := Fin.elim0

theorem empty_covers : EuclideanOpen.Covers emptyDomain emptyFamily :=
  (empty_cover_iff emptyDomain emptyFamily).mpr EuclideanOpenEmbedding.empty_points

/-- The empty ordinary cover makes its embedded domain initial, by the actual sheaf condition. -/
theorem empty_model_descent (F : Sheaf SmoothOpenSite.topology Type) :
    ∃! _b : embedding.obj emptyDomain ⟶ F, True := by
  obtain ⟨b,hb,hu⟩ := sheaf_exists_unique emptyDomain emptyFamily empty_covers F
    (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
  exact ⟨b,trivial,fun b' _ => hu b' (fun i => Fin.elim0 i)⟩

end Examples.OrdinaryOpenDescent
