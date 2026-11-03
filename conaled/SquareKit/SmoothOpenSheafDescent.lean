import SquareKit.SmoothOrdinaryGluing

/-! Experimental comparison of ordinary map gluing with actual sheaf descent.
The cover's sheaf condition and Yoneda equivalence give a unique arrow into
any sheaf; no preservation of arbitrary colimits is assumed. -/
noncomputable section
namespace SquareKit.EuclideanOpen
open CategoryTheory Opposite SmoothAlgebra SmoothPresentationSite
variable (U : Domain) {ι : Type} (g : ι → Free U.dimension)
local notation "J" => SmoothOpenSite.topology

/-- The actual generated-topology sheaf condition on this ordinary cover. -/
theorem cover_isSheafFor (hc : Covers U g) (F : Sheaf J Type) :
    Presieve.IsSheafFor F.obj (coverPresieve U g) :=
  ((isSheaf_iff_isSheaf_of_type _ _).mp F.property).isSheafFor _ (covering U g hc)

theorem sheaf_exists_unique (hc : Covers U g) (F : Sheaf J Type)
    (a : ∀ i, embedding.obj (subdomain U (g i)) ⟶ F)
    (ha : ∀ i j, embedding.map (overlapLeft U (g i) (g j)) ≫ a i =
      embedding.map (overlapRight U (g i) (g j)) ≫ a j) :
    ∃! b : embedding.obj U ⟶ F, ∀ i, embedding.map (subInclusion U (g i)) ≫ b = a i := by
  change ∀ i, (J).yoneda.obj (toSite.obj (subdomain U (g i))) ⟶ F at a
  change ∀ i j, (J).yoneda.map (toSite.map (overlapLeft U (g i) (g j))) ≫ a i =
    (J).yoneda.map (toSite.map (overlapRight U (g i) (g j))) ≫ a j at ha
  change ∃! b : (J).yoneda.obj (toSite.obj U) ⟶ F,
    ∀ i, (J).yoneda.map (toSite.map (subInclusion U (g i))) ≫ b = a i
  let x i := (J).yonedaEquiv (a i)
  have hx : Presieve.Arrows.Compatible F.obj (fun i => toSite.map (subInclusion U (g i))) x := by
    intro i j Z u v huv
    let hp := overlap_site_pullback U (g i) (g j)
    let l := hp.lift u v huv
    have hl : l ≫ toSite.map (overlapLeft U (g i) (g j)) = u := hp.lift_fst _ _ _
    have hr : l ≫ toSite.map (overlapRight U (g i) (g j)) = v := hp.lift_snd _ _ _
    change F.obj.map u.op ((J).yonedaEquiv (a i)) = F.obj.map v.op ((J).yonedaEquiv (a j))
    refine ((J).yonedaEquiv_naturality (a i) u).trans ?_
    refine (congrArg ((J).yonedaEquiv) ?_).trans ((J).yonedaEquiv_naturality (a j) v).symm
    rw [← hl,← hr,(J).yoneda.map_comp,(J).yoneda.map_comp,Category.assoc,Category.assoc]
    exact congrArg (fun k => (J).yoneda.map l ≫ k) (ha i j)
  obtain ⟨t,ht,hu⟩ := (Presieve.isSheafFor_arrows_iff _ _).mp (cover_isSheafFor U g hc F) x hx
  refine ⟨(J).yonedaEquiv.symm t,?_,?_⟩
  · intro i
    apply (J).yonedaEquiv.injective
    rw [← (J).yonedaEquiv_naturality,(J).yonedaEquiv.apply_symm_apply]
    exact ht i
  · intro b hb
    apply (J).yonedaEquiv.injective
    rw [(J).yonedaEquiv.apply_symm_apply]
    apply hu
    intro i
    rw [(J).yonedaEquiv_naturality]
    exact congrArg (J).yonedaEquiv (hb i)

/-- The embedded cover is jointly epic against every sheaf target. -/
theorem cover_jointly_epic (hc : Covers U g) (F : Sheaf J Type)
    (b c : embedding.obj U ⟶ F)
    (he : ∀ i, embedding.map (subInclusion U (g i)) ≫ b = embedding.map (subInclusion U (g i)) ≫ c) :
    b=c := by
  have ha : ∀ i j, embedding.map (overlapLeft U (g i) (g j)) ≫
      (embedding.map (subInclusion U (g i)) ≫ b) =
      embedding.map (overlapRight U (g i) (g j)) ≫ (embedding.map (subInclusion U (g j)) ≫ b) := by
    intro i j
    rw [← Category.assoc,← Category.assoc,← embedding.map_comp,← embedding.map_comp,overlap_square]
  obtain ⟨t,ht,hu⟩ := sheaf_exists_unique U g hc F (fun i => embedding.map (subInclusion U (g i)) ≫ b) ha
  exact (hu b (fun _ => rfl)).trans (hu c (fun i => (he i).symm)).symm

/-- Ordinary local gluing is the unique categorical sheaf descent of its embedded maps. -/
theorem glue_sheaf_comparison (V : Domain) (hc : Covers U g)
    (a : ∀ i, subdomain U (g i) ⟶ V) (ha : Compatible U V g a) :
    ∀ b : embedding.obj U ⟶ embedding.obj V,
      (∀ i, embedding.map (subInclusion U (g i)) ≫ b = embedding.map (a i)) ↔
        b = embedding.map (glue U V g hc a ha) := by
  intro b
  constructor
  · intro hb
    obtain ⟨c,hc',hu⟩ := sheaf_exists_unique U g hc (embedding.obj V) (fun i => embedding.map (a i))
      (fun i j => by rw [← embedding.map_comp,← embedding.map_comp,ha i j])
    exact (hu b hb).trans (hu (embedding.map (glue U V g hc a ha))
      (fun i => by rw [← embedding.map_comp,glue_restrict])).symm
  · rintro rfl i
    rw [← embedding.map_comp,glue_restrict]

end SquareKit.EuclideanOpen
