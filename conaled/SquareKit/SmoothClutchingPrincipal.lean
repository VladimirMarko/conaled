import SquareKit.SmoothClutchingTorsor
import Mathlib.CategoryTheory.Limits.Types.Pullbacks

/-! Principality and nontriviality of the actual clutching torsor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
namespace SquareKit.SmoothClutching
open SmoothOpenSite SmoothPresentationSite
variable (G : Type) [Group G] (c : G)

/-- The sheaf pullback comparison lifts every section over a chart, at every
stage, to a genuine product section with the specified base coordinate. -/
theorem chart_fiber_lift (j : lineSheaf ⟶ base) (k : totalLine G ⟶ total G c)
    (hk : IsPullback k (lineProjection G) (projection G c) j)
    (U : Siteᵒᵖ) (x : lineSheaf.obj.obj U) (p : (total G c).obj.obj U)
    (hp : (projection G c).hom.app U p = j.hom.app U x) :
    ∃ z : (totalLine G).obj.obj U, k.hom.app U z = p ∧ (lineProjection G).hom.app U z = x := by
  have h := hk.map (sheafToPresheaf SmoothOpenSite.topology Type ⋙ (evaluation _ _).obj U)
  exact Types.exists_of_isPullback h p x hp

/-- On each actual chart fiber, the unique acting label is the quotient of
the two product labels. Pullback uniqueness proves uniqueness of that label. -/
theorem chart_principal (j : lineSheaf ⟶ base) (k : totalLine G ⟶ total G c)
    (hk : IsPullback k (lineProjection G) (projection G c) j)
    (ha : prod.map (𝟙 _) k ≫ actionMap G c = localAction G lineSheaf ≫ k)
    (U : Siteᵒᵖ) (x : lineSheaf.obj.obj U) (p q : (total G c).obj.obj U)
    (hp : (projection G c).hom.app U p = j.hom.app U x)
    (hq : (projection G c).hom.app U q = j.hom.app U x) :
    ∃! g : (locallyConstantGroup G).obj.obj U, sectionAction G c U g p = q := by
  obtain ⟨a, ha₁, ha₂⟩ := chart_fiber_lift G c j k hk U x p hp
  obtain ⟨b, hb₁, hb₂⟩ := chart_fiber_lift G c j k hk U x q hq
  let ga : (locallyConstantGroup G).obj.obj U := (prod.snd : totalLine G ⟶ _).hom.app U a
  let gb : (locallyConstantGroup G).obj.obj U := (prod.snd : totalLine G ⟶ _).hom.app U b
  refine ⟨gb * ga⁻¹, ?_, ?_⟩
  · change sectionAction G c U (gb * ga⁻¹) p = q
    rw [← ha₁, sectionAction_chart G c k ha]
    have he : pairSection lineSheaf (locallyConstantGroupSheaf G) U
        ((lineProjection G).hom.app U a) ((gb * ga⁻¹) * ga) = b := by
      apply productSection_ext
      · simpa only [pairSection_fst] using ha₂.trans hb₂.symm
      · simpa only [pairSection_snd] using inv_mul_cancel_right gb ga
    exact (congrArg (k.hom.app U) he).trans hb₁
  · intro g hg
    rw [← ha₁, sectionAction_chart G c k ha, ← hb₁] at hg
    have h := hk.map (sheafToPresheaf SmoothOpenSite.topology Type ⋙ (evaluation _ _).obj U)
    have he := Types.ext_of_isPullback h hg (by
      change (lineProjection G).hom.app U
        (pairSection lineSheaf (locallyConstantGroupSheaf G) U
          ((lineProjection G).hom.app U a) (g * ga)) = (lineProjection G).hom.app U b
      simpa only [lineProjection, pairSection_fst] using ha₂.trans hb₂.symm)
    have hl := congrArg ((prod.snd : totalLine G ⟶ locallyConstantGroupSheaf G).hom.app U) he
    change (prod.snd : totalLine G ⟶ locallyConstantGroupSheaf G).hom.app U
      (pairSection lineSheaf (locallyConstantGroupSheaf G) U
        ((lineProjection G).hom.app U a) (g * ga)) = gb at hl
    rw [pairSection_snd] at hl
    exact (eq_mul_inv_iff_mul_eq).mpr hl

/-- The local coefficient calculation applies to the actual ofDisplay fibers. -/
theorem reindex_chart_principal (j : lineSheaf ⟶ base) (k : totalLine G ⟶ total G c)
    (hk : IsPullback k (lineProjection G) (projection G c) j)
    (ha : prod.map (𝟙 _) k ≫ actionMap G c = localAction G lineSheaf ≫ k)
    (x : lineSheaf.obj.Elements)
    (p q : ((action G c).reindex j).family.family.obj x) :
    ∃! g : (locallyConstantGroup G).obj.obj x.obj, ((action G c).reindex j).act x g p = q := by
  obtain ⟨g, hg, hu⟩ := chart_principal G c j k hk ha x.obj x.val p.val q.val p.property q.property
  refine ⟨g, Subtype.ext hg, ?_⟩
  intro h hh
  exact hu h (congrArg Subtype.val hh)

/-- Unique local acting labels glue across the covering base charts. -/
theorem principal (x : base.obj.Elements) (p q : (action G c).family.family.obj x) :
    ∃! g : (locallyConstantGroup G).obj.obj x.obj, (action G c).act x g p = q := by
  obtain ⟨g, hg, hu⟩ := (action G c).total_principal_of_sieve x.obj.unop ⟨x.val, p⟩ ⟨x.val, q⟩
    (SheafPushoutLocal.chartSieve inclusion inclusion x.val)
    (SheafPushoutLocal.chartSieve_cover inclusion inclusion x.val) (by
      intro V f hf
      rcases hf with ⟨y, hy⟩ | ⟨y, hy⟩
      · exact (action G c).principal_at_lift left
          (reindex_chart_principal G c left (totalChartLeft G c) (localTrivial G c).1
            (actionMap_left G c)) _ _ _ rfl y hy
      · exact (action G c).principal_at_lift right
          (reindex_chart_principal G c right (totalChartRight G c) (localTrivial G c).2
            (actionMap_right G c)) _ _ _ rfl y hy)
  refine ⟨g, eq_of_heq (Sigma.mk.inj_iff.mp hg).2, ?_⟩
  intro h hh
  exact hu h (congrArg (Sigma.mk x.val) hh)

/-- The nontrivial clutching object is a torsor in the actual smooth sheaf slice. -/
def torsor : SheafTorsor.Torsor (locallyConstantGroup G) base where
  toAction := action G c
  principal := principal G c
  locallySurjective := action_locallySurjective G c

/-- A split global section would give a forbidden section of the actual glued display. -/
theorem no_global_section (hc : c ≠ 1) : ¬ Nonempty (SplitSheaf.Tm (torsor G c).family) := by
  rintro ⟨t⟩
  apply no_section G c hc
  refine ⟨SplitSheaf.pair (torsor G c).family (𝟙 base) t ≫
    (SplitSheaf.displayIso (projection G c)).hom, ?_⟩
  rw [Category.assoc, SplitSheaf.displayIso_projection]
  exact SplitSheaf.pair_p _ _ _

/-- No equivariant isomorphism trivializes the constructed clutching torsor. -/
theorem not_trivializable (hc : c ≠ 1) :
    ¬ Nonempty (SheafTorsor.Arrow (SheafTorsor.trivial (locallyConstantGroup G) base) (torsor G c)) := by
  rw [SheafTorsor.trivializable_iff_section]
  exact no_global_section G c hc

end SquareKit.SmoothClutching
