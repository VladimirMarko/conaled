import SquareKit.Internal.Cubical.NativeUnivalenceMap
import SquareKit.Internal.Cubical.UniverseRaisingNaturality

/-! Native universe paths assembled from exact small-chart Glue codes. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u
variable {Ξ : Context.{u+1}} (a b : Ξ ⟶ smallFamilyCodes.{u})
  (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)

noncomputable def chartCode {Γ : Context.{u}} (σ : raisedContext Γ ⟶ Ξ) :
    raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u} :=
  Univalence.uaCode (σ ≫ a) (σ ≫ b) (lowerChartMap a b σ f)
    (lowerChartEquivalence a b σ f E)

def ChartCoherence : Prop := ∀ {Γ Δ : Context.{u}}
    (σ : raisedContext Γ ⟶ Ξ) (τ : Δ ⟶ Γ),
    raisedSub (liftSub (interval Γ) τ) ≫ chartCode a b f E σ =
      chartCode a b f E (raisedSub τ ≫ σ)

noncomputable def uaValue (x : (total (interval Ξ)).Elements) : SmallFamilyCode.{u} x.obj.unop :=
  (chartCode a b f E (chart (intervalBase x))).app x.obj (chartPoint x)

theorem uaValue_natural (h : ChartCoherence a b f E) {x y : (total (interval Ξ)).Elements} (g : x ⟶ y) :
    smallFamilyCodes.map g.hom (uaValue a b f E x) = uaValue a b f E y := by
  let σ := chart (intervalBase x)
  have hn := ((chartCode a b f E σ).naturality_apply g.hom (chartPoint x)).symm
  have hr := congrArg (fun c : raisedContext (total (interval (representable.{u} y.obj.unop))) ⟶
    smallFamilyCodes.{u} => c.app y.obj (chartPoint y))
    (h σ (representableMap g.hom.unop))
  have hc := congrArg (fun c : raisedContext (representable.{u} y.obj.unop) ⟶ Ξ =>
    (chartCode a b f E c).app y.obj (chartPoint y))
    (chart_restrict ((projection (interval Ξ)).mapElements.map g))
  exact hn.trans ((congrArg ((chartCode a b f E σ).app y.obj) (chartPoint_natural g)).trans
    (hr.trans hc))

noncomputable def coherentLine (h : ChartCoherence a b f E) : Term (family (total (interval Ξ))) where
  val := uaValue a b f E
  property g := uaValue_natural a b f E h g

theorem coherentLine_zero (h : ChartCoherence a b f E) : (coherentLine a b f E h).reindex (endpointSub Ξ false) = term a := by
  apply Term.ext
  intro x
  have h := congrArg (fun c => c.app x.obj ⟨⟨𝟙 x.obj.unop⟩⟩)
    (Univalence.uaCode_zero (chart x ≫ a) (chart x ≫ b)
      (lowerChartMap a b (chart x) f) (lowerChartEquivalence a b (chart x) f E))
  exact h.trans (congrArg (a.app x.obj) (chart_generic x))

theorem coherentLine_one (h : ChartCoherence a b f E) : (coherentLine a b f E h).reindex (endpointSub Ξ true) = term b := by
  apply Term.ext
  intro x
  have h := congrArg (fun c => c.app x.obj ⟨⟨𝟙 x.obj.unop⟩⟩)
    (Univalence.uaCode_one (chart x ≫ a) (chart x ≫ b)
      (lowerChartMap a b (chart x) f) (lowerChartEquivalence a b (chart x) f E))
  exact h.trans (congrArg (b.app x.obj) (chart_generic x))

noncomputable def uaFromCharts (h : ChartCoherence a b f E) : Term (paths a b) :=
  pathLam (coherentLine a b f E h) (coherentLine_zero a b f E h) (coherentLine_one a b f E h)

end SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
