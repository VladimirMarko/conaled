import SquareKit.SmoothManifoldAction
import SquareKit.SmoothDiskPresentation
import Applications.Orbifolds.FiniteActionPresentation

/-! Complete smooth arrow families for interpreted manifold actions. -/
noncomputable section
open CategoryTheory
open scoped Manifold ContDiff Orbifolds.FiniteActionPresentation
namespace SquareKit.SmoothManifoldAction
open ManifoldRealization EuclideanOpen SmoothOpenSite SmoothOrdinaryQuotient SheafActionQuotient
open SmoothDiskPresentation
namespace External
open Orbifolds.FiniteActionPresentation

variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]

abbrev SmoothMap (U : Domain) (d : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (Space d) M] :=
  {m : ordinaryOpen U → M // ContMDiff (modelWithCorners U.dimension) (modelWithCorners d) ∞ m}

/-- An external family specifies its map and both endpoints independently of
any quotient comparison. The arrow model is the product with discrete labels. -/
def Family (U : Domain) (m n : SmoothMap U d M) :=
  {a : ordinaryOpen U → Orbifolds.FiniteActionPresentation.Arrow G M //
    ContMDiff (modelWithCorners U.dimension) (arrowModel (modelWithCorners d)) ∞ a ∧
    (∀ x, source (a x) = m.val x) ∧ (∀ x, target (a x) = n.val x)}

/-- Locally constant labels are auxiliary coordinates on the independent family type. -/
def Labels (U : Domain) (m n : SmoothMap U d M) :=
  {g : LocallyConstant (Points U) G // ∀ x, g x • m.val x = n.val x}

variable {U : Domain} {m n p : SmoothMap U d M}

omit [Group G] in
/-- Smoothness of a locally constant map requires no connectedness of its domain. -/
theorem label_smooth (g : LocallyConstant (Points U) G) :
    ContMDiff (modelWithCorners U.dimension) 𝓘(ℝ, Fin 0 → ℝ) ∞
      (show ordinaryOpen U → G from g) := by
  intro x
  exact contMDiffAt_const.congr_of_eventuallyEq (g.isLocallyConstant.eventually_eq x)

def labelsEquiv (m n : SmoothMap U d M) : Labels (G := G) U m n ≃ Family (G := G) U m n where
  toFun g := ⟨fun x => (g.val x, m.val x),
    (label_smooth g.val).prodMk m.property, fun _ => rfl, g.property⟩
  invFun a := ⟨⟨fun x => (a.val x).1,
    (IsLocallyConstant.iff_continuous _).mpr a.property.1.continuous.fst⟩,
    fun x => by
      change (a.val x).1 • m.val x = _
      rw [← a.property.2.1 x]
      exact a.property.2.2 x⟩
  left_inv _ := Subtype.ext rfl
  right_inv a := Subtype.ext (funext (fun x => Prod.ext rfl (a.property.2.1 x).symm))

variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))

abbrev ChartArrow (m n : SmoothMap U d M) :=
  SheafActionQuotient.Arrow (chart (representation smoothAction).action (hat m.val m.property))
    (chart (representation smoothAction).action (hat n.val n.property))

def chartLabelsEquiv (m n : SmoothMap U d M) :
    ChartArrow smoothAction m n ≃ Labels (G := G) U m n :=
  (chartArrowEquiv (hat m.val m.property) (hat n.val n.property)).trans {
    toFun k := ⟨(ordinaryHomLabelEquiv G U k.val)⁻¹, fun x =>
      inv_smul_eq_iff.mpr ((onMap_iff smoothAction U k.val _ _ _ _).mp k.property x).symm⟩
    invFun g := ⟨(ordinaryHomLabelEquiv G U).symm g.val⁻¹,
      (onMap_iff smoothAction U _ _ _ _ _).mpr (by
        rw [Equiv.apply_symm_apply]
        exact fun x => inv_smul_eq_iff.mpr (g.property x).symm)⟩
    left_inv k := by
      apply Subtype.ext
      simp only [inv_inv, Equiv.symm_apply_apply]
    right_inv g := by
      apply Subtype.ext
      simp only [Equiv.apply_symm_apply, inv_inv] }

/-- Complete quotient arrows correspond to all smooth external families. -/
def smoothChartEquiv (m n : SmoothMap U d M) :
    ChartArrow smoothAction m n ≃ Family (G := G) U m n :=
  (chartLabelsEquiv smoothAction m n).trans (labelsEquiv m n)

theorem smoothChartEquiv_apply (f : ChartArrow smoothAction m n) (x : Points U) :
    (smoothChartEquiv smoothAction m n f).val x = (ForwardLabel.label f x, m.val x) := rfl

theorem smoothChartEquiv_left_inv (f : ChartArrow smoothAction m n) :
    (smoothChartEquiv smoothAction m n).symm (smoothChartEquiv smoothAction m n f) = f :=
  (smoothChartEquiv smoothAction m n).symm_apply_apply f

theorem smoothChartEquiv_right_inv (a : Family (G := G) U m n) :
    smoothChartEquiv smoothAction m n ((smoothChartEquiv smoothAction m n).symm a) = a :=
  (smoothChartEquiv smoothAction m n).apply_symm_apply a

namespace Family
variable {smoothAction}

def ident (m : SmoothMap U d M) : Family (G := G) U m m :=
  ⟨fun x => unit (m.val x), unit_smooth (modelWithCorners d) |>.comp m.property,
    fun _ => rfl, fun x => one_smul G (m.val x)⟩

def comp (a : Family (G := G) U m n) (b : Family (G := G) U n p) : Family (G := G) U m p :=
  labelsEquiv m p ⟨((labelsEquiv n p).symm b).val * ((labelsEquiv m n).symm a).val,
    fun x => by
      change ((b.val x).1 * (a.val x).1) • m.val x = p.val x
      rw [mul_smul]
      exact (congrArg (fun y => (b.val x).1 • y) (((labelsEquiv m n).symm a).property x)).trans
        (((labelsEquiv n p).symm b).property x)⟩

def inverse (a : Family (G := G) U m n) : Family (G := G) U n m :=
  labelsEquiv n m ⟨((labelsEquiv m n).symm a).val⁻¹,
    fun x => inv_smul_eq_iff.mpr (((labelsEquiv m n).symm a).property x).symm⟩

omit [IsManifold (modelWithCorners d) ∞ M] in
@[ext] theorem ext {a b : Family (G := G) U m n}
    (h : ∀ x, (a.val x).1 = (b.val x).1) : a = b := by
  apply Subtype.ext
  funext x
  exact Prod.ext (h x) ((a.property.2.1 x).trans (b.property.2.1 x).symm)

omit [IsManifold (modelWithCorners d) ∞ M] in
theorem comp_apply (a : Family (G := G) U m n) (b : Family (G := G) U n p) (x : Points U) :
    (a.comp b).val x = compose (a.val x).1 (b.val x).1 (m.val x) := rfl

omit [IsManifold (modelWithCorners d) ∞ M] in
theorem inverse_apply (a : Family (G := G) U m n) (x : Points U) :
    a.inverse.val x = Orbifolds.FiniteActionPresentation.inverse (a.val x) :=
  Prod.ext rfl (a.property.2.2 x).symm

end Family

theorem smoothChartEquiv_ident (m : SmoothMap U d M) :
    smoothChartEquiv smoothAction m m (Arrow.ident _) = Family.ident m := by
  apply Family.ext
  exact ForwardLabel.ident _ _

theorem smoothChartEquiv_comp (f : ChartArrow smoothAction m n) (g : ChartArrow smoothAction n p) :
    smoothChartEquiv smoothAction m p (f.comp g) =
      (smoothChartEquiv smoothAction m n f).comp (smoothChartEquiv smoothAction n p g) := by
  apply Family.ext
  exact ForwardLabel.comp f g

theorem smoothChartEquiv_inverse (f : ChartArrow smoothAction m n) :
    smoothChartEquiv smoothAction n m f.inverse = (smoothChartEquiv smoothAction m n f).inverse := by
  apply Family.ext
  exact ForwardLabel.inverse f

end External
end SquareKit.SmoothManifoldAction
