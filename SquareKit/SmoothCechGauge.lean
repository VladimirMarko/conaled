import SquareKit.SmoothCechRecovery

/-! Gauge changes retain complete ordinary transition labels and arrow families. -/
noncomputable section
open scoped Manifold ContDiff
namespace SquareKit.SmoothCech
open CategoryTheory EuclideanOpen SmoothOpenSite SmoothRepresentedCover SmoothManifoldAction
open ManifoldRealization
variable {X : Sheaf topology Type} {I : Type} {A : Atlas X I}
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (Model d) ∞ M]

/-- Restriction uses the actual smooth map of represented domains. -/
def restrictLabel {U V : Domain} (a : LocallyConstant (Points U) G) (r : V ⟶ U) :
    LocallyConstant (Points V) G :=
  LocallyConstant.comap ⟨(show EuclideanOpen.Map V U from r),
    (openMap_contMDiff r).continuous⟩ a

namespace Datum
variable (p : Datum (d := d) (G := G) (M := M) A)
variable (n : ∀ i, External.SmoothMap (A.domain i) d M)
variable (a : ∀ i, External.Labels (G := G) (A.domain i) (p.localMap i) (n i))

def gauge : Datum (d := d) (G := G) (M := M) A where
  localMap := n
  transition i j := ⟨restrictLabel (a j).val (A.right i j) * (p.transition i j).val *
    (restrictLabel (a i).val (A.left i j))⁻¹, fun x => by
      change (((a j).val _ * (p.transition i j).val x) * ((a i).val _)⁻¹) • _ = _
      dsimp only [External.SmoothMap.restrict]
      erw [mul_smul, inv_smul_eq_iff.mpr ((a i).property _).symm,
        mul_smul, (p.transition i j).property, (a j).property]
      rfl⟩
  diagonal i x := by
    have hl := congrArg (fun r : A.domain i ⟶ A.domain i =>
      (show EuclideanOpen.Map _ _ from r) x) (A.diagonal_left i)
    have hr := congrArg (fun r : A.domain i ⟶ A.domain i =>
      (show EuclideanOpen.Map _ _ from r) x) (A.diagonal_right i)
    change (a i).val _ * (p.transition i i).val _ * ((a i).val _)⁻¹ = 1
    rw [p.diagonal]
    change (a i).val ((show EuclideanOpen.Map _ _ from A.right i i)
      ((show EuclideanOpen.Map _ _ from A.diagonal i) x)) * 1 *
      ((a i).val ((show EuclideanOpen.Map _ _ from A.left i i)
      ((show EuclideanOpen.Map _ _ from A.diagonal i) x)))⁻¹ = 1
    rw [show (show EuclideanOpen.Map _ _ from A.right i i)
      ((show EuclideanOpen.Map _ _ from A.diagonal i) x) = x from hr,
      show (show EuclideanOpen.Map _ _ from A.left i i)
      ((show EuclideanOpen.Map _ _ from A.diagonal i) x) = x from hl]
    simp
  cocycle i j k x := by
    have h₁ := congrArg (fun r : A.triple i j k ⟶ A.domain i =>
      (show EuclideanOpen.Map _ _ from r) x) (A.firstThird_left i j k)
    have h₂ := congrArg (fun r : A.triple i j k ⟶ A.domain k =>
      (show EuclideanOpen.Map _ _ from r) x) (A.firstThird_right i j k)
    have h₃ := congrArg (fun r : A.triple i j k ⟶ A.domain j =>
      (show EuclideanOpen.Map _ _ from r) x) (A.secondThird_left i j k)
    have h₄ := congrArg (fun r : A.triple i j k ⟶ A.domain k =>
      (show EuclideanOpen.Map _ _ from r) x) (A.secondThird_right i j k)
    let ai : LocallyConstant (Points (A.domain i)) G := (a i).val
    let aj : LocallyConstant (Points (A.domain j)) G := (a j).val
    let ak : LocallyConstant (Points (A.domain k)) G := (a k).val
    let uij : LocallyConstant (Points (A.pair i j)) G := (p.transition i j).val
    let ujk : LocallyConstant (Points (A.pair j k)) G := (p.transition j k).val
    let uik : LocallyConstant (Points (A.pair i k)) G := (p.transition i k).val
    change ak ((show EuclideanOpen.Map _ _ from A.right i k)
        ((show EuclideanOpen.Map _ _ from A.firstThird i j k) x)) *
      uik ((show EuclideanOpen.Map _ _ from A.firstThird i j k) x) *
      (ai ((show EuclideanOpen.Map _ _ from A.left i k)
        ((show EuclideanOpen.Map _ _ from A.firstThird i j k) x)))⁻¹ =
      (ak ((show EuclideanOpen.Map _ _ from A.right j k)
        ((show EuclideanOpen.Map _ _ from A.secondThird i j k) x)) *
      ujk ((show EuclideanOpen.Map _ _ from A.secondThird i j k) x) *
      (aj ((show EuclideanOpen.Map _ _ from A.left j k)
        ((show EuclideanOpen.Map _ _ from A.secondThird i j k) x)))⁻¹) *
      (aj ((show EuclideanOpen.Map _ _ from A.right i j)
        ((show EuclideanOpen.Map _ _ from A.firstSecond i j k) x)) *
      uij ((show EuclideanOpen.Map _ _ from A.firstSecond i j k) x) *
      (ai ((show EuclideanOpen.Map _ _ from A.left i j)
        ((show EuclideanOpen.Map _ _ from A.firstSecond i j k) x)))⁻¹)
    have hu : uik ((show EuclideanOpen.Map _ _ from A.firstThird i j k) x) =
      ujk ((show EuclideanOpen.Map _ _ from A.secondThird i j k) x) *
      uij ((show EuclideanOpen.Map _ _ from A.firstSecond i j k) x) := p.cocycle i j k x
    rw [hu]
    change (show EuclideanOpen.Map _ _ from A.left i k)
      ((show EuclideanOpen.Map _ _ from A.firstThird i j k) x) =
      (show EuclideanOpen.Map _ _ from A.left i j)
      ((show EuclideanOpen.Map _ _ from A.firstSecond i j k) x) at h₁
    change (show EuclideanOpen.Map _ _ from A.right i k)
      ((show EuclideanOpen.Map _ _ from A.firstThird i j k) x) =
      (show EuclideanOpen.Map _ _ from A.third i j k) x at h₂
    change (show EuclideanOpen.Map _ _ from A.left j k)
      ((show EuclideanOpen.Map _ _ from A.secondThird i j k) x) =
      (show EuclideanOpen.Map _ _ from A.right i j)
      ((show EuclideanOpen.Map _ _ from A.firstSecond i j k) x) at h₃
    change (show EuclideanOpen.Map _ _ from A.right j k)
      ((show EuclideanOpen.Map _ _ from A.secondThird i j k) x) =
      (show EuclideanOpen.Map _ _ from A.third i j k) x at h₄
    dsimp only
    erw [h₁, h₂, h₃, h₄]
    simp only [mul_assoc, inv_mul_cancel_left]

def gaugeHom : Hom p (p.gauge n a) where
  labels := a
  commutes i j x := by
    change ((a j).val _ * (p.transition i j).val x * ((a i).val _)⁻¹) * (a i).val _ = _
    exact inv_mul_cancel_right _ _

omit [TopologicalSpace G] [DiscreteTopology G] [IsManifold (Model d) ∞ M] in
theorem gauge_transition (i j : I) (x : Points (A.pair i j)) :
    ((p.gauge n a).transition i j).val x =
      (a j).val ((show EuclideanOpen.Map _ _ from A.right i j) x) *
      (p.transition i j).val x *
      ((a i).val ((show EuclideanOpen.Map _ _ from A.left i j) x))⁻¹ := rfl

def gaugeComparison
    (smoothAction : ∀ g : G, ContMDiff (Model d) (Model d) ∞ (fun x : M => g • x)) :
    SheafActionQuotient.Arrow ((p.gauge n a).interpreted smoothAction)
      (p.interpreted smoothAction) :=
  (interpretedHomEquiv smoothAction _ _ (p.gaugeHom n a)).inverse

omit [TopologicalSpace G] [DiscreteTopology G] [IsManifold (Model d) ∞ M] in
theorem gauge_of_hom {q : Datum (d := d) (G := G) (M := M) A} (h : Hom p q) :
    p.gauge q.localMap h.labels = q := by
  refine Datum.ext _ _ ?_ ?_
  · rfl
  apply heq_of_eq
  funext i j
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  change (h.labels j).val ((show EuclideanOpen.Map _ _ from A.right i j) x) *
    (p.transition i j).val x * ((h.labels i).val ((show EuclideanOpen.Map _ _ from A.left i j) x))⁻¹ = _
  rw [← h.commutes, mul_inv_cancel_right]

def composeGauge (m : ∀ i, External.SmoothMap (A.domain i) d M)
    (b : ∀ i, External.Labels (G := G) (A.domain i) (n i) (m i)) :
    ∀ i, External.Labels (G := G) (A.domain i) (p.localMap i) (m i) :=
  fun i => ⟨(b i).val * (a i).val, fun x => by
    change ((b i).val x * (a i).val x) • _ = _
    rw [mul_smul, (a i).property, (b i).property]⟩

omit [TopologicalSpace G] [DiscreteTopology G] [IsManifold (Model d) ∞ M] in
theorem gauge_twice (m : ∀ i, External.SmoothMap (A.domain i) d M)
    (b : ∀ i, External.Labels (G := G) (A.domain i) (n i) (m i)) :
    (p.gauge n a).gauge m b = p.gauge m (p.composeGauge n a m b) := by
  refine Datum.ext _ _ ?_ ?_
  · rfl
  apply heq_of_eq
  funext i j
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  change (b j).val _ * ((a j).val _ * (p.transition i j).val x * ((a i).val _)⁻¹) * ((b i).val _)⁻¹ =
    ((b j).val _ * (a j).val _) * (p.transition i j).val x * ((b i).val _ * (a i).val _)⁻¹
  simp only [mul_inv_rev, mul_assoc]

theorem gauge_identity : p.gauge p.localMap (Hom.ident p).labels = p := p.gauge_of_hom (Hom.ident p)

end Datum

namespace TrivializedOn
variable (smoothAction : ∀ g : G, ContMDiff (Model d) (Model d) ∞ (fun x : M => g • x))
variable {P : SheafActionQuotient.Object (representation smoothAction).action X}
variable (t u : TrivializedOn A smoothAction P)

/-- Re-express the same original object through two supplied local trivializations. -/
def changeOfTrivialization : Hom t.extractedDatum u.extractedDatum :=
  t.extractArrow u (SheafActionQuotient.Arrow.ident P)

theorem changed_datum :
    t.extractedDatum.gauge u.extractedDatum.localMap (t.changeOfTrivialization smoothAction u).labels =
      u.extractedDatum := t.extractedDatum.gauge_of_hom (t.changeOfTrivialization smoothAction u)

theorem change_recovery :
    (interpretedHomEquiv smoothAction _ _ (t.changeOfTrivialization smoothAction u)).comp
      u.extractedRecovery = t.extractedRecovery := by
  have h := t.recovery_naturality u (SheafActionQuotient.Arrow.ident P)
  have hi : t.extractedRecovery.comp (SheafActionQuotient.Arrow.ident P) = t.extractedRecovery := by
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    exact Category.comp_id _
  exact h.trans hi

theorem change_identity : t.changeOfTrivialization smoothAction t = Hom.ident t.extractedDatum :=
  t.extractArrow_ident

theorem change_composite (v : TrivializedOn A smoothAction P) :
    (t.changeOfTrivialization smoothAction u).comp (u.changeOfTrivialization smoothAction v) =
      t.changeOfTrivialization smoothAction v := by
  have h := t.extractArrow_comp u v (SheafActionQuotient.Arrow.ident P) (SheafActionQuotient.Arrow.ident P)
  have hi : (SheafActionQuotient.Arrow.ident P).comp (SheafActionQuotient.Arrow.ident P) =
      SheafActionQuotient.Arrow.ident P := by
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    exact Category.id_comp _
  rw [hi] at h
  exact h.symm

end TrivializedOn

namespace Hom
variable {p q : Datum (d := d) (G := G) (M := M) A}
variable (f : Hom p q)
variable (n m : ∀ i, External.SmoothMap (A.domain i) d M)
variable (a : ∀ i, External.Labels (G := G) (A.domain i) (p.localMap i) (n i))
variable (b : ∀ i, External.Labels (G := G) (A.domain i) (q.localMap i) (m i))

def gauge : Hom (p.gauge n a) (q.gauge m b) :=
  (p.gaugeHom n a).inverse.comp (f.comp (q.gaugeHom m b))

omit [TopologicalSpace G] [DiscreteTopology G] [IsManifold (Model d) ∞ M] in
theorem gauge_labels (i : I) (x : Points (A.domain i)) :
    ((f.gauge n m a b).labels i).val x =
      (b i).val x * (f.labels i).val x * ((a i).val x)⁻¹ := rfl

end Hom
end SquareKit.SmoothCech
