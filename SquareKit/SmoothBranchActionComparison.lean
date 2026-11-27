import SquareKit.SmoothBranchRealization
import SquareKit.SmoothLocalDiffeomorphModel
import SquareKit.SmoothManifoldActionComparison

/-! Principal-test action arrows and the actual local branch coproduct. -/
noncomputable section
open CategoryTheory TopologicalSpace
open scoped Manifold ContDiff Orbifolds.FiniteActionPresentation
namespace SquareKit.SmoothBranchActionComparison
open ManifoldRealization EuclideanOpen SmoothOpenSite SmoothManifoldAction
open Orbifolds.LocalBranches

/-- Full faithfulness on a principal test, with the literal `hat` map forward. -/
def principalMapEquiv (P : Domain) {d : ℕ} (M : Type) [TopologicalSpace M]
    [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M] :
    External.SmoothMap P d M ≃ (embedding.obj P ⟶ object d M) where
  toFun f := hat f.val f.property
  invFun f := homEquiv.symm ((principalIso P).hom ≫ f)
  left_inv f := by
    change homEquiv.symm ((principalIso P).hom ≫ (principalIso P).inv ≫ homEquiv f) = f
    simp
  right_inv f := by
    change (principalIso P).inv ≫ homEquiv (homEquiv.symm ((principalIso P).hom ≫ f)) = f
    simp

section General
variable {a x y : ℕ} {A X Y J : Type}
  [TopologicalSpace A] [ChartedSpace (Space a) A] [IsManifold (modelWithCorners a) ∞ A]
  [TopologicalSpace X] [ChartedSpace (Space x) X] [IsManifold (modelWithCorners x) ∞ X]
  [TopologicalSpace Y] [ChartedSpace (Space y) Y] [IsManifold (modelWithCorners y) ∞ Y]
  {s : A → X} {t : A → Y} {U : Opens X} {V : Opens Y}
  (D : Diagram (modelWithCorners a) (modelWithCorners x) s t U V J)
  (hs : ContMDiff (modelWithCorners a) (modelWithCorners x) ∞ s)
  (ht : ContMDiff (modelWithCorners a) (modelWithCorners y) ∞ t)
  {P : Domain} (m : External.SmoothMap P x U) (n : External.SmoothMap P y V)

/-- Unconditioned principal sections of the branch coproduct. -/
def principalBranchEquiv (P : Domain) :
    External.SmoothMap P a D.region ≃ (embedding.obj P ⟶ SmoothBranchRealization.branches D) :=
  (principalMapEquiv P D.region).trans {
    toFun f := f ≫ SmoothBranchRealization.decompose D
    invFun f := f ≫ SmoothBranchRealization.assembly D
    left_inv f := by simp
    right_inv f := by simp }

@[simp] theorem principalBranchEquiv_assembly (P : Domain)
    (f : External.SmoothMap P a D.region) :
    principalBranchEquiv D P f ≫ SmoothBranchRealization.assembly D = hat f.val f.property := by
  change (hat f.val f.property ≫ SmoothBranchRealization.decompose D) ≫ _ = _
  simp

theorem principalBranchEquiv_symm_assembly (P : Domain)
    (f : embedding.obj P ⟶ SmoothBranchRealization.branches D) :
    hat ((principalBranchEquiv D P).symm f).val ((principalBranchEquiv D P).symm f).property =
      f ≫ SmoothBranchRealization.assembly D := by
  have h := principalBranchEquiv_assembly D P ((principalBranchEquiv D P).symm f)
  rw [Equiv.apply_symm_apply] at h
  exact h.symm

theorem principalBranchEquiv_restrict {Q : Domain} (r : Q ⟶ P)
    (f : External.SmoothMap P a D.region) :
    principalBranchEquiv D Q (f.restrict r) = embedding.map r ≫ principalBranchEquiv D P f := by
  change hat _ _ ≫ _ = _ ≫ hat _ _ ≫ _
  rw [← Category.assoc, hat_precomp]
  rfl

/-- An actual branch family realizes through that coproduct summand. -/
theorem principalBranchEquiv_assemble (i : J)
    (g : External.SmoothMap P x (D.domain i)) :
    hat g.val g.property ≫ SheafCoproductLocal.inclusion (fun j => object x (D.domain j)) i =
      principalBranchEquiv D P
        ⟨D.assemble i ∘ g.val, (D.assemble_smooth i).comp g.property⟩ := by
  apply (cancel_mono (SmoothBranchRealization.assemblyIso D).hom).mp
  rw [SmoothBranchRealization.assemblyIso_hom, Category.assoc,
    SmoothBranchRealization.inclusion_assembly, principalBranchEquiv_assembly, hat_postcomp]

/-- A principal section factors through one summand exactly when its actual arrow
family assembles from that branch everywhere on the test domain. -/
theorem principalBranchEquiv_factors_iff
    (f : External.SmoothMap P a D.region) (i : J) :
    (∃ b : embedding.obj P ⟶ object x (D.domain i),
      b ≫ SheafCoproductLocal.inclusion (fun j => object x (D.domain j)) i =
        principalBranchEquiv D P f) ↔
    ∃ g : External.SmoothMap P x (D.domain i), ∀ p, D.assemble i (g.val p) = f.val p := by
  constructor
  · rintro ⟨b, hb⟩
    let g := (principalMapEquiv P (D.domain i)).symm b
    have hg : hat g.val g.property = b := (principalMapEquiv P (D.domain i)).apply_symm_apply b
    have he : (⟨D.assemble i ∘ g.val, (D.assemble_smooth i).comp g.property⟩ :
        External.SmoothMap P a D.region) = f :=
      (principalBranchEquiv D P).injective ((principalBranchEquiv_assemble D i g).symm.trans
        ((congrArg (fun k => k ≫ SheafCoproductLocal.inclusion
          (fun j => object x (D.domain j)) i) hg).trans hb))
    exact ⟨g, congrFun (congrArg Subtype.val he)⟩
  · rintro ⟨g, hg⟩
    refine ⟨hat g.val g.property, ?_⟩
    have he : (⟨D.assemble i ∘ g.val, (D.assemble_smooth i).comp g.property⟩ :
        External.SmoothMap P a D.region) = f := Subtype.ext (funext hg)
    exact (principalBranchEquiv_assemble D i g).trans (congrArg (principalBranchEquiv D P) he)

abbrev RegionFamily :=
  {f : External.SmoothMap P a D.region //
    (∀ p, D.source (f.val p) = m.val p) ∧ (∀ p, D.target (f.val p) = n.val p)}

abbrev ArrowFamily :=
  {f : embedding.obj P ⟶ SmoothBranchRealization.arrowObject D //
    f ≫ SmoothBranchRealization.source D hs = hat m.val m.property ∧
    f ≫ SmoothBranchRealization.target D ht = hat n.val n.property}

/-- The arrows here land in the sheaf coproduct, so labels may vary locally. -/
abbrev BranchFamily :=
  {f : embedding.obj P ⟶ SmoothBranchRealization.branches D //
    f ≫ SmoothBranchRealization.branchSource D = hat m.val m.property ∧
    f ≫ SmoothBranchRealization.branchTarget D ht = hat n.val n.property}

/-- Endpoint equations are reflected by full faithfulness. -/
def regionArrowEquiv : RegionFamily D m n ≃ ArrowFamily D hs ht m n :=
  (principalMapEquiv P D.region).subtypeEquiv (by
    intro f
    change _ ↔ (hat f.val f.property ≫ map D.source (D.source_smooth hs) = _ ∧
      hat f.val f.property ≫ map D.target (D.target_smooth ht) = _)
    rw [hat_postcomp, hat_postcomp]
    have eqn {b : ℕ} {B : Type} [TopologicalSpace B] [ChartedSpace (Space b) B]
        [IsManifold (modelWithCorners b) ∞ B] (g h : External.SmoothMap P b B) :
        (∀ p, g.val p = h.val p) ↔ hat g.val g.property = hat h.val h.property := by
      constructor
      · intro e
        have : g = h := Subtype.ext (funext e)
        exact congrArg (principalMapEquiv P B) this
      · intro e
        exact congrFun (congrArg Subtype.val ((principalMapEquiv P B).injective e))
    exact and_congr (eqn ⟨D.source ∘ f.val, (D.source_smooth hs).comp f.property⟩ m)
      (eqn ⟨D.target ∘ f.val, (D.target_smooth ht).comp f.property⟩ n))

/-- Both directions retain the endpoint maps of the branch decomposition. -/
def arrowBranchEquiv : ArrowFamily D hs ht m n ≃ BranchFamily D ht m n where
  toFun f := ⟨f.val ≫ SmoothBranchRealization.decompose D, by
    simpa only [Category.assoc, SmoothBranchRealization.decompose_source D hs,
      SmoothBranchRealization.decompose_target] using f.property⟩
  invFun f := ⟨f.val ≫ SmoothBranchRealization.assembly D, by
    simpa only [Category.assoc, SmoothBranchRealization.assembly_source,
      SmoothBranchRealization.assembly_target] using f.property⟩
  left_inv f := by apply Subtype.ext; simp
  right_inv f := by apply Subtype.ext; simp

def regionBranchEquiv : RegionFamily D m n ≃ BranchFamily D ht m n :=
  (regionArrowEquiv D hs ht m n).trans (arrowBranchEquiv D hs ht m n)

end General

section Action
open Orbifolds.FiniteActionPresentation
open SmoothLocalDiffeomorphModel
variable {d : ℕ} {G M : Type} [Group G] [MulAction G M]
  [TopologicalSpace G] [DiscreteTopology G]
  [TopologicalSpace M] [ChartedSpace (Space d) M] [IsManifold (modelWithCorners d) ∞ M]

abbrev ActionModel := Model (source (G := G) (M := M)) (source_etale (modelWithCorners d))

def actionSource (a : ActionModel (d := d) (G := G) (M := M)) : M :=
  source (fromModel _ _ a)

def actionTarget (a : ActionModel (d := d) (G := G) (M := M)) : M :=
  target (fromModel _ _ a)

omit [Group G] [MulAction G M] in
theorem actionSource_smooth : ContMDiff (modelWithCorners d) (modelWithCorners d) ∞
    (actionSource (d := d) (G := G) (M := M)) := projection_smooth _ _

theorem actionTarget_smooth
    (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x)) :
    ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (actionTarget (d := d) (G := G) (M := M)) :=
  (target_etale (modelWithCorners d) smoothAction).contMDiff.comp (fromModel_smooth _ _)

variable {J : Type} {U V : Opens M}
  (D : Diagram (modelWithCorners d) (modelWithCorners d)
    (actionSource (d := d) (G := G) (M := M)) (actionTarget (d := d)) U V J)
  {P : Domain} (m : External.SmoothMap P d U) (n : External.SmoothMap P d V)

/-- Forget only the open-submanifold codomain, preserving the actual endpoint map. -/
def ambientMap {W : Opens M} (f : External.SmoothMap P d W) : External.SmoothMap P d M :=
  ⟨fun p => (f.val p).val, (contMDiff_subtype_val (U := W)).comp f.property⟩

/-- Native product-model families and induced-model region families have the same points. -/
def actionRegionEquiv :
    External.Family (G := G) P (ambientMap m) (ambientMap n) ≃ RegionFamily D m n where
  toFun f := ⟨⟨fun p => ⟨toModel _ _ (f.val p), by
      constructor
      · change source (f.val p) ∈ U
        rw [f.property.2.1 p]
        exact (m.val p).property
      · change target (f.val p) ∈ V
        rw [f.property.2.2 p]
        exact (n.val p).property⟩,
    (ContMDiff.subtypeVal_comp_iff D.region _).mp ((toModel_smooth (source (G := G) (M := M)) (source_etale (modelWithCorners d))).comp f.property.1)⟩,
    fun p => Subtype.ext (f.property.2.1 p), fun p => Subtype.ext (f.property.2.2 p)⟩
  invFun f := ⟨fun p => fromModel _ _ (f.val.val p).val,
    (fromModel_smooth _ _).comp ((contMDiff_subtype_val (U := D.region)).comp f.val.property),
    fun p => congrArg Subtype.val (f.property.1 p),
    fun p => congrArg Subtype.val (f.property.2 p)⟩
  left_inv f := rfl
  right_inv f := rfl

variable (smoothAction : ∀ g : G, ContMDiff (modelWithCorners d) (modelWithCorners d) ∞ (fun x : M => g • x))

/-- All smooth external arrow families, including locally varying labels. -/
def familyBranchEquiv :
    External.Family (G := G) P (ambientMap m) (ambientMap n) ≃
      BranchFamily D (actionTarget_smooth smoothAction) m n :=
  (actionRegionEquiv D m n).trans
    (regionBranchEquiv D actionSource_smooth (actionTarget_smooth smoothAction) m n)

theorem familyBranchEquiv_assembly
    (f : External.Family (G := G) P (ambientMap m) (ambientMap n)) :
    (familyBranchEquiv D m n smoothAction f).val ≫ SmoothBranchRealization.assembly D =
      hat (actionRegionEquiv D m n f).val.val (actionRegionEquiv D m n f).val.property :=
  principalBranchEquiv_assembly D P (actionRegionEquiv D m n f).val

/-- The quotient convention is inherited from the existing inverse-label comparison. -/
def chartBranchEquiv :
    External.ChartArrow smoothAction (ambientMap m) (ambientMap n) ≃
      BranchFamily D (actionTarget_smooth smoothAction) m n :=
  (External.smoothChartEquiv smoothAction (ambientMap m) (ambientMap n)).trans
    (familyBranchEquiv D m n smoothAction)

@[simp] theorem chartBranchEquiv_family
    (f : External.ChartArrow smoothAction (ambientMap m) (ambientMap n)) :
    chartBranchEquiv D m n smoothAction f =
      familyBranchEquiv D m n smoothAction
        (External.smoothChartEquiv smoothAction (ambientMap m) (ambientMap n) f) := rfl

/-- Recovering the quotient arrow gives the same native arrow family as inverse branch assembly. -/
theorem chartBranchEquiv_symm_family
    (b : BranchFamily D (actionTarget_smooth smoothAction) m n) :
    External.smoothChartEquiv smoothAction (ambientMap m) (ambientMap n)
      ((chartBranchEquiv D m n smoothAction).symm b) =
        (familyBranchEquiv D m n smoothAction).symm b := by
  exact (External.smoothChartEquiv smoothAction (ambientMap m) (ambientMap n)).apply_symm_apply _

/-- Restriction acts on the full coproduct arrow by precomposition. -/
theorem familyBranchEquiv_restrict {Q : Domain} (r : Q ⟶ P)
    (f : External.Family (G := G) P (ambientMap m) (ambientMap n)) :
    (familyBranchEquiv D (m.restrict r) (n.restrict r) smoothAction (f.restrict r)).val =
      embedding.map r ≫ (familyBranchEquiv D m n smoothAction f).val := by
  change hat _ _ ≫ _ = _ ≫ hat _ _ ≫ _
  rw [← Category.assoc, hat_precomp]
  rfl

/-- The comparison with the existing quotient arrows commutes with admitted test maps. -/
theorem chartBranchEquiv_restrict {Q : Domain} (r : Q ⟶ P)
    (f : External.ChartArrow smoothAction (ambientMap m) (ambientMap n)) :
    (chartBranchEquiv D (m.restrict r) (n.restrict r) smoothAction
      (External.restrictArrow smoothAction f r)).val =
      embedding.map r ≫ (chartBranchEquiv D m n smoothAction f).val := by
  have h := congrArg (fun a =>
    (familyBranchEquiv D (m.restrict r) (n.restrict r) smoothAction a).val)
    (External.smoothChartEquiv_restrict smoothAction f r)
  exact h.trans (familyBranchEquiv_restrict D m n smoothAction r _)

end Action
end SquareKit.SmoothBranchActionComparison
