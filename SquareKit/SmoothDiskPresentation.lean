import Applications.Orbifolds.DiskPresentation
import SquareKit.SmoothOrdinaryQuotient
import SquareKit.SmoothManifoldPrincipalMaps
import SquareKit.SmoothOrdinaryCoverRecovery

/-! Comparison of ordinary quotient chart arrows with smooth families of arrows
in the external disk action presentation. The forward action label is the
inverse of the quotient's right-translation label. -/
noncomputable section
open CategoryTheory
open scoped Manifold ContDiff
namespace SquareKit.SmoothDiskPresentation
open EuclideanOpen SmoothOrdinaryQuotient SmoothQuarterTurnArcs
open SmoothQuarterTurnQuotient SheafActionQuotient Orbifolds.QuarterTurn
namespace ForwardLabel

/-- Invert the right-translation convention for every group, without commutativity. -/
def label {G : Type} [Group G] {M : Sheaf SmoothOpenSite.topology Type}
    {a : Action (SmoothOpenSite.locallyConstantGroup G) M} {U : Domain}
    {m n : embedding.obj U ⟶ M} (f : Arrow (chart a m) (chart a n)) :
    LocallyConstant (Points U) G := (ordinaryArrowLabel f)⁻¹

theorem comp {G : Type} [Group G] {M : Sheaf SmoothOpenSite.topology Type}
    {a : Action (SmoothOpenSite.locallyConstantGroup G) M} {U : Domain}
    {m n p : embedding.obj U ⟶ M}
    (f : Arrow (chart a m) (chart a n)) (g : Arrow (chart a n) (chart a p)) (x : Points U) :
    label (f.comp g) x = label g x * label f x := by
  change (ordinaryArrowLabel (f.comp g) x)⁻¹ = _
  rw [ordinaryArrowLabel_comp, mul_inv_rev]
  rfl

theorem ident {G : Type} [Group G] {M : Sheaf SmoothOpenSite.topology Type}
    (a : Action (SmoothOpenSite.locallyConstantGroup G) M) {U : Domain}
    (m : embedding.obj U ⟶ M) (x : Points U) : label (Arrow.ident (chart a m)) x = (1 : G) := by
  change (ordinaryArrowLabel (Arrow.ident _) x)⁻¹ = _
  rw [ordinaryArrowLabel_ident, inv_one]

theorem inverse {G : Type} [Group G] {M : Sheaf SmoothOpenSite.topology Type}
    {a : Action (SmoothOpenSite.locallyConstantGroup G) M} {U : Domain}
    {m n : embedding.obj U ⟶ M} (f : Arrow (chart a m) (chart a n)) (x : Points U) :
    label f.inverse x = (label f x)⁻¹ := by
  change (ordinaryArrowLabel f.inverse x)⁻¹ = _
  rw [ordinaryArrowLabel_inverse]
  rfl

theorem restriction {G : Type} [Group G] {M : Sheaf SmoothOpenSite.topology Type}
    {a : Action (SmoothOpenSite.locallyConstantGroup G) M} {U V : Domain}
    {m n : embedding.obj V ⟶ M} (f : Arrow (chart a m) (chart a n))
    (r : U ⟶ V) (x : Points U) :
    label (m := embedding.map r ≫ m) (n := embedding.map r ≫ n)
      (f.reindex (embedding.map r)) x = label f ((show Map _ _ from r) x) := by
  exact congrArg Inv.inv (ordinaryArrowLabel_reindex f r x)
end ForwardLabel

abbrev diskValue {U : Domain} (m : U ⟶ diskDomain) (x : Points U) : Disk :=
  diskPoints ((show Map _ _ from m) x)

/-- Independent forward-arrow specification, retaining its label at every point. -/
def Family (U : Domain) (m n : U ⟶ diskDomain) :=
  {g : LocallyConstant (Points U) C4 // ∀ x, g x • diskValue m x = diskValue n x}

def chartEquiv (U : Domain) (m n : U ⟶ diskDomain) :
    Arrow (chart diskRepresentation.action (embedding.map m))
      (chart diskRepresentation.action (embedding.map n)) ≃ Family U m n :=
  (diskChartArrowEquiv U m n).trans {
    toFun k := ⟨k.val⁻¹, fun x => by
      have h := congrArg diskPoints (k.property x)
      change diskPoints (diskPoints.symm (k.val x • diskValue n x)) = diskValue m x at h
      rw [Equiv.apply_symm_apply] at h
      exact (inv_smul_eq_iff).mpr h.symm⟩
    invFun g := ⟨g.val⁻¹, fun x => by
      apply diskPoints.injective
      change diskPoints (diskPoints.symm ((g.val x)⁻¹ • diskValue n x)) = diskValue m x
      rw [Equiv.apply_symm_apply]
      exact (inv_smul_eq_iff).mpr (g.property x).symm⟩
    left_inv k := Subtype.ext (inv_inv k.val)
    right_inv g := Subtype.ext (inv_inv g.val) }

@[simp] theorem chartEquiv_label (U : Domain) (m n : U ⟶ diskDomain)
    (f : Arrow (chart diskRepresentation.action (embedding.map m))
      (chart diskRepresentation.action (embedding.map n))) :
    (chartEquiv U m n f).val = ForwardLabel.label f := rfl

namespace Family
variable {U : Domain} {m n p : U ⟶ diskDomain}

def arrow (f : Family U m n) (x : Points U) : DiskPresentation.Arrow :=
  (f.val x, diskValue m x)

@[simp] theorem source_arrow (f : Family U m n) (x : Points U) :
    DiskPresentation.source (f.arrow x) = diskValue m x := rfl
@[simp] theorem target_arrow (f : Family U m n) (x : Points U) :
    DiskPresentation.target (f.arrow x) = diskValue n x := f.property x

def ident (m : U ⟶ diskDomain) : Family U m m :=
  ⟨LocallyConstant.const _ 1, fun _x => one_smul _ _⟩
def comp (f : Family U m n) (g : Family U n p) : Family U m p :=
  ⟨g.val * f.val, fun x => by
    change (g.val x * f.val x) • _ = _
    rw [mul_smul, f.property, g.property]⟩
def inverse (f : Family U m n) : Family U n m :=
  ⟨f.val⁻¹, fun x => (inv_smul_eq_iff).mpr (f.property x).symm⟩

def hom (f : Family U m n) (x : Points U) :
    (show ActionCategory C4 Disk from diskValue m x) ⟶
      (show ActionCategory C4 Disk from diskValue n x) :=
  Functor.Elements.homMk (f.val x) (f.property x)

theorem hom_comp (f : Family U m n) (g : Family U n p) (x : Points U) :
    (f.comp g).hom x = f.hom x ≫ g.hom x := rfl

theorem arrow_comp (f : Family U m n) (g : Family U n p) (x : Points U) :
    (f.comp g).arrow x = DiskPresentation.compose (f.val x) (g.val x) (diskValue m x) := rfl

theorem arrow_inverse (f : Family U m n) (x : Points U) :
    f.inverse.arrow x = DiskPresentation.inverse (f.arrow x) := by
  change ((f.val x)⁻¹, diskValue n x) = ((f.val x)⁻¹, f.val x • diskValue m x)
  exact Prod.ext rfl (f.property x).symm

/-- The comparison produces smooth maps into the actual arrow manifold. -/
theorem arrow_smooth (f : Family U m n) :
    ContMDiff (ManifoldRealization.Model U.dimension) DiskPresentation.arrowModel ∞
      (show ManifoldRealization.ordinaryOpen U → DiskPresentation.Arrow from f.arrow) := by
  have hl : ContMDiff (ManifoldRealization.Model U.dimension) 𝓘(ℝ, Fin 0 → ℝ) ∞
      (show ManifoldRealization.ordinaryOpen U → C4 from f.val) := by
    intro x
    exact contMDiffAt_const.congr_of_eventuallyEq (f.val.isLocallyConstant.eventually_eq x)
  have hd : ContMDiff (ManifoldRealization.Model diskDomain.dimension) 𝓘(ℝ, ℂ) ∞
      (show ManifoldRealization.ordinaryOpen diskDomain → Disk from diskPoints) := by
    apply (ContMDiff.subtypeVal_comp_iff disk _).mp
    exact complexCoordinates.contDiff.contMDiff.comp contMDiff_subtype_val
  exact hl.prodMk (hd.comp (ManifoldRealization.openMap_contMDiff m))

def restrict {V : Domain} (f : Family U m n) (r : V ⟶ U) :
    Family V (r ≫ m) (r ≫ n) :=
  ⟨LocallyConstant.comap ⟨(show Map V U from r).toFun, map_continuous r⟩ f.val,
    fun x => f.property ((show Map _ _ from r) x)⟩

@[simp] theorem arrow_restrict {V : Domain} (f : Family U m n) (r : V ⟶ U) (x : Points V) :
    (f.restrict r).arrow x = f.arrow ((show Map _ _ from r) x) := rfl

@[simp] theorem hom_ident (m : U ⟶ diskDomain) (x : Points U) :
    (ident m).hom x = 𝟙 (show ActionCategory C4 Disk from diskValue m x) := rfl

theorem hom_inverse (f : Family U m n) (x : Points U) :
    f.inverse.hom x = Groupoid.inv (f.hom x) := rfl

theorem comp_assoc {q : U ⟶ diskDomain} (f : Family U m n) (g : Family U n p)
    (h : Family U p q) : (f.comp g).comp h = f.comp (g.comp h) :=
  Subtype.ext (mul_assoc h.val g.val f.val).symm

@[simp] theorem ident_comp (f : Family U m n) : (ident m).comp f = f :=
  Subtype.ext (mul_one f.val)
@[simp] theorem comp_ident (f : Family U m n) : f.comp (ident n) = f :=
  Subtype.ext (one_mul f.val)
@[simp] theorem inverse_comp (f : Family U m n) : f.inverse.comp f = ident n :=
  Subtype.ext (mul_inv_cancel f.val)
@[simp] theorem comp_inverse (f : Family U m n) : f.comp f.inverse = ident m :=
  Subtype.ext (inv_mul_cancel f.val)

@[simp] theorem restrict_ident (f : Family U m n) : f.restrict (𝟙 U) = f := rfl

theorem restrict_comp {V W : Domain} (f : Family U m n) (r : V ⟶ U) (s : W ⟶ V) :
    (f.restrict r).restrict s = f.restrict (s ≫ r) := rfl

theorem restrict_composition {V : Domain} (f : Family U m n) (g : Family U n p) (r : V ⟶ U) :
    (f.comp g).restrict r = (f.restrict r).comp (g.restrict r) := rfl

theorem restrict_inverse {V : Domain} (f : Family U m n) (r : V ⟶ U) :
    f.inverse.restrict r = (f.restrict r).inverse := rfl

end Family

theorem chartEquiv_ident (U : Domain) (m : U ⟶ diskDomain) :
    chartEquiv U m m (Arrow.ident _) = Family.ident m := by
  apply Subtype.ext
  exact DFunLike.ext _ _ (ForwardLabel.ident _ _)

theorem chartEquiv_comp (U : Domain) (m n p : U ⟶ diskDomain)
    (f : Arrow (chart diskRepresentation.action (embedding.map m))
      (chart diskRepresentation.action (embedding.map n)))
    (g : Arrow (chart diskRepresentation.action (embedding.map n))
      (chart diskRepresentation.action (embedding.map p))) :
    chartEquiv U m p (f.comp g) = (chartEquiv U m n f).comp (chartEquiv U n p g) := by
  apply Subtype.ext
  exact DFunLike.ext _ _ (ForwardLabel.comp f g)

theorem chartEquiv_inverse (U : Domain) (m n : U ⟶ diskDomain)
    (f : Arrow (chart diskRepresentation.action (embedding.map m))
      (chart diskRepresentation.action (embedding.map n))) :
    chartEquiv U n m f.inverse = (chartEquiv U m n f).inverse := by
  apply Subtype.ext
  exact DFunLike.ext _ _ (ForwardLabel.inverse f)

/-- Restricting the actual quotient arrow gives the same external arrow map.
The explicit endpoints avoid identifying embedding functor equalities by fiat. -/
theorem chartEquiv_restriction {U V : Domain} (r : U ⟶ V) (m n : V ⟶ diskDomain)
    (f : Arrow (chart diskRepresentation.action (embedding.map m))
      (chart diskRepresentation.action (embedding.map n))) (x : Points U) :
    (ForwardLabel.label (m := embedding.map r ≫ embedding.map m)
        (n := embedding.map r ≫ embedding.map n) (f.reindex (embedding.map r)) x,
      diskValue (r ≫ m) x) = (chartEquiv V m n f).arrow ((show Map _ _ from r) x) := by
  exact Prod.ext (ForwardLabel.restriction f r x) rfl

/-- Smooth arrow maps with specified source and target, independently of labels. -/
def SmoothFamily (U : Domain) (m n : U ⟶ diskDomain) :=
  {f : ManifoldRealization.ordinaryOpen U → DiskPresentation.Arrow //
    ContMDiff (ManifoldRealization.Model U.dimension) DiskPresentation.arrowModel ∞ f ∧
    (∀ x, DiskPresentation.source (f x) = diskValue m x) ∧
    (∀ x, DiskPresentation.target (f x) = diskValue n x)}

/-- Local constancy is exactly the smooth discrete-label condition. -/
def familySmoothEquiv (U : Domain) (m n : U ⟶ diskDomain) : Family U m n ≃ SmoothFamily U m n where
  toFun f := ⟨f.arrow, f.arrow_smooth, f.source_arrow, f.target_arrow⟩
  invFun f := ⟨⟨fun x => (f.val x).1,
    (IsLocallyConstant.iff_continuous _).mpr f.property.1.continuous.fst⟩, fun x => by
      change (f.val x).1 • diskValue m x = _
      rw [← f.property.2.1 x]
      exact f.property.2.2 x⟩
  left_inv f := Subtype.ext rfl
  right_inv f := by
    apply Subtype.ext
    funext x
    exact Prod.ext rfl (f.property.2.1 x).symm

/-- All smooth arrow families between these ordinary disk maps are recovered. -/
def smoothChartEquiv (U : Domain) (m n : U ⟶ diskDomain) :
    Arrow (chart diskRepresentation.action (embedding.map m))
      (chart diskRepresentation.action (embedding.map n)) ≃ SmoothFamily U m n :=
  (chartEquiv U m n).trans (familySmoothEquiv U m n)

/-- Canonical recovery through either split cover has the same external family.
This concerns canonical data of global chart objects, not arbitrary descent data. -/
theorem canonicalRecovery_comparison (U : Domain) (m n : U ⟶ diskDomain)
    (A B : SplitSheaf.Ty (embedding.obj U))
    [Presheaf.IsLocallySurjective SmoothOpenSite.topology (SplitSheaf.p A).hom]
    [Presheaf.IsLocallySurjective SmoothOpenSite.topology (SplitSheaf.p B).hom]
    (f : Descent.Map
      (Descent.canonicalDatum A (chart diskRepresentation.action (embedding.map m)))
      (Descent.canonicalDatum A (chart diskRepresentation.action (embedding.map n)))) :
    smoothChartEquiv U m n (Descent.canonicalArrowEquiv B _ _
      (Descent.recoveryArrowComparison A B _ _ f)) =
    smoothChartEquiv U m n (Descent.canonicalArrowEquiv A _ _ f) := by
  rw [Descent.recoveryArrowComparison_commutes]

end SquareKit.SmoothDiskPresentation
