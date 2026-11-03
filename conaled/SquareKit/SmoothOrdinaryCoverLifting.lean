import SquareKit.SmoothOrdinaryPullbackCover

/-! Ordinary neighborhoods refine covers of the finite-presentation site. -/
noncomputable section
open CategoryTheory Opposite
open scoped ContDiff
namespace SquareKit.EuclideanOpen
open SmoothAlgebra SmoothPresentationSite

theorem function_isUnit (U : Domain) (b : Functions U) (hb : ∀ x, b.val x ≠ 0) :
    IsUnit b := by
  let c : Functions U := ⟨fun x => (b.val x)⁻¹, by
    apply (OpenFunctions.representative_iff _ (fun x => (OpenFunctions.extendZero (Points U) b.val x)⁻¹)
      (fun x => congrArg Inv.inv (OpenFunctions.extendZero_mem b.val x))).mpr
    exact b.property.inv (fun x hx => (OpenFunctions.extendZero_mem b.val ⟨x, hx⟩) ▸ hb ⟨x, hx⟩)⟩
  apply isUnit_iff_exists_inv.mpr
  refine ⟨c, ?_⟩
  apply OpenFunctions.ext
  intro x
  exact mul_inv_cancel₀ (hb x)

theorem element_isUnit (U : Domain) (a : Localization.Principal U.defining)
    (ha : ∀ x, (Localization.toOpen U.defining a).val x ≠ 0) : IsUnit a := by
  have h := (function_isUnit U _ ha).map (Localization.fromOpen U.defining).toAlgHom
  have he := (Localization.openEquiv U.defining).symm_apply_apply a
  change IsUnit (Localization.fromOpen U.defining (Localization.toOpen U.defining a)) at h
  exact he ▸ h

def functionMap (U : Domain) (b : Functions U) : U ⟶ full 1 where
  toFun x := ⟨fun _ => b.val x, one_ne_zero⟩
  smooth _ := b.property

/-- An element nonzero at an ordinary point becomes a unit on an ordinary
principal neighborhood of that point. -/
theorem local_unit (U : Domain) (a : Localization.Principal U.defining)
    (x : Points U) (ha : (Localization.toOpen U.defining a).val x ≠ 0) :
    ∃ q : Free U.dimension, q.val x.val ≠ 0 ∧
      IsUnit (Localization.pullback (subInclusion U q) a) := by
  let f := functionMap U (Localization.toOpen U.defining a)
  let q := inverseDefining f (generator 0)
  refine ⟨q, (inverseDefining_iff f (generator 0) x).mpr ha, ?_⟩
  apply element_isUnit (subdomain U q)
  intro y
  rw [Localization.pullback_apply]
  exact (inverseDefining_iff f (generator 0) _).mp (right_ne_zero_of_mul y.property)

/-- A covering sieve, pulled back along any ordinary test, contains an ordinary
coordinate inclusion around every point of the test domain. -/
theorem covering_local_inclusion {X : Site} (S : Sieve X)
    (hS : S ∈ SmoothOpenSite.topology X) (U : Domain)
    (f : toSite.obj U ⟶ X) (x : Points U) :
    ∃ q : Free U.dimension, ∃ u : (⟨U.dimension, q⟩ : Domain) ⟶ U,
      (∀ y, ((show Map _ _ from u) y).val = y.val) ∧
      (∃ y, (show Map _ _ from u) y = x) ∧ S (toSite.map u ≫ f) := by
  induction hS generalizing U with
  | of X R hR =>
    obtain ⟨ι, s, hs, rfl⟩ := hR
    let point := (Localization.realPoints U.defining).symm x
    obtain ⟨i, hi⟩ := hs (Hom.comp point f.unop)
    let a : Localization.Principal U.defining := (smoothMap f.unop) (s i)
    have ha : (Localization.toOpen U.defining a).val x ≠ 0 := by
      exact (Localization.toOpen_realPoint U.defining x a) ▸ hi
    obtain ⟨q, hq, hu⟩ := local_unit U a x ha
    let g : X.unop ⟶ code (subdomain U q) := f.unop ≫ Localization.pullback (subInclusion U q)
    let l : localization X.unop (s i) ⟶ code (subdomain U q) :=
      PresentedLocalization.lift X.unop.equations
        (PresentedLocalization.representative X.unop.equations (s i)) g
        (by rw [PresentedLocalization.representative_eq]; exact hu)
    refine ⟨U.defining * q, subInclusion U q, fun _ => rfl,
      ⟨⟨x.val, mul_ne_zero x.property hq⟩, rfl⟩, ?_⟩
    refine ⟨_, l.op, (localizationBase X.unop (s i)).op, ⟨i⟩, ?_⟩
    exact congrArg Quiver.Hom.op
      (PresentedLocalization.lift_base X.unop.equations
        (PresentedLocalization.representative X.unop.equations (s i)) g
        (by rw [PresentedLocalization.representative_eq]; exact hu))
  | top X =>
    exact ⟨U.defining, 𝟙 U, fun _ => rfl, ⟨x, rfl⟩, trivial⟩
  | transitive X R S hR hS ihR ihS =>
    obtain ⟨q, u, hu, ⟨y, hy⟩, hr⟩ := ihR U f x
    obtain ⟨p, v, hv, ⟨z, hz⟩, hs⟩ := ihS hr ⟨U.dimension, q⟩ (𝟙 _) y
    refine ⟨p, v ≫ u, fun t => (hu _).trans (hv t),
      ⟨z, (congrArg (show Map _ _ from u) hz).trans hy⟩, ?_⟩
    simpa only [Sieve.pullback_apply, Category.comp_id, toSite.map_comp, Category.assoc] using hs

end SquareKit.EuclideanOpen
