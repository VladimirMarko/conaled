import SquareKit.SmoothOrdinaryCover
import Mathlib.CategoryTheory.Sites.Subcanonical

/-! Experimental ordinary intersections represented by actual all-stage
pullbacks. The proof uses the localization universal property over every smooth
algebra, before applying the subcanonical Yoneda embedding. -/
noncomputable section
open scoped ContDiff
namespace SquareKit.EuclideanOpen
open CategoryTheory CategoryTheory.Limits Opposite SmoothAlgebra SmoothPresentationSite Localization
variable (U : Domain) (g h : Free U.dimension)

abbrev overlap : Domain := subdomain (subdomain U g) h
abbrev overlapLeft : overlap U g h ⟶ subdomain U g := subInclusion (subdomain U g) h

def overlapRight : overlap U g h ⟶ subdomain U h :=
  {toFun x := ⟨x.val,mul_ne_zero (left_ne_zero_of_mul (left_ne_zero_of_mul x.property))
      (right_ne_zero_of_mul x.property)⟩
   smooth i := (OpenFunctions.representative_iff _ (fun x => x i) (fun _ => rfl)).mpr
     (contDiff_apply ℝ (fun _ : Fin U.dimension => ℝ) i).contDiffOn}

theorem overlap_square : overlapLeft U g h ≫ subInclusion U g = overlapRight U g h ≫ subInclusion U h :=
  OpenFunctions.Map.ext (fun _ => rfl)

theorem overlapRight_base (a : Free U.dimension) :
    Localization.pullback (overlapRight U g h) (principalBase (U.defining*h) a) =
      principalBase ((U.defining*g)*h) a := by
  apply (toOpen_bijective ((U.defining*g)*h)).injective
  apply OpenFunctions.ext
  intro x
  rw [Localization.pullback_apply,toOpen_base,toOpen_base]
  rfl

/-- All compatible maps into arbitrary smooth algebras factor uniquely. -/
theorem overlap_universal {B : Type*} [CommRing B] [Algebra ℝ B] [Structure B]
    (u : Hom (Principal (U.defining*g)) B) (v : Hom (Principal (U.defining*h)) B)
    (hc : u.comp (Localization.pullback (subInclusion U g)) =
      v.comp (Localization.pullback (subInclusion U h))) :
    ∃! w : Hom (Principal ((U.defining*g)*h)) B,
      w.comp (Localization.pullback (overlapLeft U g h))=u ∧
      w.comp (Localization.pullback (overlapRight U g h))=v := by
  have he : u.comp (principalBase (U.defining*g)) = v.comp (principalBase (U.defining*h)) := by
    have hh := congrArg (fun k : Hom (Principal U.defining) B => k.comp (principalBase U.defining)) hc
    simpa only [nested_pullback,← Hom.comp_assoc,nestedMap_base] using hh
  have hu : IsUnit (u (principalBase (U.defining*g) h)) := by
    have hv := base_isUnit (fun _ : Fin 1 => U.defining*h) 0
    change IsUnit (principalBase (U.defining*h) (U.defining*h)) at hv
    rw [(principalBase (U.defining*h)).map_mul,IsUnit.mul_iff] at hv
    have hv' := hv.2.map v.toAlgHom
    rw [show u (principalBase (U.defining*g) h) = v (principalBase (U.defining*h) h) from
      congrArg (fun k : Hom (Free U.dimension) B => k h) he]
    exact hv'
  let w := subLift (U.defining*g) h u hu
  have hl : w.comp (Localization.pullback (overlapLeft U g h)) = u := by
    rw [nested_pullback]
    exact subLift_base _ _ _ _
  have hr : w.comp (Localization.pullback (overlapRight U g h)) = v := by
    apply principal_unique (U.defining*h)
    apply Hom.ext
    intro a
    change w (Localization.pullback (overlapRight U g h) (principalBase (U.defining*h) a)) = _
    rw [overlapRight_base]
    have hw := congrArg (fun k : Hom (Free U.dimension) B => k a)
      (lift_base (fun _ : Fin 1 => (U.defining*g)*h) (u.comp (principalBase (U.defining*g)))
        (fun _ => by
          rw [(u.comp (principalBase (U.defining*g))).map_mul]
          exact ((base_isUnit (fun _ : Fin 1 => U.defining*g) 0).map u.toAlgHom).mul hu))
    exact hw.trans (congrArg (fun k : Hom (Free U.dimension) B => k a) he)
  refine ⟨w,⟨hl,hr⟩,?_⟩
  intro w' hw'
  apply sub_unique (U.defining*g) h
  simpa only [nested_pullback] using hw'.1.trans hl.symm

/-- The opposite code square is a pullback at all stages. -/
theorem overlap_site_pullback : IsPullback (toSite.map (overlapLeft U g h))
    (toSite.map (overlapRight U g h)) (toSite.map (subInclusion U g)) (toSite.map (subInclusion U h)) := by
  have hp : IsPushout
      (show code U ⟶ code (subdomain U g) from Localization.pullback (subInclusion U g))
      (show code U ⟶ code (subdomain U h) from Localization.pullback (subInclusion U h))
      (show code (subdomain U g) ⟶ code (overlap U g h) from Localization.pullback (overlapLeft U g h))
      (show code (subdomain U h) ⟶ code (overlap U g h) from Localization.pullback (overlapRight U g h)) := by
    have hu (c : PushoutCocone (show code U ⟶ code (subdomain U g) from Localization.pullback (subInclusion U g))
        (show code U ⟶ code (subdomain U h) from Localization.pullback (subInclusion U h))) :=
      overlap_universal U g h (smoothMap c.inl) (smoothMap c.inr) c.condition
    apply IsPushout.of_isColimit
      (PushoutCocone.IsColimit.mk
        (inl := show code (subdomain U g) ⟶ code (overlap U g h) from Localization.pullback (overlapLeft U g h))
        (inr := show code (subdomain U h) ⟶ code (overlap U g h) from Localization.pullback (overlapRight U g h))
        ?_ (fun c => (hu c).choose)
        (fun c => (hu c).choose_spec.1.1) (fun c => (hu c).choose_spec.1.2)
        (fun c a hl hr => (hu c).choose_spec.2 a ⟨hl,hr⟩))
    exact (Localization.pullback_comp (overlapLeft U g h) (subInclusion U g)).symm.trans
      ((congrArg (fun k : Map (overlap U g h) U => Localization.pullback k) (overlap_square U g h)).trans
        (Localization.pullback_comp (overlapRight U g h) (subInclusion U h)))
  exact hp.op.flip

theorem overlap_sheaf_pullback : IsPullback (embedding.map (overlapLeft U g h))
    (embedding.map (overlapRight U g h)) (embedding.map (subInclusion U g)) (embedding.map (subInclusion U h)) :=
  SmoothOpenSite.topology.yoneda.map_isPullback (overlap_site_pullback U g h)

end SquareKit.EuclideanOpen
