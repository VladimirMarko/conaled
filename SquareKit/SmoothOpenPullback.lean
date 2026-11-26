import SquareKit.SmoothOrdinaryPullbackCover
import SquareKit.SmoothOpenOverlap
/-! Inverse images of ordinary principal opens are pullbacks at every finite-presentation
stage. Real points detect units here; they are not used to detect equalities. -/
noncomputable section
open CategoryTheory
namespace SquareKit.SmoothPresentationSite
open SmoothAlgebra
theorem unit_of_real_points (A : Code) (a : Carrier A)
   (h : ∀ p : Hom (Carrier A) ℝ, p a ≠ 0) : IsUnit a := by
 have hc : OpenCover.Covers (fun _ : Fin 1 => a) := fun p => ⟨0, h p⟩
 obtain ⟨c, hc⟩ := (OpenCover.finite_iff A.equations (fun _ : Fin 1 => a)).mp hc
 simp only [Fin.sum_univ_one] at hc
 exact isUnit_iff_exists_inv.mpr ⟨c 0, by simpa only [mul_comm] using hc⟩
end SquareKit.SmoothPresentationSite
namespace SquareKit.EuclideanOpen
open CategoryTheory SmoothAlgebra SmoothAlgebra.Localization SmoothPresentationSite
theorem real_apply (U : Domain) (h : Hom (Principal U.defining) ℝ) (a : Principal U.defining) :
   h a = (toOpen U.defining a).val (realPoints U.defining h) := by
 exact ((toOpen_realPoint U.defining (realPoints U.defining h) a).trans
   (congrArg (fun k : Hom (Principal U.defining) ℝ => k a)
     ((realPoints U.defining).symm_apply_apply h))).symm
theorem real_map {U V : Domain} (f : U ⟶ V) (h : Hom (Principal U.defining) ℝ) :
   realPoints V.defining (h.comp (Localization.pullback f)) =
     (show Map U V from f) (realPoints U.defining h) := by
 apply Subtype.ext
 funext i
 change h (Localization.pullback f (principalBase V.defining (generator i))) = _
 exact (real_apply U h _).trans ((Localization.pullback_apply f _ _).trans
   (toOpen_base V.defining (generator i) _))
theorem inverse_unit {U V : Domain} (f : U ⟶ V) (q : freeAlgebra V.dimension)
   (B : Code) (u : Hom (Principal U.defining) (Carrier B))
   (hu : IsUnit (u (Localization.pullback f (principalBase V.defining q)))) :
   IsUnit (u (principalBase U.defining (inverseDefining f q))) := by
 apply unit_of_real_points
 intro p
 change (p.comp u) (principalBase U.defining (inverseDefining f q)) ≠ 0
 rw [point_base]
 apply (inverseDefining_iff f q _).mpr
 have hp := hu.map p.toAlgHom
 have hr := real_apply U (p.comp u) (Localization.pullback f (principalBase V.defining q))
 have he := hr.trans ((Localization.pullback_apply f _ _).trans
   (toOpen_base V.defining q _))
 exact he ▸ isUnit_iff_ne_zero.mp hp
end SquareKit.EuclideanOpen
namespace SquareKit.EuclideanOpen
open CategoryTheory CategoryTheory.Limits Opposite SmoothAlgebra SmoothAlgebra.Localization SmoothPresentationSite
theorem inverse_universal {U V : Domain} (f : U ⟶ V) (q : freeAlgebra V.dimension)
   (B : Code) (u : Hom (Principal U.defining) (Carrier B))
   (v : Hom (Principal (V.defining*q)) (Carrier B))
   (hc : u.comp (Localization.pullback f) = v.comp (Localization.pullback (subInclusion V q))) :
   ∃! w : Hom (Principal (U.defining * inverseDefining f q)) (Carrier B),
     w.comp (Localization.pullback (subInclusion U (inverseDefining f q))) = u ∧
     w.comp (Localization.pullback (inverseRestriction f q)) = v := by
 have hu : IsUnit (u (Localization.pullback f (principalBase V.defining q))) := by
   have he := congrArg (fun k : Hom (Principal V.defining) (Carrier B) => k (principalBase V.defining q)) hc
   change IsUnit ((u.comp (Localization.pullback f)) (principalBase V.defining q))
   rw [he, nested_pullback]
   exact (nested_unit V.defining q).map v.toAlgHom
 let w := subLift U.defining (inverseDefining f q) u (inverse_unit f q B u hu)
 have hl : w.comp (Localization.pullback (subInclusion U (inverseDefining f q))) = u := by
   rw [nested_pullback]
   exact subLift_base _ _ _ _
 have hr : w.comp (Localization.pullback (inverseRestriction f q)) = v := by
   apply sub_unique V.defining q
   rw [← nested_pullback V.defining q]
   have hs := (Localization.pullback_comp (inverseRestriction f q) (subInclusion V q)).symm.trans
     ((congrArg (fun k : Map _ _ => Localization.pullback k) (inverseRestriction_square f q)).trans
       (Localization.pullback_comp (subInclusion U (inverseDefining f q)) f))
   rw [← Hom.comp_assoc, hs, Hom.comp_assoc, hl]
   exact hc
 refine ⟨w, ⟨hl,hr⟩, ?_⟩
 intro w' hw'
 apply sub_unique U.defining (inverseDefining f q)
 simpa only [nested_pullback] using hw'.1.trans hl.symm
end SquareKit.EuclideanOpen
namespace SquareKit.EuclideanOpen
open CategoryTheory CategoryTheory.Limits Opposite SmoothAlgebra SmoothAlgebra.Localization SmoothPresentationSite
theorem inverse_site_pullback {U V : Domain} (f : U ⟶ V) (q : freeAlgebra V.dimension) :
   IsPullback (toSite.map (subInclusion U (inverseDefining f q)))
     (toSite.map (inverseRestriction f q)) (toSite.map f) (toSite.map (subInclusion V q)) := by
 have hp : IsPushout
     (show code V ⟶ code U from Localization.pullback f)
     (show code V ⟶ code (subdomain V q) from Localization.pullback (subInclusion V q))
     (show code U ⟶ code (subdomain U (inverseDefining f q)) from
       Localization.pullback (subInclusion U (inverseDefining f q)))
     (show code (subdomain V q) ⟶ code (subdomain U (inverseDefining f q)) from
       Localization.pullback (inverseRestriction f q)) := by
   have hu (c : PushoutCocone (show code V ⟶ code U from Localization.pullback f)
       (show code V ⟶ code (subdomain V q) from Localization.pullback (subInclusion V q))) :=
     inverse_universal f q c.pt (smoothMap c.inl) (smoothMap c.inr) c.condition
   apply IsPushout.of_isColimit
     (PushoutCocone.IsColimit.mk
       (inl := show code U ⟶ code (subdomain U (inverseDefining f q)) from
         Localization.pullback (subInclusion U (inverseDefining f q)))
       (inr := show code (subdomain V q) ⟶ code (subdomain U (inverseDefining f q)) from
         Localization.pullback (inverseRestriction f q))
       ?_ (fun c => (hu c).choose)
       (fun c => (hu c).choose_spec.1.1) (fun c => (hu c).choose_spec.1.2)
       (fun c a hl hr => (hu c).choose_spec.2 a ⟨hl,hr⟩))
   exact (Localization.pullback_comp (subInclusion U (inverseDefining f q)) f).symm.trans
     ((congrArg (fun k : Map _ _ => Localization.pullback k) (inverseRestriction_square f q).symm).trans
       (Localization.pullback_comp (inverseRestriction f q) (subInclusion V q)))
 exact hp.op.flip
theorem inverse_sheaf_pullback {U V : Domain} (f : U ⟶ V) (q : freeAlgebra V.dimension) :
   IsPullback (embedding.map (subInclusion U (inverseDefining f q)))
     (embedding.map (inverseRestriction f q)) (embedding.map f) (embedding.map (subInclusion V q)) :=
 SmoothOpenSite.topology.yoneda.map_isPullback (inverse_site_pullback f q)
end SquareKit.EuclideanOpen
