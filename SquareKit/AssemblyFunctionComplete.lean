import SquareKit.AssemblyFunction
import SquareKit.AssemblyCutComplete

/-! Completeness as an actual isomorphism between function assemblies. -/
universe u
namespace Realizability.Assembly
open CategoryTheory

noncomputable def functionPrecompose {A B : Assembly.{u}} (f : Hom A B)
    (X : Assembly.{u}) : Hom (function B X) (function A X) :=
  curry ((pair (fst _ _) ((snd _ _).comp f)).comp (evaluation B X))

@[simp] theorem functionPrecompose_apply {A B X : Assembly.{u}} (f : Hom A B)
    (h : Hom B X) (a : A.Carrier) :
    ((functionPrecompose f X).toFun h).toFun a = h.toFun (f.toFun a) :=
  curry_apply _ _ _

noncomputable def cutRestriction (X : Assembly.{u}) :
    Hom (function finalCuts X) (function iterationCuts X) := functionPrecompose cutInclusion X

noncomputable def cutFunctionExtension {X : Assembly.{u}} (hc : CutComplete X) :
    Hom (function iterationCuts X) (function finalCuts X) :=
  curry (cutExtend hc (evaluation iterationCuts X))

/-- The inverse is tracked because extension applies in the function-object
context, not merely to each global function separately. -/
noncomputable def cutRestrictionIso {X : Assembly.{u}} (hc : CutComplete X) :
    function finalCuts X ≅ function iterationCuts X where
  hom := cutRestriction X
  inv := cutFunctionExtension hc
  hom_inv_id := by
    have he : uncurry ((cutRestriction X).comp (cutFunctionExtension hc)) =
        evaluation finalCuts X := by
      apply (hc (function finalCuts X)).1
      apply Hom.ext
      rintro ⟨f, ⟨n⟩⟩
      exact (curry_apply _ _ _).trans
        ((cutExtend_value hc (evaluation iterationCuts X) ((cutRestriction X).toFun f) n).trans
          (functionPrecompose_apply cutInclusion f ⟨n⟩))
    have hh := congrArg curry he
    rw [curry_uncurry] at hh
    exact hh.trans (Hom.ext fun f => Hom.ext fun a => curry_apply _ f a)
  inv_hom_id := by
    apply Hom.ext
    intro f
    apply Hom.ext
    rintro ⟨n⟩
    exact (curry_apply _ _ _).trans (cutExtend_value hc (evaluation iterationCuts X) f n)

/-- Conversely, the tracked inverse extends every context by currying. -/
theorem cutComplete_of_restrictionIso {X : Assembly.{u}}
    (e : function finalCuts X ≅ function iterationCuts X)
    (he : e.hom = cutRestriction X) : CutComplete X := by
  intro Γ
  constructor
  · intro h k hk
    have hr : (curry h).comp e.hom = (curry k).comp e.hom := by
      rw [he]
      apply Hom.ext
      intro γ
      apply Hom.ext
      rintro ⟨n⟩
      exact (functionPrecompose_apply cutInclusion _ _).trans
        ((curry_apply h γ ⟨some n⟩).trans
          ((congrArg (fun f => f.toFun (γ, ⟨n⟩)) hk).trans
            ((curry_apply k γ ⟨some n⟩).symm.trans
              (functionPrecompose_apply cutInclusion _ _).symm)))
    have hh : curry h = curry k := by
      have h' := congrArg (fun f => f.comp e.inv) hr
      change (curry h ≫ e.hom) ≫ e.inv = (curry k ≫ e.hom) ≫ e.inv at h'
      simpa using h'
    exact (uncurry_curry h).symm.trans ((congrArg uncurry hh).trans (uncurry_curry k))
  · intro h
    refine ⟨uncurry ((curry h).comp e.inv), ?_⟩
    have hi : e.inv.comp (cutRestriction X) = Hom.id _ := by
      rw [← he]
      exact e.inv_hom_id
    apply Hom.ext
    rintro ⟨γ, ⟨n⟩⟩
    have hv := congrArg (fun f => (f.toFun ((curry h).toFun γ)).toFun ⟨n⟩) hi
    exact (functionPrecompose_apply cutInclusion _ _).symm.trans
      (hv.trans (curry_apply h γ ⟨n⟩))

theorem cutComplete_iff_restrictionIso (X : Assembly.{u}) :
    CutComplete X ↔ ∃ e : function finalCuts X ≅ function iterationCuts X,
      e.hom = cutRestriction X :=
  ⟨fun hc => ⟨cutRestrictionIso hc, rfl⟩,
    fun ⟨e, he⟩ => cutComplete_of_restrictionIso e he⟩

end Realizability.Assembly
