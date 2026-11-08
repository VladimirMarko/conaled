import SquareKit.AssemblyFunctionComplete

/-! All-context completeness is closed under tracked exponentials and retracts. -/
universe u
namespace Realizability.Assembly

def exchange (Γ A B : Assembly.{u}) : Hom (prod (prod Γ A) B) (prod (prod Γ B) A) :=
  pair (pair ((fst _ _).comp (fst _ _)) (snd _ _)) ((fst _ _).comp (snd _ _))

theorem function_cutComplete {X : Assembly.{u}} (hc : CutComplete X) (A : Assembly.{u}) :
    CutComplete (function A X) := by
  intro Γ
  constructor
  · intro h k hk
    have hh : (exchange Γ A finalCuts).comp (uncurry h) =
        (exchange Γ A finalCuts).comp (uncurry k) := by
      apply (hc (prod Γ A)).1
      apply Hom.ext
      rintro ⟨⟨γ,a⟩, ⟨n⟩⟩
      exact congrArg (fun f => (f.toFun (γ, ⟨n⟩)).toFun a) hk
    apply Hom.ext
    rintro ⟨γ,t⟩
    apply Hom.ext
    intro a
    exact congrArg (fun f => f.toFun ((γ,a),t)) hh
  · intro h
    let g := (exchange Γ A iterationCuts).comp (uncurry h)
    refine ⟨curry ((exchange Γ finalCuts A).comp (cutExtend hc g)), ?_⟩
    apply Hom.ext
    rintro ⟨γ, ⟨n⟩⟩
    apply Hom.ext
    intro a
    exact (curry_apply _ _ _).trans (cutExtend_value hc g (γ,a) n)

theorem retract_cutComplete {X Y : Assembly.{u}} (hc : CutComplete X)
    (s : Hom Y X) (r : Hom X Y) (hsr : s.comp r = Hom.id Y) : CutComplete Y := by
  intro Γ
  constructor
  · intro h k hk
    have hh : h.comp s = k.comp s := (hc Γ).1 (congrArg (fun f => f.comp s) hk)
    apply Hom.ext
    intro x
    have h₁ := congrArg (fun f => f.toFun (h.toFun x)) hsr
    have h₂ := congrArg (fun f => f.toFun (k.toFun x)) hsr
    exact h₁.symm.trans ((congrArg (fun f : Hom (prod Γ finalCuts) X => r.toFun (f.toFun x)) hh).trans h₂)
  · intro h
    refine ⟨(cutExtend hc (h.comp s)).comp r, ?_⟩
    apply Hom.ext
    rintro ⟨γ, ⟨n⟩⟩
    exact (congrArg r.toFun (cutExtend_value hc (h.comp s) γ n)).trans
      (congrArg (fun f => f.toFun (h.toFun (γ, ⟨n⟩))) hsr)

end Realizability.Assembly
