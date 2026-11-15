import SquareKit.AssemblyCutStrict
import SquareKit.AssemblyCutFinal

/-! All-context completeness and conditional extension-selected fixed points. -/
universe u
namespace Realizability.Assembly
open CategoryTheory

noncomputable def cutContextInclusion (Γ : Assembly.{u}) :
    Hom (prod Γ iterationCuts) (prod Γ finalCuts) :=
  pair (fst _ _) ((snd _ _).comp cutInclusion)

/-- Uniform completeness is restriction bijectivity in every assembly context.
No concrete object is asserted complete by this definition. -/
def CutComplete (X : Assembly.{u}) : Prop := ∀ Γ : Assembly.{u},
  Function.Bijective (fun H : Hom (prod Γ finalCuts) X => (cutContextInclusion Γ).comp H)

noncomputable def cutExtend {X Γ : Assembly.{u}} (hc : CutComplete X)
    (h : Hom (prod Γ iterationCuts) X) : Hom (prod Γ finalCuts) X :=
  ((hc Γ).2 h).choose

theorem cutExtend_restrict {X Γ : Assembly.{u}} (hc : CutComplete X)
    (h : Hom (prod Γ iterationCuts) X) :
    (cutContextInclusion Γ).comp (cutExtend hc h) = h := ((hc Γ).2 h).choose_spec

theorem cutExtend_value {X Γ : Assembly.{u}} (hc : CutComplete X)
    (h : Hom (prod Γ iterationCuts) X) (γ : Γ.Carrier) (n : Nat) :
    (cutExtend hc h).toFun (γ, ⟨some n⟩) = h.toFun (γ, ⟨n⟩) :=
  congrArg (fun f => f.toFun (γ, ⟨n⟩)) (cutExtend_restrict hc h)

theorem cutExtend_unique {X Γ : Assembly.{u}} (hc : CutComplete X)
    (h : Hom (prod Γ iterationCuts) X) (H : Hom (prod Γ finalCuts) X)
    (he : (cutContextInclusion Γ).comp H = h) : H = cutExtend hc h :=
  (hc Γ).1 (he.trans (cutExtend_restrict hc h).symm)

/-- Evaluating the uniquely extended iteration at infinity gives a tracked
map of parameters, rather than merely separate values for each parameter. -/
noncomputable def cutSelected {Γ : Assembly.{u}} (X : Monad.Algebra programLiftMonad.{u})
    (hc : CutComplete X.A) (g : Hom (prod Γ X.A) X.A) : Hom Γ X.A :=
  (pair (Hom.id Γ) (cutInfinity Γ)).comp (cutExtend hc (strictIteration X g))

theorem cutExtension_successor {Γ : Assembly.{u}} (X : Monad.Algebra programLiftMonad.{u})
    (hc : CutComplete X.A) (g : Hom (prod Γ X.A) X.A) :
    (pair (fst Γ finalCuts) ((snd Γ finalCuts).comp finalSuccessor)).comp
        (cutExtend hc (strictIteration X g)) =
      (pair (fst Γ finalCuts) (cutExtend hc (strictIteration X g))).comp g := by
  apply (hc Γ).1
  apply Hom.ext
  rintro ⟨γ, ⟨n⟩⟩
  exact (cutExtend_value hc (strictIteration X g) γ (n + 1)).trans
    ((strictIteration_succ X g γ n).trans
      (congrArg (fun x => g.toFun (γ,x)) (cutExtend_value hc (strictIteration X g) γ n)).symm)

theorem cutSelected_fixed {Γ : Assembly.{u}} (X : Monad.Algebra programLiftMonad.{u})
    (hc : CutComplete X.A) (g : Hom (prod Γ X.A) X.A) :
    (pair (Hom.id Γ) (cutSelected X hc g)).comp g = cutSelected X hc g := by
  apply Hom.ext
  intro γ
  exact (congrArg (fun f => f.toFun (γ, ⟨none⟩)) (cutExtension_successor X hc g)).symm

/-- Uniform iteration commutes with a strict algebra morphism that intertwines
both context-dependent endomaps. -/
theorem strictIteration_transport {Γ : Assembly.{u}}
    (X Y : Monad.Algebra programLiftMonad.{u}) (t : Monad.Algebra.Hom X Y)
    (g : Hom (prod Γ X.A) X.A) (h : Hom (prod Γ Y.A) Y.A)
    (ht : g.comp t.f = (pair (fst _ _) ((snd _ _).comp t.f)).comp h) :
    (strictIteration X g).comp t.f = strictIteration Y h := by
  apply Hom.ext
  rintro ⟨γ, ⟨n⟩⟩
  induction n with
  | zero => exact (congrArg (fun f => f.toFun none) t.h).symm
  | succ n ih =>
    change t.f.toFun ((strictIteration X g).toFun (γ, ⟨n + 1⟩)) =
      (strictIteration Y h).toFun (γ, ⟨n + 1⟩)
    rw [strictIteration_succ, strictIteration_succ]
    exact (congrArg (fun f => f.toFun (γ, (strictIteration X g).toFun (γ, ⟨n⟩))) ht).trans
      (congrArg (fun y => h.toFun (γ,y)) ih)

theorem cutSelected_transport {Γ : Assembly.{u}}
    (X Y : Monad.Algebra programLiftMonad.{u}) (cx : CutComplete X.A) (cy : CutComplete Y.A)
    (t : Monad.Algebra.Hom X Y) (g : Hom (prod Γ X.A) X.A) (h : Hom (prod Γ Y.A) Y.A)
    (ht : g.comp t.f = (pair (fst _ _) ((snd _ _).comp t.f)).comp h) :
    (cutSelected X cx g).comp t.f = cutSelected Y cy h := by
  have he : (cutExtend cx (strictIteration X g)).comp t.f = cutExtend cy (strictIteration Y h) := by
    apply cutExtend_unique cy
    exact (congrArg (fun k => k.comp t.f) (cutExtend_restrict cx (strictIteration X g))).trans
      (strictIteration_transport X Y t g h ht)
  exact congrArg (fun k => (pair (Hom.id Γ) (cutInfinity Γ)).comp k) he

/-- Reindex a product context by an actual tracked map. -/
def contextMap {Γ Δ : Assembly.{u}} (f : Hom Δ Γ) (A : Assembly.{u}) :
    Hom (prod Δ A) (prod Γ A) := pair ((fst _ _).comp f) (snd _ _)

theorem cutExtend_substitution {X Γ Δ : Assembly.{u}} (hc : CutComplete X)
    (h : Hom (prod Γ iterationCuts) X) (f : Hom Δ Γ) :
    (contextMap f finalCuts).comp (cutExtend hc h) =
      cutExtend hc ((contextMap f iterationCuts).comp h) := by
  apply cutExtend_unique hc
  apply Hom.ext
  rintro ⟨δ, ⟨n⟩⟩
  exact cutExtend_value hc h (f.toFun δ) n

theorem strictIteration_substitution {Γ Δ : Assembly.{u}} (X : Monad.Algebra programLiftMonad.{u})
    (g : Hom (prod Γ X.A) X.A) (f : Hom Δ Γ) :
    (contextMap f iterationCuts).comp (strictIteration X g) =
      strictIteration X ((contextMap f X.A).comp g) := by
  apply Hom.ext
  rintro ⟨δ, ⟨n⟩⟩
  induction n with
  | zero => rfl
  | succ n ih =>
    change (strictIteration X g).toFun (f.toFun δ, ⟨n + 1⟩) =
      (strictIteration X ((contextMap f X.A).comp g)).toFun (δ, ⟨n + 1⟩)
    rw [strictIteration_succ, strictIteration_succ]
    exact congrArg (fun a => g.toFun (f.toFun δ,a)) ih

theorem cutSelected_substitution {Γ Δ : Assembly.{u}} (X : Monad.Algebra programLiftMonad.{u})
    (hc : CutComplete X.A) (g : Hom (prod Γ X.A) X.A) (f : Hom Δ Γ) :
    f.comp (cutSelected X hc g) = cutSelected X hc ((contextMap f X.A).comp g) := by
  have he := (cutExtend_substitution hc (strictIteration X g) f).trans
    (congrArg (cutExtend hc) (strictIteration_substitution X g f))
  apply Hom.ext
  intro δ
  exact congrArg (fun k => k.toFun (δ, ⟨none⟩)) he

/-- Identity has many fixed points in general; extension selects its algebra's
bottom, rather than an arbitrary solution of the fixed-point equation. -/
theorem cutSelected_identity {Γ : Assembly.{u}} (X : Monad.Algebra programLiftMonad.{u})
    (hc : CutComplete X.A) (γ : Γ.Carrier) :
    (cutSelected X hc (snd Γ X.A)).toFun γ = X.a.toFun none := by
  let b : Hom Γ X.A := (cutZero Γ).comp (strictIter X (Hom.id X.A))
  have hb : ∀ γ, b.toFun γ = X.a.toFun none := fun _ => strictIter_zero X _
  have hi : ∀ n γ, (strictIteration X (snd Γ X.A)).toFun (γ, ⟨n⟩) = X.a.toFun none := by
    intro n
    induction n with
    | zero => exact fun γ => strictIteration_zero X _ γ
    | succ n ih => exact fun γ => (strictIteration_succ X _ γ n).trans (ih γ)
  have he : (fst Γ finalCuts).comp b = cutExtend hc (strictIteration X (snd Γ X.A)) := by
    apply cutExtend_unique hc
    apply Hom.ext
    rintro ⟨γ, ⟨n⟩⟩
    exact (hb γ).trans (hi n γ).symm
  exact (congrArg (fun h => h.toFun (γ, ⟨none⟩)) he).symm.trans (hb γ)

end Realizability.Assembly
