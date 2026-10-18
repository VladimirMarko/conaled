import SquareKit.Internal.DependentSheafComparison
import Examples.SplitNative

/-! Experimental source → sheaf → native stage comparison. The source proof
is reused; native functions below are values of constructed natural sheaf maps. -/
noncomputable section
namespace Examples.DependentSourceNative
open CategoryTheory Opposite SquareKit
open Internal.DependentStructural Internal.DependentStructural.SheafSem
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (M : Model.{u,v,w} J)
variable {l m n : Nat} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx l}

theorem pairing_native (σ : Sub Δ Γ) (τ : Sub Ξ Δ) (b : Base n)
    (t : Tm Δ (.family (b.sub σ.base))) (U : Cᵒᵖ) (x : (context M Ξ).carrier.obj.obj U) :
    DependentSquares.extend (A := SplitNative.family (type M Γ (.family b)) U)
      ((substitution M σ).hom.app U) (SplitNative.term (pairTerm M σ b t) U)
      ((substitution M τ).hom.app U x) =
    DependentSquares.extend (A := SplitNative.family (type M Γ (.family b)) U)
      ((substitution M (Sub.comp σ τ)).hom.app U)
      (SplitNative.term (pairTerm M (Sub.comp σ τ) b (substitutedArgument σ τ b t)) U) x := by
  have h := congrArg (fun k => k.hom.app U x) (derived_pairing M σ τ b t)
  have hl := congrArg (fun k => (substitution M τ ≫ k).hom.app U x) (pairing M σ b t)
  have hr := congrArg (fun k => k.hom.app U x)
    (pairing M (Sub.comp σ τ) b (substitutedArgument σ τ b t))
  have hs := hl.symm.trans (h.trans hr)
  have ln := congrArg (fun k => k ((substitution M τ).hom.app U x))
    (SplitNative.pairing (type M Γ (.family b)) (substitution M σ) (pairTerm M σ b t) U)
  have rn := congrArg (fun k => k x)
    (SplitNative.pairing (type M Γ (.family b)) (substitution M (Sub.comp σ τ))
      (pairTerm M (Sub.comp σ τ) b (substitutedArgument σ τ b t)) U)
  exact ln.symm.trans (hs.trans rn)

/-- Direct native operations remain available beside the opt-in source proof. -/
theorem direct_native {Γ Δ : Type u} {A : Γ → Type u} (σ : Δ → Γ)
    (t : DependentSquares.Tm (DependentSquares.tySub A σ)) :
    DependentSquares.compSub DependentSquares.p (DependentSquares.extend σ t) = σ :=
  DependentSquares.p_extend σ t

/-- Direct ordinary family clients need no source interpretation wrapper. -/
theorem direct_family {X Y Z T : Sheaf J (Type w)} (p : X ⟶ Z) (σ : Y ⟶ Z)
    (k : T ⟶ Limits.pullback p σ) :
    Family.pair p σ (k ≫ Family.comparison p σ) (k ≫ Family.reindex p σ)
      (by simp only [Category.assoc, Limits.pullback.condition]) = k := Family.pair_eta p σ k

end Examples.DependentSourceNative
