import SquareKit.Internal.PathTransport.Endpoints

/-! Derived congruence for dependent arguments. The caller supplies generated
source conversions; annotation casts are obtained from their soundness. -/
namespace SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.PathTransport

/-- Extend a converted substitution with a term already compared in a common
source type. The left substituted type must have the stated raw expression. -/
def SubEqDeriv.pairingConverted (hA : TyDeriv Γ γ A a)
    (e : SubEqDeriv Δ δ Γ γ σ s τ t)
    (hx : A.sub σ = B)
    (ha : subTyCode a s = b) (hb : subTyCode a t = b)
    (f : TmEqDeriv Δ δ B b x ξ y η) :
    SubEqDeriv Δ δ (A :: Γ) (extendCode γ a)
      (consSub x σ) (pairCode a s (castCode ha.symm ξ))
      (consSub y τ) (pairCode a t (castCode hb.symm η)) := by
  have f' := (hx.symm ▸ f).annotateType ha.symm
  apply SubEqDeriv.pairingCongr hA e
  apply f'.annotate rfl
  exact eq_of_heq ((castCode_heq _ _).trans
    ((castCode_heq _ _).symm.trans (castCode_heq _ _).symm))

/-- Congruence for substitution with a caller-selected common result type.
Raw type equality and annotation equality are separate premises. -/
def TmDeriv.substitutionCongrAt (h : TmDeriv Γ γ A a x ξ)
    (e : SubEqDeriv Δ δ Γ γ σ s τ t)
    (hraw : A.sub σ = B) (hs : subTyCode a s = b) (ht : subTyCode a t = b) :
    TmEqDeriv Δ δ B b (x.sub σ) (castCode hs (subTmCode ξ s))
      (x.sub τ) (castCode ht (subTmCode ξ t)) := by
  have f := (hraw ▸ (TmEqDeriv.substitutionCongr h e)).annotateType hs
  apply f.annotate rfl
  exact eq_of_heq ((castCode_heq _ _).trans
    ((castCode_heq _ _).trans (castCode_heq _ _).symm))

end SquareKit.Internal.PathTransport.Typed
