import SquareKit.Internal.PathTransport.ConcatenationCongr

/-! Framework-assisted regression cases for #107. The associativity case here
specializes the first path to reflexivity. It is not the required general
associativity derivation and is not independent transfer evidence. -/
namespace Examples.DependentCongruence
open SquareKit.Internal.PathTransport
open SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.PathTransport.Typed.Authoring
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def assocReflexiveEquality (hΓ : CtxDeriv Γ γ) {x z w : BasePoint Γ γ}
    (q : Path x z) (r : Path z w) :=
  (concat_congr_first hΓ (concat hΓ (Path.reflexivity hΓ x) q) q r
    (concat_beta hΓ x z q)).trans (concat_beta hΓ x w (concat hΓ q r)).symm

def assocReflexive (hΓ : CtxDeriv Γ γ) {x z w : BasePoint Γ γ}
    (q : Path x z) (r : Path z w) :=
  (TmDeriv.refl (Path.type hΓ (concat hΓ q r))
    (concat hΓ (concat hΓ (Path.reflexivity hΓ x) q) r).deriv).convert
    (TyEqDeriv.identity (Path.type hΓ (concat hΓ q r))
      (.refl (concat hΓ (concat hΓ (Path.reflexivity hΓ x) q) r).deriv)
      (assocReflexiveEquality hΓ q r))
-- Statement review: an inhabitant of the intended iterated identity, with only p specialized.
def checkedReflexiveStatement (hΓ : CtxDeriv Γ γ) {x z w : BasePoint Γ γ}
    (q : Path x z) (r : Path z w) :
    Σ t ξ, TmDeriv Γ γ
      (.identity (.identity .base x.raw w.raw)
        (concat hΓ (concat hΓ (Path.reflexivity hΓ x) q) r).raw
        (concat hΓ (Path.reflexivity hΓ x) (concat hΓ q r)).raw)
      (identityCode (identityCode (baseCode γ) x.code w.code)
        (concat hΓ (concat hΓ (Path.reflexivity hΓ x) q) r).code
        (concat hΓ (Path.reflexivity hΓ x) (concat hΓ q r)).code) t ξ :=
  ⟨_, _, assocReflexive hΓ q r⟩

/-- The same comparison accepts substitution through an arbitrary context,
including a context obtained by extending a dependent telescope. -/
def substitutedReflexiveEquality (hΓ : CtxDeriv Γ γ) {x z w : BasePoint Γ γ}
    (q : Path x z) (r : Path z w) (hs : SubDeriv Δ δ Γ γ σ s) :=
  TmEqDeriv.sub (assocReflexiveEquality hΓ q r) hs

namespace DependentArguments
open CongruenceCaller

/-- The argument operation acts on a reflexivity term depending on the
converted component of a substitution. The input conversion is actual J beta. -/
def identityAtConvertedArgument := boundIdentity.substitutionCongrAt pairedBeta
  rfl rfl (congrArg (subTyCode _) (subSound pairedBeta).symm)

/-- Extend that converted substitution by a component whose type depends on
its preceding component. The generic helper owns the nested annotation casts. -/
def dependentPair := SubEqDeriv.pairingConverted dependentType pairedBeta rfl
  rfl (congrArg (subTyCode _) (subSound pairedBeta).symm) identityAtConvertedArgument

end DependentArguments
end Examples.DependentCongruence
