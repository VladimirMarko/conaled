import SquareKit.Internal.PathTransport.Endpoints

/-! The current source has no primitive empty-substitution constructor, but
weakening and finite telescope projection supply one for every derived context.
This is an existence result, not an ambient terminality assertion. -/
namespace SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.PathTransport
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Retain the raw substitution and its semantic code with the actual derivation. -/
abbrev EmptySubstitution (Γ : RawCtx) (γ : CtxCode.{u}) :=
  (σ : RawSub) × (s : SubCode γ emptyCode) × SubDeriv Γ γ [] emptyCode σ s

def CtxDeriv.emptySubstitution {Γ γ} (h : CtxDeriv.{u} Γ γ) : EmptySubstitution Γ γ :=
  match h with
  | .empty => ⟨_, _, .id .empty⟩
  | .ext hΓ hA =>
      let e := hΓ.emptySubstitution
      ⟨_, _, .comp e.2.2 (.weaken hΓ hA)⟩
  | .path hΓ hA hx =>
      let e := hΓ.emptySubstitution
      ⟨_, _, .comp e.2.2 (.comp (.weaken hΓ hA)
        (.weaken (.ext hΓ hA) (.pathFamily hΓ hA hx)))⟩
  | .telescope hΓ hT =>
      let e := hΓ.emptySubstitution
      ⟨_, _, .comp e.2.2 (.projection hΓ hT)⟩
  | .branch hΓ hA hx hT =>
      let e := hΓ.emptySubstitution
      ⟨_, _, .comp e.2.2 (.projection hΓ (.pullback hT (.root hΓ hA hx)))⟩

end SquareKit.Internal.PathTransport.Typed
