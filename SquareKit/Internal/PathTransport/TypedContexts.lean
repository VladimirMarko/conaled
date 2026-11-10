import SquareKit.Internal.PathTransport.Typed

/-! Context witnesses recovered from the supplied typing derivations. -/
namespace SquareKit.Internal.PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u

def SubDeriv.sourceContext (hs : SubDeriv.{u} Δ δ Γ γ σ s) : CtxDeriv Δ δ :=
  match hs with
  | .id hΓ => hΓ
  | .comp _ ht => ht.sourceContext
  | .weaken hΓ hA => .ext hΓ hA
  | .projection hΓ hT => .telescope hΓ hT
  | .root hΓ _ _ => hΓ
  | .rootTail hΓ hA hx hT => .branch hΓ hA hx hT
  | .pathTailMap hΓ hA hx hT hs =>
      .telescope (.path hs.sourceContext (.sub hA hs) (.sub hx hs))
        (.pathReindex hΓ hA hx hT hs)
  | .pair _ hs _ => hs.sourceContext
termination_by sizeOf hs

mutual
def TyDeriv.context (hB : TyDeriv.{u} Γ γ B b) : CtxDeriv Γ γ :=
  match hB with
  | .base hΓ => hΓ
  | .fiber hx => hx.context
  | .identity hB _ _ => hB.context
  | .sub _ hs => hs.sourceContext
termination_by sizeOf hB

def TmDeriv.context (hx : TmDeriv.{u} Γ γ B b x ξ) : CtxDeriv Γ γ :=
  match hx with
  | .var hΓ hB => .ext hΓ hB
  | .refl hB _ => hB.context
  | .sub _ hs => hs.sourceContext
  | .pathInduction hΓ _ _ _ _ _ _ _ _ => hΓ
  | .pathInductionReindex _ _ _ _ _ _ hs _ _ _ => hs.sourceContext
  | @TmDeriv.genericJ _ _ _ _ _ _ _ _ T C c _ _ hΓ hB hx hT hc hd => .telescope (.path hΓ hB hx) hT
  | @TmDeriv.reindexJBranch _ _ _ _ _ _ _ _ T C c _ _ _ _ _ _ hΓ hB hx hT hc hd hs =>
      .branch hs.sourceContext (.sub hB hs) (.sub hx hs)
        (.pathReindex hΓ hB hx hT hs)
  | .conv hx _ _ => hx.context
termination_by sizeOf hx
end
end SquareKit.Internal.PathTransport.Typed
