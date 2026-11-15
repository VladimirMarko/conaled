import SquareKit.Internal.PathTransport.Typed

/-! Type-constructor induction with term and substitution derivations retained. -/
namespace SquareKit.Internal.PathTransport.Typed
universe u
variable (P : ∀ {Γ γ B b}, TyDeriv.{u} Γ γ B b → Prop)
variable (hbase : ∀ {Γ γ} (hΓ : CtxDeriv.{u} Γ γ), P (.base hΓ))
variable (hfiber : ∀ {Γ γ x ξ} (hx : TmDeriv.{u} Γ γ .base (baseCode γ) x ξ), P (.fiber hx))
variable (hidentity : ∀ {Γ γ B b x ξ y η} (hB : TyDeriv.{u} Γ γ B b)
  (hx : TmDeriv.{u} Γ γ B b x ξ) (hy : TmDeriv.{u} Γ γ B b y η),
  P hB → P (.identity hB hx hy))
variable (hsub : ∀ {Γ γ B b Δ δ σ s} (hB : TyDeriv.{u} Γ γ B b)
  (hs : SubDeriv.{u} Δ δ Γ γ σ s), P hB → P (.sub hB hs))

include hbase hfiber hidentity hsub in
theorem TyDeriv.familyInduction (hB : TyDeriv.{u} Γ γ B b) : P hB :=
  match hB with
  | .base hΓ => hbase hΓ
  | .fiber hx => hfiber hx
  | .identity hB hx hy => hidentity hB hx hy (hB.familyInduction)
  | .sub hB hs => hsub hB hs (hB.familyInduction)
termination_by sizeOf hB
end SquareKit.Internal.PathTransport.Typed
