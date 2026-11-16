import SquareKit.Internal.PathTransport.ComparisonTelescopeEquivalence
import SquareKit.Internal.PathTransport.GeneratedComparisonRestriction

/-! Primitive equivalences induce equivalences on the existing generated codes. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison.GeneratedEquivalence
open CategoryTheory Typed Typed.StructuralModel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (S : Signature.{u}) [S.base.map.IsEquivalence]
    (hF : ∀ c, Function.Bijective (S.fiberMap.app c))
local notation "M" => fullModel S

def CtxPres (γ : CtxCode.{u+1}) : Prop := (γ M).map.IsEquivalence
def TyPres {γ : CtxCode.{u+1}} (a : TyCode γ) : Prop := (a M).FiberEquivalences
def TelPres {γ : CtxCode.{u+1}} {n} (Ts : TelCode γ n) : Prop := TelescopeEquivalences S (Ts M)

private theorem base_pres {γ : CtxCode.{u+1}} : TyPres S (baseCode γ) := fun _ => inferInstanceAs S.base.map.IsEquivalence

include hF in
omit [S.base.map.IsEquivalence] in
private theorem fiber_pres {γ : CtxCode.{u+1}} (x : TmCode γ (baseCode γ)) :
    TyPres S (fiberCode x) := by
  apply Family.reindex_equivalences
  intro c
  exact (Discrete.equivalence (Equiv.ofBijective (S.fiberMap.app c) (hF c))).isEquivalence_functor

omit [S.base.map.IsEquivalence] in
private theorem path_pres {γ : CtxCode.{u+1}} {a : TyCode γ} {x : TmCode γ a}
    (hg : CtxPres S γ) (ha : TyPres S a) : CtxPres S (pathCode a x) := by
  let : (γ M).map.IsEquivalence := hg
  let : ((M).extend (γ M) (a M)).map.IsEquivalence := Family.extend_equivalence (a M) ha
  exact Family.extend_equivalence _
    (Family.identity_equivalences _ (Family.reindex_equivalences _ ha _) _ _)

omit [S.base.map.IsEquivalence] in
private theorem branch_pres {γ : CtxCode.{u+1}} {a : TyCode γ} {x : TmCode γ a}
    {n} {Ts : TelCode (pathCode a x) n} (hg : CtxPres S γ) (ht : TelPres S Ts) :
    CtxPres S (branchCode a x Ts) := by
  exact (ht.pullback (rootCode a x M)).total hg

-- Contexts and telescopes use both primitive premises through generatedTy.
omit [S.base.map.IsEquivalence] hF in
mutual

theorem generatedCtx [S.base.map.IsEquivalence]
    (hF : ∀ c, Function.Bijective (S.fiberMap.app c))
    {Γ : RawCtx} {γ : CtxCode.{u+1}} (deriv : CtxDeriv Γ γ) : CtxPres S γ :=
  match deriv with
  | .empty => inferInstanceAs (Functor.IsEquivalence (𝟭 _))
  | .ext (γ := γ) hΓ ha => by
    let : (γ M).map.IsEquivalence := generatedCtx hF hΓ
    exact Family.extend_equivalence _ (generatedTy hF ha)
  | .path hΓ ha _ => path_pres S (generatedCtx hF hΓ) (generatedTy hF ha)
  | .telescope hΓ ht => by
    exact (generatedTel hF ht).total (generatedCtx hF hΓ)
  | .branch hΓ _ _ ht => branch_pres S (generatedCtx hF hΓ) (generatedTel hF ht)
termination_by sizeOf deriv

theorem generatedTel [S.base.map.IsEquivalence]
    (hF : ∀ c, Function.Bijective (S.fiberMap.app c))
    {Γ : RawCtx} {γ : CtxCode.{u+1}} {n : Nat} {Δ : RawCtx} {Ts : TelCode γ n}
    (deriv : TelDeriv Γ γ n Δ Ts) : TelPres S Ts :=
  match deriv with
  | .nil _ => .nil
  | .cons ha ht => .cons (generatedTy hF ha) (generatedTel hF ht)
  | .pullback ht hs => (generatedTel hF ht).pullback _
  | .pathReindex _ _ _ ht hs => (generatedTel hF ht).pullback _
termination_by sizeOf deriv

theorem generatedTy [S.base.map.IsEquivalence]
    (hF : ∀ c, Function.Bijective (S.fiberMap.app c))
    {Γ : RawCtx} {γ : CtxCode.{u+1}} {A : Expr} {a : TyCode γ}
    (deriv : TyDeriv Γ γ A a) : TyPres S a :=
  match deriv with
  | .base _ => base_pres S
  | .fiber hx => fiber_pres S hF _
  | .identity ha hx hy => Family.identity_equivalences _ (generatedTy hF ha) _ _
  | .sub ha hs => Family.reindex_equivalences _ (generatedTy hF ha) _
termination_by sizeOf deriv
end

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison.GeneratedEquivalence
