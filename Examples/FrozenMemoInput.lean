import Examples.FrozenMemoRealization

/-! Recover input binders from the interpretation of their source declarations.
Choice selects input data whose evaluation is fixed; it does not select an
arbitrary inhabitant of the output certificate type. -/
noncomputable section
namespace Examples.FrozenMemoRealization
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open SquareKit.Internal.DependentJudgments.Contextual.Memo
open Examples.GuardedGroupoidMemo
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward false
universe u
variable (M : SquareKit.Internal.PathTransport.Typed.Model.{u}) {V : Type}
variable {Ω : List (Contextual.Judgment V)} (ρ : V → Value M.toStructuralModel)
variable (hΩ : ∀ j ∈ Ω, j.eval (Contextual.algebra M) ρ)

include hΩ in
theorem term_exists {g a t : Contextual.Expression V} (ht : Tm (Ω := Ω) g a t)
    (G : M.Context) (A : M.Family G)
    (hg : g.eval (Contextual.algebra M) ρ = .context G)
    (ha : a.eval (Contextual.algebra M) ρ = .family G A) :
    ∃ v : M.Section G A, t.eval (Contextual.algebra M) ρ = .term G A v := by
  rcases Contextual.interpret ht M ρ hΩ with ⟨G', A', v, hg', ha', hv⟩
  have eg := Value.context.inj (hg'.symm.trans hg)
  subst G'
  have ea := eq_of_heq (Value.family.inj (ha'.symm.trans ha)).2
  subst A'
  exact ⟨v,hv⟩

include hΩ in
theorem family_exists {g a : Contextual.Expression V} (ha : Ty (Ω := Ω) g a)
    (G : M.Context) (hg : g.eval (Contextual.algebra M) ρ = .context G) :
    ∃ A : M.Family G, a.eval (Contextual.algebra M) ρ = .family G A := by
  rcases Contextual.interpret ha M ρ hΩ with ⟨G', A, hg', hA⟩
  have eg := Value.context.inj (hg'.symm.trans hg)
  subst G'
  exact ⟨A,hA⟩

namespace InputRealization

include hΩ in
theorem exists_of_typing (F : Frozen.Input Ω) : Nonempty (InputRealization M ρ F) := by
  rcases Contextual.interpret F.hx M ρ hΩ with ⟨G,A,x,hG,hA,hx⟩
  rcases family_exists M ρ hΩ F.hB (M.extend G A)
    (extend_eval M ρ F.Γ F.A G A hG hA) with ⟨B,hB⟩
  rcases term_exists M ρ hΩ F.hy G A hG hA with ⟨y,hy⟩
  rcases term_exists M ρ hΩ F.hz G A hG hA with ⟨z,hz⟩
  have hP := identity_eval M ρ F.A F.x F.y G A x y hA hx hy
  rcases term_exists M ρ hΩ F.hp G (M.identity A x y) hG hP with ⟨p,hp⟩
  rcases term_exists M ρ hΩ F.hp' G (M.identity A x y) hG hP with ⟨p',hp'⟩
  have hI := identity_eval M ρ _ F.p F.p' G (M.identity A x y) p p' hP hp hp'
  rcases term_exists M ρ hΩ F.hh G _ hG hI with ⟨h,hh⟩
  have hQ := identity_eval M ρ F.A F.y F.z G A y z hA hy hz
  rcases term_exists M ρ hΩ F.hq G _ hG hQ with ⟨q,hq⟩
  have hs := sectionSub_eval M ρ F.Γ F.A F.x G A x hG hA hx
  have hU := subTy_eval M ρ F.B _ _ G B _ hB hs
  rcases term_exists M ρ hΩ F.hu G _ hG hU with ⟨b,hb⟩
  exact ⟨⟨G,A,B,x,y,z,p,p',h,q,b,hG,hA,hB,hx,hy,hz,hp,hp',hh,hq,hb⟩⟩

def ofTyping (F : Frozen.Input Ω) : InputRealization M ρ F :=
  Classical.choice (exists_of_typing M ρ hΩ F)

end InputRealization
end Examples.FrozenMemoRealization
