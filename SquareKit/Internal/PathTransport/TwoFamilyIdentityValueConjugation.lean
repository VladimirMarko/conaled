import SquareKit.Internal.PathTransport.TwoFamilyOrdinarySourceAction
import SquareKit.Internal.PathTransport.TwoFamilyIdentityFiberValueAction
import SquareKit.Internal.PathTransport.TwoFamilyIdentitySectionCell
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
def ValueConjugation {C : Type u} [Category.{u} C] {a b c d : C}
 (h : a ⟶ b) (l : a ⟶ c) (r : d ⟶ b) {V : Type u} (v : V) : Prop :=
 ∃ e : V = LocallyDiscrete (Discrete (c ⟶ d)), l ≫ identityValueArrow v e ≫ r = h
theorem valueConjugation_of_heq {C : Type u} [Category.{u} C] {a b c d : C}
 (h : a ⟶ b) (l : a ⟶ c) (r : d ⟶ b) {V : Type u} (v : V)
 (k : c ⟶ d) (hv : IdentityValueAction v k)
 (hk : l ≫ k ≫ r = h) : ValueConjugation h l r v := by
 refine ⟨type_eq_of_heq hv, ?_⟩
 rw [identityValueArrow_eq v k hv]
 exact hk
variable {Γ : Context.{u}} (A : Family Γ) (x y : TwoFamily.Section A.data)
local notation "I" => A.identity x y
def IdentityFiberValueConjugationAt
 (p q : TwoFamily.Section (I).data)
 (s : TwoFamily.Section (reindex (projectionHigher (I).data) (I).data))
 (G : Family Γ) (v : TwoFamily.Section (closedId (I).data p q) → TwoFamily.Section G.data)
 (β : TwoFamily.Section (closedId (reindex (projectionHigher (I).data) (I).data) s (variableSection (I).data)))
 (h : TwoFamily.Section (closedId (I).data p q)) : Prop := ∀ γ,
 ValueConjugation (identitySectionCell A x y p q h γ)
  (inv ((identityFiberBeta A x y γ s β).app (identitySectionValue A x y p γ)))
  ((identityFiberBeta A x y γ s β).app (identitySectionValue A x y q γ))
  ((v h).normalObj G.data γ).fiber
theorem identityFiberValue_conjugation
 (p q : TwoFamily.Section (I).data)
 (s : TwoFamily.Section (reindex (projectionHigher (I).data) (I).data))
 (G : Family Γ) (v : TwoFamily.Section (closedId (I).data p q) → TwoFamily.Section G.data)
 (β : TwoFamily.Section (closedId (reindex (projectionHigher (I).data) (I).data) s (variableSection (I).data)))
 (ha : IdentityFiberValueFormula A x y p q s G v)
 (h : TwoFamily.Section (closedId (I).data p q)) : IdentityFiberValueConjugationAt A x y p q s G v β h := by
 intro γ
 have hc := identityFiber_conjugation A x y γ s β (identitySectionCell A x y p q h γ)
 have hv := ha h γ
 have f := valueConjugation_of_heq
  (identitySectionCell A x y p q h γ)
  (inv ((identityFiberBeta A x y γ s β).app (identitySectionValue A x y p γ)))
  ((identityFiberBeta A x y γ s β).app (identitySectionValue A x y q γ))
  ((v h).normalObj G.data γ).fiber
  ((identityFiberFunctor A x y γ s).map (identitySectionCell A x y p q h γ))
 run_tac Lean.Elab.Tactic.withMainContext do
  let f ← Lean.Meta.getLocalDeclFromUserName `f
  let hv ← Lean.Meta.getLocalDeclFromUserName `hv
  let hc ← Lean.Meta.getLocalDeclFromUserName `hc
  (← Lean.Elab.Tactic.getMainGoal).assign (Lean.mkAppN f.toExpr #[hv.toExpr, hc.toExpr])
  Lean.Elab.Tactic.replaceMainGoal []
end SquareKit.Internal.PathTransport.HigherInterpretation
