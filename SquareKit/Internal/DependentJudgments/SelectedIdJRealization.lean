import SquareKit.Internal.DependentJudgments.DerivedPathSemantics

/-! Local quotation laws retain selected Id/J sections. The semantic operations
are the independently specified contextual model operations, including their
chosen eliminator, rather than proof inhabitation or endpoint equality. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.Internal.DependentJudgments.Contextual.SelectedRealization
open GuardedTheory PathTransport.Typed StructuralModel DerivedSemantics
universe u
variable (M : PathTransport.Typed.Model.{u}) {V : Type}
variable (ρ : V → Value M.toStructuralModel)

/-- A separately chosen semantic value with its actual target quotation. -/
structure Code (v : Value M.toStructuralModel) where
  quote : Expression V
  realizes : quote.eval (algebra M) ρ = v

namespace Code
variable {M ρ}

def identity {Γ : M.Context} {A : M.Family Γ} {x y : M.Section Γ A}
    (a : Code M ρ (.family Γ A)) (sx : Code M ρ (.term Γ A x))
    (sy : Code M ρ (.term Γ A y)) : Code M ρ (.family Γ (M.identity A x y)) :=
  ⟨Contextual.identity a.quote sx.quote sy.quote,
    identity_eval M ρ _ _ _ _ _ _ _ a.realizes sx.realizes sy.realizes⟩

def reflexivity {Γ : M.Context} {A : M.Family Γ} {x : M.Section Γ A}
    (a : Code M ρ (.family Γ A)) (sx : Code M ρ (.term Γ A x)) :
    Code M ρ (.term Γ (M.identity A x x) (M.reflexivity A x)) :=
  ⟨Contextual.reflexivity a.quote sx.quote,
    reflexivity_eval M ρ _ _ _ _ _ a.realizes sx.realizes⟩

def subTm {Γ Δ : M.Context} {A : M.Family Γ} {t : M.Section Γ A}
    {σ : M.Substitution Δ Γ} (st : Code M ρ (.term Γ A t))
    (ss : Code M ρ (.substitution Δ Γ σ)) :
    Code M ρ (.term Δ (M.subTy A σ) (M.subTm t σ)) :=
  ⟨Contextual.subTm st.quote ss.quote,
    subTm_eval M ρ _ _ _ _ _ _ _ st.realizes ss.realizes⟩

/-- This local law accepts any finite dependent tail and the actual typed
motive and branch. Its output is the chosen J section, not some inhabitant. -/
def j {Γ : M.Context} {A : M.Family Γ} {x : M.Section Γ A} {n : Nat}
    {T : Telescope M.toStructuralModel (M.pathContext A x) n} {D : M.Family T.total}
    {d : M.Section (Telescope.pullback M.toStructuralModel T (M.rootSub A x)).total
      (M.subTy D (M.rootTail A x T))}
    (sa : Code M ρ (.family Γ A)) (sx : Code M ρ (.term Γ A x))
    (sT : Code M ρ (.telescope (M.pathContext A x) n T))
    (sD : Code M ρ (.family T.total D))
    (sd : Code M ρ (.term (Telescope.pullback M.toStructuralModel T (M.rootSub A x)).total
      (M.subTy D (M.rootTail A x T)) d)) :
    Code M ρ (.term T.total D (M.j A x T D d)) := by
  refine ⟨Contextual.j sa.quote sx.quote sT.quote sD.quote sd.quote, ?_⟩
  change operation M .j ![sa.quote.eval (algebra M) ρ, sx.quote.eval (algebra M) ρ,
    sT.quote.eval (algebra M) ρ, sD.quote.eval (algebra M) ρ, sd.quote.eval (algebra M) ρ] = _
  simp only [sa.realizes, sx.realizes, sT.realizes, sD.realizes, sd.realizes]
  simp [operation]

/-- Derived transport uses the model's actual J, motive and endpoint action. -/
def transport {Γ : M.Context} {A : M.Family Γ} {B : M.Family (M.extend Γ A)}
    {x y : M.Section Γ A} {p : M.Section Γ (M.identity A x y)}
    {b : M.Section Γ (M.subTy B (M.sectionSub A x))}
    (sg : Code M ρ (.context Γ)) (sa : Code M ρ (.family Γ A))
    (sB : Code M ρ (.family (M.extend Γ A) B))
    (sx : Code M ρ (.term Γ A x)) (sy : Code M ρ (.term Γ A y))
    (sp : Code M ρ (.term Γ (M.identity A x y) p))
    (sb : Code M ρ (.term Γ (M.subTy B (M.sectionSub A x)) b)) :
    Code M ρ (.term Γ (M.subTy B (M.sectionSub A y)) (transportValue M A B x y p b)) :=
  ⟨Contextual.transport sg.quote sa.quote sB.quote sx.quote sy.quote sp.quote sb.quote,
    transport_eval M ρ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      sg.realizes sa.realizes sB.realizes sx.realizes sy.realizes sp.realizes sb.realizes⟩

/-- Semantic apd and its quotation retain the supplied higher path and section. -/
def apd {Γ : M.Context} {A : M.Family Γ} {B : M.Family (M.extend Γ A)}
    {x y : M.Section Γ A} {p : M.Section Γ (M.identity A x y)}
    {t : M.Section (M.extend Γ A) B}
    (sg : Code M ρ (.context Γ)) (sa : Code M ρ (.family Γ A))
    (sB : Code M ρ (.family (M.extend Γ A) B))
    (sx : Code M ρ (.term Γ A x)) (sy : Code M ρ (.term Γ A y))
    (sp : Code M ρ (.term Γ (M.identity A x y) p))
    (st : Code M ρ (.term (M.extend Γ A) B t)) :
    Code M ρ (.term Γ (M.identity (M.subTy B (M.sectionSub A y))
      (transportValue M A B x y p (M.subTm t (M.sectionSub A x)))
      (M.subTm t (M.sectionSub A y))) (apdValue M A B x y p t)) :=
  ⟨Contextual.apd sg.quote sa.quote sB.quote sx.quote sy.quote sp.quote st.quote,
    apd_eval M ρ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      sg.realizes sa.realizes sB.realizes sx.realizes sy.realizes sp.realizes st.realizes⟩

end Code
end SquareKit.Internal.DependentJudgments.Contextual.SelectedRealization
