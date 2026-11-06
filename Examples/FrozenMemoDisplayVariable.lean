import Examples.FrozenMemoDisplayRealization
/-! Evaluate retained variables through the original frozen display pullbacks. -/
noncomputable section
namespace Examples.FrozenMemoStages
open SquareKit.Internal.PathTransport.Typed
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual
open SquareKit.Internal.DependentJudgments.Contextual.DerivedSemantics
open SquareKit.Internal.DependentJudgments.Contextual.Memo
open Examples.GuardedGroupoidMemo
universe u
variable (M : Model.{u}) {V : Type} (ρ : V → Value M.toStructuralModel)
structure DisplayTerm (Γ : M.Context) (t : Contextual.Expression V) where
 family : M.Family Γ
 value : M.Section Γ family
 eval : t.eval (Contextual.algebra M) ρ = .term Γ family value
variable {M ρ} {Ω : List (Contextual.Judgment V)}
def displayWeaken {g G} {D : Frozen.Display Ω g} (R : DisplayRealization M ρ D G)
 (hg : g.eval (Contextual.algebra M) ρ = .context G)
 {t : Contextual.Expression V} (s : DisplayTerm M ρ G t) : DisplayTerm M ρ R.total (D.weakenTerm t) :=
 match R with
 | .nil _ _ => s
 | .cons ha tail G A hA rest =>
   displayWeaken rest (extend_eval M ρ _ _ _ _ hg hA)
    ⟨M.subTy s.family (M.weaken G A), M.subTm s.value (M.weaken G A),
     subTm_eval M ρ _ _ _ _ _ _ _ s.eval (weaken_eval M ρ _ _ _ _ hg hA)⟩
def displayVariable {g G} {D : Frozen.Display Ω g} (R : DisplayRealization M ρ D G)
 (hg : g.eval (Contextual.algebra M) ρ = .context G)
 (v : Frozen.Display.Variable D) : DisplayTerm M ρ R.total v.term :=
 match R, v with
 | .cons ha tail G A hA rest, .here _ _ =>
   displayWeaken rest (extend_eval M ρ _ _ _ _ hg hA)
    ⟨M.subTy A (M.weaken G A), M.genericVariable G A,
     generic_eval M ρ _ _ _ _ hg hA⟩
 | .cons ha tail G _A hA rest, .there _ _ v =>
   displayVariable rest (extend_eval M ρ _ _ _ _ hg hA) v
variable (M : Model.{u}) (A : M.Family M.empty) (B : M.Family (M.extend M.empty A))
local notation "env" => Examples.FrozenMemoSignature.environment M A B
local notation "S" => M.toStructuralModel

def sigmaHomotopy : DisplayTerm M env (sigmaData M A B).display.total
 (Contextual.subTm signature.input.h signature.sigma) := by
 let v := displayVariable (sigmaData M A B).display (initial_eval M A B).context_eval
  (signature.homotopySlot.pullback signature.point.hx.family.context signature.duplicate_typed)
 exact ⟨v.family, v.value,
  (Contextual.interpret signature.sigma_homotopy_retained M env
   (Examples.FrozenMemoSignature.inputs M A B)).trans v.eval⟩

def tauHomotopy : DisplayTerm M env (tauData M A B).display.total signature.thetaInput.h := by
 let v := displayVariable (tauData M A B).display (initial_eval M A B).context_eval
  (signature.delta_homotopySlot.pullback signature.point.hx.family.context signature.deltaX_as_z.section)
 exact ⟨v.family, v.value,
  (Contextual.interpret signature.tau_homotopy_retained M env
   (Examples.FrozenMemoSignature.inputs M A B)).trans v.eval⟩
end Examples.FrozenMemoStages

namespace Examples.GuardedGroupoidMemo.DisplayRealization
open SquareKit.Internal.DependentJudgments
open SquareKit.Internal.DependentJudgments.Contextual
open SquareKit.Internal.DependentJudgments.Contextual.Memo
universe u
variable {M : SquareKit.Internal.PathTransport.Typed.Model.{u}} {V : Type}
 {ρ : V → Value M.toStructuralModel} {Ω : List (Contextual.Judgment V)}
 {g a : Contextual.Expression V} {ha : Ty (Ω := Ω) g a} {tail : Frozen.Display Ω (extend g a)} {G : M.Context}
def headFamily (R : DisplayRealization M ρ (.cons ha tail) G) : M.Family G :=
 match R with | .cons _ _ _ A _ _ => A
def rest (R : DisplayRealization M ρ (.cons ha tail) G) :
 DisplayRealization M ρ tail (M.extend G R.headFamily) :=
 match R with | .cons _ _ _ _ _ r => r
end Examples.GuardedGroupoidMemo.DisplayRealization
