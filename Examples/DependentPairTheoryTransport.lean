import SquareKit.DependentPairTemplates
import Examples.DependentPairTheoryModels

/-! The frozen pair client, its two raw substitutions, and its independent
selected declaration interpretation. Typing derivations live separately. -/
namespace SquareKit.DependentPairTheoryTransport
open DependentTheoryMaps DependentPairPresentations

abbrev SingleV := Fin 1 ⊕ Empty
abbrev ClientV := Fin 1 ⊕ (Fin 1 ⊕ (Fin 1 ⊕ Empty))

def n : ClientV := .inr (.inr (.inl 0))
def y : ClientV := .inr (.inl 0)
def z : ClientV := .inl 0
def m : SingleV := .inl 0

def N : PExpr V := .app (.declaration .N) (fun i => nomatch i)
def B (n : PExpr V) : PExpr V :=
  .app (.declaration .B) (Fin.cases (zero n) (fun i => nomatch i))
def C (n y : PExpr V) : PExpr V :=
  .app (.declaration .C) (Fin.cases (zero n) (Fin.cases (zero y) (fun i => nomatch i)))
def s (m : PExpr V) : PExpr V :=
  .app (.declaration .s) (Fin.cases (zero m) (fun i => nomatch i))
def d (k : PExpr V) : PExpr V :=
  .app (.declaration .d) (Fin.cases (zero k) (fun i => nomatch i))
def t (m : PExpr V) : PExpr V :=
  .app (.declaration .t) (Fin.cases (zero m) (fun i => nomatch i))
def u (m : PExpr V) : PExpr V :=
  .app (.declaration .u) (Fin.cases (zero m) (fun i => nomatch i))

def familyB : PExpr (Fin 1 ⊕ V) := B (.var (.inl 0))
def q : PExpr ClientV := Projection.pair N familyB (.var n) (.var y)
def clientType : PExpr ClientV := C (.var n) (Projection.snd N familyB q)
def selectedRaw : PExpr ClientV := .var z

def sigmaRaw : ClientV → PExpr SingleV
  | .inl _ => u (.var m)
  | .inr (.inl _) => t (.var m)
  | .inr (.inr (.inl _)) => s (.var m)
  | .inr (.inr (.inr e)) => e.elim

def tauRaw : SingleV → PExpr SingleV
  | .inl _ => d (.var m)
  | .inr e => e.elim

@[simp] theorem subst_u (σ : V → PExpr W) (e : PExpr V) :
    Expr.subst σ (u e) = u (Expr.subst σ e) := by
  simp only [u, Expr.subst]
  congr 1
  funext i
  change Fin 1 at i
  fin_cases i
  exact Elimination.subst_zero σ e

@[simp] theorem selected_sigma : Expr.subst sigmaRaw selectedRaw = u (.var m) := rfl

@[simp] theorem selected_twice :
    Expr.subst tauRaw (Expr.subst sigmaRaw selectedRaw) = u (d (.var m)) := by
  rw [selected_sigma, subst_u]
  rfl

/-- Generic template substitution supplies the second transport step. -/
theorem translated_selected_twice :
    Expr.subst (fun v => G.act (tauRaw v)) (G.act (Expr.subst sigmaRaw selectedRaw)) =
      G.act (u (d (.var m))) := by
  rw [← G.substitution, selected_twice]

/-- The translated dependent type follows the same two substitutions. -/
theorem translated_type_twice :
    Expr.subst (fun v => G.act (tauRaw v)) (G.act (Expr.subst sigmaRaw clientType)) =
      G.act (Expr.subst (fun v => Expr.subst tauRaw (sigmaRaw v)) clientType) :=
  G_two_substitutions clientType sigmaRaw tauRaw

/-- A typed declaration fragment fixes the selected semantic value independently
of the proof engine or the pair templates. -/
inductive IndexTerm (V : Type) where
  | var : V → IndexTerm V
  | successor : IndexTerm V → IndexTerm V
  | double : IndexTerm V → IndexTerm V

namespace IndexTerm

def meaning (ρ : V → Nat) : IndexTerm V → Nat
  | .var v => ρ v
  | .successor e => DependentPairTheoryModels.s (meaning ρ e)
  | .double e => DependentPairTheoryModels.d (meaning ρ e)

def expression : IndexTerm V → PExpr V
  | .var v => .var v
  | .successor e => s (expression e)
  | .double e => d (expression e)
end IndexTerm

/-- The declaration u returns the chosen section, not an arbitrary inhabitant. -/
def selectedMeaning (ρ : V → Nat) (e : IndexTerm V) :
    DependentPairTheoryModels.ClientC
      (DependentPairTheoryModels.s (e.meaning ρ)) (DependentPairTheoryModels.t (e.meaning ρ)) :=
  DependentPairTheoryModels.sectionU (e.meaning ρ)

def finalIndex : IndexTerm SingleV := .double (.var m)

theorem final_expression :
    Expr.subst tauRaw (Expr.subst sigmaRaw selectedRaw) = u finalIndex.expression := selected_twice

/-- The same selected source term and its G image quote this declaration value. -/
theorem final_selected_value : selectedMeaning (fun _ => 2) finalIndex = (⟨6, by decide⟩ : Fin 7) := rfl

theorem final_selected_fixture : selectedMeaning (fun _ => 2) finalIndex =
    DependentPairTheoryModels.selectedSection
      (DependentPairTheoryModels.sigma (DependentPairTheoryModels.tau 2)) := rfl

end SquareKit.DependentPairTheoryTransport
