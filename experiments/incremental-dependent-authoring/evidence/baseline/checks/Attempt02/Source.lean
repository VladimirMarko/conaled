import Examples.IncrementalDependentTrialSpec
import Examples.DependentPairTypedClient
import SquareKit.DependentPairTheoryMap

namespace IncrementalNative
open SquareKit SquareKit.DependentTheoryMaps SquareKit.DependentPairPresentations
open SquareKit.DependentPairJudgments SquareKit.DependentPairTheoryTransport
open SquareKit.DependentPairTypedClient
namespace Spec
export Examples.IncrementalDependentTrialSpec (Op run selected Packet demo demoAnswer substitutedAnswer wrongAnswer sigma tau)
end Spec

inductive Ix where
  | input
  | succ (e : Ix)
  | dbl (e : Ix)

def Ix.eval (n : Nat) : Ix → Nat
  | .input => n
  | .succ e => e.eval n + 1
  | .dbl e => 2 * e.eval n

def Ix.quote : Ix → PExpr SingleV
  | .input => .var m
  | .succ e => s e.quote
  | .dbl e => d e.quote

def step (op : Spec.Op) (e : Ix) : Ix :=
  match op with | .successor => .succ e | .double => .dbl e

def generate (ops : List Spec.Op) (e : Ix := .input) : Ix :=
  match ops with | [] => e | op :: rest => generate rest (step op e)

theorem generate_append (xs ys : List Spec.Op) (e : Ix) :
    generate (xs ++ ys) e = generate ys (generate xs e) := by
  induction xs generalizing e with
  | nil => rfl
  | cons x xs ih => exact ih (step x e)

theorem eval_generate (ops : List Spec.Op) (e : Ix) (n : Nat) :
    (generate ops e).eval n = Spec.run ops (e.eval n) := by
  induction ops generalizing e with
  | nil => rfl
  | cons op ops ih =>
    rw [generate, ih]
    cases op <;> rfl

theorem eval_append (xs ys : List Spec.Op) (n : Nat) :
    (generate (xs ++ ys)).eval n = (generate ys).eval ((generate xs).eval n) := by
  rw [generate_append, eval_generate, eval_generate]
  rfl

-- This interpreter is restricted to generated arithmetic indices, dependent
-- pair construction, and the chosen second observation.
inductive SourcePair where | pair (index : Ix)
inductive SourceCode where | snd (p : SourcePair)
inductive TargetPair where | pack (index : Ix)
inductive TargetCode where | splitSecond (p : TargetPair)

def SourcePair.exec (n : Nat) : SourcePair → Spec.Packet
  | .pair e => ⟨e.eval n + 1, ⟨e.eval n + 1, by omega⟩⟩
def SourceCode.exec (n : Nat) : SourceCode → Spec.Packet
  | .snd p => let v := p.exec n; ⟨v.1, v.2⟩
def TargetPair.exec (n : Nat) : TargetPair → Spec.Packet
  | .pack e => ⟨e.eval n + 1, ⟨e.eval n + 1, by omega⟩⟩
def TargetCode.exec (n : Nat) : TargetCode → Spec.Packet
  | .splitSecond p => match p.exec n with | ⟨k, b⟩ => ⟨k, b⟩
def translatePair : SourcePair → TargetPair | .pair e => .pack e
def translate : SourceCode → TargetCode | .snd p => .splitSecond (translatePair p)

def SourcePair.quote : SourcePair → PExpr SingleV
  | .pair e => Projection.pair N familyB (s e.quote) (t e.quote)
def SourceCode.quote : SourceCode → PExpr SingleV
  | .snd p => Projection.snd N familyB p.quote

def TargetPair.quote : TargetPair → EExpr SingleV
  | .pack e => Elimination.pack (G.act N) (G.act familyB)
      (G.act (s e.quote)) (G.act (t e.quote))
def TargetCode.quote : TargetCode → EExpr SingleV
  | .splitSecond p => Elimination.second (G.act N) (G.act familyB) p.quote

theorem quotation (c : SourceCode) : (translate c).quote = G.act c.quote := by
  cases c with | snd p => cases p <;> simp [translate, translatePair,
    SourceCode.quote, SourcePair.quote, TargetCode.quote, TargetPair.quote]
theorem execution (c : SourceCode) (n : Nat) :
    (translate c).exec n = c.exec n := by
  cases c with | snd p => cases p <;> rfl

def program (ops : List Spec.Op) (e : Ix := .input) : SourceCode :=
  .snd (.pair (generate ops e))

theorem selected (ops : List Spec.Op) (e : Ix) (n : Nat) :
    (translate (program ops e)).exec n = Spec.selected ops (e.eval n) := by
  simp only [translate, program, translatePair, TargetCode.exec, TargetPair.exec,
    Spec.selected, eval_generate]

theorem selected_append (xs ys : List Spec.Op) (n : Nat) :
    (translate (program (xs ++ ys))).exec n =
      (translate (program ys)).exec ((generate xs).eval n) := by
  change (⟨_, ⟨_, _⟩⟩ : Spec.Packet) = ⟨_, ⟨_, _⟩⟩
  simp only [eval_append]

theorem empty_selected (n : Nat) :
    (translate (program [])).exec n = Spec.selected [] n := selected [] .input n

def Ix.typed : (e : Ix) → Proof (Judgment.term Γn e.quote N)
  | .input => varN
  | .succ e => declaration (.s Γn e.quote)
      (Fin.cases contextN (Fin.cases e.typed (fun i => Fin.elim0 i)))
  | .dbl e => declaration (.d Γn e.quote)
      (Fin.cases contextN (Fin.cases e.typed (fun i => Fin.elim0 i)))

def familyTyped : Proof (Judgment.type (.extend Γn N) (familyB : PExpr (Fin 1 ⊕ SingleV))) := by
  have hc := ctxExtend Γn N contextN (typeN Γn contextN)
  have hx : Proof (Judgment.term (.extend Γn N) (.var (.inl 0)) N) := by
    simpa [Context.lookup, N] using varTerm (.extend Γn N) (.inl 0) hc
  exact declaration (.B (.extend Γn N) (.var (.inl 0)))
    (Fin.cases hc (Fin.cases hx (fun i => Fin.elim0 i)))

def raw (e : Ix) := (SourceCode.snd (.pair e)).quote
def resultType (e : Ix) : PExpr SingleV := B (s e.quote)

def rawTyped (e : Ix) : Proof (Judgment.term Γn (raw e) (resultType e)) := by
  have hs := (Ix.succ e).typed
  have ht : Proof (Judgment.term Γn (t e.quote) (Elimination.instantiate familyB (s e.quote))) := by
    simpa [DependentPairDeclarations.Rule.schema, Elimination.instantiate, familyB, B, Expr.subst] using
      declaration (.t Γn e.quote) (Fin.cases contextN (Fin.cases e.typed (fun i => Fin.elim0 i)))
  have hp := pairRule (.pair Γn N familyB (s e.quote) (t e.quote))
    (Fin.cases contextN (Fin.cases (typeN Γn contextN) (Fin.cases familyTyped
      (Fin.cases hs (Fin.cases ht (fun i => Fin.elim0 i))))))
  have ho := pairRule (.second Γn N familyB (SourcePair.pair e).quote)
    (Fin.cases contextN (Fin.cases (typeN Γn contextN) (Fin.cases familyTyped
      (Fin.cases hp (fun i => Fin.elim0 i)))))
  have hf := pairRule (.firstBeta Γn N familyB (s e.quote) (t e.quote))
    (Fin.cases contextN (Fin.cases (typeN Γn contextN) (Fin.cases familyTyped
      (Fin.cases hs (Fin.cases ht (fun i => Fin.elim0 i))))))
  have he := structural (.familyCong Γn N familyB
      (Projection.fst N familyB (SourcePair.pair e).quote) (s e.quote))
    (Fin.cases contextN (Fin.cases (typeN Γn contextN) (Fin.cases familyTyped (Fin.cases hf (fun i => Fin.elim0 i)))))
  exact structural (.convert Γn (raw e)
      (Elimination.instantiate familyB (Projection.fst N familyB (SourcePair.pair e).quote))
      (resultType e)) (Fin.cases ho (Fin.cases he (fun i => Fin.elim0 i)))

def afterF (e : Ix) : Derivation (projectionPresentation true) (fun _ => Empty)
    (Judgment.term Γn (raw e) (resultType e)) := projectionInclusion.transport (fun _ h => Empty.elim h) (rawTyped e)
def afterG (e : Ix) := compile (rawTyped e)
theorem twoStage (e : Ix) : afterG e =
    fullG.transportClosed (TypedSubstitution.fullEliminationLocal _) (afterF e) := rfl

end IncrementalNative
