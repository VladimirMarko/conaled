import Examples.DependentPairTypedClient
import SquareKit.DependentPairAdministrativeCompilation

/-! Actual constructor and projection derivations for the computed pair client. -/
namespace SquareKit.DependentPairComputedTyping
open DependentTheoryMaps DependentPairPresentations DependentPairJudgments
open DependentPairTheoryTransport DependentPairTypedClient Judgment

def indexTyped : (e : IndexTerm SingleV) → Proof (term Γn e.expression N)
  | .var v => by
    cases v with
    | inl i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact varN
    | inr e => exact e.elim
  | .successor e => declaration (.s Γn e.expression)
      (Fin.cases contextN (Fin.cases (indexTyped e) (fun i => Fin.elim0 i)))
  | .double e => declaration (.d Γn e.expression)
      (Fin.cases contextN (Fin.cases (indexTyped e) (fun i => Fin.elim0 i)))

def familyTyped : Proof (type (.extend Γn N) familyB) := by
  have hc := ctxExtend Γn N contextN (typeN Γn contextN)
  have hx : Proof (term (.extend Γn N) (.var (.inl 0)) N) := by
    simpa [Context.lookup, N] using varTerm (.extend Γn N) (.inl 0) hc
  exact declaration (.B (.extend Γn N) (.var (.inl 0)))
    (Fin.cases hc (Fin.cases hx (fun i => Fin.elim0 i)))

def pairRaw (e : IndexTerm SingleV) : PExpr SingleV :=
  Projection.pair N familyB (s e.expression) (t e.expression)

def secondRaw (e : IndexTerm SingleV) : PExpr SingleV :=
  Projection.snd N familyB (pairRaw e)

def componentsFromTyped (e : IndexTerm SingleV) (he : Proof (term Γn e.expression N)) :
    ∀ i : Fin (ProjectionRule.components Γn N familyB (s e.expression) (t e.expression)).length,
      Proof ((ProjectionRule.components Γn N familyB (s e.expression) (t e.expression)).get i) := by
  refine Fin.cases contextN (Fin.cases (typeN Γn contextN) (Fin.cases familyTyped
    (Fin.cases (declaration (.s Γn e.expression)
      (Fin.cases contextN (Fin.cases he (fun i => Fin.elim0 i))))
      (Fin.cases ?_ (fun i => Fin.elim0 i)))))
  have ht := declaration (.t Γn e.expression)
    (Fin.cases contextN (Fin.cases he (fun i => Fin.elim0 i)))
  change Proof (term Γn (t e.expression) (Elimination.instantiate familyB (s e.expression)))
  change Proof (term Γn (t e.expression) (B (s e.expression))) at ht
  simpa [Elimination.instantiate, familyB, B, Expr.subst] using ht

def componentsTyped (e : IndexTerm SingleV) := componentsFromTyped e (indexTyped e)

def pairFromTyped (e : IndexTerm SingleV) (he : Proof (term Γn e.expression N)) :
    Proof (term Γn (pairRaw e) (Projection.P N familyB)) :=
  pairRule (.pair Γn N familyB (s e.expression) (t e.expression)) (componentsFromTyped e he)

def pairTyped (e : IndexTerm SingleV) := pairFromTyped e (indexTyped e)

def secondFromPair (e : IndexTerm SingleV)
    (hp : Proof (term Γn (pairRaw e) (Projection.P N familyB))) : Proof
    (term Γn (secondRaw e) (Elimination.instantiate familyB (Projection.fst N familyB (pairRaw e)))) :=
  pairRule (.second Γn N familyB (pairRaw e))
    (Fin.cases contextN (Fin.cases (typeN Γn contextN)
      (Fin.cases familyTyped (Fin.cases hp (fun i => Fin.elim0 i)))))

def secondTyped (e : IndexTerm SingleV) := secondFromPair e (pairTyped e)

def secondBeta (e : IndexTerm SingleV) : Proof
    (termEq Γn (secondRaw e) (t e.expression) (B (s e.expression))) := by
  have h := pairRule (.secondBeta Γn N familyB (s e.expression) (t e.expression)) (componentsTyped e)
  simpa [secondRaw, pairRaw, ProjectionRule.schema, Elimination.instantiate,
    familyB, B, Expr.subst] using h

def compiledSecond (e : IndexTerm SingleV) := compile (secondTyped e)

def successorSub : SingleV → PExpr SingleV
  | .inl _ => s (.var m)
  | .inr e => e.elim

def successorSubTyped : TypedSubstitution.Typed (R := R) (H := fun _ => Empty)
    Γn Γn successorSub where
  context := contextN
  component v := by
    cases v with
    | inl i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simpa [Γn, Context.lookup, successorSub, N, Form.subst, Expr.subst_rename,
        Proof, TypedSubstitution.Proof, Judgment.term, IndexTerm.expression, m] using
          indexTyped (.successor (.var m))
    | inr e => exact e.elim

def secondSigma (e : IndexTerm SingleV) :=
  TypedSubstitution.substituteFullProjection false (secondTyped e) Γn successorSub successorSubTyped

def secondTwice (e : IndexTerm SingleV) :=
  TypedSubstitution.substituteFullProjection false (secondSigma e) Γn tauRaw tauTyped

def compiledTwice (e : IndexTerm SingleV) := compile (secondTwice e)

end SquareKit.DependentPairComputedTyping
