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

def componentsTyped (e : IndexTerm SingleV) :
    ∀ i : Fin (ProjectionRule.components Γn N familyB (s e.expression) (t e.expression)).length,
      Proof ((ProjectionRule.components Γn N familyB (s e.expression) (t e.expression)).get i) := by
  refine Fin.cases contextN (Fin.cases (typeN Γn contextN) (Fin.cases familyTyped
    (Fin.cases (indexTyped (.successor e)) (Fin.cases ?_ (fun i => Fin.elim0 i)))))
  have ht := declaration (.t Γn e.expression)
    (Fin.cases contextN (Fin.cases (indexTyped e) (fun i => Fin.elim0 i)))
  change Proof (term Γn (t e.expression) (Elimination.instantiate familyB (s e.expression)))
  change Proof (term Γn (t e.expression) (B (s e.expression))) at ht
  simpa [Elimination.instantiate, familyB, B, Expr.subst] using ht

def pairTyped (e : IndexTerm SingleV) : Proof (term Γn (pairRaw e) (Projection.P N familyB)) :=
  pairRule (.pair Γn N familyB (s e.expression) (t e.expression)) (componentsTyped e)

def secondTyped (e : IndexTerm SingleV) : Proof
    (term Γn (secondRaw e) (Elimination.instantiate familyB (Projection.fst N familyB (pairRaw e)))) :=
  pairRule (.second Γn N familyB (pairRaw e))
    (Fin.cases contextN (Fin.cases (typeN Γn contextN)
      (Fin.cases familyTyped (Fin.cases (pairTyped e) (fun i => Fin.elim0 i)))))

def secondBeta (e : IndexTerm SingleV) : Proof
    (termEq Γn (secondRaw e) (t e.expression) (B (s e.expression))) := by
  have h := pairRule (.secondBeta Γn N familyB (s e.expression) (t e.expression)) (componentsTyped e)
  simpa [secondRaw, pairRaw, ProjectionRule.schema, Elimination.instantiate,
    familyB, B, Expr.subst] using h

def compiledSecond (e : IndexTerm SingleV) := compile (secondTyped e)

end SquareKit.DependentPairComputedTyping
