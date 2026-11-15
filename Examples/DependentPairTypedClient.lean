import Examples.DependentPairTheoryTransport
import SquareKit.DependentDeclarationMaps
import SquareKit.DependentProjectionInclusion
import SquareKit.DependentProjectionPresentationSubstitution

/-! Closed derivations of the selected dependent client. -/
namespace SquareKit.DependentPairTypedClient
open DependentTheoryMaps DependentPairPresentations DependentPairJudgments
open DependentPairTheoryTransport
open Elimination (instantiate)

abbrev R := projectionPresentation false
abbrev Proof (j : Judgment projectionSignature) := Derivation R (fun _ => Empty) j

def structural (r : StructuralRule projectionSignature)
    (ps : ∀ i : Fin (StructuralRule.schema r).premises.length,
      Proof ((StructuralRule.schema r).premises.get i)) : Proof (StructuralRule.schema r).conclusion :=
  Derivation.rule (R := R) (.inl r) ps

def declaration (r : DependentPairDeclarations.Rule projectionSignature)
    (ps : ∀ i : Fin (r.schema DependentPairDeclarations.projection).premises.length,
      Proof ((r.schema DependentPairDeclarations.projection).premises.get i)) :
    Proof (r.schema DependentPairDeclarations.projection).conclusion :=
  Derivation.rule (R := R) (.inr (.inr (.inr (.inl r)))) ps

def pairRule (r : ProjectionRule false)
    (ps : ∀ i : Fin r.schema.premises.length, Proof (r.schema.premises.get i)) :
    Proof r.schema.conclusion := Derivation.rule (R := R) (.inr (.inl r)) ps

def declarationCongruence (r : DependentPairDeclarations.Congruence projectionSignature)
    (ps : ∀ i : Fin (r.schema DependentPairDeclarations.projection).premises.length,
      Proof ((r.schema DependentPairDeclarations.projection).premises.get i)) :
    Proof (r.schema DependentPairDeclarations.projection).conclusion :=
  Derivation.rule (R := R) (.inr (.inr (.inr (.inr r)))) ps

def Γn : Context projectionSignature SingleV := .extend .empty N
def Γny : Context projectionSignature (Fin 1 ⊕ SingleV) := .extend Γn (B (.var (.inl 0)))
def Γ : Context projectionSignature ClientV :=
  .extend Γny (C (.var (.inr (.inl 0))) (.var (.inl 0)))

open Judgment

def emptyContext : Proof (ctx (.empty : Context projectionSignature Empty)) :=
  structural .empty (fun i => Fin.elim0 i)

def ctxExtend (Γ : Context projectionSignature V) (A : PExpr V)
    (hΓ : Proof (ctx Γ)) (hA : Proof (type Γ A)) : Proof (ctx (.extend Γ A)) :=
  structural (.extend Γ A) (Fin.cases hΓ (Fin.cases hA (fun i => Fin.elim0 i)))

def varTerm (Γ : Context projectionSignature V) (v : V) (hΓ : Proof (ctx Γ)) :
    Proof (term Γ (.var v) (Γ.lookup v)) :=
  structural (.variable Γ v) (Fin.cases hΓ (fun i => Fin.elim0 i))

def typeN (Γ : Context projectionSignature V) (hΓ : Proof (ctx Γ)) : Proof (type Γ N) :=
  declaration (.N Γ) (Fin.cases hΓ (fun i => Fin.elim0 i))

def contextN : Proof (ctx Γn) := ctxExtend .empty N emptyContext (typeN .empty emptyContext)

def varN : Proof (term Γn (.var m) N) := by
  simpa [Γn, m, Context.lookup, N] using varTerm Γn m contextN

def contextNY : Proof (ctx Γny) := by
  apply ctxExtend Γn (B (.var (.inl 0))) contextN
  exact declaration (.B Γn (.var m))
    (Fin.cases contextN (Fin.cases varN (fun i => Fin.elim0 i)))

def typeC : Proof (type Γny (C (.var (.inr (.inl 0))) (.var (.inl 0)))) := by
  apply declaration (.C Γny (.var (.inr (.inl 0))) (.var (.inl 0)))
  refine Fin.cases contextNY (Fin.cases ?_ (Fin.cases ?_ (fun i => Fin.elim0 i)))
  · simpa [Γny, Γn, Context.lookup, N, DependentPairDeclarations.Rule.schema] using varTerm Γny (.inr (.inl 0)) contextNY
  · simpa [Γny, Context.lookup, B, DependentPairDeclarations.Rule.schema] using varTerm Γny (.inl 0) contextNY

def context : Proof (ctx Γ) := ctxExtend Γny _ contextNY typeC

def selectedN : Proof (term Γ (.var n) N) := by
  simpa [Γ, Γny, Γn, n, Context.lookup, N] using varTerm Γ n context

def selectedY : Proof (term Γ (.var y) (B (.var n))) := by
  simpa [Γ, Γny, n, y, Context.lookup, B] using varTerm Γ y context

def selectedZ : Proof (term Γ (.var z) (C (.var n) (.var y))) := by
  simpa [Γ, n, y, z, Context.lookup, C] using varTerm Γ z context

/-- The shared client is a conversion of the chosen variable z, not a witness search. -/
def selectedClient : Proof (term Γ selectedRaw clientType) := by
  have hA := typeN Γ context
  have hc := ctxExtend Γ N context hA
  have hx : Proof (term (.extend Γ N) (.var (.inl 0)) N) := by
    simpa [Context.lookup, N] using varTerm (.extend Γ N) (.inl 0) hc
  have hB : Proof (type (.extend Γ N) familyB) :=
    declaration (.B (.extend Γ N) (.var (.inl 0)))
      (Fin.cases hc (Fin.cases hx (fun i => Fin.elim0 i)))
  have hy : Proof (term Γ (.var y) (instantiate familyB (.var n))) := by
    simpa [Elimination.instantiate, familyB, B, Expr.subst] using selectedY
  have heq : Proof (termEq Γ (Projection.snd N familyB q) (.var y) (B (.var n))) := by
    have h := pairRule (.secondBeta Γ N familyB (.var n) (.var y))
      (Fin.cases context (Fin.cases hA (Fin.cases hB
        (Fin.cases selectedN (Fin.cases hy (fun i => Fin.elim0 i))))))
    simpa [ProjectionRule.schema, q, Elimination.instantiate, familyB, B, Expr.subst] using h
  have hn := structural (.termRefl Γ (.var n) N) (Fin.cases selectedN (fun i => Fin.elim0 i))
  have ht : Proof (typeEq Γ clientType (C (.var n) (.var y))) :=
    declarationCongruence (.C Γ (.var n) (.var n) (Projection.snd N familyB q) (.var y))
      (Fin.cases context (Fin.cases hn (Fin.cases heq (Fin.cases selectedY (fun i => Fin.elim0 i)))))
  have hs := structural (.typeSymm Γ clientType (C (.var n) (.var y)))
    (Fin.cases ht (fun i => Fin.elim0 i))
  exact structural (.convert Γ (.var z) (C (.var n) (.var y)) clientType)
    (Fin.cases selectedZ (Fin.cases hs (fun i => Fin.elim0 i)))

open TypedSubstitution

def sigmaTyped : Typed (R := R) (H := fun _ => Empty) Γ Γn sigmaRaw where
  context := contextN
  component v := by
    have hs := declaration (.s Γn (.var m))
      (Fin.cases contextN (Fin.cases varN (fun i => Fin.elim0 i)))
    have ht := declaration (.t Γn (.var m))
      (Fin.cases contextN (Fin.cases varN (fun i => Fin.elim0 i)))
    have hu := declaration (.u Γn (.var m))
      (Fin.cases contextN (Fin.cases varN (fun i => Fin.elim0 i)))
    cases v with
    | inl i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simpa [Γ, Γny, Γn, Context.lookup, sigmaRaw, u, C, s, t,
        DependentPairDeclarations.Rule.schema, Form.subst, Expr.subst_rename,
        Proof, TypedSubstitution.Proof, Judgment.term] using hu
    | inr v =>
      cases v with
      | inl i =>
        have hi : i = 0 := Subsingleton.elim _ _
        subst i
        simpa [Γ, Γny, Γn, Context.lookup, sigmaRaw, t, B, s,
          DependentPairDeclarations.Rule.schema, Form.subst, Expr.subst_rename,
        Proof, TypedSubstitution.Proof, Judgment.term] using ht
      | inr v =>
        cases v with
        | inl i =>
          have hi : i = 0 := Subsingleton.elim _ _
          subst i
          simpa [Γ, Γny, Γn, Context.lookup, sigmaRaw, s, N,
            DependentPairDeclarations.Rule.schema, Form.subst, Expr.subst_rename,
        Proof, TypedSubstitution.Proof, Judgment.term] using hs
        | inr v => exact Empty.elim v

def tauTyped : Typed (R := R) (H := fun _ => Empty) Γn Γn tauRaw where
  context := contextN
  component v := by
    cases v with
    | inl i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      have hd := declaration (.d Γn (.var m))
        (Fin.cases contextN (Fin.cases varN (fun i => Fin.elim0 i)))
      simpa [Γn, Context.lookup, tauRaw, d, N,
        DependentPairDeclarations.Rule.schema, Form.subst, Expr.subst_rename,
        Proof, TypedSubstitution.Proof, Judgment.term] using hd
    | inr v => exact Empty.elim v

/-- Both substitutions use the proved admissibility theorem for the complete
projection presentation. The selected syntax is exactly u(d(k)). -/
def selectedSigma : Proof (term Γn (u (.var m)) (Expr.subst sigmaRaw clientType)) :=
  substituteFullProjection false selectedClient Γn sigmaRaw sigmaTyped

def selectedTwice : Proof
    (term Γn (u (d (.var m))) (Expr.subst tauRaw (Expr.subst sigmaRaw clientType))) := by
  have h := substituteFullProjection false selectedSigma Γn tauRaw tauTyped
  change Proof (term Γn (Expr.subst tauRaw (u (.var m)))
    (Expr.subst tauRaw (Expr.subst sigmaRaw clientType))) at h
  simpa only [DependentPairTheoryTransport.subst_u, Expr.subst_var, tauRaw, m] using h

/-- The first interpretation replays the complete independent beta/eta table. -/
def selectedAfterF : Derivation (projectionPresentation true) (fun _ => Empty)
    (term Γn (u (d (.var m))) (Expr.subst tauRaw (Expr.subst sigmaRaw clientType))) :=
  projectionInclusion.transport (fun _ h => Empty.elim h) selectedTwice

end SquareKit.DependentPairTypedClient
