import Examples.DependentPairSharedFragment

/-! Native typing and actual fullG provenance for the bounded shared-meaning
fragment. The target interface is the compiled image of these derivations. -/
noncomputable section
namespace SquareKit.DependentPairSharedTyping
open DependentTheoryMaps DependentPairPresentations DependentPairJudgments
open DependentPairTheoryTransport DependentPairTypedClient DependentPairComputedTyping
open DependentPairSharedFragment Judgment

def sourceJudgment : Shape → Judgment projectionSignature
  | .index e => term Γn e.expression N
  | .packet e => term Γn (pairRaw e) (Projection.P N familyB)
  | .second e => term Γn (secondRaw e)
      (Elimination.instantiate familyB (Projection.fst N familyB (pairRaw e)))

abbrev Native (j : Sentence p) := DependentPairTypedClient.Proof (sourceJudgment j.shape)

/-- Each rule consumes its actual premise derivation. The pair constructor
obtains both components from its typed index; projection uses its typed pair. -/
def nativeRule (r : Step) (xs : (i : r.Arity) →
    DependentPairTypedClient.Proof (sourceJudgment (r.premise i))) :
    DependentPairTypedClient.Proof (sourceJudgment r.conclusion) := by
  cases r with
  | «variable» v => exact indexTyped (.var v)
  | successor e =>
    exact declaration (.s Γn e.expression)
      (Fin.cases contextN (Fin.cases (xs ()) (fun i => Fin.elim0 i)))
  | double e =>
    exact declaration (.d Γn e.expression)
      (Fin.cases contextN (Fin.cases (xs ()) (fun i => Fin.elim0 i)))
  | pair e => exact pairFromTyped e (xs ())
  | second e => exact secondFromPair e (xs ())

def nativeModel (p : Phase) : DependentBranchTheoryMaps.Model (rules p) Native where
  rule := nativeRule

def nativeProof {p s} (d : DependentPairSharedFragment.Proof p s) :
    DependentPairTypedClient.Proof (sourceJudgment s) :=
  d.interpret (nativeModel p) (fun _ e => e.elim)

theorem native_translate {p q s} (d : DependentPairSharedFragment.Proof p s) :
    nativeProof (translate (q := q) d) = nativeProof d := by
  apply DependentBranchTheoryMaps.TheoryMap.interpret_transport
    (pass p q) (nativeModel p) (nativeModel q) (fun _ => id)
  · intro r xs
    rfl
  · intro j e
    exact e.elim

/-- This selected target proof is obtained by the existing full local rule
certificates. Its semantic interface retains the bounded source provenance;
it is not an interpreter for arbitrary elimination-calculus proofs. -/
def targetProof {s} (d : DependentPairSharedFragment.Proof .target s) :
    Derivation eliminationPresentation (fun _ => Empty) (Judgment.map G (sourceJudgment s)) :=
  compile (nativeProof d)

theorem translation_is_fullG {p s} (d : DependentPairSharedFragment.Proof p s) :
    targetProof (translate d) = compile (nativeProof d) := by
  unfold targetProof
  rw [native_translate]

theorem two_stages_is_fullG {s} (d : DependentPairSharedFragment.Proof .source s) :
    targetProof (translate (translate (q := .extended) d)) = compile (nativeProof d) := by
  rw [translation_is_fullG, native_translate]

/-- The native route uses the retained F inclusion and genuine G certificates,
including their administrative typed substitutions, before final erasure. -/
theorem two_stages_native_certificates {s} (d : DependentPairSharedFragment.Proof .source s) :
    targetProof (translate (translate (q := .extended) d)) =
      Administrative.erase (TypedSubstitution.fullEliminationLocal _) (fun _ h => Empty.elim h)
        (Administrative.pairFG.transport (fun _ h => Empty.elim h)
          (Administrative.embed (nativeProof d))) := by
  rw [two_stages_is_fullG]
  exact (Administrative.pair_erases _).symm

theorem native_index (p : Phase) (e : IndexTerm SingleV) :
    nativeProof (indexProof p e) = indexTyped e := by
  induction e with
  | var v => rfl
  | successor e ih =>
    change declaration (.s Γn e.expression)
      (Fin.cases contextN (Fin.cases (nativeProof (indexProof p e)) (fun i => Fin.elim0 i))) = _
    rw [ih]
    rfl
  | double e ih =>
    change declaration (.d Γn e.expression)
      (Fin.cases contextN (Fin.cases (nativeProof (indexProof p e)) (fun i => Fin.elim0 i))) = _
    rw [ih]
    rfl

theorem native_packet (p : Phase) (e : IndexTerm SingleV) :
    nativeProof (packetProof p e) = pairTyped e := by
  change pairFromTyped e (nativeProof (indexProof p e)) = _
  rw [native_index]
  rfl

theorem native_second (p : Phase) (e : IndexTerm SingleV) :
    nativeProof (secondProof p e) = secondTyped e := by
  change secondFromPair e (nativeProof (packetProof p e)) = _
  rw [native_packet]
  rfl

theorem compiled_second (e : IndexTerm SingleV) :
    targetProof (translate (secondProof .source e)) = compiledSecond e := by
  rw [translation_is_fullG, native_second]
  rfl

def sourceTerm : Shape → PExpr SingleV
  | .index e => e.expression
  | .packet e => pairRaw e
  | .second e => secondRaw e

def targetTerm (s : Shape) : EExpr SingleV := G.act (sourceTerm s)

theorem target_pair (e : IndexTerm SingleV) : targetTerm (.packet e) =
    Elimination.pack (G.act N) (G.act familyB) (G.act (s e.expression)) (G.act (t e.expression)) :=
  G_pair _ _ _ _

theorem target_second (e : IndexTerm SingleV) : targetTerm (.second e) =
    Elimination.second (G.act N) (G.act familyB) (G.act (pairRaw e)) :=
  G_second _ _ _

def firstIndex : IndexTerm SingleV := .successor (.var m)
def finalIndex : IndexTerm SingleV := .successor (.double (.var m))

theorem first_substitution : Expr.subst successorSub (secondRaw (.var m)) = secondRaw firstIndex := by
  simp [secondRaw, pairRaw, firstIndex, IndexTerm.expression, familyB, N, B, s, t,
    DependentPairDeclarations.Projection.N, DependentPairDeclarations.Projection.B,
    DependentPairDeclarations.Projection.s, DependentPairDeclarations.Projection.t,
    Expr.lift, successorSub, m]

theorem second_substitution : Expr.subst tauRaw (secondRaw firstIndex) = secondRaw finalIndex := by
  simp [secondRaw, pairRaw, firstIndex, finalIndex, IndexTerm.expression, familyB, N, B, s, t, d,
    DependentPairDeclarations.Projection.N, DependentPairDeclarations.Projection.B,
    DependentPairDeclarations.Projection.s, DependentPairDeclarations.Projection.t,
    DependentPairDeclarations.Projection.d, Expr.lift, tauRaw, m]

theorem selected_second_substitution :
    Expr.subst tauRaw (Expr.subst successorSub (secondRaw (.var m))) = secondRaw finalIndex := by
  rw [first_substitution, second_substitution]

theorem target_second_substitution :
    Expr.subst (fun v => G.act (tauRaw v))
      (Expr.subst (fun v => G.act (successorSub v)) (targetTerm (.second (.var m)))) =
        targetTerm (.second finalIndex) := by
  unfold targetTerm sourceTerm
  rw [← G.substitution, ← G.substitution, selected_second_substitution]

/-- The final term and dependent type are obtained by the actual two typed
substitutions, not merely by constructing another derivation at the final index. -/
def twiceTyped : DependentPairTypedClient.Proof (sourceJudgment (.second finalIndex)) := by
  have h := secondTwice (.var m)
  change DependentPairTypedClient.Proof (term Γn
    (Expr.subst tauRaw (Expr.subst successorSub (secondRaw (.var m))))
    (Expr.subst tauRaw (Expr.subst successorSub
      (Elimination.instantiate familyB (Projection.fst N familyB (pairRaw (.var m))))))) at h
  simpa [sourceJudgment, secondRaw, pairRaw, finalIndex, IndexTerm.expression,
    familyB, N, B, s, t, d, DependentPairDeclarations.Projection.N,
    DependentPairDeclarations.Projection.B, DependentPairDeclarations.Projection.s,
    DependentPairDeclarations.Projection.t, DependentPairDeclarations.Projection.d,
    Expr.lift, successorSub, tauRaw, m] using h

def compiledTwiceTyped : Derivation eliminationPresentation (fun _ => Empty)
    (Judgment.map G (sourceJudgment (.second finalIndex))) := compile twiceTyped

end SquareKit.DependentPairSharedTyping
