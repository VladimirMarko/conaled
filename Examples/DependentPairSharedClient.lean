import Examples.DependentPairSharedQuotation
import Examples.DependentPairSharedCapabilities
import Examples.DependentPairSharedSubstitution

/-! A selected dependent result shared by actual native proof compilation and
an executable compiler. The semantic domain is the bounded proof image. -/
namespace SquareKit.DependentPairSharedClient
open DependentTheoryMaps DependentPairTheoryTransport DependentPairSharedFragment
open DependentPairSharedTyping
set_option backward.isDefEq.respectTransparency false

abbrev clientIndex := DependentPairSharedTyping.finalIndex

def initial := secondProof .source (.var m)
def finalProof := secondProof .source clientIndex

def initialCode := compileCode initial
def substitutedCode := (initialCode.substitute sigmaIndex).substitute tauIndex

def targetCode := ((compileCode finalProof).pass .extended).pass .target

def environment (_ : SingleV) : Nat := 2

/-- This expected result is specified independently of either compiler. -/
def answer : Packet := ⟨6, ⟨6, by decide⟩⟩

theorem substitutions_compute_code : substitutedCode = compileCode finalProof := rfl

theorem first_substitution_changes_result :
    (initialCode.substitute sigmaIndex).run environment ≠ initialCode.run environment := by
  intro h
  have := congrArg (fun p : Packet => p.1) h
  change 4 = 3 at this
  omega

theorem second_substitution_changes_result :
    substitutedCode.run environment ≠ (initialCode.substitute sigmaIndex).run environment := by
  intro h
  have := congrArg (fun p : Packet => p.1) h
  change 6 = 4 at this
  omega

/-- Substitution is execution in the composed environment, including the
selected dependent packet, not just its first component. -/
theorem two_substitutions_environment : substitutedCode.run environment =
    initialCode.run (fun v => (sigmaIndex v).meaning
      (fun w => (tauIndex w).meaning environment)) := by
  unfold substitutedCode
  rw [Code.substitute_run, Code.substitute_run]

theorem selected_meaning : meaning environment finalProof = answer := by
  rw [meaning_expected]
  rfl

theorem substituted_execution : substitutedCode.run environment = answer := by
  rw [substitutions_compute_code, compileCode_sound, selected_meaning]

theorem target_execution : targetCode.run environment = answer := by
  change (((compileCode finalProof).pass .extended).pass .target).run environment = answer
  rw [Code.pass_run, Code.pass_run, compileCode_sound, selected_meaning]

/-- The two routes meet at the same selected value through the existing
capability composition theorem. -/
theorem selected_joint :
    (realization .target).decode environment ⟨.second clientIndex⟩
      (twoStageCompatible.realization.map environment ⟨.second clientIndex⟩ (compileCode finalProof)) =
    (proofs .target).interpret environment ⟨.second clientIndex⟩
      (twoStageCompatible.proof.map ⟨.second clientIndex⟩ finalProof) :=
  two_stage_joint environment finalProof

theorem targetCode_is_compiled : targetCode =
    compileCode (translate (q := .target) (translate (q := .extended) finalProof)) := by
  rw [compileCode_translate, compileCode_translate]
  rfl

/-- The executable program quotes precisely the term in the actual fullG
compiled dependent judgment, rather than an unrelated program with equal output. -/
theorem targetCode_quote : targetCode.targetQuote = targetTerm (.second clientIndex) := by
  rw [targetCode_is_compiled, compiled_target_quote]

/-- General joint compiler result: native typing uses actual fullG certificates;
code has exactly that raw term and evaluates to the bounded source meaning.
The native proof retains provenance; arbitrary target trees are outside scope. -/
theorem compiled_image {s} (d : DependentPairSharedFragment.Proof .source s) (ρ) :
    targetProof (translate (q := .target) (translate (q := .extended) d)) =
      DependentPairJudgments.compile (nativeProof d) ∧
    (compileCode (translate (q := .target) (translate (q := .extended) d))).targetQuote =
      targetTerm s ∧
    (compileCode (translate (q := .target) (translate (q := .extended) d))).run ρ = meaning ρ d := by
  refine ⟨two_stages_is_fullG d, compiled_target_quote _, ?_⟩
  rw [compileCode_sound, translate_meaning, translate_meaning]

/-- The independently constructed native substitution proof and canonical
bounded proof inhabit the same dependent judgment. No proof-tree equality is asserted. -/
def nativeSubstituted := twiceTyped
def targetSubstituted := compiledTwiceTyped

/-- Genuine G syntax and the actual two object substitutions agree with the
program quotation. The type alignment is checked by nativeSubstituted above. -/
theorem substituted_target_quote :
    Expr.subst (fun v => DependentPairPresentations.G.act (tauRaw v))
      (Expr.subst (fun v => DependentPairPresentations.G.act
        (DependentPairComputedTyping.successorSub v)) (targetTerm (.second (.var m)))) =
      targetCode.targetQuote := by
  rw [targetCode_quote]
  exact target_second_substitution

/-- Same index and inhabited fiber, but a different selected component. -/
def wrongAnswer : Packet := ⟨6, ⟨0, by decide⟩⟩

theorem wrong_same_index : wrongAnswer.1 = answer.1 := rfl

theorem wrong_selection : wrongAnswer ≠ answer := by
  intro h
  have := congrArg (fun p : Packet => p.2.val) h
  change 0 = 6 at this
  omega

theorem execution_rejects_wrong_selection : targetCode.run environment ≠ wrongAnswer := by
  rw [target_execution]
  exact Ne.symm wrong_selection

end SquareKit.DependentPairSharedClient
