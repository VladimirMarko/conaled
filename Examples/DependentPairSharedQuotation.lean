import Examples.DependentPairSharedTyping
import Examples.DependentPairSharedCode
import SquareKit.DependentDeclarationMaps

/-! Executable code quotes the actual term carried by the fullG typing proof.
This prevents agreement of selected values alone from standing in for a syntax
connection between independent programs. -/
namespace SquareKit.DependentPairSharedFragment
open DependentTheoryMaps DependentPairPresentations DependentPairTheoryTransport
open DependentPairComputedTyping DependentPairSharedTyping
set_option backward.isDefEq.respectTransparency false

def Code.sourceQuote : {p : Phase} → {t : Tag} → Code p t → PExpr SingleV
  | _, _, .load v => .var v
  | _, _, .successor c => s c.sourceQuote
  | _, _, .double c => d c.sourceQuote
  | _, _, .pair c => Projection.pair N familyB (s c.sourceQuote) (t c.sourceQuote)
  | _, _, .etaPair c => Projection.pair N familyB (s c.sourceQuote) (t c.sourceQuote)
  | _, _, .pack c => Projection.pair N familyB (s c.sourceQuote) (t c.sourceQuote)
  | _, _, .project c => Projection.snd N familyB c.sourceQuote
  | _, _, .etaProject c => Projection.snd N familyB c.sourceQuote
  | _, _, .split c => Projection.snd N familyB c.sourceQuote

def Code.targetQuote : {p : Phase} → {t : Tag} → Code p t → EExpr SingleV
  | _, _, .load v => .var v
  | _, _, .successor c => DependentPairDeclarations.Elimination.s c.targetQuote
  | _, _, .double c => DependentPairDeclarations.Elimination.d c.targetQuote
  | _, _, .pair c => Elimination.pack (G.act N) (G.act familyB)
      (DependentPairDeclarations.Elimination.s c.targetQuote) (DependentPairDeclarations.Elimination.t c.targetQuote)
  | _, _, .etaPair c => Elimination.pack (G.act N) (G.act familyB)
      (DependentPairDeclarations.Elimination.s c.targetQuote) (DependentPairDeclarations.Elimination.t c.targetQuote)
  | _, _, .pack c => Elimination.pack (G.act N) (G.act familyB)
      (DependentPairDeclarations.Elimination.s c.targetQuote) (DependentPairDeclarations.Elimination.t c.targetQuote)
  | _, _, .project c => Elimination.second (G.act N) (G.act familyB) c.targetQuote
  | _, _, .etaProject c => Elimination.second (G.act N) (G.act familyB) c.targetQuote
  | _, _, .split c => Elimination.second (G.act N) (G.act familyB) c.targetQuote

/-- Real syntax preservation for every code tree, including the dependent
second-projection motive hidden in `Elimination.second`. -/
theorem Code.quote_G {p k} (c : Code p k) : G.act c.sourceQuote = c.targetQuote := by
  induction c with
  | load v => exact G.on_var v
  | successor c ih =>
    change G.act (DependentPairDeclarations.Terms.s DependentPairDeclarations.projection c.sourceQuote) = _
    rw [DependentPairDeclarations.G_s, ih]
    rfl
  | double c ih =>
    change G.act (DependentPairDeclarations.Terms.d DependentPairDeclarations.projection c.sourceQuote) = _
    rw [DependentPairDeclarations.G_d, ih]
    rfl
  | pair c ih | etaPair c ih | pack c ih =>
    simp only [Code.sourceQuote, Code.targetQuote, G_pair]
    change Elimination.pack _ _
      (G.act (DependentPairDeclarations.Terms.s DependentPairDeclarations.projection c.sourceQuote))
      (G.act (DependentPairDeclarations.Terms.t DependentPairDeclarations.projection c.sourceQuote)) = _
    rw [DependentPairDeclarations.G_s, DependentPairDeclarations.G_t, ih]
  | project c ih | etaProject c ih | split c ih =>
    simp only [Code.sourceQuote, Code.targetQuote, G_second, ih]

@[simp] theorem packetCode_quote (p) (c : Code p .index) :
    (packetCode p c).sourceQuote = Projection.pair N familyB (s c.sourceQuote) (t c.sourceQuote) := by
  cases p <;> rfl
@[simp] theorem secondCode_quote (p) (c : Code p .packet) :
    (secondCode p c).sourceQuote = Projection.snd N familyB c.sourceQuote := by cases p <;> rfl

theorem code_rule_quote (p) (r : Step) (cs : (i : r.Arity) → Code p (r.premise i).tag)
    (hs : ∀ i, (cs i).sourceQuote = sourceTerm (r.premise i)) :
    ((codeModel p).rule r cs).sourceQuote = sourceTerm r.conclusion := by
  cases r with
  | «variable» v => rfl
  | successor e => change s (cs ()).sourceQuote = s e.expression; rw [hs ()]; rfl
  | double e => change d (cs ()).sourceQuote = d e.expression; rw [hs ()]; rfl
  | pair e =>
    change (packetCode p (cs ())).sourceQuote = pairRaw e
    rw [packetCode_quote, hs ()]
    rfl
  | second e =>
    change (secondCode p (cs ())).sourceQuote = secondRaw e
    rw [secondCode_quote, hs ()]
    rfl

theorem interpret_code_quote {p} {j : Sentence p}
    (d : DependentBranchTheoryMaps.Derivation (rules p) (fun _ => Empty) j) :
    (d.interpret (codeModel p) (fun _ e => e.elim)).sourceQuote = sourceTerm j.shape := by
  induction d with
  | hyp e => exact e.elim
  | rule r ds ih => exact code_rule_quote p r _ ih

theorem compiled_source_quote {p s} (d : Proof p s) :
    (compileCode d).sourceQuote = sourceTerm s := interpret_code_quote d

theorem compiled_target_quote {s} (d : Proof .target s) :
    (compileCode d).targetQuote = targetTerm s := by
  rw [← Code.quote_G, compiled_source_quote]
  rfl

end SquareKit.DependentPairSharedFragment
