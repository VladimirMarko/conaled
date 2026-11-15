import Examples.DependentPairComputedTyping
import SquareKit.DependentBranchSemantics

/-! A bounded dependent pair fragment, with an explicit quotation into the
retained projection and elimination theories. Its proof trees retain the rules
used to construct the selected value. -/
namespace SquareKit.DependentPairSharedFragment
open DependentTheoryMaps DependentPairTheoryTransport
set_option backward.isDefEq.respectTransparency false

inductive Phase where | source | extended | target
  deriving DecidableEq

inductive Shape where
  | index (e : IndexTerm SingleV)
  | packet (e : IndexTerm SingleV)
  | second (e : IndexTerm SingleV)

structure Sentence (p : Phase) where
  shape : Shape

inductive Step where
  | variable (v : SingleV)
  | successor (e : IndexTerm SingleV)
  | double (e : IndexTerm SingleV)
  | pair (e : IndexTerm SingleV)
  | second (e : IndexTerm SingleV)

def Step.Arity : Step → Type
  | .variable _ => Empty
  | _ => Unit

def Step.premise : (r : Step) → r.Arity → Shape
  | .variable _, i => nomatch i
  | .successor e, _ => .index e
  | .double e, _ => .index e
  | .pair e, _ => .index e
  | .second e, _ => .packet e

def Step.conclusion : Step → Shape
  | .variable v => .index (.var v)
  | .successor e => .index (.successor e)
  | .double e => .index (.double e)
  | .pair e => .packet e
  | .second e => .second e

def rules (p : Phase) : DependentBranchTheoryMaps.Rules (Sentence p) where
  Label := Step
  Arity := Step.Arity
  premise r i := ⟨r.premise i⟩
  conclusion r := ⟨r.conclusion⟩

abbrev Proof (p : Phase) (s : Shape) :=
  DependentBranchTheoryMaps.Derivation (rules p) (fun _ => Empty) (⟨s⟩ : Sentence p)

def indexProof (p : Phase) : (e : IndexTerm SingleV) → Proof p (.index e)
  | .var v => DependentBranchTheoryMaps.Derivation.rule (R := rules p) (Step.variable v) (fun i => nomatch i)
  | .successor e => DependentBranchTheoryMaps.Derivation.rule (R := rules p) (Step.successor e) (fun _ => indexProof p e)
  | .double e => DependentBranchTheoryMaps.Derivation.rule (R := rules p) (Step.double e) (fun _ => indexProof p e)

def packetProof (p : Phase) (e : IndexTerm SingleV) : Proof p (.packet e) :=
  DependentBranchTheoryMaps.Derivation.rule (R := rules p) (Step.pair e) (fun _ => indexProof p e)

def secondProof (p : Phase) (e : IndexTerm SingleV) : Proof p (.second e) :=
  DependentBranchTheoryMaps.Derivation.rule (R := rules p) (Step.second e) (fun _ => packetProof p e)

/-- The sentence map changes its quotation phase. The target quote is G, so
pair and projection become pack and dependent split, not the original syntax. -/
def sentenceMap {p q : Phase} (j : Sentence p) : Sentence q := ⟨j.shape⟩

def pass (p q : Phase) : DependentBranchTheoryMaps.TheoryMap (rules p) (rules q) sentenceMap where
  certificate r := DependentBranchTheoryMaps.Derivation.rule (R := rules q) r (fun i => .hyp ⟨i,rfl⟩)

def translate {p q} {s} (d : Proof p s) : Proof q s :=
  (pass p q).transport (fun _ e => e.elim) d

end SquareKit.DependentPairSharedFragment
