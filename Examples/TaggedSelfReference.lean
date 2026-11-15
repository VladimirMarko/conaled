import SquareKit.SelfReference.FiniteModel
import SquareKit.SelfReference.Graph
import SquareKit.SelfReference.Transport

/-! Checked native and shared callers for tagged self-reference (#460). -/
namespace Examples.TaggedSelfReference
open scoped SquareKit.SelfReference
open SquareKit.SelfReference SquareKit.DependentTheoryMaps
open SquareKit.SelfReference.Presentation

/-- Axiom witnesses are retained when changing propositional parameters. -/
inductive Image (T : Theory) (f : Nat → Formula) : Theory where
  | ax {P} : T P → Image T f (Formula.subst f P)

def shift (n : Nat) : Formula := .atom (n + 10)

def shiftedPositive : Theorem (Image FiniteModel.Axioms shift) (.atom 12 ⟶ .atom 12) :=
  substitute shift (fun _ => Image.ax) FiniteModel.positiveApplication

def shiftedDiagonal : Diagonal (Image FiniteModel.Axioms shift) (.atom 12 ⟶ .atom 12) :=
  substituteDiagonal shift (fun _ => Image.ax) FiniteModel.positiveDiagonal

example : shiftedDiagonal.sentence = .atom 11 := rfl

/-- Encoding and decoding preserve the actual native derivation, not only its goal. -/
example : decode (encode FiniteModel.positiveApplication) = FiniteModel.positiveApplication :=
  decode_encode _

example : ¬ Nonempty (Tree FiniteModel.Axioms
    (fun j => {_i : Fin 1 // ([□Formula.bot], □Formula.bot) = j})
    ([□Formula.bot], Formula.bot)) :=
  no_truth_elimination_certificate FiniteModel.consistent FiniteModel.bottomDiagonal

def namedBottom : NamedConstruction FiniteModel.Axioms .bot where
  name := 0
  diagonal := FiniteModel.bottomDiagonal
  named := rfl

example : namedBottom.diagonal.sentence = .atom (namedBottom.graph .provability).erase.selectedName :=
  namedBottom.selected_retained .provability

example : (namedBottom.graph .truth).erase = (namedBottom.graph .provability).erase := rfl

abbrev NoAxioms : Theory := fun _ => Empty

/-- Two different occurrences of precisely the same whole judgment. -/
abbrev Repeated (P : Formula) (j : Judgment) := {_i : Fin 2 // ([], P) = j}

def repeated (P : Formula) : Tree NoAxioms (Repeated P) ([], P) :=
  node (.elim [] P P) (fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · exact node (.intro [] P P) (fun _ =>
        node (.closed [P] P) (fun _ => .hyp ⟨0, rfl⟩))
    · have : j = 0 := Fin.eq_zero j
      subst j
      exact .hyp ⟨1, rfl⟩)

/-- Ordered meta-premise observations of actual trees, including duplicates. -/
def occurrences {T : Theory} {H : Judgment → Type}
    (name : ∀ j, H j → Nat) {j} : Tree T H j → List Nat
  | .hyp h => [name _ h]
  | .rule r ds => (List.ofFn (fun i => occurrences name (ds i))).flatten

example (P : Formula) : occurrences (fun _ p => p.val.val) (repeated P) = [0, 1] := rfl

def renameMap : TheoryMap (rules NoAxioms) (rules NoAxioms) (mapJudgment shift) :=
  substitution shift (fun _ h => nomatch h)

/-- Nonidentity atom renaming preserves both equal-judgment premise occurrences. -/
example (P : Formula) : occurrences (fun _ (i : Fin 2) => i.val)
    (renameMap.transport (H' := fun _ => Fin 2) (fun _ p => p.val) (repeated P)) = [0, 1] := rfl

def tautology : Formula := .atom 0 ⟶ .atom 0

def firstProof : ClosedTree NoAxioms ([], tautology) := encode (.identity (.atom 0))
def secondProof : ClosedTree NoAxioms ([], tautology) :=
  encode (.elim (.identity tautology) (.identity (.atom 0)))

/-- The first proof is a smaller tree; these are distinguishable retained values. -/
def ruleCount {T : Theory} {H : Judgment → Type} {j} : Tree T H j → Nat
  | .hyp _ => 0
  | .rule _ ds => 1 + (List.ofFn (fun i => ruleCount (ds i))).sum

example : ruleCount firstProof = 2 := rfl
example : ruleCount secondProof = 5 := rfl

/-- Grafting dispatches by occurrence even when their judgments are identical. -/
def plug : ∀ j, Repeated tautology j → ClosedTree NoAxioms j :=
  fun _ p => p.property ▸ (if p.val = 0 then firstProof else secondProof)

example : ruleCount ((repeated tautology).graft plug) = 10 := rfl

def shiftedPlug : ∀ j, Repeated tautology j → ClosedTree NoAxioms (mapJudgment shift j) :=
  fun j p => renameMap.transport (fun _ (e : Empty) => e) (plug j p)

/-- The exact tree equality comes from the existing transport/graft law. -/
example : renameMap.transport (fun _ (e : Empty) => e) ((repeated tautology).graft plug) =
    (renameMap.transport (H' := fun j =>
      {_p : Repeated tautology ([], tautology) // mapJudgment shift ([], tautology) = j})
      (fun j p => by
        have e := p.property
        cases e
        exact ⟨p, rfl⟩) (repeated tautology)).graft
      (fun _ p => p.property ▸ shiftedPlug _ p.val) := by
  apply TheoryMap.transport_graft
  intro j p
  rcases p with ⟨i, hi⟩
  cases hi
  rfl

/-- Two successive, nonidentity parameter changes compose on the whole proof tree. -/
example : ((substitution shift (fun _ a => Image.ax a)).comp
      (substitution shift (fun _ a => Image.ax a))).transport
      (fun _ (e : Empty) => e) (encode FiniteModel.positiveApplication) =
    (substitution shift (T := Image FiniteModel.Axioms shift)
      (fun _ a => Image.ax a)).transport (H' := fun _ => Empty) (fun _ (e : Empty) => e)
      ((substitution shift (fun _ a => Image.ax a)).transport
        (fun _ (e : Empty) => e) (encode FiniteModel.positiveApplication)) :=
  substitution_comp shift shift (fun _ a => Image.ax a) (fun _ a => Image.ax a) _

end Examples.TaggedSelfReference
