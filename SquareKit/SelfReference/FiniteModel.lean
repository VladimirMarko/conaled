import SquareKit.SelfReference.Native

/-! An inhabited modal interpretation and rejected laws for #460. -/
namespace SquareKit.SelfReference.FiniteModel

inductive World where
  | root | leaf
  deriving DecidableEq

/-- Atom zero is the bottom diagonal; every other atom is true. -/
def model : Model where
  World := World
  access u v := u = .root ∧ v = .leaf
  transitive := by rintro u v w ⟨_, hv⟩ ⟨hv', _⟩; cases hv.symm.trans hv'
  atom n w := n = 0 → w = .root

def negative : Formula := .atom 0
def positive : Formula := .atom 1
def target : Formula := .atom 2 ⟶ .atom 2

/-- Exactly four named diagonal axioms. There is no arbitrary validity axiom. -/
inductive Axioms : Theory where
  | negativeForward : Axioms (negative ⟶ (□negative ⟶ .bot))
  | negativeBackward : Axioms ((□negative ⟶ .bot) ⟶ negative)
  | positiveForward : Axioms (positive ⟶ (□positive ⟶ target))
  | positiveBackward : Axioms ((□positive ⟶ target) ⟶ positive)

theorem valid_axioms (P : Formula) (a : Axioms P) : model.Valid P := by
  cases a <;> intro w <;> cases w <;>
    simp [Model.holds, model, negative, positive, target]

def bottomDiagonal : Diagonal Axioms .bot where
  sentence := negative
  forward := .ax .negativeForward
  backward := .ax .negativeBackward

def positiveDiagonal : Diagonal Axioms target where
  sentence := positive
  forward := .ax .positiveForward
  backward := .ax .positiveBackward

theorem consistent : Consistent Axioms := model.consistent .root valid_axioms

def positiveReflection : Theorem Axioms (□target ⟶ target) :=
  .intro (.closed (.identity (.atom 2)))

/-- Uses the public conditional Löb construction with concrete diagonal trees. -/
def positiveApplication : Theorem Axioms target := lob positiveDiagonal positiveReflection

theorem positiveApplication_valid : model.Valid target :=
  fun w => positiveApplication.sound model valid_axioms w (fun i => Fin.elim0 i)

theorem rejected_reflection : ¬ Nonempty (Theorem Axioms (□Formula.bot ⟶ .bot)) :=
  no_reflection consistent bottomDiagonal

theorem rejected_transparency : ¬ Nonempty (Derives Axioms [□Formula.bot] .bot) :=
  no_contextual_reflection consistent bottomDiagonal

/-- An actual hypothesis proof exists, but its proposed open necessitation does not. -/
def openSentence : Derives Axioms [negative] negative := .here

theorem rejected_open_necessitation : ¬ Nonempty (Derives Axioms [negative] (□negative)) := by
  rintro ⟨d⟩
  have h := d.sound model valid_axioms World.root
    (by intro i; refine Fin.cases ?_ (fun j => Fin.elim0 j) i
        simp [Model.holds, model, negative])
  have bad := h .leaf ⟨rfl, rfl⟩
  simp [Model.holds, model, negative] at bad

/-- Ordinary contextual identity does not suffice for theorem-level reflection. -/
theorem no_open_necessitation_rule : ¬ Nonempty
    (∀ (Γ : Context) (P : Formula), Derives Axioms Γ P → Derives Axioms Γ (□P)) := by
  rintro ⟨rule⟩
  exact rejected_open_necessitation ⟨rule _ _ openSentence⟩

/-- Transparency plus the bottom diagonal is deliberately incompatible.
This extends the axiom theory, and is not the consistent fixture above. -/
inductive TransparentAxioms : Theory where
  | original {P} : Axioms P → TransparentAxioms P
  | quote : TransparentAxioms (negative ⟶ □negative)
  | reflect : TransparentAxioms (□negative ⟶ negative)

def transparentDiagonal : Diagonal TransparentAxioms .bot where
  sentence := negative
  forward := .ax (.original .negativeForward)
  backward := .ax (.original .negativeBackward)

def curryBottom : Theorem TransparentAxioms .bot :=
  curry transparentDiagonal (.ax .quote) (.ax .reflect)

theorem transparent_inconsistent : ¬ Consistent TransparentAxioms := fun h => h ⟨curryBottom⟩

end SquareKit.SelfReference.FiniteModel
