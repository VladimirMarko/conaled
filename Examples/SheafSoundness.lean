import SquareKit.Internal.SheafSoundness
import Examples.SheafFormula

/-! Experimental source-to-sheaf proof consumers on the finite diamond site. -/
namespace Examples.SheafSoundness
open CategoryTheory Opposite SquareKit.Internal SquareKit.SheafImage
open Examples.SheafImage Examples.SheafImage.Diamond
open Examples.SheafContexts Examples.SheafContexts.Kind
open Examples.SheafFormula

def eRefl : Formula Op [e,b] Relation := .eq (.var .zero) (.var .zero)
def bRefl : Formula Op [b] Relation := .eq (.var .zero) (.var .zero)

theorem eRefl_top : interp eRefl = ⊤ := by ext j ρ; exact iff_true_intro rfl

theorem local_premise (x : Bool) : (interp (.ex eRefl)).obj (op X) (boolEnv (op X) x) := by
  change (localImage (interp eRefl)
    (SquareKit.Internal.SheafContexts.projection relModel sort_sheaves)).obj _ _
  rw [eRefl_top]
  exact Examples.SheafContexts.locally_at_X x

theorem no_global_premise (x : Bool) :
    ¬ (relModel.formula (.ex eRefl)).obj (op X) (boolEnv (op X) x) := by
  rintro ⟨ρ, _, _⟩
  exact no_pointwise_witness ⟨ρ .zero, trivial, rfl⟩

/-- The source rule eliminates E into a conclusion independent of E. -/
theorem eliminateE : Derives (.ex eRefl) bRefl := .elim .refl

theorem elimination_at_X (x : Bool) : (interp bRefl).obj (op X) (boolEnv (op X) x) :=
  SquareKit.Internal.SheafContexts.sound relModel sort_sheaves relation_sheaves eliminateE
    (op X) (local_premise x)

/-- Frobenius.forward uses elimWith; both hypotheses here hold at X. -/
theorem frobenius_at_X (x : Bool) :
    (interp (.ex (.conj bRefl.shift eRefl))).obj (op X) (boolEnv (op X) x) :=
  SquareKit.Internal.SheafContexts.sound relModel sort_sheaves relation_sheaves
    (Frobenius.forward bRefl eRefl) (op X) ⟨rfl, local_premise x⟩

/-- The generic source theorem interprets both derivations, independently of comparison. -/
theorem source_frobenius (h : Formula Op [b] Relation) :
    interp (.conj h (.ex eRefl)) = interp (.ex (.conj h.shift eRefl)) :=
  SquareKit.Internal.SheafContexts.frobenius_valid relModel sort_sheaves relation_sheaves h eRefl

theorem semantic_frobenius (h : Formula Op [b] Relation) :
    interp (.ex (.conj h.shift eRefl)) = interp h ⊓ localImage (interp eRefl)
      (SquareKit.Internal.SheafContexts.projection relModel sort_sheaves) :=
  SquareKit.Internal.SheafContexts.frobenius_semantic_comparison
    relModel sort_sheaves relation_sheaves h eRefl

/-- Reorder the already computed conjunction; the earlier support calculation is reused. -/
theorem selective_body : interp (.ex (.conj equalAtom.shift eRefl)) = interp combined := by
  change localImage (interp equalAtom.shift ⊓ interp eRefl)
    (SquareKit.Internal.SheafContexts.projection relModel sort_sheaves) =
    localImage (interp eRefl ⊓ interp equalAtom.shift)
      (SquareKit.Internal.SheafContexts.projection relModel sort_sheaves)
  exact congrArg (fun Q => localImage Q
    (SquareKit.Internal.SheafContexts.projection relModel sort_sheaves (s := e) (Γ := [b])))
    (inf_comm _ _)

/-- Source interpretation connects the selective sequent to its earlier W/U computation. -/
theorem selective_source : interp (.conj equalAtom (.ex eRefl)) = selected.preimage (sub forget).hom :=
  (source_frobenius equalAtom).trans (selective_body.trans combined_predicate)

theorem selective_source_U (x : Bool) :
    (interp (.conj equalAtom (.ex eRefl))).obj (op U) (boolEnv (op U) x) := by
  rw [selective_source]
  exact Or.inr rfl

theorem selective_source_not_V (x : Bool) :
    ¬ (interp (.conj equalAtom (.ex eRefl))).obj (op V) (boolEnv (op V) x) := by
  rw [selective_source]; change ¬ (V = W ∨ V = U); decide

theorem selective_source_not_X (x : Bool) :
    ¬ (interp (.conj equalAtom (.ex eRefl))).obj (op X) (boolEnv (op X) x) := by
  rw [selective_source]; change ¬ (X = W ∨ X = U); decide

/-- Introduce a Bool witness equal to the natural negation of the old variable. -/
def witnessBody : Formula Op [b,b] Relation := .eq (.var .zero) neg.shift

theorem introduce_negation : Derives (witnessBody.instantiate neg) (.ex witnessBody) :=
  .intro witnessBody neg

theorem introduction_at_X (x : Bool) :
    (interp (.ex witnessBody)).obj (op X) (boolEnv (op X) x) :=
  SquareKit.Internal.SheafContexts.sound relModel sort_sheaves relation_sheaves
    introduce_negation (op X) rfl

/-- Apply the actual source subst constructor to that introduction derivation. -/
theorem substitute_introduction :
    Derives ((witnessBody.instantiate neg).subst negate) ((FormulaCore.ex witnessBody).subst negate) :=
  .subst negate introduce_negation

theorem substituted_introduction_at_X (x : Bool) :
    (interp ((FormulaCore.ex witnessBody).subst negate)).obj (op X) (boolEnv (op X) x) :=
  SquareKit.Internal.SheafContexts.sound relModel sort_sheaves relation_sheaves
    substitute_introduction (op X) rfl

-- Ordinary graph clients remain available without sheaf parameters.
example (n : Nat) : ∃ m, m = n + 1 ∧ 2 * (n + 1) = 2 * m :=
  (Graph.inSet (fun x => x + 1) (fun x => 2 * x) n _).mpr rfl

end Examples.SheafSoundness
