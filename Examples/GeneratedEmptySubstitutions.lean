import SquareKit.Internal.DependentJudgments.GeneratedSubstitutions
import Examples.DependentStructureBoundary

/-! Source-generated uniqueness and its failure when a primitive substitution
assumption is admitted. Both statements use the same source equality. -/
namespace Examples.GeneratedEmptySubstitutions
open SquareKit.Internal.DependentJudgments (Value)
open SquareKit.Internal.DependentJudgments.Contextual SquareKit.GuardedTheory CategoryTheory
set_option backward.isDefEq.respectTransparency false

namespace Closed
variable {V : Type} {Ω : List (Judgment V)} {A t : Expression V}

/-- Pair a supplied term into an extension, then forget it. This generated
arrow is compared with the empty tuple by a source equality derivation. -/
def pairThenForget (hA : Ty (Ω := Ω) empty A)
    (ht : Tm (Ω := Ω) empty (subTy A (identitySub empty)) t) :
    GeneratedArrow closedArrows Ω .empty .empty
      (comp (weaken empty A) (pair A (identitySub empty) t)) :=
  .comp (.weaken .empty hA) (.pair hA (.identity .empty) ht)

def pairThenForget_eq (hA : Ty (Ω := Ω) empty A)
    (ht : Tm (Ω := Ω) empty (subTy A (identitySub empty)) t) :
    Equal (Ω := Ω)
      (comp (weaken empty A) (pair A (identitySub empty) t))
      (identitySub empty) := (pairThenForget hA ht).empty_unique

/-- Two dependent extensions have the canonical iterated projection as the
unique arrow to empty, including composites and equality conversions. -/
def dependentTail_unique {B σ : Expression V}
    (hA : Ty (Ω := Ω) empty A) (hB : Ty (Ω := Ω) (extend empty A) B)
    (f : GeneratedArrow closedArrows Ω (GeneratedContext.twoExtensions hA hB) .empty σ) :
    Equal (Ω := Ω) σ
      (comp (comp (identitySub empty) (weaken empty A))
        (weaken (extend empty A) B)) := f.empty_unique

end Closed

namespace Declarations
abbrev M := DependentStructureBoundary.ReachableLoops.model
def A : Expression (Fin 2) := .var 0
def t : Expression (Fin 2) := .var 1
def assumptions : List (Judgment (Fin 2)) :=
  [family empty A, term empty (subTy A (identitySub empty)) t]

def typeDeclaration : Ty (Ω := assumptions) empty A := .hypothesis (by simp [assumptions])
def termDeclaration : Tm (Ω := assumptions) empty (subTy A (identitySub empty)) t :=
  .hypothesis (by simp [assumptions])

/-- The type of the declared term is established from the preceding type
declaration; there is no substitution declaration in this example. -/
def termType : Ty (Ω := assumptions) empty (subTy A (identitySub empty)) :=
  typeDeclaration.substitute Ctx.empty.identity

def assignment : Fin 2 → Value M.toStructuralModel :=
  ![.family () (), .term () () ()]

theorem satisfied : ∀ p ∈ assumptions, p.eval (algebra M) assignment := by
  intro p hp
  rcases List.mem_cons.mp hp with h | h
  · subst p
    exact ⟨(), (), rfl, rfl⟩
  · have h' := List.mem_singleton.mp h
    subst p
    refine ⟨(), (), (), rfl, ?_, rfl⟩
    simp [Term.eval, algebra, SquareKit.Internal.DependentJudgments.operation,
      assignment, A, subTy, identitySub, empty, M, DependentStructureBoundary.ReachableLoops.model]

def discarded_pair := Closed.pairThenForget_eq typeDeclaration termDeclaration

/-- A second family mentions the preceding generic variable in both identity
endpoints. Its typing is derived rather than a new raw assumption. -/
def dependentFamily := typeDeclaration.generic.identity typeDeclaration.generic
def dependentContext := GeneratedContext.twoExtensions typeDeclaration dependentFamily

def dependentEmpty := GeneratedArrow.toEmpty (P := closedArrows) dependentContext

def dependentEmpty_unique :=
  Closed.dependentTail_unique typeDeclaration dependentFamily dependentEmpty

end Declarations

namespace Hypothesis
abbrev M := DependentStructureBoundary.ReachableLoops.model
def arrow : Expression Unit := .var ()
def assumptions : List (Judgment Unit) := [substitution empty empty arrow]

def assignment (_ : Unit) : Value M.toStructuralModel := .substitution () () true

theorem satisfied : ∀ p ∈ assumptions, p.eval (algebra M) assignment := by
  intro p hp
  have h : p = substitution empty empty arrow := List.mem_singleton.mp hp
  subst p
  exact ⟨(), (), true, rfl, rfl, rfl⟩

/-- Definedness of equality assumptions is vacuous here and cannot impose
empty-context uniqueness on the admitted primitive arrow. -/
theorem typedAssumptions : TypedAssumptions assumptions := by
  intro s t h
  have h' : Atom.eq s t = substitution empty empty arrow := List.mem_singleton.mp h
  cases h'

def generated : GeneratedArrow (hypothesisArrows assumptions) assumptions .empty .empty arrow :=
  .generator .empty .empty (by exact List.mem_singleton_self _)
    (.hypothesis (List.mem_singleton_self _))

/-- An actual source hypothesis denotes true, while identity denotes false.
Soundness therefore rules out the proposed source equality. -/
theorem not_equal : ¬ Nonempty (Equal (Ω := assumptions) arrow (identitySub empty)) := by
  rintro ⟨d⟩
  have h := interpret d M assignment satisfied
  change Value.substitution (M := M.toStructuralModel) () () true =
    Value.substitution () () false at h
  have hbool : true = false := eq_of_heq (Value.substitution.inj h).2.2
  cases hbool

/-- The same expression is excluded by the closed generated-arrow grammar. -/
theorem not_closed :
    ¬ Nonempty (GeneratedArrow closedArrows assumptions .empty .empty arrow) := by
  rintro ⟨f⟩
  exact not_equal ⟨f.empty_unique⟩

def object : GeneratedCategory.Object (hypothesisArrows assumptions) assumptions :=
  GeneratedCategory.emptyObject _ _

def arrowClass : object ⟶ object := Quotient.mk _ ⟨arrow, generated⟩

theorem distinct_classes : arrowClass ≠ 𝟙 object := by
  intro h
  exact not_equal (Quotient.exact h)

theorem not_terminal : ¬ Subsingleton (object ⟶ object) := by
  intro h
  exact distinct_classes (@Subsingleton.elim _ h _ _)

end Hypothesis
end Examples.GeneratedEmptySubstitutions
