import Applications.Convolution.Polynomial
import Applications.Languages.Machines

/-!
# One checked pipeline: weighted convolution → symbolic derivatives → tries

The first decoder forgets natural-number multiplicity. A finite polynomial is
compiled into a regular expression by dropping zero terms and taking the
union of the remaining words. The symbolic derivative recognizer, and then
its finite trie observations, reuse the same semantic interface. All stages
compose as actual `Squares.Square`s.
-/

namespace LanguageDerivatives

universe u
variable {α : Type u} [DecidableEq α]

def wordRegex : List α → Regex α
  | [] => .epsilon
  | a :: w => smartMul (.char a) (wordRegex w)

omit [DecidableEq α] in
theorem wordRegex_correct (u : List α) : (wordRegex u).matches' = {u} := by
  induction u with
  | nil => rfl
  | cons a u ih =>
    rw [wordRegex, smartMul_correct, ih]
    apply Language.ext
    intro w
    rw [Language.mem_mul]
    change (∃ x, x = [a] ∧ ∃ y, y = u ∧ x ++ y = w) ↔ w = a :: u
    simp [eq_comm]

def monomialRegex (u : List α) (r : ℕ) : Regex α :=
  if r = 0 then .zero else wordRegex u

theorem monomialRegex_correct (u : List α) (r : ℕ) :
    (monomialRegex u r).matches' = Convolution.support (Convolution.monomial u r) := by
  by_cases hr : r = 0
  · subst r
    simp only [monomialRegex, if_pos rfl, RegularExpression.matches'_zero,
      Convolution.monomial_zero]
    exact (Convolution.supportHom.map_zero).symm
  · rw [monomialRegex, if_neg hr, wordRegex_correct]
    apply Language.ext; intro w
    change w = u ↔ Convolution.monomial u r w ≠ 0
    rw [Convolution.monomial_apply]
    by_cases h : u = w
    · subst w; simp [hr]
    · simp [h, Ne.symm h]

def compilePolynomial : Convolution.Polynomial α ℕ → Regex α
  | [] => .zero
  | (u, r) :: p => smartPlus (monomialRegex u r) (compilePolynomial p)

theorem compilePolynomial_correct (p : Convolution.Polynomial α ℕ) :
    (compilePolynomial p).matches' = Convolution.support (Convolution.Polynomial.denote p) := by
  induction p with
  | nil => exact (Convolution.supportHom.map_zero).symm
  | cons ur p ih =>
    rcases ur with ⟨u, r⟩
    rw [compilePolynomial, smartPlus_correct, monomialRegex_correct, ih]
    exact (Convolution.supportHom.map_add (Convolution.monomial u r)
      (Convolution.Polynomial.denote p)).symm

def polynomialCompilationSquare :
    Squares.Square (Convolution.Polynomial.languageRep α) (rep α) where
  impl := compilePolynomial
  spec := id
  commutes := compilePolynomial_correct

def polynomialRecognitionSquare (w : List α) :
    Squares.Square (Convolution.Polynomial.languageRep α) truthRep.{u} :=
  Squares.compose (recognitionSquare w) polynomialCompilationSquare

def polynomialSnapshotSquare (n : ℕ) :
    Squares.Square (Convolution.Polynomial.languageRep α) (boundedRep α n) :=
  Squares.compose (snapshotSquare n) polynomialCompilationSquare

theorem compiled_product_recognizes (p q : Convolution.Polynomial α ℕ) (w : List α) :
    recognize (compilePolynomial (Convolution.Polynomial.mul p q)) w = true ↔
      ∃ u, Convolution.Polynomial.denote p u ≠ 0 ∧
        ∃ v, Convolution.Polynomial.denote q v ≠ 0 ∧ u ++ v = w := by
  rw [recognize_correct, compilePolynomial_correct, Convolution.Polynomial.denote_mul,
    Convolution.support_mul, Language.mem_mul]
  rfl

/-- Compiler optimization, convolution, and trie compilation share one invariant. -/
theorem normalized_product_snapshot (p q : Convolution.Polynomial α ℕ)
    (w : List α) (n : ℕ) (hw : w.length ≤ n) :
    ((polynomialSnapshotSquare n).impl
      (Convolution.Polynomial.normalize (Convolution.Polynomial.mul p q))).lookup w = some true ↔
      (Convolution.Polynomial.denote p * Convolution.Polynomial.denote q) w ≠ 0 := by
  change (regexMachine.unfold
      (compilePolynomial (Convolution.Polynomial.normalize (Convolution.Polynomial.mul p q))) n).lookup w = some true ↔ _
  rw [Machine.lookup_unfold _ _ _ _ hw, Option.some.injEq,
    Machine.run_correct regexMachine_correct, compilePolynomial_correct,
    Convolution.Polynomial.denote_normalize, Convolution.Polynomial.denote_mul]
  rfl

example : recognize (compilePolynomial
    (Convolution.Polynomial.mul Convolution.Polynomial.sampleP Convolution.Polynomial.sampleQ))
    "abc".toList = true := by decide

example : ((polynomialSnapshotSquare 3).impl
    (Convolution.Polynomial.mul Convolution.Polynomial.sampleP Convolution.Polynomial.sampleQ)).lookup "abc".toList = some true := by decide

end LanguageDerivatives
