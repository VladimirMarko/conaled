import Applications.Languages.Parser
import Applications.Languages.Regex

/-!
# Forgetting witnesses commutes with recognition

The proof-relevant parser is built independently of Mathlib's regular-expression
matcher. This module connects it to the optimized Boolean implementation for
every ordinary regular expression and every input word, including nullable
stars. The common semantic target is membership after existentially forgetting
parse witnesses.
-/

namespace LanguageDerivatives

universe u
variable {α : Type u}

def witnessLanguage : Regex α → LanguageWitnesses.Language α
  | .zero => fun _ => PEmpty
  | .epsilon => LanguageWitnesses.epsilon
  | .char a => LanguageWitnesses.atom a
  | .plus p q => fun w => witnessLanguage p w ⊕ witnessLanguage q w
  | .comp p q => LanguageWitnesses.Concat (witnessLanguage p) (witnessLanguage q)
  | .star p => LanguageWitnesses.Star (witnessLanguage p)

def compileProofParser (p : Regex α) : LanguageWitnesses.Parser (witnessLanguage p) :=
  match p with
  | .zero => .zero
  | .epsilon => .epsilon
  | .char a => .atom a
  | .plus p q => .union (compileProofParser p) (compileProofParser q)
  | .comp p q => .concat (compileProofParser p) (compileProofParser q)
  | .star p => .star (compileProofParser p)

private theorem witnessesForWords (P : LanguageWitnesses.Language α)
    (ws : List (List α)) (h : ∀ w ∈ ws, Nonempty (P w)) :
    ∃ ps : List (LanguageWitnesses.ParsedWord P), ps.map Sigma.fst = ws := by
  induction ws with
  | nil => exact ⟨[], rfl⟩
  | cons w ws ih =>
    obtain ⟨p⟩ := h w (by simp)
    obtain ⟨ps, hps⟩ := ih (fun v hv => h v (by simp [hv]))
    exact ⟨⟨w, p⟩ :: ps, by simp [hps]⟩

private theorem flattenWitnessWords {P : LanguageWitnesses.Language α}
    (ps : List (LanguageWitnesses.ParsedWord P)) :
    (ps.map Sigma.fst).flatten = LanguageWitnesses.flattenParses ps := by
  induction ps <;> simp [LanguageWitnesses.flattenParses, *]

theorem witnessLanguage_correct (p : Regex α) (w : List α) :
    Nonempty (witnessLanguage p w) ↔ w ∈ p.matches' := by
  induction p generalizing w with
  | zero =>
    constructor
    · rintro ⟨p⟩; exact p.elim
    · intro h; exact h.elim
  | epsilon =>
    change Nonempty (LanguageWitnesses.Evidence (w = [])) ↔ w = []
    exact ⟨fun ⟨h⟩ => h.proof, fun h => ⟨⟨h⟩⟩⟩
  | char a =>
    change Nonempty (LanguageWitnesses.Evidence (w = [a])) ↔ w = [a]
    exact ⟨fun ⟨h⟩ => h.proof, fun h => ⟨⟨h⟩⟩⟩
  | plus p q hp hq =>
    rw [RegularExpression.plus_def, RegularExpression.matches'_add, Language.mem_add]
    change Nonempty (witnessLanguage p w ⊕ witnessLanguage q w) ↔ _
    constructor
    · rintro ⟨h | h⟩
      · exact Or.inl ((hp w).mp ⟨h⟩)
      · exact Or.inr ((hq w).mp ⟨h⟩)
    · rintro (h | h)
      · obtain ⟨x⟩ := (hp w).mpr h; exact ⟨.inl x⟩
      · obtain ⟨x⟩ := (hq w).mpr h; exact ⟨.inr x⟩
  | comp p q hp hq =>
    rw [RegularExpression.comp_def, RegularExpression.matches'_mul, Language.mem_mul]
    constructor
    · rintro ⟨⟨u, v, huv, x, y⟩⟩
      exact ⟨u, (hp u).mp ⟨x⟩, v, (hq v).mp ⟨y⟩, huv⟩
    · rintro ⟨u, hu, v, hv, huv⟩
      obtain ⟨x⟩ := (hp u).mpr hu
      obtain ⟨y⟩ := (hq v).mpr hv
      exact ⟨⟨u, v, huv, x, y⟩⟩
  | star p hp =>
    rw [RegularExpression.matches'_star, Language.mem_kstar]
    constructor
    · rintro ⟨⟨ps, hps⟩⟩
      refine ⟨ps.map Sigma.fst, ?_, ?_⟩
      · rw [flattenWitnessWords]; exact hps.symm
      · intro v hv
        obtain ⟨⟨u, x⟩, _, rfl⟩ := List.mem_map.mp hv
        exact (hp u).mp ⟨x⟩
    · rintro ⟨ws, hw, hws⟩
      obtain ⟨ps, hps⟩ := witnessesForWords (witnessLanguage p) ws
        (fun v hv => (hp v).mpr (hws v hv))
      refine ⟨⟨ps, ?_⟩⟩
      rw [← flattenWitnessWords, hps, ← hw]

/-- No finite test set: the two independently constructed recognizers agree universally. -/
theorem recognizers_agree [DecidableEq α] (p : Regex α) (w : List α) :
    ((compileProofParser p).parse w).test = recognize p w := by
  have h : ((compileProofParser p).parse w).test = true ↔ recognize p w = true :=
    (LanguageWitnesses.Parser.parse_correct _ _).trans
      ((witnessLanguage_correct p w).trans (recognize_correct p w).symm)
  cases hl : ((compileProofParser p).parse w).test <;>
    cases hr : recognize p w <;> simp_all

def eraseWitnesses (P : LanguageWitnesses.Language α) : Language α := {w | Nonempty (P w)}

theorem erase_derivative (P : LanguageWitnesses.Language α) (a : α) :
    eraseWitnesses (LanguageWitnesses.derivative P a) = residual a (eraseWitnesses P) := rfl

theorem erase_witnessLanguage (p : Regex α) : eraseWitnesses (witnessLanguage p) = p.matches' := by
  apply Language.ext; exact witnessLanguage_correct p

example : ((compileProofParser (.star (.plus .epsilon (.char 'a')))).parse
    "aaa".toList).test = recognize (.star (.plus .epsilon (.char 'a'))) "aaa".toList :=
  recognizers_agree _ _

end LanguageDerivatives
