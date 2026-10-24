import SquareKit.Internal.GraphTarget

/-! Source translation for the fixed equality-only graph signature.
Terms and formulas translate computationally. Source derivations inhabit Prop;
`translate_derivation` therefore supplies target code existentially in Prop.
The concrete graph codes below are explicit data for an emitter to consume.
-/
namespace SquareKit.Internal.GraphTarget

abbrev SourceTerm := Internal.Term Graph.Arrow
abbrev SourceFormula := Internal.Formula Graph.Arrow

def translateTerm : SourceTerm Γ s → Term Γ s
  | .var i => .var i
  | .app f t => .app f (translateTerm t)

def translateSub (σ : Internal.Sub Graph.Arrow Γ Δ) : Sub Γ Δ :=
  fun i => translateTerm (σ i)

def translateFormula : SourceFormula Γ → Formula Γ
  | .atom r _ _ => nomatch r
  | .eq a b => .eq (translateTerm a) (translateTerm b)
  | .conj p q => .conj (translateFormula p) (translateFormula q)
  | .ex p => .ex (translateFormula p)

theorem translate_term_subst (t : SourceTerm Γ s) (σ : Internal.Sub Graph.Arrow Γ Δ) :
    translateTerm (t.subst σ) = (translateTerm t).subst (translateSub σ) := by
  induction t with
  | var => rfl
  | app f t ih => simp only [Internal.Term.subst, translateTerm, Term.subst, ih]

theorem translate_lift (σ : Internal.Sub Graph.Arrow Γ Δ) :
    @translateSub _ _ (Internal.Sub.lift (b := b) σ) = @Sub.lift _ _ b (translateSub σ) := by
  funext s i
  cases i with
  | zero => rfl
  | succ i => exact translate_term_subst (σ i) _

theorem translate_formula_subst (p : SourceFormula Γ) (σ : Internal.Sub Graph.Arrow Γ Δ) :
    translateFormula (p.subst σ) = (translateFormula p).subst (translateSub σ) := by
  induction p generalizing Δ with
  | atom r => exact nomatch r
  | eq a b => simp only [Internal.FormulaCore.subst, translateFormula, Formula.subst,
      translate_term_subst]
  | conj p q hp hq => simp only [Internal.FormulaCore.subst, translateFormula,
      Formula.subst, hp, hq]
  | ex p ih => simp only [Internal.FormulaCore.subst, translateFormula,
      Formula.subst, ih, translate_lift]

theorem translate_shift (p : SourceFormula Γ) :
    translateFormula (p.shift (s := s)) = (translateFormula p).shift :=
  translate_formula_subst p _

theorem translate_single (t : SourceTerm Γ s) :
    @translateSub _ _ (Internal.single t) = @single _ _ (translateTerm t) := by
  funext s i
  cases i <;> rfl

theorem translate_instantiate (p : SourceFormula (s :: Γ)) (t : SourceTerm Γ s) :
    translateFormula (p.instantiate t) = (translateFormula p).instantiate (translateTerm t) := by
  simp only [Internal.FormulaCore.instantiate, Formula.instantiate,
    translate_formula_subst, translate_single]

/-- The same typed variable assignment interprets both ordered contexts. -/
theorem term_comparison (M : Interpretation Graph.Arrow) (ρ : Internal.Env M Γ)
    (t : SourceTerm Γ s) : (translateTerm t).eval M ρ = t.eval M ρ := by
  induction t with
  | var => rfl
  | app f t ih => simp only [translateTerm, Term.eval, Internal.Term.eval, ih]

theorem formula_comparison (M : Interpretation Graph.Arrow) (ρ : Internal.Env M Γ)
    (p : SourceFormula Γ) : (translateFormula p).eval M ρ ↔ p.eval M ρ := by
  induction p with
  | atom r => exact nomatch r
  | eq a b => simp only [translateFormula, Formula.eval, Internal.FormulaCore.eval,
      term_comparison]
  | conj p q hp hq => exact and_congr (hp ρ) (hq ρ)
  | ex p ih => exact exists_congr (fun x => ih (ρ.extend x))

/-- Substitution commutes with the context assignment, including under binders. -/
theorem substitution_comparison (M : Interpretation Graph.Arrow)
    (σ : Internal.Sub Graph.Arrow Γ Δ) (ρ : Internal.Env M Δ) :
    (fun {s} (i : Var Γ s) => (translateSub σ i).eval M ρ) =
      (fun {s} (i : Var Γ s) => (σ i).eval M ρ) := by
  funext s i
  exact term_comparison M ρ (σ i)

/-- No choice or elimination from source Prop into Type is used. -/
theorem translate_derivation (d : Internal.Derives p q) :
    Nonempty (Code (translateFormula p) (translateFormula q)) := by
  induction d with
  | ident => exact ⟨.ident⟩
  | cut _ _ hp hq => rcases hp with ⟨hp⟩; rcases hq with ⟨hq⟩; exact ⟨.cut hp hq⟩
  | left => exact ⟨.left⟩
  | right => exact ⟨.right⟩
  | pair _ _ hp hq => rcases hp with ⟨hp⟩; rcases hq with ⟨hq⟩; exact ⟨.pair hp hq⟩
  | refl => exact ⟨.refl⟩
  | symm _ ih => rcases ih with ⟨ih⟩; exact ⟨.symm ih⟩
  | trans _ _ hp hq => rcases hp with ⟨hp⟩; rcases hq with ⟨hq⟩; exact ⟨.trans hp hq⟩
  | congr _ ih => rcases ih with ⟨ih⟩; exact ⟨.congr ih⟩
  | intro p t => rw [translate_instantiate]; exact ⟨.intro _ _⟩
  | subst σ _ ih =>
    rw [translate_formula_subst, translate_formula_subst]
    rcases ih with ⟨ih⟩; exact ⟨.subst (translateSub σ) ih⟩
  | elimWith _ ih =>
    simp only [translateFormula, translate_shift] at ih ⊢
    rcases ih with ⟨ih⟩; exact ⟨.elimWith ih⟩
  | elim _ ih =>
    rw [translate_shift] at ih
    rcases ih with ⟨ih⟩; exact ⟨.elim ih⟩

/-- Equality is of proofs of the same native proposition, not witness data. -/
theorem proof_comparison (M : Interpretation Graph.Arrow) (ρ : Internal.Env M Γ)
    {p q : SourceFormula Γ} (d : Internal.Derives p q)
    (k : Code (translateFormula p) (translateFormula q)) (h : p.eval M ρ) :
    (formula_comparison M ρ q).mp
      (sound M k ρ ((formula_comparison M ρ p).mpr h)) = Internal.sound M d ρ h :=
  Subsingleton.elim _ _

/-- Explicit target code with witness binder before the two endpoint binders. -/
def forward : Code (translateFormula (Graph.composite Graph.Arrow.first Graph.Arrow.second))
    (translateFormula (Graph.result Graph.Arrow.first Graph.Arrow.second)) :=
  .elim (.trans .right (.congr .left))

def backward : Code (translateFormula (Graph.result Graph.Arrow.first Graph.Arrow.second))
    (translateFormula (Graph.composite Graph.Arrow.first Graph.Arrow.second)) :=
  .cut (.pair .refl .ident)
    (.intro (translateFormula (Graph.body Graph.Arrow.first Graph.Arrow.second))
      (.app .first (.var .zero)))

/-- The declaration codes are available without extracting a source proof. -/
def forwardDeclaration : Declaration :=
  ⟨[.input, .output], translateFormula (Graph.composite .first .second),
    translateFormula (Graph.result .first .second), forward⟩

def backwardDeclaration : Declaration :=
  ⟨[.input, .output], translateFormula (Graph.result .first .second),
    translateFormula (Graph.composite .first .second), backward⟩

/-- Native observation with independently stated endpoints and witness order. -/
theorem graph_equivalence {A B C : Type v} (f : A → B) (g : B → C) (x : A) (z : C) :
    (∃ y, y = f x ∧ z = g y) ↔ z = g (f x) :=
  ⟨sound (Graph.model f g) forward (Graph.environment f g x z),
   sound (Graph.model f g) backward (Graph.environment f g x z)⟩

theorem forward_comparison {A B C : Type v} (f : A → B) (g : B → C)
    (x : A) (z : C) (h : ∃ y, y = f x ∧ z = g y) :
    (graph_equivalence f g x z).mp h = (Graph.inSet f g x z).mp h :=
  proof_comparison (Graph.model f g) (Graph.environment f g x z)
    (Graph.forward Graph.Arrow.first Graph.Arrow.second) forward h

theorem backward_comparison {A B C : Type v} (f : A → B) (g : B → C)
    (x : A) (z : C) (h : z = g (f x)) :
    (graph_equivalence f g x z).mpr h = (Graph.inSet f g x z).mpr h :=
  proof_comparison (Graph.model f g) (Graph.environment f g x z)
    (Graph.backward Graph.Arrow.first Graph.Arrow.second) backward h

end SquareKit.Internal.GraphTarget
