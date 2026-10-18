import SquareKit.Internal.SheafFormula
import Examples.SheafContexts

/-! Experimental finite evidence for closed sheaf formulas and substitution. -/
namespace Examples.SheafFormula
open CategoryTheory Opposite SquareKit.Internal SquareKit.SheafImage
open Examples.SheafImage Examples.SheafImage.Diamond
open Examples.SheafContexts Examples.SheafContexts.Kind

inductive Relation : Kind → Kind → Type where | selectedEq : Relation b b

/-- Argument equality together with the previously specified W/U support. -/
def selectedEq : Subfunctor (Presheaf.product (model.carrier b) (model.carrier b)) where
  obj j p := p.1 = p.2 ∧ selective.obj j ()
  map := by
    intro j k f p hp
    exact ⟨hp.1, selective.map f (a := ()) hp.2⟩

theorem selectedEq_isSheaf : Presieve.IsSheaf topology selectedEq.toFunctor := by
  apply (Subfunctor.isSheaf_iff _
    (SquareKit.Internal.SheafContexts.product_isSheaf model carriers_areSheaves b b)).mpr
  intro a p hp
  rcases a with ⟨a⟩
  have hw := hp W (Examples.SheafBaseChange.fromW a) (by decide)
  refine ⟨hw.1, ?_⟩
  apply (Subfunctor.isSheaf_iff selective terminal_isSheaf).mp selective_isSheaf (op a) ()
  exact topology.superset_covering (by intro j f hf; exact hf.2) hp

def relModel : Presheaf.Model (J := Diamond) Op Relation where
  carrier := model.carrier
  arrow := model.arrow
  relation
    | .selectedEq => selectedEq

theorem sort_sheaves (s : Kind) : Presieve.IsSheaf topology (relModel.carrier s) :=
  carriers_areSheaves s

theorem relation_sheaves {s t} (r : Relation s t) :
    Presieve.IsSheaf topology (relModel.relation r).toFunctor := by
  cases r
  exact selectedEq_isSheaf

abbrev interp {Γ : List Kind} (p : Formula Op Γ Relation) :=
  SquareKit.Internal.SheafContexts.formula relModel sort_sheaves p

theorem interp_isSheaf (p : Formula Op Γ Relation) : Presieve.IsSheaf topology (interp p).toFunctor :=
  SquareKit.Internal.SheafContexts.formula_isSheaf relModel sort_sheaves relation_sheaves p

def existsE : Formula Op [] Relation := .ex (.eq (.var (Var.zero (s := e))) (.var .zero))

/-- The formula interpreter uses the same context projection/local image as #54. -/
theorem existsE_image : interp existsE = localImage ⊤ (proj (s := e) (Γ := [])) := by
  change localImage (relModel.equality _ _)
    (SquareKit.Internal.SheafContexts.projection relModel sort_sheaves (s := e) (Γ := [])) = _
  have he : relModel.equality (.var (Var.zero (s := e) (Γ := []))) (.var .zero) = ⊤ := by
    ext j ρ; exact iff_true_intro rfl
  rw [he]
  rfl

theorem existsE_at_X : (interp existsE).obj (op X) (empty (op X)) := by
  rw [existsE_image, context_top]
  trivial

theorem presheaf_existsE_false : ¬ (relModel.formula existsE).obj (op X) (empty (op X)) := by
  rintro ⟨ρ, _, _⟩
  exact no_pointwise_witness ⟨ρ .zero, trivial, rfl⟩

theorem evaluated_existsE_false : ¬ existsE.eval (relModel.fiber (op X)) (empty (op X)) := by
  intro h
  exact presheaf_existsE_false ((relModel.evaluation _ _ _).mpr h)

def equalAtom : Formula Op [b] Relation := .atom .selectedEq (.var .zero) (.var .zero)
def unequalAtom : Formula Op [b] Relation := .atom .selectedEq (.var .zero) neg

def combined : Formula Op [b] Relation :=
  .ex (.conj (.eq (.var (Var.zero (s := e))) (.var .zero)) equalAtom.shift)

/-- The atom is exactly the previously selected predicate on Bool environments. -/
theorem equalAtom_predicate : interp equalAtom = selected.preimage (sub forget).hom := by
  ext j ρ
  change (ρ .zero = ρ .zero ∧ selective.obj j ()) ↔ selective.obj j ()
  exact and_iff_right rfl

/-- Conjunction under existence is computed using the general Frobenius law. -/
theorem combined_predicate : interp combined = selected.preimage (sub forget).hom := by
  have he : relModel.equality (.var (Var.zero (s := e) (Γ := [b]))) (.var .zero) = ⊤ := by
    ext j ρ; exact iff_true_intro rfl
  have hs : interp equalAtom.shift = (interp equalAtom).preimage
      (SquareKit.Internal.SheafContexts.projection relModel sort_sheaves (s := e)).hom := by
    ext j ρ
    rfl
  change localImage (relModel.equality _ _ ⊓ interp (equalAtom.shift (s := e)))
    (SquareKit.Internal.SheafContexts.projection relModel sort_sheaves (s := e)) = _
  rw [he, hs]
  have hf := frobenius (⊤ : Subfunctor (relModel.context [e,b]))
    (SquareKit.Internal.SheafContexts.projection relModel sort_sheaves (s := e))
    (interp equalAtom) (interp_isSheaf equalAtom)
  have ht : localImage ⊤ (SquareKit.Internal.SheafContexts.projection relModel sort_sheaves
      (s := e) (Γ := [b])) = ⊤ := by
    exact extended_top
  rw [hf, ht, top_inf_eq, equalAtom_predicate]

theorem combined_at_U (x : Bool) : (interp combined).obj (op U) (boolEnv (op U) x) := by
  rw [combined_predicate]
  exact Or.inr rfl

theorem combined_not_V (x : Bool) : ¬ (interp combined).obj (op V) (boolEnv (op V) x) := by
  rw [combined_predicate]
  change ¬ (V = W ∨ V = U)
  decide

theorem combined_not_X (x : Bool) : ¬ (interp combined).obj (op X) (boolEnv (op X) x) := by
  rw [combined_predicate]
  change ¬ (X = W ∨ X = U)
  decide

theorem unequalAtom_false (j : Diamondᵒᵖ) (x : Bool) :
    ¬ (interp unequalAtom).obj j (boolEnv j x) := by
  intro h
  have he : x = !x := h.1
  cases x <;> cases he

/-- Nonidentity substitution exercises the uniform theorem under the binder. -/
theorem combined_negation : interp (combined.subst negate) =
    (interp combined).preimage (sub negate).hom := by
  have h := SquareKit.Internal.SheafContexts.formula_substitution relModel sort_sheaves combined negate
  have hs : (SquareKit.Internal.SheafContexts.substitution relModel sort_sheaves negate).hom =
      (sub negate).hom := by
    ext j ρ s i
    cases i with
    | zero => rfl
    | succ i => nomatch i
  rw [hs] at h
  exact h

theorem negate_environment (j : Diamondᵒᵖ) (x : Bool) :
    @Eq ((ctx [b]).obj.obj j) ((sub negate).hom.app j (boolEnv j x)) (@boolEnv j (!x)) := by
  funext s i
  cases i with
  | zero => rfl
  | succ i => nomatch i

theorem combined_negation_at_U (x : Bool) :
    (interp (combined.subst negate)).obj (op U) (boolEnv (op U) x) := by
  rw [combined_negation]
  change (interp combined).obj _ ((sub negate).hom.app _ _)
  rw [negate_environment]
  exact combined_at_U (!x)

theorem combined_negation_not_X (x : Bool) :
    ¬ (interp (combined.subst negate)).obj (op X) (boolEnv (op X) x) := by
  rw [combined_negation]
  change ¬ (interp combined).obj _ ((sub negate).hom.app _ _)
  rw [negate_environment]
  exact combined_not_X (!x)

example (j k : Diamondᵒᵖ) (f : j ⟶ k) (ρ : Env (relModel.fiber j) [b])
    (h : (interp combined).obj j ρ) : (interp combined).obj k (relModel.restrict f ρ) :=
  SquareKit.Internal.SheafContexts.formula_restrict relModel sort_sheaves combined f ρ h

-- Formula semantics remains opt-in beside the ordinary graph interface.
example (n : Nat) : ∃ m, m = n + 1 ∧ 2 * (n + 1) = 2 * m :=
  (Graph.inSet (fun x => x + 1) (fun x => 2 * x) n _).mpr rfl

end Examples.SheafFormula
