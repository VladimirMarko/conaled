import SquareKit.Internal.Cubical.Faces
import Mathlib.Data.Finset.Sort

/-! Every semantic face is represented by a finite endpoint formula. -/
namespace SquareKit.Cubical.Face

inductive Formula (n : ℕ) where
  | bot | top
  | atom (i : Fin n) (b : Bool)
  | meet (a b : Formula n)
  | join (a b : Formula n)

def Formula.eval : Formula n → Carrier n
  | .bot => Face.bot n
  | .top => Face.top n
  | .atom i b => Face.atom i b
  | .meet a b => Face.meet a.eval b.eval
  | .join a b => Face.join a.eval b.eval

def Formula.conjunction (l : List (Formula n)) : Formula n := l.foldr .meet .top
def Formula.disjunction (l : List (Formula n)) : Formula n := l.foldr .join .bot

theorem Formula.conjunction_holds (l : List (Formula n)) (ρ : Assignment n) :
    (conjunction l).eval.holds ρ = true ↔ ∀ p ∈ l, p.eval.holds ρ = true := by
  induction l with
  | nil => simp [conjunction,eval,Face.top]
  | cons a l ih =>
    simp only [conjunction,List.foldr_cons,eval,Face.meet,Bool.and_eq_true]
    rw [show (List.foldr Formula.meet Formula.top l).eval.holds ρ = true ↔ _ from ih]
    simp

theorem Formula.disjunction_holds (l : List (Formula n)) (ρ : Assignment n) :
    (disjunction l).eval.holds ρ = true ↔ ∃ p ∈ l, p.eval.holds ρ = true := by
  induction l with
  | nil => simp [disjunction,eval,Face.bot]
  | cons a l ih =>
    simp only [disjunction,List.foldr_cons,eval,Face.join,Bool.or_eq_true]
    rw [show (List.foldr Formula.join Formula.bot l).eval.holds ρ = true ↔ _ from ih]
    simp

noncomputable def principal (τ : Assignment n) : Formula n :=
  .conjunction ((Finset.univ : Finset (Fin n)).toList.map (fun i =>
    match τ i with | none => .top | some b => .atom i b))

theorem principal_holds (τ ρ : Assignment n) : (principal τ).eval.holds ρ = true ↔ Refines τ ρ := by
  unfold principal
  rw [Formula.conjunction_holds]
  simp only [List.forall_mem_map,Finset.mem_toList,Finset.mem_univ,true_implies]
  apply forall_congr'
  intro i
  cases h : τ i with
  | none => simp [Formula.eval,top,PartialDimension.Refines]
  | some b => simp [Formula.eval,atom,PartialDimension.Refines,eq_comm]

noncomputable def normalForm (φ : Carrier n) : Formula n :=
  .disjunction (((Finset.univ : Finset (Assignment n)).toList.filter (fun τ => φ.holds τ)).map principal)

theorem normalForm_holds (φ : Carrier n) (ρ : Assignment n) :
    (normalForm φ).eval.holds ρ = true ↔ φ.holds ρ = true := by
  unfold normalForm
  rw [Formula.disjunction_holds]
  simp only [List.mem_map,exists_exists_and_eq_and,List.mem_filter,Finset.mem_toList,Finset.mem_univ,
    true_and,principal_holds]
  exact (disjunctive_normal_form φ ρ).symm

/-- No arbitrary upward-closed predicate adds faces beyond finite formulas. -/
theorem normalForm_eval (φ : Carrier n) : (normalForm φ).eval = φ := by
  ext ρ
  have h := normalForm_holds φ ρ
  exact Bool.eq_iff_iff.mpr h

end SquareKit.Cubical.Face
