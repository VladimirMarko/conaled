import Applications.Optimization.Basic
import SquareKit.Relations

/-!
# Indexed relational realization contracts

The index `I` can be a problem/workload pair. Both sides retain it in the
output, so neither membership nor an approximation bound loses its problem.
A decoder may discard implementation details but does not choose a tie-breaker.
-/

namespace Optimization

universe u

/-- Equal problem/workload inputs. -/
def inputRep (I : Type u) : Relational.RelRep.{u} := ⟨I, I, Eq⟩

/-- Set-valued output specifications with index-preserving membership. -/
def membershipRep {I P R : Type u} (decode : R → P) : Relational.RelRep.{u} where
  R := I × R
  S := I × Set P
  Rel r s := r.1 = s.1 ∧ decode r.2 ∈ s.2

/-- Observe permitted outputs through any function, retaining the problem index.
No objective, injectivity or inverse is needed to forget witness detail. -/
def observationSquare {I P Q : Type u} (observe : P → Q) :
    Relational.RelSquare (membershipRep (I := I) (id : P → P))
      (membershipRep (I := I) (id : Q → Q)) where
  impl r := (r.1, observe r.2)
  spec s := (s.1, observe '' s.2)
  preserves h := ⟨h.1, ⟨_, h.2, rfl⟩⟩

/-- An ordinary optimality proof supplies a relational square without syntax
translation. Existence of `realize` with this proof already entails attainment. -/
def selectionSquare {I P R K : Type u} [Preorder K]
    (A : I → Set P) (J : I → P → K) (decode : R → P) (realize : I → R)
    (correct : ∀ i, decode (realize i) ∈ minimizers (A i) (J i)) :
    Relational.RelSquare (inputRep I) (membershipRep (I := I) decode) where
  impl i := (i, realize i)
  spec i := (i, minimizers (A i) (J i))
  preserves := by
    rintro i _ rfl
    exact ⟨rfl, correct i⟩

/-- Classical exact selection, restricted to inputs with attainment evidence. -/
noncomputable def attainedSelectionSquare {I P K : Type u} [Preorder K]
    (A : I → Set P) (J : I → P → K) :
    Relational.RelSquare (inputRep {i // Attained (A i) (J i)})
      (membershipRep (I := {i // Attained (A i) (J i)}) (id : P → P)) :=
  selectionSquare (fun i => A i.val) (fun i => J i.val) id
    (fun i => select i.property) (fun i => select_mem i.property)

/-- Approximate realizations are feasible and meet a stated bound. A client may
supply an additive or multiplicative bound on an infimum, without attainment. -/
def boundRep {I P R K : Type u} [Preorder K]
    (A : I → Set P) (J : I → P → K) (decode : R → P) : Relational.RelRep.{u} where
  R := I × R
  S := I × K
  Rel r s := r.1 = s.1 ∧ decode r.2 ∈ A s.1 ∧ J s.1 (decode r.2) ≤ s.2

def boundSquare {I P R K : Type u} [Preorder K]
    (A : I → Set P) (J : I → P → K) (decode : R → P)
    (realize : I → R) (bound : I → K)
    (feasible : ∀ i, decode (realize i) ∈ A i)
    (within : ∀ i, J i (decode (realize i)) ≤ bound i) :
    Relational.RelSquare (inputRep I) (boundRep A J decode) where
  impl i := (i, realize i)
  spec i := (i, bound i)
  preserves := by
    rintro i _ rfl
    exact ⟨rfl, feasible i, within i⟩

end Optimization
