import Examples.IndexedCompositional
import Examples.ObservationExtension

namespace ConstructionObservationAuthorA
open SquareKit.IndexedCompositional
open IndexedCompositionalExamples.Vectors

-- This composes existing constructors; it adds no primitive signature operation.
def frame {X : Nat → Type} {n} (a b : Nat) (t : Term signature X n) :
    Term signature X (n+2) := cons a (double (cons b t))

theorem leaf_direct {n} (v : Vec n) (k : Fin n) :
    read (rule.lift native) (.leaf v) k = v k := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    refine Fin.cases rfl (fun j => ?_) k
    exact ih (fun l => v l.succ) j

theorem double_direct {n} (t : Term signature Vec n) (k : Fin n) :
    read (rule.lift native) (double t) k = 2 * read (rule.lift native) t k := by
  induction n with
  | zero => exact Fin.elim0 k
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) k
    · rfl
    · change read (rule.lift native) (double ((rule.lift native (n+1) t).2 ())) j =
        2 * read (rule.lift native) ((rule.lift native (n+1) t).2 ()) j
      exact ih _ j

theorem frame_direct {n} (a b : Nat) (v : Vec n) (k : Fin (n+2)) :
    read (rule.lift native) (frame a b (.leaf v)) k =
      Fin.cases a (Fin.cases (2*b) (fun j => 2*v j)) k := by
  refine Fin.cases rfl (fun j => ?_) k
  change read (rule.lift native) (double (cons b (.leaf v))) j = _
  rw [double_direct]
  refine Fin.cases rfl (fun l => ?_) j
  change 2 * read (rule.lift native) (.leaf v) l = 2 * v l
  rw [leaf_direct]

theorem frame_direct_expanded {n} (a b : Nat) (v : Vec n) (k : Fin (n+2)) :
    read (rule.lift emptyCoalgebra) (Term.bind expand (frame a b (.leaf v))) k =
      Fin.cases a (Fin.cases (2*b) (fun j => 2*v j)) k := by
  rw [substituted]
  exact frame_direct a b v k

end ConstructionObservationAuthorA
