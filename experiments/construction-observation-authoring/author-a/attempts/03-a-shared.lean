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

theorem frame_shared {n} (a b : Nat) (v : Vec n) (k : Fin (n+2)) :
    read (rule.lift native) (frame a b (.leaf v)) k =
      Fin.cases a (Fin.cases (2*b) (fun j => 2*v j)) k := by
  rw [correct]
  refine Fin.cases rfl (fun j => ?_) k
  refine Fin.cases rfl (fun l => ?_) j
  rfl

theorem frame_shared_expanded {n} (a b : Nat) (v : Vec n) (k : Fin (n+2)) :
    read (rule.lift emptyCoalgebra) (Term.bind expand (frame a b (.leaf v))) k =
      Fin.cases a (Fin.cases (2*b) (fun j => 2*v j)) k := by
  rw [substituted]
  exact frame_shared a b v k

def emptyVector : Vec 0 := Fin.elim0
def singletonVector : Vec 1 := fun _ => 13

theorem empty_direct (k : Fin 2) :
    read (rule.lift native) (frame 7 11 (.leaf emptyVector)) k =
      Fin.cases 7 (fun _ => 22) k := by
  rw [frame_direct]
  refine Fin.cases rfl (fun j => ?_) k
  refine Fin.cases rfl (fun l => Fin.elim0 l) j

theorem empty_shared (k : Fin 2) :
    read (rule.lift native) (frame 7 11 (.leaf emptyVector)) k =
      Fin.cases 7 (fun _ => 22) k := by
  rw [frame_shared]
  refine Fin.cases rfl (fun j => ?_) k
  refine Fin.cases rfl (fun l => Fin.elim0 l) j

theorem nonempty_direct :
    List.ofFn (read (rule.lift native) (frame 7 11 (.leaf singletonVector))) =
      [7,22,26] := by
  have h := funext (frame_direct 7 11 singletonVector)
  rw [h]
  rfl

theorem nonempty_shared :
    List.ofFn (read (rule.lift native) (frame 7 11 (.leaf singletonVector))) =
      [7,22,26] := by
  have h := funext (frame_shared 7 11 singletonVector)
  rw [h]
  rfl

theorem established_client :
    read (rule.lift native) (double (cons 7 (cons 11 nil))) 1 = 22 := by
  rw [correct]
  rfl

end ConstructionObservationAuthorA
