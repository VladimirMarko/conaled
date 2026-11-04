p='Examples/ConstructionObservationAuthorA.lean'
s=open(p).read().replace('end ConstructionObservationAuthorA','''theorem frame_shared {n} (a b : Nat) (v : Vec n) (k : Fin (n+2)) :
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

end ConstructionObservationAuthorA''')
open(p,'w').write(s)
