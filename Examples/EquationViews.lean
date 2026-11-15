import Examples.EquationTranspose

/-! Matched direct and view-based vector extensions. New rows are authored in
constructor order, new columns in observer order; old cells are retained. -/
namespace Examples.EquationViews
open SquareKit.EquationTranspose
open Examples.EquationTranspose.Vectors

/-- Start without repeat or size, rather than restricting after the addition. -/
inductive BaseConstructor : Nat → Type
  | nil : BaseConstructor 0
  | cons (n : Nat) : BaseConstructor (n+1)

def embed : BaseConstructor n → Constructor n
  | .nil => .nil
  | .cons n => .cons n

def base := restrictObservers
  (restrictConstructors equations BaseConstructor (fun _ => embed))
  (fun _ => Unit) (fun _ _ => .at)

/-- The new row returns its payload at every valid lookup index. -/
def repeatRow (n : Nat) (_ : Unit) (_ : Unit) :
    Expr Prim (Slot (Fin n) Nat) Nat := .var .second

def withRepeat := (transpose base).addConstructors (fun _ => Unit) (fun _ => Nat) repeatRow

theorem old_constructor_cells (n : Nat) (c : BaseConstructor n) :
    withRepeat.body n (.inl c) () = (transpose base).body n c () :=
  CodataProgram.addConstructors_old _ _ _ _ _ _ _

theorem repeat_data_roundtrip : transpose (untranspose withRepeat) = withRepeat :=
  transpose_untranspose _

theorem repeat_codata_roundtrip :
    untranspose (transpose (untranspose withRepeat)) = untranspose withRepeat :=
  untranspose_transpose _

/-- The ordinary direct implementation remains a function on finite indices. -/
def directRepeat (n x : Nat) : Fin n → Nat := fun _ => x

theorem repeat_matches_direct (n x : Nat) (i : Fin n) :
    (untranspose withRepeat).observe meaning () ⟨.inr (), x⟩ i = directRepeat n x i := by
  exact (untranspose_preserves withRepeat meaning (.inr ()) x () i).trans rfl

/-- Column authoring uses the actual extended constructor family. -/
def withSize := (untranspose withRepeat).addObservers (fun _ => Unit)
  (fun _ => Unit) (fun _ => Nat)
  (fun n _ _ => .prim (.size n) (.var .second))

theorem old_observer_cells (n : Nat) (c : BaseConstructor n ⊕ Unit) :
    withSize.body n (.inl ()) c = (untranspose withRepeat).body n () c :=
  DataProgram.addObservers_old _ _ _ _ _ _ _ _

/-- Retention composes through both view changes and both additions. -/
theorem old_lookup_after_views (n : Nat) (c : BaseConstructor n) :
    withSize.body n (.inl ()) (.inl c) = base.body n () c := by
  calc
    _ = (untranspose withRepeat).body n () (.inl c) := old_observer_cells n (.inl c)
    _ = (untranspose (transpose base)).body n () c :=
      congrArg Expr.swap (old_constructor_cells n c)
    _ = base.body n () c := congrArg (fun p => p.body n () c) (untranspose_transpose base)

theorem size_data_roundtrip : untranspose (transpose withSize) = withSize :=
  untranspose_transpose _

theorem size_codata_roundtrip :
    transpose (untranspose (transpose withSize)) = transpose withSize :=
  transpose_untranspose _

def directSize {n : Nat} (_ : Fin n → Nat) : Nat := n

theorem size_matches_direct (n x : Nat) :
    (transpose withSize).construct meaning (i := n) (.inr ()) x (.inr ()) () = directSize (directRepeat n x) := by
  exact (transpose_preserves withSize meaning (i := n) (.inr ()) x (.inr ()) ()).trans rfl

/-- A matched input distinguishes the new size equation from the lookup equation. -/
example : (transpose withSize).construct meaning (i := 2) (.inr ()) 7 (.inr ()) () = 2 :=
  size_matches_direct 2 7

example : (untranspose withRepeat).observe meaning (i := 2) () ⟨.inr (), 7⟩ ⟨1, by decide⟩ = 7 :=
  repeat_matches_direct 2 7 _

/-- The original head/tail case still uses the retained nil/cons lookup column. -/
example : (transpose withSize).construct meaning (.inl (.cons 1))
    (7, fun _ => 11) (.inl ()) ⟨1, by decide⟩ = 11 := by
  exact (transpose_preserves withSize meaning (.inl (.cons 1))
    (7, fun _ => 11) (.inl ()) ⟨1, by decide⟩).trans rfl

/-- Extension and transposition cannot supply a lookup argument at index zero. -/
theorem empty_lookup_impossible
    (i : ((signature.addObservers (fun _ => Unit) (fun _ => Unit) (fun _ => Nat)).arguments
      (Sum.inl (Observer.at (n := 0))))) : False := Fin.elim0 i

end Examples.EquationViews
