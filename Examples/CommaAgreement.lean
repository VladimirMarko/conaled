import SquareKit.CommaVertical
import SquareKit.Combinators

/-! Independent exact representations: one retains a Boolean implementation
state, the other stores only the number. Agreement checks the number while
preserving the independent implementation state. -/
namespace Examples.CommaAgreement
open SquareKit SquareKit.Comma SquareKit.Comma.Exact

abbrev tagged : Squares.Rep := ⟨Nat × Bool, Nat, Prod.fst⟩
abbrev plain : Squares.Rep := ⟨Nat, Nat, id⟩
abbrev stepTagged : Squares.Square tagged tagged :=
  ⟨fun p => (p.1 + 1, !p.2), fun n => n + 1, fun _ => rfl⟩
abbrev stepPlain : Squares.Square plain plain :=
  ⟨fun n => n + 1, fun n => n + 1, fun _ => rfl⟩
abbrev doubleTagged : Squares.Square tagged tagged :=
  ⟨fun p => (p.1 * 2, p.2), fun n : Nat => n * 2, fun _ => rfl⟩
abbrev doublePlain : Squares.Square plain plain :=
  ⟨fun n : Nat => n * 2, fun n : Nat => n * 2, fun _ => rfl⟩

/-- Compose both independent implementations via the shared agreement theorem. -/
theorem independent_composition :
    agree (d₂ := (id : Nat → Nat)) (e₂ := (id : Nat → Nat))
      (categoryOps.comp (ofSquare doubleTagged) (ofSquare stepTagged))
      (categoryOps.comp (ofSquare doublePlain) (ofSquare stepPlain)) rfl =
    categoryOps.comp (agree (d₂ := (id : Nat → Nat)) (e₂ := (id : Nat → Nat))
      (ofSquare doubleTagged) (ofSquare doublePlain) rfl)
      (agree (d₂ := (id : Nat → Nat)) (e₂ := (id : Nat → Nat))
        (ofSquare stepTagged) (ofSquare stepPlain) rfl) :=
  agree_comp (d₂ := (id : Nat → Nat)) (e₂ := (id : Nat → Nat)) (h₂ := (id : Nat → Nat))
    (ofSquare stepTagged) (ofSquare stepPlain)
    (ofSquare doubleTagged) (ofSquare doublePlain) rfl rfl

/-- The public synchronization adapter computes both outputs, including state. -/
theorem synchronized_execution :
    ((Squares.synchronize (Squares.compose doubleTagged stepTagged)
      (Squares.compose doublePlain stepPlain) (fun _ => rfl)).impl
        ⟨((3, true), 3), rfl⟩).val = ((8, false), 8) := by
  change ((agree (d₂ := (id : Nat → Nat)) (e₂ := (id : Nat → Nat))
    (categoryOps.comp (ofSquare doubleTagged) (ofSquare stepTagged))
    (categoryOps.comp (ofSquare doublePlain) (ofSquare stepPlain)) rfl).left
      ⟨((3, true), 3), rfl⟩).val = ((8, false), 8)
  rw [independent_composition]
  rfl

/-- Reinterpret a number by doubling it; the computation increments by two. -/
abbrev doubledStep : Squares.Square (plain.after (fun n : Nat => n * 2))
    (plain.after (fun n : Nat => n * 2)) :=
  ⟨fun n : Nat => n + 1, fun n : Nat => n + (2 : Nat), fun n => Nat.add_mul n 1 2⟩

/-- Arbitrary tagged inputs retain their state through the general vertical operation. -/
theorem vertical_execution (n : Nat) (b : Bool) :
    let pasted := vertical (equalityCongr FunctionCategory.ops) FunctionCategory.laws
      (ofSquare stepTagged) (ofSquare doubledStep) rfl
    (pasted.left (n, b), (after (I := interpretation) (ofRep tagged) Nat
      (fun n : Nat => n * 2)).connector (n, b)) = ((n + 1, !b), n * 2) := rfl

/-- The pasted square's contract recovers the expected doubled output. -/
theorem vertical_output (n : Nat) (b : Bool) :
    let pasted := vertical (equalityCongr FunctionCategory.ops) FunctionCategory.laws
      (ofSquare stepTagged) (ofSquare doubledStep) rfl
    (after (I := interpretation) (ofRep tagged) Nat (fun n : Nat => n * 2)).connector
      (pasted.left (n, b)) = n * 2 + 2 :=
  congrFun (vertical (equalityCongr FunctionCategory.ops) FunctionCategory.laws
    (ofSquare stepTagged) (ofSquare doubledStep) rfl).commutes (n, b)

end Examples.CommaAgreement
