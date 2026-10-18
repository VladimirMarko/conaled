import SquareKit.Relations
import SquareKit.Internal.Associativity

/-! Existential composition of relations and explicit intermediate witnesses.
Ordinary callers supply relations, preserving maps, and pointwise agreement.
-/
namespace Relational
universe u
variable {A B C D A' B' C' D' : Type u}

/-- Compose predicates through an existential middle value. -/
def compRel (R : A → B → Prop) (S : B → C → Prop) : A → C → Prop :=
  fun a c => ∃ b, R a b ∧ S b c

abbrev existential (R : A → B → Prop) (S : B → C → Prop) : RelRep.{u} :=
  ⟨A, C, compRel R S⟩

/-- The ordinary associativity law is the interpreted internal proof. -/
theorem compRel_assoc (R : A → B → Prop) (S : B → C → Prop) (T : C → D → Prop)
    (a : A) (d : D) : compRel (compRel R S) T a d ↔ compRel R (compRel S T) a d :=
  SquareKit.Internal.Associativity.inSet R S T a d

/-- Map the middle witness; agreement need only be pointwise. -/
def existentialSquare {R : A → B → Prop} {S : B → C → Prop}
    {R' : A' → B' → Prop} {S' : B' → C' → Prop}
    (f : RelSquare ⟨A, B, R⟩ ⟨A', B', R'⟩)
    (g : RelSquare ⟨B, C, S⟩ ⟨B', C', S'⟩)
    (middle : ∀ b, f.spec b = g.impl b) :
    RelSquare (existential R S) (existential R' S') where
  impl := f.impl
  spec := g.spec
  preserves := by
    rintro a c ⟨b, hr, hs⟩
    refine ⟨f.spec b, f.preserves hr, ?_⟩
    rw [middle]
    exact g.preserves hs

/-- Change both predicates while retaining both horizontal maps. -/
def transportRelations {A B : RelRep.{u}} (f : RelSquare A B)
    (P : A.R → A.S → Prop) (Q : B.R → B.S → Prop)
    (hP : ∀ r s, A.Rel r s ↔ P r s) (hQ : ∀ r s, B.Rel r s ↔ Q r s) :
    RelSquare ⟨A.R, A.S, P⟩ ⟨B.R, B.S, Q⟩ where
  impl := f.impl
  spec := f.spec
  preserves h := (hQ _ _).mp (f.preserves ((hP _ _).mpr h))

/-- Transport both endpoint relations using the interpreted associativity
proof, then compare both maps through the public square extensionality law. -/
theorem existential_reassociate
    {R : A → B → Prop} {S : B → C → Prop} {T : C → D → Prop}
    {R' : A' → B' → Prop} {S' : B' → C' → Prop} {T' : C' → D' → Prop}
    (f : RelSquare ⟨A, B, R⟩ ⟨A', B', R'⟩)
    (g : RelSquare ⟨B, C, S⟩ ⟨B', C', S'⟩)
    (h : RelSquare ⟨C, D, T⟩ ⟨C', D', T'⟩)
    (fg : ∀ b, f.spec b = g.impl b) (gh : ∀ c, g.spec c = h.impl c) :
    transportRelations (existentialSquare (existentialSquare f g fg) h gh)
      (compRel R (compRel S T)) (compRel R' (compRel S' T'))
      (compRel_assoc R S T) (compRel_assoc R' S' T') =
      existentialSquare f (existentialSquare g h gh) fg :=
  RelSquare.ext (fun _ => rfl) (fun _ => rfl)

/-- All three values are data. The two relation certificates remain in Prop. -/
structure Intermediate (R : A → B → Prop) (S : B → C → Prop) where
  source : A
  middle : B
  target : C
  first : R source middle
  second : S middle target

def intermediateRep (R : A → B → Prop) (S : B → C → Prop) : Squares.Rep.{u} :=
  ⟨Intermediate R S, C, Intermediate.target⟩

def Intermediate.forget {R : A → B → Prop} {S : B → C → Prop}
    (w : Intermediate R S) : (witness (existential R S)).R :=
  ⟨(w.source, w.target), w.middle, w.first, w.second⟩

def forgetIntermediate (R : A → B → Prop) (S : B → C → Prop) :
    Squares.Square (intermediateRep R S) (witness (existential R S)) where
  impl := Intermediate.forget
  spec := id
  commutes _ := rfl

/-- A map of explicit witnesses uses the same middle map as existentialSquare. -/
def intermediateSquare {R : A → B → Prop} {S : B → C → Prop}
    {R' : A' → B' → Prop} {S' : B' → C' → Prop}
    (f : RelSquare ⟨A, B, R⟩ ⟨A', B', R'⟩)
    (g : RelSquare ⟨B, C, S⟩ ⟨B', C', S'⟩)
    (middle : ∀ b, f.spec b = g.impl b) :
    Squares.Square (intermediateRep R S) (intermediateRep R' S') where
  impl w := ⟨f.impl w.source, f.spec w.middle, g.spec w.target,
    f.preserves w.first, by rw [middle]; exact g.preserves w.second⟩
  spec := g.spec
  commutes _ := rfl

/-- Forgetting the intermediate data commutes with both induced maps. -/
theorem forgetIntermediate_natural {R : A → B → Prop} {S : B → C → Prop}
    {R' : A' → B' → Prop} {S' : B' → C' → Prop}
    (f : RelSquare ⟨A, B, R⟩ ⟨A', B', R'⟩)
    (g : RelSquare ⟨B, C, S⟩ ⟨B', C', S'⟩)
    (middle : ∀ b, f.spec b = g.impl b) :
    Squares.compose (forgetIntermediate R' S') (intermediateSquare f g middle) =
      Squares.compose (witnessSquare (existentialSquare f g middle))
        (forgetIntermediate R S) :=
  Squares.Square.ext (fun _ => rfl) (fun _ => rfl)
end Relational
