import Applications.Parallel.Scan

/-!
# Algorithm recipes preserve functor composition

Two isomorphic product shapes can carry different algorithms.  A `ScanPlan`
therefore remembers product versus functor-composition nodes, independently
of the resulting `Shape`.  Every local constructor builds an actual scanner
and its commuting-square proof.  Right powers, left powers, and bushes are
different recipes even when their flattened types have the same size.
-/

namespace Applications.Parallel

universe u

variable {M : Type u} [Monoid M]

structure Scanner (s : Shape) (M : Type u) [Monoid M] where
  run : s.Data M → s.Data M × M
  correct : ∀ x, (s.flatten (run x).1, (run x).2) = sequential 1 (s.flatten x)

namespace Scanner

def square {s : Shape} (p : Scanner s M) :
    Squares.Square (s.rep M) (Squares.product (s.rep M) ⟨M, M, id⟩) where
  impl := p.run
  spec := sequential 1
  commutes := p.correct

def product {s t : Shape} (p : Scanner s M) (q : Scanner t M) :
    Scanner (.prod s t) M where
  run := fun x =>
    let l := p.run x.1
    let r := q.run x.2
    ((l.1, t.map (l.2 * ·) r.1), l.2 * r.2)
  correct := fun x => by
    have hl₁ := congrArg Prod.fst (p.correct x.1)
    have hl₂ := congrArg Prod.snd (p.correct x.1)
    have hr₁ := congrArg Prod.fst (q.correct x.2)
    have hr₂ := congrArg Prod.snd (q.correct x.2)
    simp only at hl₁ hl₂ hr₁ hr₂
    simp only [Shape.flatten, Shape.flatten_map, hl₁, hl₂, hr₁, hr₂]
    exact (sequential_product _ _).symm

/-- Compose *algorithms*, not merely their flattened shape descriptions. -/
def compose {s t : Shape} (outer : Scanner s M) (inner : Scanner t M) :
    Scanner (s.subst t) M where
  run := fun x =>
    let scanned := s.scanNestedWith t outer.run inner.run (s.split t x)
    (s.join t scanned.1, scanned.2)
  correct := fun x => by
    rw [Shape.flatten_join]
    rw [s.scanNestedWith_correct t outer.run inner.run outer.correct inner.correct]
    rw [Shape.flatten_split]

def unit : Scanner .empty M where
  run := fun _ => (PUnit.unit, 1)
  correct := fun _ => rfl

def singleton : Scanner .leaf M where
  run := fun x => (1, x)
  correct := fun x => by simp [Shape.flatten, sequential]

/-- Dynamic choice retains its tag; decoding forgets the chosen grouping. -/
def choiceRep (s t : Shape) (M : Type u) : Squares.Rep where
  R := Sum (s.Data M) (t.Data M)
  S := List M
  decode := Sum.elim s.flatten t.flatten

def choice {s t : Shape} (p : Scanner s M) (q : Scanner t M) :
    Squares.Square (choiceRep s t M)
      (Squares.product (choiceRep s t M) ⟨M, M, id⟩) where
  impl := fun x => match x with
    | .inl a => (.inl (p.run a).1, (p.run a).2)
    | .inr b => (.inr (q.run b).1, (q.run b).2)
  spec := sequential 1
  commutes := fun x => by
    cases x with
    | inl a => exact p.correct a
    | inr b => exact q.correct b

def voidRep (M : Type u) : Squares.Rep where
  R := PEmpty
  S := List M
  decode := fun x => nomatch x

def void (M : Type u) [Monoid M] :
    Squares.Square (voidRep M) (Squares.product (voidRep M) ⟨M, M, id⟩) where
  impl := fun x => nomatch x
  spec := sequential 1
  commutes := fun x => nomatch x

end Scanner

inductive ScanPlan where
  | empty
  | leaf
  | prod (left right : ScanPlan)
  | comp (outer inner : ScanPlan)
  deriving Repr, DecidableEq

namespace ScanPlan

def shape : ScanPlan → Shape
  | .empty => .empty
  | .leaf => .leaf
  | .prod s t => .prod s.shape t.shape
  | .comp s t => s.shape.subst t.shape

def scanner : (p : ScanPlan) → Scanner p.shape M
  | .empty => .unit
  | .leaf => .singleton
  | .prod s t => s.scanner.product t.scanner
  | .comp s t => s.scanner.compose t.scanner

theorem correct (p : ScanPlan) (x : p.shape.Data M) :
    (p.shape.flatten (p.scanner.run x).1, (p.scanner.run x).2) =
      sequential 1 (p.shape.flatten x) :=
  p.scanner.correct x

def pair : ScanPlan := .prod .leaf .leaf

def rightPow (p : ScanPlan) : Nat → ScanPlan
  | 0 => .leaf
  | n + 1 => .comp p (p.rightPow n)

def leftPow (p : ScanPlan) : Nat → ScanPlan
  | 0 => .leaf
  | n + 1 => .comp (p.leftPow n) p

def bush : Nat → ScanPlan
  | 0 => pair
  | n + 1 => .comp (bush n) (bush n)

theorem rightPow_size (p : ScanPlan) (n : Nat) :
    (p.rightPow n).shape.size = p.shape.size ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [rightPow, shape, Shape.size_subst, ih, Nat.pow_succ, Nat.mul_comm]

theorem leftPow_size (p : ScanPlan) (n : Nat) :
    (p.leftPow n).shape.size = p.shape.size ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [leftPow, shape, Shape.size_subst, ih, Nat.pow_succ]

end ScanPlan
end Applications.Parallel
