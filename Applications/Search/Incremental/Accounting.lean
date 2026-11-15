/-! An explicit unit-operation interpretation for the two search machines.
Map access is priced as one logical cell access. Rational and integer arithmetic
have the supplied scalar price; this is not a bit-cost or Lean heap model. -/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Incremental.Accounting
variable {α β : Type}

inductive Event where
  | read
  | write
  | compare
  | add
  | multiply
  | divide
  | denominator
  | allocate
  | branch
  deriving DecidableEq, Repr

abbrev Prices := Event → Nat
abbrev Trace := List Event
abbrev Measured (α : Type) := α × Trace

def bill (prices : Prices) (events : Trace) : Nat :=
  (events.map prices).sum

def unitPrices : Prices := fun _ => 1

def pure (x : α) : Measured α := (x, [])

def bind (x : Measured α) (f : α → Measured β) : Measured β :=
  let y := f x.1
  (y.1, x.2 ++ y.2)

theorem bill_append (prices : Prices) (xs ys : Trace) :
    bill prices (xs ++ ys) = bill prices xs + bill prices ys := by
  simp [bill]

@[simp] theorem bill_unit (xs : Trace) : bill unitPrices xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change 1 + bill unitPrices xs = xs.length + 1
    rw [ih, Nat.add_comm]

end Search.Incremental.Accounting
