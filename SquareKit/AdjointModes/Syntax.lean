import SquareKit.AdjointModes.Resources

/-! A combinator presentation of the multiplicative, two-mode shift fragment.
A source context is represented by its tensor at L and product at U. Upward
formation cannot capture an arbitrary L input: `upMap` changes both endpoints,
and the unit starts at U. No additive conjunction or implication is included. -/
namespace SquareKit.AdjointModes

inductive Ty : Mode → Type
  | atom (m) : Ty m
  | one (m) : Ty m
  | times {m} : Ty m → Ty m → Ty m
  | down : Ty .unrestricted → Ty .linear
  | up : Ty .linear → Ty .unrestricted

abbrev Signature := {m : Mode} → Ty m → Ty m → Type

inductive Term (P : Signature) : {m : Mode} → Ty m → Ty m → Type
  | prim {m A B} : P (m := m) A B → Term P A B
  | id {m A} : Term P (m := m) A A
  | comp {m A B C} : Term P (m := m) B C → Term P A B → Term P A C
  | times {m A B C D} : Term P (m := m) A B → Term P C D →
      Term P (.times A C) (.times B D)
  | swap {m A B} : Term P (m := m) (.times A B) (.times B A)
  | assoc {m A B C} : Term P (m := m) (.times (.times A B) C) (.times A (.times B C))
  | unassoc {m A B C} : Term P (m := m) (.times A (.times B C)) (.times (.times A B) C)
  | unitor {m A} : Term P (m := m) (.times (.one m) A) A
  | ununitor {m A} : Term P (m := m) A (.times (.one m) A)
  | copy {A} : Term P (m := .unrestricted) A (.times A A)
  | discard {A} : Term P (m := .unrestricted) A (.one .unrestricted)
  | downMap {A B} : Term P A B → Term P (.down A) (.down B)
  | upMap {A B} : Term P A B → Term P (.up A) (.up B)
  | unit {A} : Term P A (.up (.down A))
  | counit {A} : Term P (.down (.up A)) A
  | downTimes {A B} : Term P (.down (.times A B)) (.times (.down A) (.down B))
  | timesDown {A B} : Term P (.times (.down A) (.down B)) (.down (.times A B))
  | downOne : Term P (.down (.one .unrestricted)) (.one .linear)
  | oneDown : Term P (.one .linear) (.down (.one .unrestricted))

/-- U meanings are ordinary sets; L meanings have a conserved resource degree. -/
structure Atoms where
  unrestricted : Type
  linear : Resource

def Ty.meaning (v : Atoms) : {m : Mode} → Ty m → Resource
  | _, .atom .unrestricted => AdjointModes.down v.unrestricted
  | _, .atom .linear => v.linear
  | _, .one _ => AdjointModes.one
  | _, .times A B => tensor (A.meaning v) (B.meaning v)
  | _, .down A => AdjointModes.down (A.meaning v).Carrier
  | _, .up A => AdjointModes.down (AdjointModes.up (A.meaning v))

theorem Ty.unrestricted_zero (v : Atoms) (A : Ty .unrestricted)
    (x : (A.meaning v).Carrier) : (A.meaning v).degree x = 0 := by
  generalize hm : Mode.unrestricted = m at A
  induction A with
  | atom m => cases hm; rfl
  | one m => rfl
  | times A B ihA ihB =>
    cases hm
    exact congrArg₂ (· + ·) (ihA rfl x.1) (ihB rfl x.2)
  | down A => cases hm
  | up A => rfl

abbrev PrimitiveMeaning (v : Atoms) (P : Signature) :=
  {m : Mode} → {A B : Ty m} → P A B → Map (A.meaning v) (B.meaning v)

/-- Forget the resource restriction, retaining the entire selected payload. -/
def Ty.Payload (v : Atoms) : {m : Mode} → Ty m → Type
  | _, .atom .unrestricted => v.unrestricted
  | _, .atom .linear => v.linear.Carrier
  | _, .one _ => Unit
  | _, .times A B => A.Payload v × B.Payload v
  | _, .down A => A.Payload v
  | _, .up A => A.Payload v

def Ty.forget (v : Atoms) : {m : Mode} → (A : Ty m) → (A.meaning v).Carrier → A.Payload v
  | _, .atom .unrestricted, x => x
  | _, .atom .linear, x => x
  | _, .one _, x => x
  | _, .times A B, x => (A.forget v x.1, B.forget v x.2)
  | _, .down A, x => A.forget v x
  | _, .up A, x => A.forget v x.val

end SquareKit.AdjointModes
