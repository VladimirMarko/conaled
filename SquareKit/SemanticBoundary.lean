import Squares

/-! A set-level semantic-client boundary derived from existing computation squares.
Raw representations remain available to compiler code. Clients taking `Handle`
cannot distinguish representatives with equal decoded meanings. This quotient
uses host equality; it is not a construction for arbitrary higher identities. -/

namespace Squares.SemanticBoundary

universe u

def semanticSetoid (A : Rep.{u}) : Setoid A.R where
  r x y := A.decode x = A.decode y
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

def Handle (A : Rep.{u}) := Quotient (semanticSetoid A)

def pack {A : Rep.{u}} (x : A.R) : Handle A := Quotient.mk _ x

def meaning {A : Rep.{u}} : Handle A → A.S :=
  Quotient.lift A.decode (fun _ _ h => h)

@[simp] theorem meaning_pack {A : Rep.{u}} (x : A.R) :
    meaning (pack x) = A.decode x := rfl

/-- Every total pure client of handles respects the specified equivalence. -/
theorem client_invariant {A : Rep.{u}} {T : Sort v}
    (client : Handle A → T) {x y : A.R} (h : A.decode x = A.decode y) :
    client (pack x) = client (pack y) :=
  congrArg client (Quotient.sound h)

/-- Existing local commuting evidence derives descent to semantic handles. -/
def lift {A B : Rep.{u}} (f : Square A B) : Handle A → Handle B :=
  Quotient.lift (fun x => pack (f.impl x)) (by
    intro x y h
    apply Quotient.sound
    exact (f.commutes x).trans ((congrArg f.spec h).trans (f.commutes y).symm))

@[simp] theorem lift_pack {A B : Rep.{u}} (f : Square A B) (x : A.R) :
    lift f (pack x) = pack (f.impl x) := rfl

theorem lift_meaning {A B : Rep.{u}} (f : Square A B) (x : Handle A) :
    meaning (lift f x) = f.spec (meaning x) :=
  Quotient.inductionOn x f.commutes

theorem lift_identity {A : Rep.{u}} (x : Handle A) :
    lift (identity A) x = x := Quotient.inductionOn x (fun _ => rfl)

theorem lift_compose {A B C : Rep.{u}} (g : Square B C) (f : Square A B)
    (x : Handle A) : lift (compose g f) x = lift g (lift f x) :=
  Quotient.inductionOn x (fun _ => rfl)

/-- Replacing an implementation of the same specification preserves its output handle. -/
theorem implementation_independent {A B : Rep.{u}} (f g : Square A B)
    (sameSpec : ∀ s, f.spec s = g.spec s) (x : Handle A) : lift f x = lift g x := by
  induction x using Quotient.inductionOn with
  | h x =>
    exact Quotient.sound ((f.commutes x).trans
      ((sameSpec (A.decode x)).trans (g.commutes x).symm))

end Squares.SemanticBoundary
