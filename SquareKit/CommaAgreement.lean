import SquareKit.CommaExact

/-! Agreement of exact connectors is a subtype of pairs. Both implementations
remain available, and both must produce the same observation. -/
namespace SquareKit.Comma.Exact
universe u

/-- The pullback carrier, with its common observation as connector. -/
def agreement {R₁ R₂ S : Type u} (d₁ : R₁ → S) (d₂ : R₂ → S) : Object where
  left := {p : R₁ × R₂ // d₁ p.1 = d₂ p.2}
  right := S
  connector p := d₁ p.val.1

/-- Two comma squares with the same semantic arrow act on the agreement carrier. -/
def agree {R₁ R₂ S T₁ T₂ U : Type u}
    {d₁ : R₁ → S} {d₂ : R₂ → S} {e₁ : T₁ → U} {e₂ : T₂ → U}
    (f : Arrow ⟨R₁, S, d₁⟩ ⟨T₁, U, e₁⟩)
    (g : Arrow ⟨R₂, S, d₂⟩ ⟨T₂, U, e₂⟩) (same : f.right = g.right) :
    Arrow (agreement d₁ d₂) (agreement e₁ e₂) where
  left p := ⟨(f.left p.val.1, g.left p.val.2),
    (congrFun f.commutes p.val.1).trans
      ((congrFun same _).trans ((congrArg g.right p.property).trans
        (congrFun g.commutes p.val.2).symm))⟩
  right := f.right
  commutes := funext fun p => congrFun f.commutes p.val.1

def agreementFirst {R₁ R₂ S : Type u} (d₁ : R₁ → S) (d₂ : R₂ → S) :
    Arrow (agreement d₁ d₂) ⟨R₁, S, d₁⟩ :=
  ⟨fun p => p.val.1, id, rfl⟩

def agreementSecond {R₁ R₂ S : Type u} (d₁ : R₁ → S) (d₂ : R₂ → S) :
    Arrow (agreement d₁ d₂) ⟨R₂, S, d₂⟩ :=
  ⟨fun p => p.val.2, id, funext fun p => p.property.symm⟩

theorem agree_first {R₁ R₂ S T₁ T₂ U : Type u}
    {d₁ : R₁ → S} {d₂ : R₂ → S} {e₁ : T₁ → U} {e₂ : T₂ → U}
    (f : Arrow ⟨R₁, S, d₁⟩ ⟨T₁, U, e₁⟩)
    (g : Arrow ⟨R₂, S, d₂⟩ ⟨T₂, U, e₂⟩) (same : f.right = g.right) :
    categoryOps.comp (agreementFirst e₁ e₂) (agree f g same) =
      categoryOps.comp f (agreementFirst d₁ d₂) := rfl

theorem agree_second {R₁ R₂ S T₁ T₂ U : Type u}
    {d₁ : R₁ → S} {d₂ : R₂ → S} {e₁ : T₁ → U} {e₂ : T₂ → U}
    (f : Arrow ⟨R₁, S, d₁⟩ ⟨T₁, U, e₁⟩)
    (g : Arrow ⟨R₂, S, d₂⟩ ⟨T₂, U, e₂⟩) (same : f.right = g.right) :
    categoryOps.comp (agreementSecond e₁ e₂) (agree f g same) =
      categoryOps.comp g (agreementSecond d₁ d₂) := Hom.ext rfl same

/-- Agreement is stable under horizontal composition of both implementations. -/
theorem agree_comp {R₁ R₂ S T₁ T₂ U V₁ V₂ W : Type u}
    {d₁ : R₁ → S} {d₂ : R₂ → S} {e₁ : T₁ → U} {e₂ : T₂ → U}
    {h₁ : V₁ → W} {h₂ : V₂ → W}
    (f₁ : Arrow ⟨R₁, S, d₁⟩ ⟨T₁, U, e₁⟩)
    (f₂ : Arrow ⟨R₂, S, d₂⟩ ⟨T₂, U, e₂⟩)
    (g₁ : Arrow ⟨T₁, U, e₁⟩ ⟨V₁, W, h₁⟩)
    (g₂ : Arrow ⟨T₂, U, e₂⟩ ⟨V₂, W, h₂⟩)
    (sf : f₁.right = f₂.right) (sg : g₁.right = g₂.right) :
    agree (categoryOps.comp g₁ f₁) (categoryOps.comp g₂ f₂)
      (by change (fun x => g₁.right (f₁.right x)) = (fun x => g₂.right (f₂.right x)); rw [sf, sg]) =
      categoryOps.comp (agree g₁ g₂ sg) (agree f₁ f₂ sf) := rfl
end SquareKit.Comma.Exact
