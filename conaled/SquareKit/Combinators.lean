import SquareKit.CommaAgreement

/-! Reusable exact representations, vector lifting and synchronized implementations. -/
universe u
namespace Squares

def exact (A : Type u) : Rep.{u} := ⟨A, A, id⟩

def exactSquare {A B : Type u} (f : A → B) : Square (exact A) (exact B) :=
  ⟨f, f, fun _ => rfl⟩

def indexed (ι : Type u) (A : Rep.{u}) : Rep.{u} where
  R := ι → A.R
  S := ι → A.S
  decode x i := A.decode (x i)

def mapIndexed {A B : Rep.{u}} (ι : Type u) (f : Square A B) :
    Square (indexed ι A) (indexed ι B) where
  impl x i := f.impl (x i)
  spec x i := f.spec (x i)
  commutes x := funext fun i => f.commutes (x i)

theorem mapIndexed_compose {A B C : Rep.{u}} (ι : Type u)
    (g : Square B C) (f : Square A B) :
    mapIndexed ι (compose g f) = compose (mapIndexed ι g) (mapIndexed ι f) :=
  Square.ext (fun _ => rfl) (fun _ => rfl)

/-- A pullback: two implementations must decode to the same semantic value. -/
def synchronized {R₁ R₂ S : Type u} (d₁ : R₁ → S) (d₂ : R₂ → S) : Rep.{u} :=
  SquareKit.Comma.Exact.toRep (SquareKit.Comma.Exact.agreement d₁ d₂)

def synchronize {R₁ R₂ S T₁ T₂ U : Type u}
    {d₁ : R₁ → S} {d₂ : R₂ → S} {e₁ : T₁ → U} {e₂ : T₂ → U}
    (f : Square ⟨R₁, S, d₁⟩ ⟨T₁, U, e₁⟩)
    (g : Square ⟨R₂, S, d₂⟩ ⟨T₂, U, e₂⟩)
    (same : ∀ s, f.spec s = g.spec s) :
    Square (synchronized d₁ d₂) (synchronized e₁ e₂) :=
  SquareKit.Comma.Exact.toSquare (SquareKit.Comma.Exact.agree
    (SquareKit.Comma.Exact.ofSquare f) (SquareKit.Comma.Exact.ofSquare g) (funext same))

@[simp] theorem synchronized_as_agreement {R₁ R₂ S : Type u}
    (d₁ : R₁ → S) (d₂ : R₂ → S) :
    SquareKit.Comma.Exact.ofRep (synchronized d₁ d₂) =
      SquareKit.Comma.Exact.agreement d₁ d₂ := rfl

@[simp] theorem synchronize_as_agree {R₁ R₂ S T₁ T₂ U : Type u}
    {d₁ : R₁ → S} {d₂ : R₂ → S} {e₁ : T₁ → U} {e₂ : T₂ → U}
    (f : Square ⟨R₁, S, d₁⟩ ⟨T₁, U, e₁⟩)
    (g : Square ⟨R₂, S, d₂⟩ ⟨T₂, U, e₂⟩)
    (same : ∀ s, f.spec s = g.spec s) :
    SquareKit.Comma.Exact.ofSquare (synchronize f g same) =
      SquareKit.Comma.Exact.agree (d₁ := d₁) (d₂ := d₂) (e₁ := e₁) (e₂ := e₂)
        (SquareKit.Comma.Exact.ofSquare f)
        (SquareKit.Comma.Exact.ofSquare g) (funext same) := rfl

theorem synchronize_agrees {R₁ R₂ S T₁ T₂ U : Type u}
    {d₁ : R₁ → S} {d₂ : R₂ → S} {e₁ : T₁ → U} {e₂ : T₂ → U}
    (f : Square ⟨R₁, S, d₁⟩ ⟨T₁, U, e₁⟩)
    (g : Square ⟨R₂, S, d₂⟩ ⟨T₂, U, e₂⟩)
    (same : ∀ s, f.spec s = g.spec s) (p : (synchronized d₁ d₂).R) :
    e₁ ((synchronize f g same).impl p).val.1 =
      e₂ ((synchronize f g same).impl p).val.2 :=
  ((synchronize f g same).impl p).property

end Squares
