import SquareKit.Internal.PathTransport.ComparisonHorizontalReindex

noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory CategoryTheory.Functor
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

/-- Horizontal composition of the actual base/fiber signature maps. -/
def Signature.horizontal (S T : Signature.{u}) (h : S.base.right = T.base.left)
    (hB : HEq S.rightFiber T.leftFiber) : Signature.{u} := by
  rcases S with ⟨⟨C₀, C₁, R⟩, B₀, B₁, α⟩
  rcases T with ⟨⟨C₁', C₂, Q⟩, B₁', B₂, β⟩
  dsimp at h
  cases h
  dsimp at hB
  cases eq_of_heq hB
  exact ⟨⟨C₀, C₂, R ⋙ Q⟩, B₀, B₂, α ≫ whiskerLeft R β⟩

theorem Signature.horizontal_base (S T : Signature.{u})
    (h : S.base.right = T.base.left) (hB : HEq S.rightFiber T.leftFiber) :
    (S.horizontal T h hB).base = S.base.horizontal T.base h := by
  rcases S with ⟨⟨C₀, C₁, R⟩, B₀, B₁, α⟩
  rcases T with ⟨⟨C₁', C₂, Q⟩, B₁', B₂, β⟩
  dsimp at h
  cases h
  dsimp at hB
  cases eq_of_heq hB
  rfl

theorem Signature.horizontal_primitive_middle (S T : Signature.{u})
    (h : S.base.right = T.base.left) (hB : HEq S.rightFiber T.leftFiber) :
    HEq S.primitive.right T.primitive.left := by
  rcases S with ⟨⟨C₀, C₁, R⟩, B₀, B₁, α⟩
  rcases T with ⟨⟨C₁', C₂, Q⟩, B₁', B₂, β⟩
  dsimp at h
  cases h
  dsimp at hB
  cases eq_of_heq hB
  rfl

/-- Discrete primitive fibers preserve horizontal signature composition. -/
theorem Signature.horizontal_primitive (S T : Signature.{u})
    (h : S.base.right = T.base.left) (hB : HEq S.rightFiber T.leftFiber) :
    HEq (S.horizontal T h hB).primitive
      (S.primitive.horizontal T.primitive h (S.horizontal_primitive_middle T h hB)) := by
  rcases S with ⟨⟨C₀, C₁, R⟩, B₀, B₁, α⟩
  rcases T with ⟨⟨C₁', C₂, Q⟩, B₁', B₂, β⟩
  dsimp at h
  cases h
  dsimp at hB
  cases eq_of_heq hB
  apply heq_of_eq
  refine @Family.ext _ _ _ rfl rfl ?_
  apply heq_of_eq
  change whiskerRight (α ≫ whiskerLeft R β) discrete = _
  rw [whiskerRight_comp]
  rfl

theorem Signature.horizontal_baseFamily_middle (S T : Signature.{u})
    (h : S.base.right = T.base.left) {Γ Δ : Context.{u}} (hΓ : Γ.right = Δ.left) :
    HEq (S.baseFamily Γ).right (T.baseFamily Δ).left := by
  rcases S with ⟨⟨C₀, C₁, R⟩, B₀, B₁, α⟩
  rcases T with ⟨⟨C₁', C₂, Q⟩, B₁', B₂, β⟩
  cases Γ; cases Δ
  dsimp at h hΓ
  cases h; cases hΓ
  rfl

theorem Signature.horizontal_baseFamily (S T : Signature.{u})
    (h : S.base.right = T.base.left) (hB : HEq S.rightFiber T.leftFiber)
    {Γ Δ : Context.{u}} (hΓ : Γ.right = Δ.left) :
    (S.horizontal T h hB).baseFamily (Γ.horizontal Δ hΓ) =
      (S.baseFamily Γ).horizontal (T.baseFamily Δ) hΓ
        (S.horizontal_baseFamily_middle T h hΓ) := by
  rcases S with ⟨⟨C₀, C₁, R⟩, B₀, B₁, α⟩
  rcases T with ⟨⟨C₁', C₂, Q⟩, B₁', B₂, β⟩
  cases Γ; cases Δ
  dsimp at h hΓ
  cases h; cases hΓ
  dsimp at hB
  cases eq_of_heq hB
  rfl

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
