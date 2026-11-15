import SquareKit.Internal.PathTransport.ComparisonHorizontalSignature

noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

theorem Family.reindex_heq {Γ Γ' Δ Δ' : Context.{u}} (hΓ : Γ = Γ') (hΔ : Δ = Δ')
    {A : Family Γ} {B : Family Γ'} (hA : HEq A B)
    {σ : Substitution Δ Γ} {τ : Substitution Δ' Γ'} (hσ : HEq σ τ) :
    HEq (A.reindex σ) (B.reindex τ) := by
  cases hΓ; cases hΔ; cases eq_of_heq hA; cases eq_of_heq hσ; rfl

theorem Signature.horizontal_baseSubstitution_middle (S T : Signature.{u})
    (h : S.base.right = T.base.left) {Γ Δ : Context.{u}} (hΓ : Γ.right = Δ.left)
    (x : Section (S.baseFamily Γ)) (y : Section (T.baseFamily Δ))
    (hx : HEq x.right y.left) : HEq (S.baseSubstitution x).right (T.baseSubstitution y).left := by
  rcases S with ⟨⟨C₀, C₁, R⟩, B₀, B₁, α⟩
  rcases T with ⟨⟨C₁', C₂, Q⟩, B₁', B₂, β⟩
  cases Γ; cases Δ
  dsimp at h hΓ
  cases h; cases hΓ
  exact heq_of_eq (congrArg baseFunctor (eq_of_heq hx))

/-- The composed base point retains its two given endpoint sections. -/
def Signature.horizontal_point (S T : Signature.{u})
    (h : S.base.right = T.base.left) (hB : HEq S.rightFiber T.leftFiber)
    {Γ Δ : Context.{u}} (hΓ : Γ.right = Δ.left)
    (x : Section (S.baseFamily Γ)) (y : Section (T.baseFamily Δ))
    (hx : HEq x.right y.left) : Section ((S.horizontal T h hB).baseFamily (Γ.horizontal Δ hΓ)) :=
  cast (congrArg Section (S.horizontal_baseFamily T h hB hΓ).symm)
    (x.horizontal y hΓ (S.horizontal_baseFamily_middle T h hΓ) hx)

theorem Signature.horizontal_baseSubstitution (S T : Signature.{u})
    (h : S.base.right = T.base.left) (hB : HEq S.rightFiber T.leftFiber)
    {Γ Δ : Context.{u}} (hΓ : Γ.right = Δ.left)
    (x : Section (S.baseFamily Γ)) (y : Section (T.baseFamily Δ)) (hx : HEq x.right y.left) :
    HEq ((S.horizontal T h hB).baseSubstitution (S.horizontal_point T h hB hΓ x y hx))
      ((S.baseSubstitution x).horizontal (T.baseSubstitution y) h hΓ
        (S.horizontal_baseSubstitution_middle T h hΓ x y hx)) := by
  rcases S with ⟨⟨C₀, C₁, R⟩, B₀, B₁, α⟩
  rcases T with ⟨⟨C₁', C₂, Q⟩, B₁', B₂, β⟩
  cases Γ; cases Δ
  dsimp at h hΓ
  cases h; cases hΓ
  dsimp at hB
  cases eq_of_heq hB
  rcases x with ⟨x₀, x₁, hc⟩
  rcases y with ⟨y₀, y₁, hd⟩
  dsimp at hx
  cases eq_of_heq hx
  apply heq_of_eq
  apply Substitution.ext <;> rfl

theorem Signature.horizontal_fiber_middle (S T : Signature.{u})
    (h : S.base.right = T.base.left) (hB : HEq S.rightFiber T.leftFiber)
    {Γ Δ : Context.{u}} (hΓ : Γ.right = Δ.left)
    (x : Section (S.baseFamily Γ)) (y : Section (T.baseFamily Δ)) (hx : HEq x.right y.left) :
    HEq (S.fiber x).right (T.fiber y).left :=
  S.primitive.horizontal_reindex_middle T.primitive (S.baseSubstitution x) (T.baseSubstitution y)
    h hΓ (S.horizontal_primitive_middle T h hB)
    (S.horizontal_baseSubstitution_middle T h hΓ x y hx)

/-- Primitive dependent fibers preserve composition at the actual composed
base section, including the family-reindexing transports. -/
theorem Signature.horizontal_fiber (S T : Signature.{u})
    (h : S.base.right = T.base.left) (hB : HEq S.rightFiber T.leftFiber)
    {Γ Δ : Context.{u}} (hΓ : Γ.right = Δ.left)
    (x : Section (S.baseFamily Γ)) (y : Section (T.baseFamily Δ)) (hx : HEq x.right y.left) :
    (S.horizontal T h hB).fiber (S.horizontal_point T h hB hΓ x y hx) =
      (S.fiber x).horizontal (T.fiber y) hΓ (S.horizontal_fiber_middle T h hB hΓ x y hx) := by
  apply eq_of_heq
  apply (Family.reindex_heq (S.horizontal_base T h hB) rfl
    (S.horizontal_primitive T h hB) (S.horizontal_baseSubstitution T h hB hΓ x y hx)).trans
  exact heq_of_eq (S.primitive.horizontal_reindex T.primitive (S.baseSubstitution x)
    (T.baseSubstitution y) h hΓ (S.horizontal_primitive_middle T h hB)
    (S.horizontal_baseSubstitution_middle T h hΓ x y hx))

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
