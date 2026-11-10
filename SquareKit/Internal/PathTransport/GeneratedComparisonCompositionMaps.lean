import SquareKit.Internal.PathTransport.GeneratedComparisonComposition

/-! Extract horizontal composition as equality on the common endpoint codes. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u

theorem Context.relabel_composition {Γ Δ Θ : Context.{u}} (h : Γ.Composes Δ Θ)
    {C D E : Grpd.{u,u}} (hΓL : Γ.left = C) (hΓR : Γ.right = D)
    (hΔL : Δ.left = D) (hΔR : Δ.right = E) (hΘL : Θ.left = C) (hΘR : Θ.right = E) :
    Γ.relabel hΓL hΓR ⋙ Δ.relabel hΔL hΔR = Θ.relabel hΘL hΘR := by
  rcases h with ⟨hm, he⟩
  cases he
  subst C; subst D; subst E
  cases Γ; cases Δ; dsimp at hm; cases hm
  rfl

theorem Family.relabel_composition {Γ Δ Θ : Context.{u}}
    {A : Family Γ} {B : Family Δ} {F : Family Θ} (h : A.Composes B F)
    {C D E : Grpd.{u,u}} (hΓL : Γ.left = C) (hΓR : Γ.right = D)
    (hΔL : Δ.left = D) (hΔR : Δ.right = E) (hΘL : Θ.left = C) (hΘR : Θ.right = E)
    {P : C ⥤ Grpd.{u,u}} {Q : D ⥤ Grpd.{u,u}} {R : E ⥤ Grpd.{u,u}}
    (hAL : HEq A.left P) (hAR : HEq A.right Q)
    (hBL : HEq B.left Q) (hBR : HEq B.right R) (hFL : HEq F.left P) (hFR : HEq F.right R) :
    HEq (A.relabelMap hΓL hΓR hAL hAR ≫
      CategoryTheory.Functor.whiskerLeft (Γ.relabel hΓL hΓR) (B.relabelMap hΔL hΔR hBL hBR))
      (F.relabelMap hΘL hΘR hFL hFR) := by
  rcases h with ⟨⟨hm, he⟩, hmiddle, hf⟩
  cases he
  cases eq_of_heq hf
  subst C; subst D; subst E
  cases Γ; cases Δ; dsimp at hm; cases hm
  cases A; cases B; dsimp at hmiddle; cases eq_of_heq hmiddle
  dsimp at hAL hAR hBR
  cases eq_of_heq hAL; cases eq_of_heq hAR; cases eq_of_heq hBR
  rfl

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
