import SquareKit.Internal.Cubical.CocycleFillingSubstitution
import SquareKit.Internal.Cubical.FamilyData

/-! The cocycle presheaf has a constructed uniform filling operation. -/
namespace SquareKit.Cubical.CategoryCocycles
open CategoryTheory Presheaf

noncomputable def cocycleFilling (Γ : Context.{0}) : Filling (cocycleFamily Γ) where
  fill _p _φ b := boxFill b

theorem cocycleFilling_lawful (Γ : Context.{0}) : (cocycleFilling Γ).Lawful where
  fills _p _φ b := boxFill_fills b
  uniform _p _φ b σ := boxFill_reindex b σ

noncomputable def lawfulCocycleFamily (Γ : Context.{0}) : LawfulFamily Γ :=
  ⟨⟨cocycleFamily Γ,cocycleFilling Γ⟩,cocycleFilling_lawful Γ⟩

end SquareKit.Cubical.CategoryCocycles
