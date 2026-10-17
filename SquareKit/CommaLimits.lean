import SquareKit.CommaLawful
import Mathlib.CategoryTheory.Limits.Comma

/-! For lawful categories only the right interpretation must preserve the
particular limit. No preservation assumption on the left interpretation is
needed. The raw construction in `CommaProducts` instead retains executable
chosen operations without source laws, using strong comparisons on both sides.
Both constructions have the same component objects and projections. The
joint-reflection result below identifies any such raw cone with a limit once
its components are limits; uniqueness then supplies the canonical isomorphism.
-/
namespace SquareKit.Comma
open CategoryTheory CategoryTheory.Limits
universe u₁ v₁ u₂ v₂ u₃ v₃ w z
variable {A : Type u₁} {B : Type u₂} {T : Type u₃}
variable [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} T]
variable {L : A ⥤ T} {R : B ⥤ T} {I : Type w} [Category.{z} I]

noncomputable def lawfulLimitCone (F : I ⥤ CategoryTheory.Comma L R)
    [PreservesLimit (F ⋙ CategoryTheory.Comma.snd L R) R]
    (a : Cone (F ⋙ CategoryTheory.Comma.fst L R))
    {b : Cone (F ⋙ CategoryTheory.Comma.snd L R)} (hb : IsLimit b) : Cone F :=
  CategoryTheory.Comma.coneOfPreserves F a hb

noncomputable def lawfulLimitIsLimit (F : I ⥤ CategoryTheory.Comma L R)
    [PreservesLimit (F ⋙ CategoryTheory.Comma.snd L R) R]
    {a : Cone (F ⋙ CategoryTheory.Comma.fst L R)} (ha : IsLimit a)
    {b : Cone (F ⋙ CategoryTheory.Comma.snd L R)} (hb : IsLimit b) :
    IsLimit (lawfulLimitCone F a hb) :=
  CategoryTheory.Comma.coneOfPreservesIsLimit F ha hb

/-- This applies to the exact conversion of a raw product/terminal cone as well
as to any other shape: its universal property is checked componentwise. -/
def lawfulConeIsLimit {F : I ⥤ CategoryTheory.Comma L R} (c : Cone F)
    [PreservesLimit (F ⋙ CategoryTheory.Comma.snd L R) R]
    (ha : IsLimit ((CategoryTheory.Comma.fst L R).mapCone c))
    (hb : IsLimit ((CategoryTheory.Comma.snd L R).mapCone c)) : IsLimit c :=
  CategoryTheory.Comma.fstSndJointlyReflectLimit ha hb

noncomputable def lawfulConeComparison {F : I ⥤ CategoryTheory.Comma L R} (c : Cone F)
    [PreservesLimit (F ⋙ CategoryTheory.Comma.snd L R) R]
    (ha : IsLimit ((CategoryTheory.Comma.fst L R).mapCone c))
    (hb : IsLimit ((CategoryTheory.Comma.snd L R).mapCone c)) :
    c.pt ≅ (lawfulLimitCone F ((CategoryTheory.Comma.fst L R).mapCone c) hb).pt :=
  (lawfulConeIsLimit c ha hb).conePointUniqueUpToIso (lawfulLimitIsLimit F ha hb)
end SquareKit.Comma
