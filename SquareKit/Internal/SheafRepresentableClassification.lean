import SquareKit.Internal.PresheafFamilyClassification
import SquareKit.SplitSheaf

/-! Derived evaluation recovery transports sheafness of dependent total spaces.
This does not assert sheafness of arbitrary code presheaves. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.RepresentableClassification
open CategoryTheory
universe u v w
variable {C : Type v} [Category.{w} C] {Γ : Context.{u} C}

/-- The recovered family comparison induces an isomorphism of total spaces. -/
def Evaluation.totalIso {A D : Family Γ} (E : Evaluation A D) :
    SplitPresheaf.extension D ≅ SplitPresheaf.extension A :=
  (Over.forget Γ).mapIso ((ElementFamilies.totalFunctor Γ).mapIso E.iso)

/-- Local evaluation recovers a sheaf total whenever the original total is a sheaf. -/
theorem Evaluation.total_isSheaf {A D : Family Γ} (E : Evaluation A D)
    (J : GrothendieckTopology C) (h : Presheaf.IsSheaf J (SplitPresheaf.extension A)) :
    Presheaf.IsSheaf J (SplitPresheaf.extension D) :=
  (Presheaf.isSheaf_of_iso_iff (J := J) E.totalIso).2 h

/-- Ordinary-family decoding preserves actual sheaf displays. -/
def PresheafFamily.decodeSheaf {J : GrothendieckTopology C}
    {Γ : Sheaf J (Type (max u w))} (A : SplitSheaf.Ty Γ) : SplitSheaf.Ty Γ where
  family := system.decode universalDecode (system.code A.family)
  isSheaf := (evaluation A.family).total_isSheaf J A.isSheaf

/-- Recovery is an isomorphism of sheaves, not just their underlying presheaves. -/
def PresheafFamily.decodeSheafIso {J : GrothendieckTopology C}
    {Γ : Sheaf J (Type (max u w))} (A : SplitSheaf.Ty Γ) :
    SplitSheaf.extension (decodeSheaf A) ≅ SplitSheaf.extension A :=
  (fullyFaithfulSheafToPresheaf J _).preimageIso (evaluation A.family).totalIso

/-- The recovered total space retains its original display over the context. -/
theorem PresheafFamily.decodeSheafIso_projection {J : GrothendieckTopology C}
    {Γ : Sheaf J (Type (max u w))} (A : SplitSheaf.Ty Γ) :
    (decodeSheafIso A).hom ≫ SplitSheaf.p A = SplitSheaf.p (decodeSheaf A) := by
  apply (sheafToPresheaf J (Type (max u w))).map_injective
  exact ((ElementFamilies.totalFunctor Γ.obj).mapIso (evaluation A.family).iso).hom.w

end SquareKit.RepresentableClassification
