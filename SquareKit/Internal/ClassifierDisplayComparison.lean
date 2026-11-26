import SquareKit.Internal.CoherentFamilyClassification
import SquareKit.SplitPresheaf

/-! Coherent local codes compared with actual dependent displays.
Comprehension is constructed as a total functor, not supplied as a classifier axiom.
This is a comparison on presheaf contexts, not a chosen small universe. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.ClassifierDisplayComparison
open CategoryTheory Limits
open CoherentFamilyClassification
universe u v w
variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)

/-- Every coherent code determines a display, and every display is recovered,
including all maps over the context. -/
noncomputable def equivalence : Code F.Elements (Type w) ≌ Over F :=
  (CoherentFamilyClassification.equivalence F.Elements (Type w)).trans
    (ElementFamilies.equivalence F).symm

/-- Context extension of an arbitrary coherent code. -/
abbrev extension (A : Code F.Elements (Type w)) :=
  SplitPresheaf.extension ((decode F.Elements (Type w)).obj A)

abbrev projection (A : Code F.Elements (Type w)) : extension F A ⟶ F :=
  SplitPresheaf.p ((decode F.Elements (Type w)).obj A)

/-- The display comparison uses this actual extension, with its projection. -/
theorem equivalence_obj (A : Code F.Elements (Type w)) :
    (equivalence F).functor.obj A = Over.mk (projection F A) := rfl

/-- A code map induces a map over the context, without an invertibility assumption. -/
theorem map_projection {A B : Code F.Elements (Type w)} (α : A ⟶ B) :
    ((equivalence F).functor.map α).left ≫ projection F B = projection F A :=
  Over.w _

variable {F} {G H : C ⥤ Type w}

/-- Reindexing coherent codes agrees with substitution of their decoded displays.
The comparison is derived from identity-view recovery, not postulated. -/
def displayReindex (A : Code F.Elements (Type w)) (σ : G ⟶ F) :
    Over.mk (projection G ((reindex σ.mapElements).obj A)) ≅
      Over.mk (SplitPresheaf.p (SplitPresheaf.tySub ((decode F.Elements (Type w)).obj A) σ)) :=
  (ElementFamilies.totalFunctor G).mapIso ((decodeReindex σ.mapElements).app A)

/-- Substitution gives a genuine pullback of the decoded context extension. -/
theorem extension_pullback (A : Code F.Elements (Type w)) (σ : G ⟶ F) :
    IsPullback (SplitPresheaf.lift ((decode F.Elements (Type w)).obj A) σ)
      (SplitPresheaf.p (SplitPresheaf.tySub ((decode F.Elements (Type w)).obj A) σ))
      (projection F A) σ :=
  SplitPresheaf.extension_pullback _ σ

/-- Maps into the constructed extension are exactly substitutions paired with terms.
This is the comprehension universal property, including arbitrary source contexts. -/
def comprehension (A : Code F.Elements (Type w)) :
    (G ⟶ extension F A) ≃
      (Σ σ : G ⟶ F, SplitPresheaf.Tm
        (SplitPresheaf.tySub ((decode F.Elements (Type w)).obj A) σ)) where
  toFun k := ⟨k ≫ projection F A, SplitPresheaf.tmSub (SplitPresheaf.q _) k⟩
  invFun t := SplitPresheaf.pair _ t.1 t.2
  left_inv _ := rfl
  right_inv _ := rfl

/-- Pairing commutes with a further substitution, as an equality of actual maps. -/
theorem comprehension_natural (A : Code F.Elements (Type w)) (σ : G ⟶ F)
    (t : SplitPresheaf.Tm (SplitPresheaf.tySub ((decode F.Elements (Type w)).obj A) σ))
    (τ : H ⟶ G) :
    (comprehension A).symm ⟨τ ≫ σ, SplitPresheaf.tmSub t τ⟩ =
      τ ≫ (comprehension A).symm ⟨σ, t⟩ := rfl

end SquareKit.ClassifierDisplayComparison
