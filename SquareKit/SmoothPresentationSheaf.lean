import SquareKit.SmoothPrincipalTopology
import SquareKit.SmoothDescentHom
import Mathlib.CategoryTheory.Sites.Canonical

/-! Experimental categorical scalar sheafness and subcanonicity for the generated
finite-principal smooth topology. Matching families are tested on actual overlaps. -/
noncomputable section
namespace SquareKit.SmoothPresentationSite
open CategoryTheory Opposite SmoothAlgebra PresentedLocalization PrincipalCover

abbrev scalarData : Siteᵒᵖ ⥤ Type where
  obj X := Carrier X.unop.unop
  map f := ↾(smoothMap f.unop.unop).toFun

private theorem overlap_square (A : Code) (s t : Carrier A) :
    (show localization A s ⟶ localization A (s*t) from atLeft A.equations s t).op ≫
      (localizationBase A s).op =
    (show localization A t ⟶ localization A (s*t) from atRight A.equations s t).op ≫
      (localizationBase A t).op := by
  exact congrArg Quiver.Hom.op ((atLeft_base A.equations s t).trans (atRight_base A.equations s t).symm)

theorem scalar_principal (A : Code) {k : ℕ} (s : Fin k → Carrier A) (hs : Covers s) :
    Presieve.IsSheafFor scalarData (principalPresieve A s) := by
  apply (Presieve.isSheafFor_arrows_iff _ _).mpr
  intro a ha
  have hc : AtCompatible A.equations s a := by
    intro i j
    exact ha i j (op (localization A (s i*s j)))
      (show localization A (s i) ⟶ localization A (s i*s j) from atLeft A.equations (s i) (s j)).op
      (show localization A (s j) ⟶ localization A (s i*s j) from atRight A.equations (s i) (s j)).op
      (overlap_square A (s i) (s j))
  refine ⟨(atDescentEquiv A.equations s hs).symm ⟨a,hc⟩,fun i => at_glue_spec _ _ _ _ i,?_⟩
  intro b hb
  exact at_separated A.equations s hs b _ (fun i => (hb i).trans (at_glue_spec A.equations s hs ⟨a,hc⟩ i).symm)

theorem scalar_isSheaf : Presieve.IsSheaf topology scalarData :=
  (isSheaf_iff_principal scalarData).mpr (fun A _ s hs => scalar_principal A s hs)

/-- Every representable, for every source presentation, satisfies descent on generators. -/
theorem yoneda_principal (B A : Code) {k : ℕ} (s : Fin k → Carrier A) (hs : Covers s) :
    Presieve.IsSheafFor (yoneda.obj (op B)) (principalPresieve A s) := by
  apply (Presieve.isSheafFor_arrows_iff _ _).mpr
  intro a ha
  let h : ∀ i, Hom (Carrier B) (At A.equations (s i)) := fun i => smoothMap (a i).unop
  have hc : HomCompatible A.equations s h := by
    intro i j
    have he := ha i j (op (localization A (s i*s j)))
      (show localization A (s i) ⟶ localization A (s i*s j) from atLeft A.equations (s i) (s j)).op
      (show localization A (s j) ⟶ localization A (s i*s j) from atRight A.equations (s i) (s j)).op
      (overlap_square A (s i) (s j))
    exact congrArg Quiver.Hom.unop he
  let g : B ⟶ A := glueHom A.equations s hs h hc
  refine ⟨g.op,fun i => ?_,?_⟩
  · apply Quiver.Hom.unop_inj
    exact glueHom_factor A.equations s hs h hc i
  · intro b hb
    apply Quiver.Hom.unop_inj
    exact glueHom_unique A.equations s hs h hc (smoothMap b.unop)
      (fun i => congrArg Quiver.Hom.unop (hb i))

theorem yoneda_isSheaf (B : Site) : Presieve.IsSheaf topology (yoneda.obj B) :=
  (isSheaf_iff_principal _).mpr (fun A _ s hs => yoneda_principal B.unop A s hs)

instance : topology.Subcanonical := GrothendieckTopology.Subcanonical.of_isSheaf_yoneda_obj topology yoneda_isSheaf

/-- The scalar is an object of the actual generated-topology sheaf category. -/
def scalar : Sheaf topology Type := ⟨scalarData,(isSheaf_iff_isSheaf_of_type _ _).mpr scalar_isSheaf⟩

end SquareKit.SmoothPresentationSite
