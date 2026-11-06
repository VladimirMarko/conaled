import SquareKit.Internal.PathTransport.TwoFamilyVariableFiber
import SquareKit.Internal.PathTransport.TwoFamilyConstantProjection
import SquareKit.Internal.PathTransport.TwoLocallyDiscreteUnderlying
import SquareKit.Internal.PathTransport.TwoFamilyStructuralModel
import SquareKit.NaturalConjugation
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 100000
universe u
variable {Γ : Context.{u}} (A : Family Γ) (x y : TwoFamily.Section A.data) (γ : Γ)
local notation "I" => (A.identity x y)
theorem variableSectionFiber_obj (B : Family Γ) (δ : Γ) (a : B.data.obj δ) :
 ((variableSectionFiber B δ (variableSection B.data)).lift.obj a).fiber = a := by
 apply eq_of_heq
 exact (TwoFamily.Section.cast_obj_fiber _ _ a).trans
   (TwoFamily.Section.reindex_obj_fiber _ _ _ a)
theorem variableSectionFiber_map (B : Family Γ) (δ : Γ) {a b : B.data.obj δ} (f : a ⟶ b) :
 HEq ((variableSectionFiber B δ (variableSection B.data)).lift.map f).fiber f := by
 have h1 := TwoFamily.Section.cast_map_fiber (variableFamily_fiber B δ)
   ((variableSection B.data).reindex _ (fiberInclusion B.data δ)) f
 have h2 := TwoFamily.Section.reindex_map_fiber _ (variableSection B.data) (fiberInclusion B.data δ) f
 have h3 : HEq ((variableSection B.data).lift.map ((fiberInclusion B.data δ).map f)).fiber f :=
   eqToHom_comp_heq _ _
 exact h1.trans (h2.trans h3)
noncomputable def identityFiberFunctor
 (s : TwoFamily.Section (reindex (projectionHigher (I).data) (I).data)) :=
 locallyDiscreteUnderlying ((variableSectionFiber I γ s).lift.comp
   (constantDiscreteProjection ((I).data.obj γ) _))
noncomputable def identityFiberComparison
 (s t : TwoFamily.Section (reindex (projectionHigher (I).data) (I).data))
 (p : TwoFamily.Section (closedId (reindex (projectionHigher (I).data) (I).data) s t)) :=
 locallyDiscreteComparison (strongPostcomp (variableStrongFiber I γ s t p)
  (constantDiscreteProjection ((I).data.obj γ) _))
private theorem discrete_as_heq {X Y : Type u} {a : Discrete X} {b : Discrete Y}
 (e : X = Y) (h : HEq a b) : HEq a.as b.as := by
 cases e
 cases eq_of_heq h
 rfl
theorem identityFiberFunctor_variable :
 identityFiberFunctor A x y γ (variableSection (I).data) = 𝟭 _ := by
 refine Functor.hext (F := identityFiberFunctor A x y γ (variableSection (I).data)) (G := 𝟭 _) ?_ ?_
 · intro a
   exact congrArg LocallyDiscrete.as (variableSectionFiber_obj I γ ⟨a⟩)
 · intro a b f
   have h := variableSectionFiber_map I γ (show (⟨a⟩ : LocallyDiscrete _) ⟶ ⟨b⟩ from ⟨f⟩)
   exact discrete_as_heq (congrArg₂ (fun a b => a ⟶ b)
     (congrArg LocallyDiscrete.as (variableSectionFiber_obj I γ ⟨a⟩))
     (congrArg LocallyDiscrete.as (variableSectionFiber_obj I γ ⟨b⟩))) h
noncomputable def identityFiberBeta
 (s : TwoFamily.Section (reindex (projectionHigher (I).data) (I).data))
 (p : TwoFamily.Section (closedId (reindex (projectionHigher (I).data) (I).data) s (variableSection (I).data))) :
 identityFiberFunctor A x y γ s ⟶ 𝟭 _ :=
 identityFiberComparison A x y γ s (variableSection (I).data) p ≫
  eqToHom (identityFiberFunctor_variable A x y γ)
local instance : IsGroupoid ((openIdCat A.data).obj ((endpointPair A.data x y).lift.obj γ)) :=
 A.locallyGroupoid γ _ _
instance identityFiberBeta_app_isIso
 (s : TwoFamily.Section (reindex (projectionHigher (I).data) (I).data))
 (p : TwoFamily.Section (closedId (reindex (projectionHigher (I).data) (I).data) s (variableSection (I).data)))
 (a : (openIdCat A.data).obj ((endpointPair A.data x y).lift.obj γ)) :
 IsIso ((identityFiberBeta A x y γ s p).app a) := IsGroupoid.all_isIso _
theorem identityFiber_conjugation
 (s : TwoFamily.Section (reindex (projectionHigher (I).data) (I).data))
 (p : TwoFamily.Section (closedId (reindex (projectionHigher (I).data) (I).data) s (variableSection (I).data)))
 {a b : (x.normalObj A.data γ).fiber ⟶ (y.normalObj A.data γ).fiber} (h : a ⟶ b) :
 inv ((identityFiberBeta A x y γ s p).app a) ≫
  (identityFiberFunctor A x y γ s).map h ≫ (identityFiberBeta A x y γ s p).app b = h := by
 exact SquareKit.natural_conjugation (identityFiberBeta A x y γ s p) h
end SquareKit.Internal.PathTransport.HigherInterpretation
