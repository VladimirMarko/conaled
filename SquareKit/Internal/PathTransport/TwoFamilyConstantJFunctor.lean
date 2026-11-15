import SquareKit.Internal.PathTransport.TwoFamilyOrdinarySections
import SquareKit.Internal.PathTransport.TwoFamilyConstantJ
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {Γ Δ : Type u} [Bicategory.{u,u} Γ] [Strict Γ] [Bicategory.{u,u} Δ] [Strict Δ]
theorem constantFamily_reindex (C : StrictTwoCategory.{u,u,u}) (σ : StrictPseudofunctor Δ Γ) :
 reindex σ (constantFamily Γ C) = constantFamily Δ C := by
 apply strictFunctorData_ext
 apply prelaxData_ext
 · intro x; rfl
 · intro x y f; rfl
 · intro x y f g α; rfl
private theorem discrete_as_heq {X Y : Type u} {a : Discrete X} {b : Discrete Y}
 (e : X = Y) (h : HEq a b) : HEq a.as b.as := by
 cases e
 cases eq_of_heq h
 rfl
variable (C : Type u) [Groupoid.{u} C]
variable (i : StrictPseudofunctor Δ Γ) (r : StrictPseudofunctor Γ Δ)
variable (η : Pseudofunctor.StrongTrans (r.comp i).toPseudofunctor (StrictPseudofunctor.id Γ).toPseudofunctor)
variable (d : TwoFamily.Section (reindex i (constantFamily Γ (discreteCategory C))))
set_option maxHeartbeats 1000000 in
theorem constantSectionFunctor_retractionJ :
 constantSectionFunctor Γ C (retractionJ i r η (constantFamily Γ (discreteCategory C)) d) =
 r.toFunctor ⋙ constantSectionFunctor Δ C (Section.cast (constantFamily_reindex (discreteCategory C) i) d) := by
 have ho : ∀ x, (constantSectionFunctor Γ C (retractionJ i r η (constantFamily Γ (discreteCategory C)) d)).obj x =
   (constantSectionFunctor Δ C (Section.cast (constantFamily_reindex (discreteCategory C) i) d)).obj (r.obj x) := by
  intro x
  exact congrArg LocallyDiscrete.as (eq_of_heq
   ((retractionJ_constant_obj (discreteCategory C) i r η d x).trans
    (Section.cast_obj_fiber (constantFamily_reindex (discreteCategory C) i) d (r.obj x)).symm))
 refine Functor.hext ho ?_
 intro x y f
 have h := (retractionJ_constant_map (discreteCategory C) i r η d f).trans
  (Section.cast_map_fiber (constantFamily_reindex (discreteCategory C) i) d (r.map f)).symm
 exact discrete_as_heq (congrArg₂ (fun a b : C => a ⟶ b) (ho x) (ho y)) h
end SquareKit.Internal.PathTransport.HigherInterpretation
