import SquareKit.Internal.PathTransport.TwoFunctorJointReflection
import SquareKit.Internal.PathTransport.TwoFamilySectionNormalization
import SquareKit.Internal.PathTransport.TwoFamilyPathContext

/-! Pair dependent sections through jointly faithful endpoint projections.
Their object, arrow, and genuine cell observations determine the pair. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)

def endpointProjectionOriginal (side : Bool) : StrictPseudofunctor (Total (endpointFamily F)) (Total F) :=
  StrongMap.toHigher (if side then (firstEndpoint F).toStrong else (secondEndpoint F).toStrong)

def endpointProjectionData (side : Bool) : PrelaxFunctorStruct (Total (endpointFamily F)) (Total F) :=
  match side with
  | true => {
      obj := fun x => ⟨x.base,x.fiber.1⟩
      map := fun p => ⟨p.base,p.fiber.1⟩
      map₂ := fun α => ⟨α.base,α.fiber.1⟩ }
  | false => {
      obj := fun x => ⟨x.base,x.fiber.2⟩
      map := fun p => ⟨p.base,p.fiber.2⟩
      map₂ := fun α => ⟨α.base,α.fiber.2⟩ }

theorem endpointProjectionData_eq (side : Bool) :
    endpointProjectionData F side = (endpointProjectionOriginal F side).toPrelaxFunctorStruct := by
  cases side
  all_goals
    apply prelaxData_ext
    · intro x; rfl
    · intro x y p
      apply total_hom_hext F rfl rfl
      · rfl
      · apply HEq.symm
        simp [endpointProjectionData, endpointProjectionOriginal,
 StrongMap.toHigher, StrongMap.map,
          StrictTwoTransformation.Trans.toStrong, firstEndpoint, secondEndpoint]
        all_goals exact Category.id_comp _
    · intro x y p q α
      apply total_cell_hext F rfl rfl
      · apply total_hom_hext F rfl rfl
        · rfl
        · apply HEq.symm
          simp [endpointProjectionData, endpointProjectionOriginal,
 StrongMap.toHigher, StrongMap.map,
            StrictTwoTransformation.Trans.toStrong, firstEndpoint, secondEndpoint]
          all_goals exact Category.id_comp _
      · apply total_hom_hext F rfl rfl
        · rfl
        · apply HEq.symm
          simp [endpointProjectionData, endpointProjectionOriginal,
 StrongMap.toHigher, StrongMap.map,
            StrictTwoTransformation.Trans.toStrong, firstEndpoint, secondEndpoint]
          all_goals exact Category.id_comp _
      · rfl
      · apply HEq.symm
        simp [endpointProjectionData, endpointProjectionOriginal,
 StrongMap.toHigher, StrongMap.map₂,
          StrictTwoTransformation.Trans.toStrong, firstEndpoint, secondEndpoint]
        all_goals
          rw [StrongMap.classifier_eqToHom_app]
          exact eqToHom_left_heq _ _

def endpointProjection (side : Bool) : StrictPseudofunctor (Total (endpointFamily F)) (Total F) :=
  strictFunctorOfEqualData (endpointProjectionOriginal F side) (endpointProjectionData F side)
    (endpointProjectionData_eq F side)
end SquareKit.Internal.PathTransport.TwoFamily
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ) (s t : Section F)
def endpointPairData : PrelaxFunctorStruct Γ (Total (endpointFamily F)) where
  obj x := ⟨x, ((s.normalObj F x).fiber, (t.normalObj F x).fiber)⟩
  map p := ⟨p, ((s.normalMap F p).fiber, (t.normalMap F p).fiber)⟩
  map₂ α := ⟨α, ((s.normalCell F α).fiber, (t.normalCell F α).fiber)⟩
end SquareKit.Internal.PathTransport.TwoFamily
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe up vp
private theorem prod_hext {A C : Type up} {B D : Type vp} (p : A × B) (q : C × D)
    (h1 : HEq p.1 q.1) (h2 : HEq p.2 q.2) : HEq p q := by
  cases type_eq_of_heq h1
  cases type_eq_of_heq h2
  exact heq_of_eq (Prod.ext (eq_of_heq h1) (eq_of_heq h2))
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
theorem endpoint_hom_ext {x y : Total (endpointFamily F)} (p q : x ⟶ y)
    (h1 : (endpointProjection F true).map p = (endpointProjection F true).map q)
    (h2 : (endpointProjection F false).map p = (endpointProjection F false).map q) : p = q := by
  apply eq_of_heq
  apply total_hom_hext (endpointFamily F) rfl rfl
  · exact congr_arg_heq (fun f => f.base) h1
  · exact prod_hext _ _ (congr_arg_heq (fun f => f.fiber) h1)
      (congr_arg_heq (fun f => f.fiber) h2)
theorem endpoint_cell_ext {x y : Total (endpointFamily F)} {p q : x ⟶ y} (α β : p ⟶ q)
    (h1 : (endpointProjection F true).map₂ α = (endpointProjection F true).map₂ β)
    (h2 : (endpointProjection F false).map₂ α = (endpointProjection F false).map₂ β) : α = β := by
  apply eq_of_heq
  apply total_cell_hext (endpointFamily F) rfl rfl HEq.rfl HEq.rfl
  · exact congr_arg_heq (fun a => a.base) h1
  · exact prod_hext _ _ (congr_arg_heq (fun a => a.fiber) h1)
      (congr_arg_heq (fun a => a.fiber) h2)

variable (s t : Section F)
def endpointPair : Section (endpointFamily F) where
  lift := strictFunctorOfJointReflection (endpointPairData F s t)
    (endpointProjection F true) (endpointProjection F false)
    (s.normalized F).lift (t.normalized F).lift rfl rfl
    (endpoint_hom_ext F) (endpoint_cell_ext F)
  over := StrictTwoTransformation.functor_ext rfl

theorem endpointPair_first : (endpointPair F s t).lift.comp (endpointProjection F true) = s.lift := by
  have h : (endpointPair F s t).lift.comp (endpointProjection F true) =
      (s.normalized F).lift := strictFunctorData_ext rfl
  exact h.trans (congrArg Section.lift (s.normalized_eq F))

theorem endpointPair_second : (endpointPair F s t).lift.comp (endpointProjection F false) = t.lift := by
  have h : (endpointPair F s t).lift.comp (endpointProjection F false) =
      (t.normalized F).lift := strictFunctorData_ext rfl
  exact h.trans (congrArg Section.lift (t.normalized_eq F))
end SquareKit.Internal.PathTransport.TwoFamily

namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
theorem endpoint_obj_ext (x y : Total (endpointFamily F))
    (h1 : (endpointProjection F true).obj x = (endpointProjection F true).obj y)
    (h2 : (endpointProjection F false).obj x = (endpointProjection F false).obj y) : x = y := by
  apply total_obj_hext (endpointFamily F)
  · exact congrArg (fun a => a.base) h1
  · have h : x.base = y.base := congrArg (fun a => a.base) h1
    cases x with | mk xb xf =>
      cases y with | mk yb yf =>
        dsimp at h
        subst yb
        apply heq_of_eq
        apply Prod.ext
        · exact eq_of_heq (congr_arg_heq (fun a => a.fiber) h1)
        · exact eq_of_heq (congr_arg_heq (fun a => a.fiber) h2)
theorem endpoint_functor_ext {Δ : Type*} [Bicategory Δ] [Strict Δ]
    (H K : StrictPseudofunctor Δ (Total (endpointFamily F)))
    (h1 : H.comp (endpointProjection F true) = K.comp (endpointProjection F true))
    (h2 : H.comp (endpointProjection F false) = K.comp (endpointProjection F false)) : H = K :=
  strictFunctorJointExt _ _ (endpoint_obj_ext F) (endpoint_hom_ext F) (endpoint_cell_ext F) H K h1 h2

theorem diagonal_endpoint (side : Bool) :
    (diagonalTotal F).comp (endpointProjection F side) = StrictPseudofunctor.id (Total F) := by
  cases side
  all_goals
    apply strictFunctorData_ext
    apply prelaxData_ext
    · intro x; rfl
    · intro x y p
      apply total_hom_hext F rfl rfl
      · rfl
      · first | exact heq_of_eq (diagonal_fiber_fst F p) | exact heq_of_eq (diagonal_fiber_snd F p)
    · intro x y p q α
      apply total_cell_hext F rfl rfl
      · apply total_hom_hext F rfl rfl
        · rfl
        · first | exact heq_of_eq (diagonal_fiber_fst F p) | exact heq_of_eq (diagonal_fiber_snd F p)
      · apply total_hom_hext F rfl rfl
        · rfl
        · first | exact heq_of_eq (diagonal_fiber_fst F q) | exact heq_of_eq (diagonal_fiber_snd F q)
      · rfl
      · first | exact diagonal_cell_fst_heq F α | exact diagonal_cell_snd_heq F α

theorem endpointPair_diagonal (s : Section F) :
    (endpointPair F s s).lift = s.lift.comp (diagonalTotal F) := by
  apply endpoint_functor_ext F
  · rw [endpointPair_first]
    symm
    calc
      (s.lift.comp (diagonalTotal F)).comp (endpointProjection F true) =
          s.lift.comp ((diagonalTotal F).comp (endpointProjection F true)) :=
        StrictTwoTransformation.functor_ext rfl
      _ = s.lift := by rw [diagonal_endpoint]; exact StrictTwoTransformation.functor_comp_id _
  · rw [endpointPair_second]
    symm
    calc
      (s.lift.comp (diagonalTotal F)).comp (endpointProjection F false) =
          s.lift.comp ((diagonalTotal F).comp (endpointProjection F false)) :=
        StrictTwoTransformation.functor_ext rfl
      _ = s.lift := by rw [diagonal_endpoint]; exact StrictTwoTransformation.functor_comp_id _
end SquareKit.Internal.PathTransport.TwoFamily
