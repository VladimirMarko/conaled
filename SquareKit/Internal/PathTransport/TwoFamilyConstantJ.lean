import SquareKit.Internal.PathTransport.TwoFamilyConstantProjection
import SquareKit.Internal.PathTransport.TwoFamilyRetractionJ
/-! Transport in a constant higher family retains the branch fiber action.
Retraction J therefore acts on objects and arrows by precomposition with its retraction. -/
namespace SquareKit.Internal.PathTransport.HigherInterpretation
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {Γ Δ : Type u} [Bicategory.{u,u} Γ] [Strict Γ] [Bicategory.{u,u} Δ] [Strict Δ]
variable (C : StrictTwoCategory.{u,u,u}) {σ τ : StrictPseudofunctor Δ Γ}
variable (η : Pseudofunctor.StrongTrans σ.toPseudofunctor τ.toPseudofunctor)
variable (s : TwoFamily.Section (TwoFamily.reindex σ (constantFamily Γ C)))
theorem transport_constant_obj (x : Δ) :
 ((s.transport (constantFamily Γ C) η).lift.obj x).fiber = (s.lift.obj x).fiber := rfl
set_option maxHeartbeats 200000 in
theorem transport_constant_map {x y : Δ} (f : x ⟶ y) :
 ((s.transport (constantFamily Γ C) η).lift.map f).fiber = (s.lift.map f).fiber := by
 change ((strongPostcomp η (constantFamily Γ C)).naturality (s.lift.map f).base).inv.app
   (s.lift.obj x).fiber ≫ (s.lift.map f).fiber = _
 simp only [strongPostcomp, Iso.trans_inv, Iso.symm_inv,
  StrictPseudofunctor.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv]
 simp [constantFamily]
 change (𝟙 _ ≫ (s.lift.map f).fiber) = _
 exact Category.id_comp _
variable (i : StrictPseudofunctor Δ Γ) (r : StrictPseudofunctor Γ Δ)
variable (ε : Pseudofunctor.StrongTrans (r.comp i).toPseudofunctor (StrictPseudofunctor.id Γ).toPseudofunctor)
variable (d : TwoFamily.Section (TwoFamily.reindex i (constantFamily Γ C)))
theorem retractionJ_constant_obj (x : Γ) :
 HEq (((TwoFamily.retractionJ i r ε (constantFamily Γ C) d).lift.obj x).fiber)
  ((d.lift.obj (r.obj x)).fiber) := by
 let E := constantFamily Γ C
 let pulled := TwoFamily.Section.cast (TwoFamily.reindex_comp E i r) (d.reindex _ r)
 exact (TwoFamily.Section.cast_obj_fiber (TwoFamily.reindex_id E) (pulled.transport E ε) x).trans
  ((heq_of_eq (transport_constant_obj C ε pulled x)).trans
   ((TwoFamily.Section.cast_obj_fiber (TwoFamily.reindex_comp E i r) (d.reindex _ r) x).trans
    (d.reindex_obj_fiber _ r x)))
set_option maxHeartbeats 1000000 in
theorem retractionJ_constant_map {x y : Γ} (f : x ⟶ y) :
 HEq (((TwoFamily.retractionJ i r ε (constantFamily Γ C) d).lift.map f).fiber)
  ((d.lift.map (r.map f)).fiber) := by
 let E := constantFamily Γ C
 let pulled := TwoFamily.Section.cast (TwoFamily.reindex_comp E i r) (d.reindex _ r)
 exact (TwoFamily.Section.cast_map_fiber (TwoFamily.reindex_id E) (pulled.transport E ε) f).trans
  ((heq_of_eq (transport_constant_map C ε pulled f)).trans
   ((TwoFamily.Section.cast_map_fiber (TwoFamily.reindex_comp E i r) (d.reindex _ r) f).trans
    (d.reindex_map_fiber _ r f)))
end SquareKit.Internal.PathTransport.HigherInterpretation
