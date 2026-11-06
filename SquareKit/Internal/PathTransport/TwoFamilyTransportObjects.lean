import SquareKit.Internal.PathTransport.TwoFamilyRetractionJ
import SquareKit.Internal.PathTransport.TwoFamilySectionNormalization
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
universe u v w u' v' w'
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Bicategory.Strict Γ]
variable {Δ : Type*} [Bicategory Δ] [Bicategory.Strict Δ]
variable (E : Family.{u,v,w,u',v',w'} Γ)
variable {σ τ : StrictPseudofunctor Δ Γ}
theorem Section.normalObj_fiber_heq (s : Section E) (x : Γ) :
    HEq (s.normalObj E x).fiber (s.lift.obj x).fiber :=
  total_obj_fiber_heq_family rfl (heq_of_eq (s.normalObj_eq E x))

theorem Section.cast_normalObj {F G : Family.{u,v,w,u',v',w'} Γ} (e : F = G)
    (s : Section F) (x : Γ) :
    HEq ((Section.cast e s).normalObj G x).fiber (s.normalObj F x).fiber := by
  cases e
  rfl

theorem Section.reindex_normalObj (s : Section E) (σ : StrictPseudofunctor Δ Γ) (x : Δ) :
    ((s.reindex E σ).normalObj (TwoFamily.reindex σ E) x).fiber =
      (s.normalObj E (σ.obj x)).fiber := by
  apply eq_of_heq
  exact ((s.reindex E σ).normalObj_fiber_heq _ x).trans
    ((s.reindex_obj_fiber E σ x).trans (s.normalObj_fiber_heq E (σ.obj x)).symm)

theorem Section.transport_normalObj
    (η : Pseudofunctor.StrongTrans σ.toPseudofunctor τ.toPseudofunctor)
    (s : Section (TwoFamily.reindex σ E)) (x : Δ) :
    ((s.transport E η).normalObj (TwoFamily.reindex τ E) x).fiber =
      (E.map (η.app x)).obj ((s.normalObj (TwoFamily.reindex σ E) x).fiber) := by
  conv_lhs => rw [← s.normalized_eq (TwoFamily.reindex σ E)]
  rfl

variable {A : Type*} [Bicategory A] [Bicategory.Strict A]
theorem retractionJ_normalObj (i : StrictPseudofunctor A Γ) (r : StrictPseudofunctor Γ A)
    (η : Pseudofunctor.StrongTrans (r.comp i).toPseudofunctor
      (StrictPseudofunctor.id Γ).toPseudofunctor)
    (d : Section (TwoFamily.reindex i E)) (x : Γ) :
    ((retractionJ i r η E d).normalObj E x).fiber =
      (E.map (η.app x)).obj ((d.normalObj (TwoFamily.reindex i E) (r.obj x)).fiber) := by
  apply eq_of_heq
  apply (Section.cast_normalObj (reindex_id E) _ x).trans
  rw [Section.transport_normalObj]
  have h := (Section.cast_normalObj (reindex_comp E i r)
    (d.reindex (TwoFamily.reindex i E) r) x).trans
    (heq_of_eq (d.reindex_normalObj (TwoFamily.reindex i E) r x))
  exact heq_of_eq (congrArg (fun z => (E.map (η.app x)).obj z) (eq_of_heq h))
end SquareKit.Internal.PathTransport.TwoFamily
