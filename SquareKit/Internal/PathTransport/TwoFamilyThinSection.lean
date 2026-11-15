import SquareKit.Internal.PathTransport.TwoFamilyComprehension
/-! Section extensionality when fiber 2-cells are unique. Fiber arrows remain observable. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w uΓ vΓ wΓ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable (F : Family.{uΓ,vΓ,wΓ,u,v,w} Γ)
variable [∀ γ (a b : F.obj γ) (p q : a ⟶ b), Subsingleton (p ⟶ q)]
private theorem cell_hext_thin {x x' y y' : Total F} (hx : x = x') (hy : y = y')
    {p q : x ⟶ y} {p' q' : x' ⟶ y'} (hp : HEq p p') (hq : HEq q q')
    (α : p ⟶ q) (β : p' ⟶ q') (hb : HEq α.base β.base) : HEq α β := by
  subst x'
  subst y'
  cases eq_of_heq hp
  cases eq_of_heq hq
  apply heq_of_eq
  apply Pseudofunctor.CoGrothendieck.Hom.ext _ _ (eq_of_heq hb)
  exact Subsingleton.elim _ _

theorem Section.ext_thin_fibers (s t : Section F)
    (ho : ∀ x, HEq (s.lift.obj x).fiber (t.lift.obj x).fiber)
    (hm : ∀ {x y} (p : x ⟶ y), HEq (s.lift.map p).fiber (t.lift.map p).fiber) : s = t := by
  have hobj (x : Γ) : s.lift.obj x = t.lift.obj x := by
    apply total_obj_hext F _ (ho x)
    exact (congrArg (fun H => H.obj x) s.over).trans (congrArg (fun H => H.obj x) t.over).symm
  have hmap {x y : Γ} (p : x ⟶ y) : HEq (s.lift.map p) (t.lift.map p) := by
    apply total_hom_hext F (hobj x) (hobj y) _ _ _ (hm p)
    exact (congr_arg_heq (fun H => H.map p) s.over).trans
      (congr_arg_heq (fun H => H.map p) t.over).symm
  have hcell {x y : Γ} {p q : x ⟶ y} (α : p ⟶ q) : HEq (s.lift.map₂ α) (t.lift.map₂ α) := by
    apply cell_hext_thin F (hobj x) (hobj y) (hmap p) (hmap q)
    exact (congr_arg_heq (fun H => H.map₂ α) s.over).trans
      (congr_arg_heq (fun H => H.map₂ α) t.over).symm
  have hl : s.lift = t.lift := strictFunctorData_ext
    (prelaxData_ext _ _ hobj (fun p => hmap p) (fun α => hcell α))
  cases s
  cases t
  cases hl
  rfl

theorem Section.hext_thin_fibers {G : Family.{uΓ,vΓ,wΓ,u,v,w} Γ} (e : F = G)
    (s : Section F) (t : Section G)
    (ho : ∀ x, HEq (s.lift.obj x).fiber (t.lift.obj x).fiber)
    (hm : ∀ {x y} (p : x ⟶ y), HEq (s.lift.map p).fiber (t.lift.map p).fiber) : HEq s t := by
  cases e
  exact heq_of_eq (Section.ext_thin_fibers F s t ho (fun p => hm p))
end SquareKit.Internal.PathTransport.TwoFamily
