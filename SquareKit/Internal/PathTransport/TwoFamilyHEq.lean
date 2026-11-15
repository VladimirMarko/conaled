import SquareKit.Internal.PathTransport.TwoFamilyData
import SquareKit.Internal.PathTransport.TwoFunctorData

/-! Extensionality across a proved equality of higher families. All base and fiber
observations are retained, including genuine cells and their dependent boundaries. -/
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w uΓ vΓ wΓ uΔ vΔ wΔ
variable {Γ : Type uΓ} [Bicategory.{wΓ,vΓ} Γ] [Strict Γ]
variable {Δ : Type uΔ} [Bicategory.{wΔ,vΔ} Δ] [Strict Δ]
variable {F G : Family.{uΓ,vΓ,wΓ,u,v,w} Γ}

theorem total_obj_hext_family (e : F = G) {x : Total F} {y : Total G}
    (hb : x.base = y.base) (hf : HEq x.fiber y.fiber) : HEq x y := by
  cases e
  exact heq_of_eq (total_obj_hext F hb hf)

omit [Strict Γ] in
theorem total_obj_base_heq_family (e : F = G) {x : Total F} {y : Total G}
    (h : HEq x y) : x.base = y.base := by
  cases e
  cases eq_of_heq h
  rfl

omit [Strict Γ] in
theorem total_obj_fiber_heq_family (e : F = G) {x : Total F} {y : Total G}
    (h : HEq x y) : HEq x.fiber y.fiber := by
  cases e
  cases eq_of_heq h
  rfl

theorem total_hom_hext_family (e : F = G) {x y : Total F} {x' y' : Total G}
    (hx : HEq x x') (hy : HEq y y') {p : x ⟶ y} {q : x' ⟶ y'}
    (hb : HEq p.base q.base) (hf : HEq p.fiber q.fiber) : HEq p q := by
  cases e
  exact total_hom_hext F (eq_of_heq hx) (eq_of_heq hy) p q hb hf

theorem total_hom_base_heq_family (e : F = G) {x y : Total F} {x' y' : Total G}
    (hx : HEq x x') (hy : HEq y y') {p : x ⟶ y} {q : x' ⟶ y'}
    (h : HEq p q) : HEq p.base q.base := by
  cases e
  cases eq_of_heq hx
  cases eq_of_heq hy
  cases eq_of_heq h
  rfl

theorem total_hom_fiber_heq_family (e : F = G) {x y : Total F} {x' y' : Total G}
    (hx : HEq x x') (hy : HEq y y') {p : x ⟶ y} {q : x' ⟶ y'}
    (h : HEq p q) : HEq p.fiber q.fiber := by
  cases e
  cases eq_of_heq hx
  cases eq_of_heq hy
  cases eq_of_heq h
  rfl

theorem total_cell_hext_family (e : F = G) {x y : Total F} {x' y' : Total G}
    (hx : HEq x x') (hy : HEq y y') {p q : x ⟶ y} {p' q' : x' ⟶ y'}
    (hp : HEq p p') (hq : HEq q q') {α : p ⟶ q} {β : p' ⟶ q'}
    (hb : HEq α.base β.base) (hf : HEq α.fiber β.fiber) : HEq α β := by
  cases e
  exact total_cell_hext F (eq_of_heq hx) (eq_of_heq hy) hp hq α β hb hf

theorem total_cell_base_heq_family (e : F = G) {x y : Total F} {x' y' : Total G}
    (hx : HEq x x') (hy : HEq y y') {p q : x ⟶ y} {p' q' : x' ⟶ y'}
    (hp : HEq p p') (hq : HEq q q') {α : p ⟶ q} {β : p' ⟶ q'}
    (h : HEq α β) : HEq α.base β.base := by
  cases e
  cases eq_of_heq hx
  cases eq_of_heq hy
  cases eq_of_heq hp
  cases eq_of_heq hq
  cases eq_of_heq h
  rfl

theorem total_cell_fiber_heq_family (e : F = G) {x y : Total F} {x' y' : Total G}
    (hx : HEq x x') (hy : HEq y y') {p q : x ⟶ y} {p' q' : x' ⟶ y'}
    (hp : HEq p p') (hq : HEq q q') {α : p ⟶ q} {β : p' ⟶ q'}
    (h : HEq α β) : HEq α.fiber β.fiber := by
  cases e
  cases eq_of_heq hx
  cases eq_of_heq hy
  cases eq_of_heq hp
  cases eq_of_heq hq
  cases eq_of_heq h
  rfl

omit [Strict Γ] in
theorem family_obj_action_heq (e : F = G) {x x' y y' : Γ}
    (hx : x = x') (hy : y = y') {f : x ⟶ y} {g : x' ⟶ y'}
    (hf : HEq f g) {a : F.obj x} {b : G.obj x'} (ha : HEq a b) :
    HEq ((F.map f).obj a) ((G.map g).obj b) := by
  cases e
  cases hx
  cases hy
  cases eq_of_heq hf
  cases eq_of_heq ha
  rfl

omit [Strict Γ] in
theorem family_arrow_action_heq (e : F = G) {x x' y y' : Γ}
    (hx : x = x') (hy : y = y') {f : x ⟶ y} {g : x' ⟶ y'}
    (hf : HEq f g) {a b : F.obj x} {a' b' : G.obj x'}
    (ha : HEq a a') (hb : HEq b b') {p : a ⟶ b} {q : a' ⟶ b'}
    (hp : HEq p q) : HEq ((F.map f).map p) ((G.map g).map q) := by
  cases e
  cases hx
  cases hy
  cases eq_of_heq hf
  cases eq_of_heq ha
  cases eq_of_heq hb
  cases eq_of_heq hp
  rfl

omit [Strict Γ] in
theorem family_cell_action_heq (e : F = G) {x x' y y' : Γ}
    (hx : x = x') (hy : y = y') {f : x ⟶ y} {g : x' ⟶ y'}
    (hf : HEq f g) {a b : F.obj x} {a' b' : G.obj x'}
    (ha : HEq a a') (hb : HEq b b') {p q : a ⟶ b} {p' q' : a' ⟶ b'}
    (hp : HEq p p') (hq : HEq q q') {α : p ⟶ q} {β : p' ⟶ q'}
    (hα : HEq α β) : HEq ((F.map f).map₂ α) ((G.map g).map₂ β) := by
  cases e
  cases hx
  cases hy
  cases eq_of_heq hf
  cases eq_of_heq ha
  cases eq_of_heq hb
  cases eq_of_heq hp
  cases eq_of_heq hq
  cases eq_of_heq hα
  rfl

theorem total_cell_boundary_heq_family (e : F = G) {x y : Total F} {x' y' : Total G}
    (hx : HEq x x') (hy : HEq y y') {p q : x ⟶ y} {p' q' : x' ⟶ y'}
    (hp : HEq p p') (hq : HEq q q') {α : p ⟶ q} {β : p' ⟶ q'}
    (h : HEq α β) : HEq ((F.map₂ α.base).app x.fiber ≫ q.fiber)
      ((G.map₂ β.base).app x'.fiber ≫ q'.fiber) := by
  cases e
  cases eq_of_heq hx
  cases eq_of_heq hy
  cases eq_of_heq hp
  cases eq_of_heq hq
  cases eq_of_heq h
  rfl

theorem total_functor_hext_family {F' G' : Family.{uΔ,vΔ,wΔ,u,v,w} Δ}
    (e : F = G) (e' : F' = G')
    (H : StrictPseudofunctor (Total F) (Total F'))
    (K : StrictPseudofunctor (Total G) (Total G'))
    (ho : ∀ x x', HEq x x' → HEq (H.obj x) (K.obj x'))
    (hm : ∀ {x y x' y'} (_hx : HEq x x') (_hy : HEq y y')
      (p : x ⟶ y) (q : x' ⟶ y'), HEq p q → HEq (H.map p) (K.map q))
    (hc : ∀ {x y x' y'} (_hx : HEq x x') (_hy : HEq y y')
      {p q : x ⟶ y} {p' q' : x' ⟶ y'} (_hp : HEq p p') (_hq : HEq q q')
      (α : p ⟶ q) (β : p' ⟶ q'), HEq α β → HEq (H.map₂ α) (K.map₂ β)) : HEq H K := by
  cases e
  cases e'
  apply heq_of_eq
  apply strictFunctorData_ext
  apply prelaxData_ext
  · intro x; exact eq_of_heq (ho x x HEq.rfl)
  · intro x y p; exact hm HEq.rfl HEq.rfl p p HEq.rfl
  · intro x y p q α; exact hc HEq.rfl HEq.rfl HEq.rfl HEq.rfl α α HEq.rfl
theorem total_trans_hext_family {F' G' : Family.{uΔ,vΔ,wΔ,u,v,w} Δ}
    (e : F = G) (e' : F' = G')
    {H K : StrictPseudofunctor (Total F) (Total F')}
    {H' K' : StrictPseudofunctor (Total G) (Total G')}
    (hH : HEq H H') (hK : HEq K K')
    (η : StrictTwoTransformation.Trans H K) (θ : StrictTwoTransformation.Trans H' K')
    (ha : ∀ x x', HEq x x' → HEq (η.app x) (θ.app x')) : HEq η θ := by
  cases e
  cases e'
  cases eq_of_heq hH
  cases eq_of_heq hK
  apply heq_of_eq
  apply StrictTwoTransformation.Trans.ext
  intro x
  exact eq_of_heq (ha x x HEq.rfl)

end SquareKit.Internal.PathTransport.TwoFamily
