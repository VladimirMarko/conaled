import SquareKit.Internal.PathTransport.TwoFunctorData
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w'
variable {A : Type u} [Bicategory.{w,v} A] [Strict A]
variable {B : Type u'} [Bicategory.{w',v'} B] [Strict B]
variable (F : StrictPseudofunctor A B) (D : PrelaxFunctorStruct B A)
variable (hL : F.toPrelaxFunctorStruct.comp D = PrelaxFunctorStruct.id A)
variable (hR : D.comp F.toPrelaxFunctorStruct = PrelaxFunctorStruct.id B)

omit [Strict A] [Strict B] in
include hL in
theorem inverseData_map_injective {x y : A} : Function.Injective (F.map (X := x) (Y := y)) := by
  intro p q h
  have hd := congrArg (fun k : F.obj x ⟶ F.obj y => D.map k) h
  exact eq_of_heq ((congr_arg_heq (fun G => G.map p) hL).symm.trans
    ((heq_of_eq hd).trans (congr_arg_heq (fun G => G.map q) hL)))

omit [Strict A] [Strict B] in
include hL in
theorem inverseData_cell_injective {x y : A} {p q : x ⟶ y} :
    Function.Injective (F.map₂ (f := p) (g := q)) := by
  intro α β h
  have hd := congrArg (fun k : F.map p ⟶ F.map q => D.map₂ k) h
  exact eq_of_heq ((congr_arg_heq (fun G => G.map₂ α) hL).symm.trans
    ((heq_of_eq hd).trans (congr_arg_heq (fun G => G.map₂ β) hL)))

include hL hR in
theorem inverseData_map_id (x : B) : D.map (𝟙 x) = 𝟙 (D.obj x) := by
  apply inverseData_map_injective F D hL
  rw [F.map_id]
  exact eq_of_heq ((congr_arg_heq (fun G => G.map (𝟙 x)) hR).trans
    (congr_arg_heq (fun G => 𝟙 (G.obj x)) hR).symm)

include hL hR in
theorem inverseData_map_comp {x y z : B} (p : x ⟶ y) (q : y ⟶ z) :
    D.map (p ≫ q) = D.map p ≫ D.map q := by
  apply inverseData_map_injective F D hL
  rw [F.map_comp]
  exact eq_of_heq ((congr_arg_heq (fun G => G.map (p ≫ q)) hR).trans
    (congr_arg_heq (fun G => G.map p ≫ G.map q) hR).symm)

include hL hR in
theorem inverseData_cell_id {x y : B} (p : x ⟶ y) : D.map₂ (𝟙 p) = 𝟙 (D.map p) := by
  apply inverseData_cell_injective F D hL
  rw [F.map₂_id]
  exact eq_of_heq ((congr_arg_heq (fun G => G.map₂ (𝟙 p)) hR).trans
    (congr_arg_heq (fun G => 𝟙 (G.map p)) hR).symm)

include hL hR in
theorem inverseData_cell_comp {x y : B} {p q r : x ⟶ y} (α : p ⟶ q) (β : q ⟶ r) :
    D.map₂ (α ≫ β) = D.map₂ α ≫ D.map₂ β := by
  apply inverseData_cell_injective F D hL
  rw [F.map₂_comp]
  exact eq_of_heq ((congr_arg_heq (fun G => G.map₂ (α ≫ β)) hR).trans
    (congr_arg_heq (fun G => G.map₂ α ≫ G.map₂ β) hR).symm)

omit [Strict A] [Strict B] in
private theorem mapped_left_cast_heq {x y z : A} (p : x ⟶ y) {q r : y ⟶ z}
    (α : q ⟶ r) {s t : x ⟶ z} (hs : s = p ≫ q) (ht : t = p ≫ r) :
    HEq (F.map₂ (eqToHom hs ≫ p ◁ α ≫ eqToHom ht.symm))
      (F.map p ◁ F.map₂ α) := by
  rw [F.map₂_comp, F.map₂_comp, F.map₂_eqToHom, F.map₂_eqToHom,
    F.map₂_whisker_left]
  simp only [F.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

omit [Strict A] [Strict B] in
private theorem mapped_right_cast_heq {x y z : A} {p q : x ⟶ y} (α : p ⟶ q)
    (r : y ⟶ z) {s t : x ⟶ z} (hs : s = p ≫ r) (ht : t = q ≫ r) :
    HEq (F.map₂ (eqToHom hs ≫ α ▷ r ≫ eqToHom ht.symm))
      (F.map₂ α ▷ F.map r) := by
  rw [F.map₂_comp, F.map₂_comp, F.map₂_eqToHom, F.map₂_eqToHom,
    F.map₂_whisker_right]
  simp only [F.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

def strictFunctorOfInverseData : StrictPseudofunctor B A :=
  StrictPseudofunctor.mk'' {
    toPrelaxFunctorStruct := D
    map_id := inverseData_map_id F D hL hR
    map_comp := inverseData_map_comp F D hL hR
    map₂_id := inverseData_cell_id F D hL hR
    map₂_comp := inverseData_cell_comp F D hL hR
    map₂_whisker_left := by
      intro x y z p q r α
      apply inverseData_cell_injective F D hL
      apply eq_of_heq
      apply HEq.trans (congr_arg_heq (fun G => G.map₂ (p ◁ α)) hR)
      symm
      apply HEq.trans (mapped_left_cast_heq F (D.map p) (D.map₂ α)
        (inverseData_map_comp F D hL hR p q) (inverseData_map_comp F D hL hR p r))
      exact congr_arg_heq (fun G => G.map p ◁ G.map₂ α) hR
    map₂_whisker_right := by
      intro x y z p q α r
      apply inverseData_cell_injective F D hL
      apply eq_of_heq
      apply HEq.trans (congr_arg_heq (fun G => G.map₂ (α ▷ r)) hR)
      symm
      apply HEq.trans (mapped_right_cast_heq F (D.map₂ α) (D.map r)
        (inverseData_map_comp F D hL hR p r) (inverseData_map_comp F D hL hR q r))
      exact congr_arg_heq (fun G => G.map₂ α ▷ G.map r) hR
  }
theorem strictFunctorOfInverseData_left_inverse :
    F.comp (strictFunctorOfInverseData F D hL hR) = StrictPseudofunctor.id A :=
  strictFunctorData_ext hL

theorem strictFunctorOfInverseData_right_inverse :
    (strictFunctorOfInverseData F D hL hR).comp F = StrictPseudofunctor.id B :=
  strictFunctorData_ext hR
end SquareKit.Internal.PathTransport
