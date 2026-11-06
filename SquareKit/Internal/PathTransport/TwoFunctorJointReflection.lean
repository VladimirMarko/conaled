import SquareKit.Internal.PathTransport.TwoFunctorData
/-! Strict higher functor laws reflected jointly by two observation functors.
The supplied equations concern raw operations; coherence is derived from the
observed functors and joint injectivity, including both whiskering laws. -/
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 200000
variable {A B C E : Type*} [Bicategory A] [Bicategory B] [Bicategory C] [Bicategory E]
variable [Strict A] [Strict B] [Strict C] [Strict E]
omit [Strict B] [Strict C] in
private theorem map₂_transport_heq (P : StrictPseudofunctor B C)
    {x y : B} {p p' q q' : x ⟶ y} (hp : p = p') (hq : q = q') (α : p' ⟶ q') :
    HEq (P.map₂ (eqToHom hp ≫ α ≫ eqToHom hq.symm)) (P.map₂ α) := by
  cases hp
  cases hq
  simp
omit [Strict B] [Strict C] in
private theorem map₂_left_heq (P : StrictPseudofunctor B C)
    {x y z : B} (p : x ⟶ y) {q r : y ⟶ z} (α : q ⟶ r) :
    HEq (P.map₂ (p ◁ α)) (P.map p ◁ P.map₂ α) := by
  rw [P.map₂_whisker_left]
  simp only [P.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl
omit [Strict B] [Strict C] in
private theorem map₂_right_heq (P : StrictPseudofunctor B C)
    {x y z : B} {p q : x ⟶ y} (α : p ⟶ q) (r : y ⟶ z) :
    HEq (P.map₂ (α ▷ r)) (P.map₂ α ▷ P.map r) := by
  rw [P.map₂_whisker_right]
  simp only [P.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  rfl

def strictFunctorOfJointReflection (D : PrelaxFunctorStruct A B)
    (P : StrictPseudofunctor B C) (Q : StrictPseudofunctor B E)
    (S : StrictPseudofunctor A C) (T : StrictPseudofunctor A E)
    (hS : D.comp P.toPrelaxFunctorStruct = S.toPrelaxFunctorStruct)
    (hT : D.comp Q.toPrelaxFunctorStruct = T.toPrelaxFunctorStruct)
    (rh : ∀ {x y : B} (p q : x ⟶ y), P.map p = P.map q → Q.map p = Q.map q → p = q)
    (rc : ∀ {x y : B} {p q : x ⟶ y} (α β : p ⟶ q),
      P.map₂ α = P.map₂ β → Q.map₂ α = Q.map₂ β → α = β) :
    StrictPseudofunctor A B := by
  let K := strictFunctorOfEqualData S (D.comp P.toPrelaxFunctorStruct) hS
  let L := strictFunctorOfEqualData T (D.comp Q.toPrelaxFunctorStruct) hT
  have hi : ∀ x, D.map (𝟙 x) = 𝟙 (D.obj x) := by
    intro x
    exact rh _ _ ((K.map_id x).trans (P.map_id _).symm)
      ((L.map_id x).trans (Q.map_id _).symm)
  have hm : ∀ {x y z} (p : x ⟶ y) (q : y ⟶ z), D.map (p ≫ q) = D.map p ≫ D.map q := by
    intro x y z p q
    exact rh _ _ ((K.map_comp p q).trans (P.map_comp _ _).symm)
      ((L.map_comp p q).trans (Q.map_comp _ _).symm)
  refine StrictPseudofunctor.mk'' {
    toPrelaxFunctorStruct := D
    map_id := hi
    map_comp := hm
    map₂_id := ?_
    map₂_comp := ?_
    map₂_whisker_left := ?_
    map₂_whisker_right := ?_ }
  · intro x y p
    exact rc _ _ ((K.map₂_id p).trans (P.map₂_id _).symm)
      ((L.map₂_id p).trans (Q.map₂_id _).symm)
  · intro x y p q r α β
    exact rc _ _ ((K.map₂_comp α β).trans (P.map₂_comp _ _).symm)
      ((L.map₂_comp α β).trans (Q.map₂_comp _ _).symm)
  · intro x y z p q r α
    apply rc
    · apply eq_of_heq
      exact (map₂_left_heq K p α).trans
        ((map₂_transport_heq P (hm p q) (hm p r) _).trans (map₂_left_heq P (D.map p) (D.map₂ α))).symm
    · apply eq_of_heq
      exact (map₂_left_heq L p α).trans
        ((map₂_transport_heq Q (hm p q) (hm p r) _).trans (map₂_left_heq Q (D.map p) (D.map₂ α))).symm
  · intro x y z p q α r
    apply rc
    · apply eq_of_heq
      exact (map₂_right_heq K α r).trans
        ((map₂_transport_heq P (hm p r) (hm q r) _).trans (map₂_right_heq P (D.map₂ α) (D.map r))).symm
    · apply eq_of_heq
      exact (map₂_right_heq L α r).trans
        ((map₂_transport_heq Q (hm p r) (hm q r) _).trans (map₂_right_heq Q (D.map₂ α) (D.map r))).symm

omit [Strict B] [Strict C] [Strict E] in
private theorem reflect_hom_heq
    (P : StrictPseudofunctor B C) (Q : StrictPseudofunctor B E)
    (rh : ∀ {x y : B} (p q : x ⟶ y), P.map p = P.map q → Q.map p = Q.map q → p = q)
    {x x' y y' : B} (hx : x = x') (hy : y = y') (p : x ⟶ y) (q : x' ⟶ y')
    (hP : HEq (P.map p) (P.map q)) (hQ : HEq (Q.map p) (Q.map q)) : HEq p q := by
  cases hx
  cases hy
  exact heq_of_eq (rh p q (eq_of_heq hP) (eq_of_heq hQ))
omit [Strict B] [Strict C] [Strict E] in
private theorem reflect_cell_heq
    (P : StrictPseudofunctor B C) (Q : StrictPseudofunctor B E)
    (rc : ∀ {x y : B} {p q : x ⟶ y} (α β : p ⟶ q),
      P.map₂ α = P.map₂ β → Q.map₂ α = Q.map₂ β → α = β)
    {x x' y y' : B} (hx : x = x') (hy : y = y')
    {p q : x ⟶ y} {p' q' : x' ⟶ y'} (hp : HEq p p') (hq : HEq q q')
    (α : p ⟶ q) (β : p' ⟶ q')
    (hP : HEq (P.map₂ α) (P.map₂ β)) (hQ : HEq (Q.map₂ α) (Q.map₂ β)) : HEq α β := by
  cases hx
  cases hy
  cases eq_of_heq hp
  cases eq_of_heq hq
  exact heq_of_eq (rc α β (eq_of_heq hP) (eq_of_heq hQ))

omit [Strict A] [Strict B] [Strict C] [Strict E] in
theorem strictFunctorJointExt
    (P : StrictPseudofunctor B C) (Q : StrictPseudofunctor B E)
    (ro : ∀ x y, P.obj x = P.obj y → Q.obj x = Q.obj y → x = y)
    (rh : ∀ {x y : B} (p q : x ⟶ y), P.map p = P.map q → Q.map p = Q.map q → p = q)
    (rc : ∀ {x y : B} {p q : x ⟶ y} (α β : p ⟶ q),
      P.map₂ α = P.map₂ β → Q.map₂ α = Q.map₂ β → α = β)
    (H K : StrictPseudofunctor A B) (hP : H.comp P = K.comp P)
    (hQ : H.comp Q = K.comp Q) : H = K := by
  have ho : ∀ x, H.obj x = K.obj x := fun x => ro _ _
    (congrArg (fun L => L.obj x) hP) (congrArg (fun L => L.obj x) hQ)
  have hm : ∀ {x y} (p : x ⟶ y), HEq (H.map p) (K.map p) := fun {x y} p =>
    reflect_hom_heq P Q rh (ho x) (ho y) _ _
      (congr_arg_heq (fun L => L.map p) hP) (congr_arg_heq (fun L => L.map p) hQ)
  apply strictFunctorData_ext
  apply prelaxData_ext
  · exact ho
  · exact hm
  · intro x y p q α
    exact reflect_cell_heq P Q rc (ho x) (ho y) (hm p) (hm q) _ _
      (congr_arg_heq (fun L => L.map₂ α) hP) (congr_arg_heq (fun L => L.map₂ α) hQ)
end SquareKit.Internal.PathTransport
