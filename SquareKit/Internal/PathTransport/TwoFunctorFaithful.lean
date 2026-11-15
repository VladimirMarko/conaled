import SquareKit.Internal.PathTransport.TwoFunctorData
namespace SquareKit.Internal.PathTransport
open CategoryTheory Bicategory
variable {A B C : Type*} [Bicategory A] [Bicategory B] [Bicategory C]
variable (H : StrictPseudofunctor B C)
variable (ho : Function.Injective H.obj)
variable (hm : ∀{x y : B}, Function.Injective (H.map (X := x) (Y := y)))
variable (hc : ∀{x y : B} {p q : x ⟶ y}, Function.Injective (H.map₂ (f := p) (g := q)))
include hm in
private theorem map_heq_reflect {x y x' y' : B} (hx : x = x') (hy : y = y')
    (p : x ⟶ y) (q : x' ⟶ y') (h : HEq (H.map p) (H.map q)) : HEq p q := by
  cases hx; cases hy
  exact heq_of_eq (hm (eq_of_heq h))
include hc in
private theorem cell_heq_reflect {x y x' y' : B} (hx : x = x') (hy : y = y')
    {p q : x ⟶ y} {p' q' : x' ⟶ y'} (hp : HEq p p') (hq : HEq q q')
    (α : p ⟶ q) (β : p' ⟶ q') (h : HEq (H.map₂ α) (H.map₂ β)) : HEq α β := by
  cases hx; cases hy
  cases eq_of_heq hp; cases eq_of_heq hq
  exact heq_of_eq (hc (eq_of_heq h))
include ho hm hc in
theorem strictFunctor_postcomp_injective {F G : StrictPseudofunctor A B}
    (h : F.comp H = G.comp H) : F = G := by
  have hO (a : A) : F.obj a = G.obj a := ho (congrArg (fun K => K.obj a) h)
  have hM {a b : A} (p : a ⟶ b) : HEq (F.map p) (G.map p) :=
    map_heq_reflect H (@hm) (hO a) (hO b) _ _ (congr_arg_heq (fun K => K.map p) h)
  apply strictFunctorData_ext
  apply prelaxData_ext _ _ hO
  · exact @hM
  · intro a b p q α
    exact cell_heq_reflect H (@hc) (hO a) (hO b) (hM p) (hM q) _ _
      (congr_arg_heq (fun K => K.map₂ α) h)
end SquareKit.Internal.PathTransport
