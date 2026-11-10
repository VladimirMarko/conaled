import SquareKit.TensorOperations
import SquareKit.CartesianLaws

namespace SquareKit
universe u v

/-- Semantic bifunctor laws, separate from structural coherence. -/
structure TensorLaws {O : Type u} {C : CategoryOps.{u,v} O}
    (E : HomEquiv C) (T : TensorOps C) : Prop where
  congr : ∀ {a b c d} {f f' : C.Hom a c} {g g' : C.Hom b d},
    E.Rel f f' → E.Rel g g' → E.Rel (T.map f g) (T.map f' g')
  ident : ∀ a b, E.Rel (T.map (C.ident (a := a)) (C.ident (a := b))) C.ident
  comp : ∀ {a b c d e f} (h : C.Hom c e) (k : C.Hom d f) (f : C.Hom a c) (g : C.Hom b d),
    E.Rel (C.comp (T.map h k) (T.map f g)) (T.map (C.comp h f) (C.comp k g))

namespace TensorLaws
variable {O : Type u} {C : CategoryOps.{u,v} O} {E : HomEquiv C} {P : ProductOps C}

theorem ofProducts (CC : CategoryCongr C E) (CL : CategoryLaws C E)
    (PC : ProductCongr E P) (PL : ProductLaws E P) : TensorLaws E (TensorOps.ofProducts P) where
  congr := Cartesian.tensor_congr CC PC
  ident := Cartesian.tensor_ident CL PC PL
  comp := Cartesian.tensor_comp CC CL PC PL

open CategoryTheory MonoidalCategory

theorem ofMonoidal (O : Type u) [Category.{v} O] [MonoidalCategory O] :
    TensorLaws (equality (ofCategory O)) (TensorOps.ofMonoidal O) where
  congr := by intros; subst_vars; rfl
  ident := id_tensorHom_id
  comp h k f g := tensorHom_comp_tensorHom f g h k

end TensorLaws
end SquareKit
