import SquareKit.CategoryMap

/-! Object reindexing needs no injectivity, category laws, or structure comparisons. -/
namespace SquareKit.ObjectReindex
universe u v r
variable {O : Type u} {J : Type r}
def ops (C : CategoryOps.{u,v} O) (F : J → O) : CategoryOps J where
  Hom a b := C.Hom (F a) (F b)
  ident := C.ident
  comp := C.comp

def forget (C : CategoryOps.{u,v} O) (F : J → O) : RawMap (ops C F) C := ⟨F,id⟩
def equiv {C : CategoryOps.{u,v} O} (F : J → O) (E : HomEquiv C) : HomEquiv (ops C F) :=
  (forget C F).induced E

theorem forget_laws {C : CategoryOps.{u,v} O} (F : J → O) (E : HomEquiv C) :
    MapLaws (forget C F) (equiv F E) E :=
  (forget C F).inducedLaws E (E.refl _) (fun _ _ => E.refl _)
theorem congr {C : CategoryOps.{u,v} O} (F : J → O) {E : HomEquiv C} (CC : CategoryCongr C E) :
    CategoryCongr (ops C F) (equiv F E) := ⟨CC.comp⟩
theorem laws {C : CategoryOps.{u,v} O} (F : J → O) {E : HomEquiv C} (CL : CategoryLaws C E) :
    CategoryLaws (ops C F) (equiv F E) := ⟨CL.id_comp,CL.comp_id,CL.assoc⟩
end SquareKit.ObjectReindex
