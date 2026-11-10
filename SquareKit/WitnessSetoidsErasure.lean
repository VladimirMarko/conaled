import SquareKit.WitnessSetoidsDistribution

namespace SquareKit.WitnessSetoids
universe u v

/-- Erasure forgets witnesses; it does not select a representative of a relation. -/
def eraseObj (A : Obj.{u,v}) : SetoidCategory.Obj.{u} where
  Carrier := A.Carrier
  relation := {
    r := fun x y => Nonempty (A.Rel x y)
    iseqv := ⟨fun x => ⟨A.refl x⟩, fun ⟨h⟩ => ⟨A.symm h⟩,
      fun ⟨h⟩ ⟨k⟩ => ⟨A.trans h k⟩⟩ }

def eraseHom {A B : Obj.{u,v}} (f : Hom A B) :
    SetoidCategory.Hom (eraseObj A) (eraseObj B) :=
  ⟨f.toFun, fun ⟨h⟩ => ⟨f.congr h⟩⟩

def eraseMap : RawMap ops.{u,v} SetoidCategory.ops where
  obj := eraseObj
  map := eraseHom

theorem erase_ident (A : Obj.{u,v}) : eraseHom (ops.ident (a := A)) =
    SetoidCategory.ops.ident := rfl

theorem erase_comp {A B C : Obj.{u,v}} (g : Hom B C) (f : Hom A B) :
    eraseHom (ops.comp g f) = SetoidCategory.ops.comp (eraseHom g) (eraseHom f) := rfl

theorem eraseLaws : MapLaws eraseMap.{u,v} equiv.erase SetoidCategory.equiv where
  congr := fun ⟨h⟩ x => ⟨h x⟩
  ident := fun {A} _ => ⟨A.refl _⟩
  comp := fun {_ _ C} _ _ _ => ⟨C.refl _⟩

/-- Erased product relations agree in both directions without choosing witnesses. -/
theorem erase_prod_relation (A B : Obj.{u,v}) (x y : A.Carrier × B.Carrier) :
    (eraseObj (prod A B)).relation.r x y ↔
      (SetoidCategory.prod (eraseObj A) (eraseObj B)).relation.r x y :=
  ⟨fun ⟨h,k⟩ => ⟨⟨h⟩,⟨k⟩⟩, fun ⟨⟨h⟩,⟨k⟩⟩ => ⟨h,k⟩⟩

/-- The product comparison preserves the underlying pair exactly. -/
def eraseProduct (A B : Obj.{u,v}) :
    SetoidCategory.Hom (eraseObj (prod A B))
      (SetoidCategory.prod (eraseObj A) (eraseObj B)) :=
  ⟨id, fun h => (erase_prod_relation A B _ _).mp h⟩

def eraseProductInv (A B : Obj.{u,v}) :
    SetoidCategory.Hom (SetoidCategory.prod (eraseObj A) (eraseObj B))
      (eraseObj (prod A B)) :=
  ⟨id, fun h => (erase_prod_relation A B _ _).mpr h⟩

theorem erase_pair {A B C : Obj.{u,v}} (f : Hom A B) (g : Hom A C) :
    SetoidCategory.ops.comp (eraseProduct B C) (eraseHom (products.pair f g)) =
      SetoidCategory.products.pair (eraseHom f) (eraseHom g) := rfl

theorem erase_fst (A B : Obj.{u,v}) :
    SetoidCategory.ops.comp SetoidCategory.products.fst (eraseProduct A B) =
      eraseHom (products.fst (a := A) (b := B)) := rfl

theorem erase_snd (A B : Obj.{u,v}) :
    SetoidCategory.ops.comp SetoidCategory.products.snd (eraseProduct A B) =
      eraseHom (products.snd (a := A) (b := B)) := rfl

theorem erase_sum_relation (A B : Obj.{u,v}) (x y : Sum A.Carrier B.Carrier) :
    (eraseObj (sum A B)).relation.r x y ↔
      (SetoidCategory.sum (eraseObj A) (eraseObj B)).relation.r x y := by
  cases x <;> cases y
  · exact ⟨fun ⟨h⟩ => .inl ⟨h⟩, fun h => by cases h with | inl h => exact h⟩
  · exact ⟨fun ⟨h⟩ => h.elim, fun h => by cases h⟩
  · exact ⟨fun ⟨h⟩ => h.elim, fun h => by cases h⟩
  · exact ⟨fun ⟨h⟩ => .inr ⟨h⟩, fun h => by cases h with | inr h => exact h⟩

def eraseSum (A B : Obj.{u,v}) :
    SetoidCategory.Hom (eraseObj (sum A B))
      (SetoidCategory.sum (eraseObj A) (eraseObj B)) :=
  ⟨id, fun h => (erase_sum_relation A B _ _).mp h⟩

def eraseSumInv (A B : Obj.{u,v}) :
    SetoidCategory.Hom (SetoidCategory.sum (eraseObj A) (eraseObj B))
      (eraseObj (sum A B)) :=
  ⟨id, fun h => (erase_sum_relation A B _ _).mpr h⟩

theorem erase_inl (A B : Obj.{u,v}) :
    SetoidCategory.ops.comp (eraseSum A B) (eraseHom (coproducts.inl (a := A) (b := B))) =
      SetoidCategory.coproducts.inl := rfl

theorem erase_inr (A B : Obj.{u,v}) :
    SetoidCategory.ops.comp (eraseSum A B) (eraseHom (coproducts.inr (a := A) (b := B))) =
      SetoidCategory.coproducts.inr := rfl

theorem erase_copair {A B C : Obj.{u,v}} (f : Hom A C) (g : Hom B C) :
    SetoidCategory.ops.comp (SetoidCategory.coproducts.copair (eraseHom f) (eraseHom g))
      (eraseSum A B) = eraseHom (coproducts.copair f g) := rfl

/-- Erasure of an exponential retains the underlying congruent function. -/
def eraseExponential (A B : Obj.{u,u}) :
    SetoidCategory.Hom (eraseObj (exponential A B))
      (SetoidCategory.exponential (eraseObj A) (eraseObj B)) :=
  ⟨eraseHom, fun ⟨h⟩ x => ⟨h x⟩⟩

/-- Comparison recovers evaluation, including the product and exponential maps. -/
theorem erase_evaluation (A B : Obj.{u,u}) :
    SetoidCategory.ops.comp (eraseHom (closed.evaluation (a := A) (b := B)))
      (eraseProductInv (exponential A B) A) =
    SetoidCategory.ops.comp SetoidCategory.closed.evaluation
      (SetoidCategory.products.pair
        (SetoidCategory.ops.comp (eraseExponential A B) SetoidCategory.products.fst)
        SetoidCategory.products.snd) := rfl

theorem erase_curry {X A B : Obj.{u,u}} (f : Hom (prod X A) B) :
    SetoidCategory.ops.comp (eraseExponential A B) (eraseHom (closed.curry f)) =
      SetoidCategory.closed.curry (SetoidCategory.ops.comp (eraseHom f) (eraseProductInv X A)) := rfl

end SquareKit.WitnessSetoids
