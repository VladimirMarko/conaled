import SquareKit.CommaVertical
import SquareKit.CommaProducts

/-! Arrows and squares specialize the shared comma construction at identity maps. -/
namespace SquareKit.RawArrow
universe u v
variable {O : Type u} (C : CategoryOps.{u,v} O)
abbrev Obj := Comma.Obj (RawMap.id C) (RawMap.id C)
variable {C}
abbrev Hom (E : HomEquiv C) := @Comma.Hom O O O C C C (RawMap.id C) (RawMap.id C) E
variable {E : HomEquiv C}

def transpose {a b : Obj C} (f : Hom E a b) :
    Hom E (⟨a.left, b.left, f.left⟩ : Obj C) (⟨a.right, b.right, f.right⟩ : Obj C) :=
  ⟨a.connector, b.connector, E.symm f.commutes⟩

@[simp] theorem transpose_transpose {a b : Obj C} (f : Hom E a b) :
    transpose (transpose f) = f := by cases f; rfl

/-- Object composition needs equality of the middle objects, not of arrows. -/
def compose (b a : Obj C) (middle : b.left = a.right) : Obj C := by
  rcases a with ⟨a₀,a₁,f⟩; rcases b with ⟨b₀,b₁,g⟩
  dsimp at middle; cases middle
  exact ⟨a₀,b₁,C.comp g f⟩

@[simp] theorem compose_mk {a b c : O} (g : C.Hom b c) (f : C.Hom a b) :
    compose (⟨b,c,g⟩ : Obj C) ⟨a,b,f⟩ rfl = ⟨a,c,C.comp g f⟩ := rfl

def identityObj (a : O) : Obj C := ⟨a,a,C.ident⟩

def identityHom (CL : CategoryLaws C E) {a b : O} (f : C.Hom a b) :
    Hom E (identityObj a) (identityObj b) :=
  ⟨f,f,E.trans (CL.id_comp f) (E.symm (CL.comp_id f))⟩

abbrev ops (CC : CategoryCongr C E) (CL : CategoryLaws C E) :=
  Comma.ops CC CL (RawMap.id_laws E) (RawMap.id_laws E)
abbrev equiv (CC : CategoryCongr C E) (CL : CategoryLaws C E) :=
  Comma.equiv CC CL (RawMap.id_laws E) (RawMap.id_laws E)

def identityMap (CC : CategoryCongr C E) (CL : CategoryLaws C E) : RawMap C (ops CC CL) :=
  ⟨identityObj, identityHom CL⟩

theorem identityMap_laws (CC : CategoryCongr C E) (CL : CategoryLaws C E) :
    MapLaws (identityMap CC CL) E (equiv CC CL) :=
  ⟨fun h => ⟨h,h⟩, ⟨E.refl _,E.refl _⟩, fun _ _ => ⟨E.refl _,E.refl _⟩⟩

/-- The more general comma pasting theorem needs semantic middle compatibility. -/
def vertical (CC : CategoryCongr C E) (CL : CategoryLaws C E)
    {a b c a' b' c' : O} {h : C.Hom a b} {k : C.Hom b c}
    {h' : C.Hom a' b'} {k' : C.Hom b' c'}
    (f : Hom E (⟨a,b,h⟩ : Obj C) ⟨a',b',h'⟩)
    (g : Hom E (⟨b,c,k⟩ : Obj C) ⟨b',c',k'⟩) (middle : E.Rel f.right g.left) :
    Hom E (compose (⟨b,c,k⟩ : Obj C) ⟨a,b,h⟩ rfl)
      (compose (⟨b',c',k'⟩ : Obj C) ⟨a',b',h'⟩ rfl) :=
  Comma.vertical CC CL f g middle

/-- Felix's equality compatibility is a specialization of semantic compatibility. -/
def verticalEq (CC : CategoryCongr C E) (CL : CategoryLaws C E)
    {a b c a' b' c' : O} {h : C.Hom a b} {k : C.Hom b c}
    {h' : C.Hom a' b'} {k' : C.Hom b' c'}
    (f : Hom E (⟨a,b,h⟩ : Obj C) ⟨a',b',h'⟩)
    (g : Hom E (⟨b,c,k⟩ : Obj C) ⟨b',c',k'⟩) (middle : f.right = g.left) :=
  vertical CC CL f g (middle ▸ E.refl f.right)

/-- Pasting along explicit middle-object equalities recovers the source's arbitrary objects. -/
def verticalAlong (CC : CategoryCongr C E) (CL : CategoryLaws C E)
    {a b c d : Obj C} (f : Hom E a b) (g : Hom E c d)
    (sourceMiddle : c.left = a.right) (targetMiddle : d.left = b.right)
    (middle : HEq f.right g.left) :
    Hom E (compose c a sourceMiddle) (compose d b targetMiddle) := by
  rcases a with ⟨a₀,a₁,h⟩; rcases b with ⟨b₀,b₁,h'⟩
  rcases c with ⟨c₀,c₁,k⟩; rcases d with ⟨d₀,d₁,k'⟩
  dsimp at sourceMiddle targetMiddle
  cases sourceMiddle; cases targetMiddle
  exact verticalEq CC CL f g (eq_of_heq middle)

def products (CC : CategoryCongr C E) (CL : CategoryLaws C E) (P : ProductOps C)
    (PC : ProductCongr E P) (PL : ProductLaws E P) : ProductOps (ops CC CL) :=
  Comma.productOps CC CL (RawMap.id_laws E) (RawMap.id_laws E)
    (ProductMap.id P) (ProductMap.id P)
    (fun _ _ => Comparison.id_laws CL _) (fun _ _ => Comparison.id_laws CL _)
    (ProductMap.id_laws CL P) (ProductMap.id_laws CL P) PC PL

theorem products_laws (CC : CategoryCongr C E) (CL : CategoryLaws C E) (P : ProductOps C)
    (PC : ProductCongr E P) (PL : ProductLaws E P) :
    ProductLaws (equiv CC CL) (products CC CL P PC PL) :=
  Comma.productLaws CC CL (RawMap.id_laws E) (RawMap.id_laws E)
    (ProductMap.id P) (ProductMap.id P)
    (fun _ _ => Comparison.id_laws CL _) (fun _ _ => Comparison.id_laws CL _)
    (ProductMap.id_laws CL P) (ProductMap.id_laws CL P) PC PL PL PL
end SquareKit.RawArrow
