import SquareKit.WitnessCommaVertical
import SquareKit.WitnessCommaProducts
import SquareKit.RawArrow
namespace SquareKit.WitnessArrow
universe u v
variable {O : Type u} (C : CategoryOps.{u,v} O)
abbrev Obj := Comma.Obj (RawMap.id C) (RawMap.id C)
variable {C}
abbrev Hom (E : WitnessEquivalence C) := @WitnessComma.Hom O O O C C C (RawMap.id C) (RawMap.id C) E
variable {E : WitnessEquivalence C}

def transpose {a b : Obj C} (f : Hom E a b) :
    Hom E (⟨a.left, b.left, f.left⟩ : Obj C) (⟨a.right, b.right, f.right⟩ : Obj C) :=
  ⟨a.connector, b.connector, E.symm f.commutes⟩

/-- Reuse the established raw object composition and its middle-object equality. -/
abbrev compose := @RawArrow.compose O C

@[simp] theorem compose_mk {a b c : O} (g : C.Hom b c) (f : C.Hom a b) :
    compose (⟨b,c,g⟩ : Obj C) ⟨a,b,f⟩ rfl = ⟨a,c,C.comp g f⟩ := rfl

abbrev identityObj := @RawArrow.identityObj O C

def identityHom (CL : E.Laws) {a b : O} (f : C.Hom a b) :
    Hom E (identityObj a) (identityObj b) :=
  ⟨f,f,E.trans (CL.id_comp f) (E.symm (CL.comp_id f))⟩

abbrev ops (CC : E.Congr) (CL : E.Laws) :=
  WitnessComma.ops CC CL (WitnessEquivalence.Preservation.id E) (WitnessEquivalence.Preservation.id E)
abbrev equiv (CC : E.Congr) (CL : E.Laws) :=
  WitnessComma.equiv CC CL (WitnessEquivalence.Preservation.id E) (WitnessEquivalence.Preservation.id E)

def identityMap (CC : E.Congr) (CL : E.Laws) : RawMap C (ops CC CL) :=
  ⟨identityObj, identityHom CL⟩

def identityMap_laws (CC : E.Congr) (CL : E.Laws) :
    WitnessEquivalence.Preservation (identityMap CC CL) E (equiv CC CL) :=
  ⟨fun h => ⟨h,h⟩, ⟨E.refl _,E.refl _⟩, fun _ _ => ⟨E.refl _,E.refl _⟩⟩

/-- The more general comma pasting theorem needs semantic middle compatibility. -/
def vertical (CC : E.Congr) (CL : E.Laws)
    {a b c a' b' c' : O} {h : C.Hom a b} {k : C.Hom b c}
    {h' : C.Hom a' b'} {k' : C.Hom b' c'}
    (f : Hom E (⟨a,b,h⟩ : Obj C) ⟨a',b',h'⟩)
    (g : Hom E (⟨b,c,k⟩ : Obj C) ⟨b',c',k'⟩) (middle : E.Rel f.right g.left) :
    Hom E (compose (⟨b,c,k⟩ : Obj C) ⟨a,b,h⟩ rfl)
      (compose (⟨b',c',k'⟩ : Obj C) ⟨a',b',h'⟩ rfl) :=
  WitnessComma.vertical CC CL f g middle

/-- Felix's equality compatibility is a specialization of semantic compatibility. -/
def verticalEq (CC : E.Congr) (CL : E.Laws)
    {a b c a' b' c' : O} {h : C.Hom a b} {k : C.Hom b c}
    {h' : C.Hom a' b'} {k' : C.Hom b' c'}
    (f : Hom E (⟨a,b,h⟩ : Obj C) ⟨a',b',h'⟩)
    (g : Hom E (⟨b,c,k⟩ : Obj C) ⟨b',c',k'⟩) (middle : f.right = g.left) :=
  vertical CC CL f g (middle ▸ E.refl f.right)

/-- Pasting along explicit middle-object equalities recovers the source's arbitrary objects. -/
def verticalAlong (CC : E.Congr) (CL : E.Laws)
    {a b c d : Obj C} (f : Hom E a b) (g : Hom E c d)
    (sourceMiddle : c.left = a.right) (targetMiddle : d.left = b.right)
    (middle : HEq f.right g.left) :
    Hom E (compose c a sourceMiddle) (compose d b targetMiddle) := by
  rcases a with ⟨a₀,a₁,h⟩; rcases b with ⟨b₀,b₁,h'⟩
  rcases c with ⟨c₀,c₁,k⟩; rcases d with ⟨d₀,d₁,k'⟩
  dsimp at sourceMiddle targetMiddle
  cases sourceMiddle; cases targetMiddle
  exact verticalEq CC CL f g (eq_of_heq middle)

def products (CC : E.Congr) (CL : E.Laws) (P : ProductOps C)
    (PC : WitnessEquivalence.ProductCongr E P) (PL : WitnessEquivalence.ProductLaws E P) : ProductOps (ops CC CL) :=
  WitnessComma.productOps CC CL (WitnessEquivalence.Preservation.id E) (WitnessEquivalence.Preservation.id E)
    (ProductMap.id P) (ProductMap.id P)
    (fun _ _ => WitnessEquivalence.Comparison.id_laws CL _) (fun _ _ => WitnessEquivalence.Comparison.id_laws CL _)
    (WitnessEquivalence.ProductMap.id_laws CL P) (WitnessEquivalence.ProductMap.id_laws CL P) PC PL

def products_laws (CC : E.Congr) (CL : E.Laws) (P : ProductOps C)
    (PC : WitnessEquivalence.ProductCongr E P) (PL : WitnessEquivalence.ProductLaws E P) :
    WitnessEquivalence.ProductLaws (equiv CC CL) (products CC CL P PC PL) :=
  WitnessComma.productLaws CC CL (WitnessEquivalence.Preservation.id E) (WitnessEquivalence.Preservation.id E)
    (ProductMap.id P) (ProductMap.id P)
    (fun _ _ => WitnessEquivalence.Comparison.id_laws CL _) (fun _ _ => WitnessEquivalence.Comparison.id_laws CL _)
    (WitnessEquivalence.ProductMap.id_laws CL P) (WitnessEquivalence.ProductMap.id_laws CL P) PC PL PL PL
theorem erase_transpose {a b : Obj C} (f : Hom E a b) :
    (transpose f).erase = RawArrow.transpose f.erase := Comma.Hom.ext rfl rfl

/-- Transposition preserves the two connector arrows, but need not preserve its witness twice. -/
theorem transpose_twice_sides {a b : Obj C} (f : Hom E a b) :
    (transpose (transpose f)).left = f.left ∧ (transpose (transpose f)).right = f.right :=
  ⟨rfl,rfl⟩

def terminal (CC : E.Congr) (CL : E.Laws) (T : TerminalOps C)
    (TL : WitnessEquivalence.TerminalLaws E T) : TerminalOps (ops CC CL) :=
  WitnessComma.terminalOps CC CL (WitnessEquivalence.Preservation.id E)
    (WitnessEquivalence.Preservation.id E) (TerminalMap.id T) (TerminalMap.id T)
    (WitnessEquivalence.Comparison.id_laws CL _)
    (WitnessEquivalence.TerminalMap.id_laws CL T) (WitnessEquivalence.TerminalMap.id_laws CL T) TL

def terminal_laws (CC : E.Congr) (CL : E.Laws) (T : TerminalOps C)
    (TL : WitnessEquivalence.TerminalLaws E T) :
    WitnessEquivalence.TerminalLaws (equiv CC CL) (terminal CC CL T TL) :=
  ⟨fun f => ⟨TL.unique f.left,TL.unique f.right⟩⟩
def products_congr (CC : E.Congr) (CL : E.Laws) (P : ProductOps C)
    (PC : WitnessEquivalence.ProductCongr E P) (PL : WitnessEquivalence.ProductLaws E P) :
    WitnessEquivalence.ProductCongr (equiv CC CL) (products CC CL P PC PL) :=
  ⟨fun h k => ⟨PC.pair h.1 k.1,PC.pair h.2 k.2⟩⟩
end SquareKit.WitnessArrow
