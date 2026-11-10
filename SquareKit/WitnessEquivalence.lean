import SquareKit.CategoryMap

namespace SquareKit
universe u v w u' v' w'

/-- Computational relation witnesses with reflexivity, symmetry and transitivity.
No equations between these operations, or uniqueness of witnesses, are fields. -/
structure WitnessEquivalence {O : Type u} (C : CategoryOps.{u,v} O) where
  Rel : {a b : O} → C.Hom a b → C.Hom a b → Type w
  refl : ∀ {a b} (f : C.Hom a b), Rel f f
  symm : ∀ {a b} {f g : C.Hom a b}, Rel f g → Rel g f
  trans : ∀ {a b} {f g h : C.Hom a b}, Rel f g → Rel g h → Rel f h

namespace WitnessEquivalence
variable {O : Type u} {C : CategoryOps.{u,v} O}

def erase (E : WitnessEquivalence C) : HomEquiv C where
  homSetoid _ _ := {
    r := fun f g => Nonempty (E.Rel f g)
    iseqv := ⟨fun f => ⟨E.refl f⟩,
      fun ⟨h⟩ => ⟨E.symm h⟩, fun ⟨h⟩ ⟨k⟩ => ⟨E.trans h k⟩⟩ }

def ofHomEquiv (E : HomEquiv C) : WitnessEquivalence C where
  Rel f g := PLift (E.Rel f g)
  refl f := ⟨E.refl f⟩
  symm h := ⟨E.symm h.down⟩
  trans h k := ⟨E.trans h.down k.down⟩

theorem erase_ofHomEquiv (E : HomEquiv C) {a b} (f g : C.Hom a b) :
    (ofHomEquiv E).erase.Rel f g ↔ E.Rel f g :=
  ⟨fun ⟨h⟩ => h.down, fun h => ⟨⟨h⟩⟩⟩

/-- Computational congruence, not a proposition asserting its existence. -/
structure Congr (E : WitnessEquivalence C) where
  comp : ∀ {a b c} {g g' : C.Hom b c} {f f' : C.Hom a b},
    E.Rel g g' → E.Rel f f' → E.Rel (C.comp g f) (C.comp g' f')

structure Laws (E : WitnessEquivalence C) where
  id_comp : ∀ {a b} (f : C.Hom a b), E.Rel (C.comp C.ident f) f
  comp_id : ∀ {a b} (f : C.Hom a b), E.Rel (C.comp f C.ident) f
  assoc : ∀ {a b c d} (h : C.Hom c d) (g : C.Hom b c) (f : C.Hom a b),
    E.Rel (C.comp (C.comp h g) f) (C.comp h (C.comp g f))

theorem Congr.erase {E : WitnessEquivalence C} (K : E.Congr) : CategoryCongr C E.erase where
  comp := fun ⟨h⟩ ⟨k⟩ => ⟨K.comp h k⟩

theorem Laws.erase {E : WitnessEquivalence C} (L : E.Laws) : CategoryLaws C E.erase where
  id_comp f := ⟨L.id_comp f⟩
  comp_id f := ⟨L.comp_id f⟩
  assoc h g f := ⟨L.assoc h g f⟩

def liftCongr {E : HomEquiv C} (K : CategoryCongr C E) : (ofHomEquiv E).Congr where
  comp h k := ⟨K.comp h.down k.down⟩

def liftLaws {E : HomEquiv C} (L : CategoryLaws C E) : (ofHomEquiv E).Laws where
  id_comp f := ⟨L.id_comp f⟩
  comp_id f := ⟨L.comp_id f⟩
  assoc h g f := ⟨L.assoc h g f⟩

variable {P : Type u'} {D : CategoryOps.{u',v'} P}

/-- Pullback of the actual witness type along a raw interpretation. -/
def induced (F : RawMap C D) (H : WitnessEquivalence D) : WitnessEquivalence C where
  Rel f g := H.Rel (F.map f) (F.map g)
  refl f := H.refl (F.map f)
  symm := H.symm
  trans := H.trans

structure Preservation (F : RawMap C D) (E : WitnessEquivalence C)
    (H : WitnessEquivalence D) where
  congr : ∀ {a b} {f g : C.Hom a b}, E.Rel f g → H.Rel (F.map f) (F.map g)
  ident : ∀ {a}, H.Rel (F.map (C.ident (a := a))) D.ident
  comp : ∀ {a b c} (g : C.Hom b c) (f : C.Hom a b),
    H.Rel (F.map (C.comp g f)) (D.comp (F.map g) (F.map f))

theorem Preservation.erase {F : RawMap C D} {E : WitnessEquivalence C}
    {H : WitnessEquivalence D} (L : Preservation F E H) : MapLaws F E.erase H.erase where
  congr := fun ⟨h⟩ => ⟨L.congr h⟩
  ident := ⟨L.ident⟩
  comp g f := ⟨L.comp g f⟩

/-- Reflection returns a chosen source witness rather than mere inhabitation. -/
def Reflection (F : RawMap C D) (E : WitnessEquivalence C)
    (H : WitnessEquivalence D) :=
  ∀ {a b} {f g : C.Hom a b}, H.Rel (F.map f) (F.map g) → E.Rel f g

def transportLaws {F : RawMap C D} {E : WitnessEquivalence C}
    {H : WitnessEquivalence D} (L : Preservation F E H) (R : Reflection F E H)
    (HC : H.Congr) (HL : H.Laws) : E.Laws where
  id_comp _f := R (H.trans (L.comp _ _) (H.trans (HC.comp L.ident (H.refl _)) (HL.id_comp _)))
  comp_id _f := R (H.trans (L.comp _ _) (H.trans (HC.comp (H.refl _) L.ident) (HL.comp_id _)))
  assoc _h _g _f := R (H.trans (L.comp _ _) (H.trans (HC.comp (L.comp _ _) (H.refl _))
    (H.trans (HL.assoc _ _ _) (H.trans (HC.comp (H.refl _) (H.symm (L.comp _ _)))
      (H.symm (L.comp _ _))))))

end WitnessEquivalence
end SquareKit
