import SquareKit.Category

namespace SquareKit
universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄

namespace HomEquiv
variable {O : Type u₁} {C : CategoryOps.{u₁,v₁} O} (E : HomEquiv C)
theorem refl {a b} (f : C.Hom a b) : E.Rel f f := (E.homSetoid a b).refl f
theorem symm {a b} {f g : C.Hom a b} (h : E.Rel f g) : E.Rel g f :=
  (E.homSetoid a b).symm h
theorem trans {a b} {f g h : C.Hom a b} (p : E.Rel f g) (q : E.Rel g h) : E.Rel f h :=
  (E.homSetoid a b).trans p q
end HomEquiv

/-- Object and arrow data, independent of equivalence and laws. -/
structure RawMap {O : Type u₁} {P : Type u₂}
    (C : CategoryOps.{u₁,v₁} O) (D : CategoryOps.{u₂,v₂} P) where
  obj : O → P
  map : {a b : O} → C.Hom a b → D.Hom (obj a) (obj b)

structure MapLaws {O : Type u₁} {P : Type u₂}
    {C : CategoryOps.{u₁,v₁} O} {D : CategoryOps.{u₂,v₂} P}
    (F : RawMap C D) (E : HomEquiv C) (H : HomEquiv D) : Prop where
  congr : ∀ {a b} {f g : C.Hom a b}, E.Rel f g → H.Rel (F.map f) (F.map g)
  ident : ∀ {a}, H.Rel (F.map (C.ident (a := a))) D.ident
  comp : ∀ {a b c} (g : C.Hom b c) (f : C.Hom a b),
    H.Rel (F.map (C.comp g f)) (D.comp (F.map g) (F.map f))

namespace RawMap
variable {O : Type u₁} {P : Type u₂} {Q : Type u₃}
variable {C : CategoryOps.{u₁,v₁} O} {D : CategoryOps.{u₂,v₂} P}
variable {K : CategoryOps.{u₃,v₃} Q}

def id (C : CategoryOps.{u₁,v₁} O) : RawMap C C := ⟨fun a => a, fun f => f⟩
def comp (F : RawMap C D) (G : RawMap D K) : RawMap C K :=
  ⟨fun a => G.obj (F.obj a), fun f => G.map (F.map f)⟩

def induced (F : RawMap C D) (H : HomEquiv D) : HomEquiv C where
  homSetoid _ _ := {
    r := fun f g => H.Rel (F.map f) (F.map g)
    iseqv := ⟨fun _ => H.refl _, H.symm, H.trans⟩ }

/-- Local operation preservation suffices for the relation induced by a map. -/
theorem inducedLaws (F : RawMap C D) (H : HomEquiv D)
    (hi : ∀ {a}, H.Rel (F.map (C.ident (a := a))) D.ident)
    (hc : ∀ {a b c} (g : C.Hom b c) (f : C.Hom a b),
      H.Rel (F.map (C.comp g f)) (D.comp (F.map g) (F.map f))) :
    MapLaws F (F.induced H) H := ⟨fun h => h, hi, hc⟩

theorem id_laws (E : HomEquiv C) : MapLaws (id C) E E where
  congr h := h
  ident := E.refl _
  comp _ _ := E.refl _

theorem comp_laws {F : RawMap C D} {G : RawMap D K}
    {E : HomEquiv C} {H : HomEquiv D} {J : HomEquiv K}
    (LF : MapLaws F E H) (LG : MapLaws G H J) : MapLaws (F.comp G) E J where
  congr h := LG.congr (LF.congr h)
  ident := J.trans (LG.congr LF.ident) LG.ident
  comp g f := J.trans (LG.congr (LF.comp g f)) (LG.comp _ _)

/-- Reflection is required only when the caller chooses a relation independently. -/
def Reflects (F : RawMap C D) (E : HomEquiv C) (H : HomEquiv D) : Prop :=
  ∀ {a b} {f g : C.Hom a b}, H.Rel (F.map f) (F.map g) → E.Rel f g

theorem induced_reflects (F : RawMap C D) (H : HomEquiv D) :
    F.Reflects (F.induced H) H := fun h => h

theorem transportCongr {F : RawMap C D} {E : HomEquiv C} {H : HomEquiv D}
    (L : MapLaws F E H) (R : F.Reflects E H) (HC : CategoryCongr D H) :
    CategoryCongr C E where
  comp hg hf := R (H.trans (L.comp _ _) (H.trans (HC.comp (L.congr hg) (L.congr hf))
    (H.symm (L.comp _ _))))

theorem transportLaws {F : RawMap C D} {E : HomEquiv C} {H : HomEquiv D}
    (L : MapLaws F E H) (R : F.Reflects E H)
    (HC : CategoryCongr D H) (HL : CategoryLaws D H) : CategoryLaws C E where
  id_comp _f := R (H.trans (L.comp _ _) (H.trans (HC.comp L.ident (H.refl _)) (HL.id_comp _)))
  comp_id _f := R (H.trans (L.comp _ _) (H.trans (HC.comp (H.refl _) L.ident) (HL.comp_id _)))
  assoc _h _g _f := R (H.trans (L.comp _ _) (H.trans (HC.comp (L.comp _ _) (H.refl _))
    (H.trans (HL.assoc _ _ _) (H.trans (HC.comp (H.refl _) (H.symm (L.comp _ _)))
      (H.symm (L.comp _ _))))))

/-- A map descends to the separately constructed lawful hom quotients. -/
def quotientFunctor (F : RawMap C D) {E : HomEquiv C} {H : HomEquiv D}
    (L : MapLaws F E H) (CC : CategoryCongr C E) (CL : CategoryLaws C E)
    (DC : CategoryCongr D H) (DL : CategoryLaws D H) :
    letI := HomQuotient.category CC CL
    letI := HomQuotient.category DC DL
    CategoryTheory.Functor (HomQuotient C E) (HomQuotient D H) := by
  letI := HomQuotient.category CC CL
  letI := HomQuotient.category DC DL
  exact {
    obj := fun a => ⟨F.obj a.as⟩
    map := fun f => Quotient.liftOn f (fun f => Quotient.mk _ (F.map f))
      (fun _ _ h => Quotient.sound (L.congr h))
    map_id := fun _ => Quotient.sound L.ident
    map_comp := fun f g => Quotient.inductionOn₂ f g (fun f g => Quotient.sound (L.comp g f)) }

/-- For equality-lawful models the same data is an ordinary Mathlib functor. -/
def toFunctor {O : Type u₁} {P : Type u₂}
    [CategoryTheory.Category.{v₁} O] [CategoryTheory.Category.{v₂} P]
    (F : RawMap (ofCategory O) (ofCategory P))
    (L : MapLaws F (equality _) (equality _)) : CategoryTheory.Functor O P where
  obj := F.obj
  map := F.map
  map_id _ := L.ident
  map_comp f g := L.comp g f

def ofFunctor {O : Type u₁} {P : Type u₂}
    [CategoryTheory.Category.{v₁} O] [CategoryTheory.Category.{v₂} P]
    (F : CategoryTheory.Functor O P) : RawMap (ofCategory O) (ofCategory P) :=
  ⟨F.obj, F.map⟩

theorem ofFunctor_laws {O : Type u₁} {P : Type u₂}
    [CategoryTheory.Category.{v₁} O] [CategoryTheory.Category.{v₂} P]
    (F : CategoryTheory.Functor O P) : MapLaws (ofFunctor F) (equality _) (equality _) where
  congr := by intros; subst_vars; rfl
  ident := F.map_id _
  comp g f := F.map_comp f g

@[simp] theorem toFunctor_ofFunctor {O : Type u₁} {P : Type u₂}
    [CategoryTheory.Category.{v₁} O] [CategoryTheory.Category.{v₂} P]
    (F : CategoryTheory.Functor O P) : toFunctor (ofFunctor F) (ofFunctor_laws F) = F := rfl

@[simp] theorem comp_obj (F : RawMap C D) (G : RawMap D K) (a : O) :
    (F.comp G).obj a = G.obj (F.obj a) := rfl
@[simp] theorem comp_map (F : RawMap C D) (G : RawMap D K) {a b} (f : C.Hom a b) :
    (F.comp G).map f = G.map (F.map f) := rfl
@[simp] theorem id_comp (F : RawMap C D) : (id C).comp F = F := rfl
@[simp] theorem comp_id (F : RawMap C D) : F.comp (id D) = F := rfl

@[simp] theorem comp_assoc {R : Type u₄} {N : CategoryOps.{u₄,v₄} R}
    (F : RawMap C D) (G : RawMap D K) (H : RawMap K N) :
    (F.comp G).comp H = F.comp (G.comp H) := rfl

end RawMap
end SquareKit
