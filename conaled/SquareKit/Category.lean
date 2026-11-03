import Mathlib.CategoryTheory.Quotient

/-! Raw operations and laws modulo a chosen hom equivalence. Composition runs
its right argument first, as in the existing compiler interfaces. -/
namespace SquareKit
universe u v

structure CategoryOps (Obj : Type u) where
  Hom : Obj → Obj → Type v
  ident : {a : Obj} → Hom a a
  comp : {a b c : Obj} → Hom b c → Hom a b → Hom a c

structure HomEquiv {Obj : Type u} (C : CategoryOps.{u,v} Obj) where
  homSetoid : (a b : Obj) → Setoid (C.Hom a b)

abbrev HomEquiv.Rel {Obj : Type u} {C : CategoryOps.{u,v} Obj}
    (E : HomEquiv C) {a b : Obj} := (E.homSetoid a b).r

structure CategoryCongr {Obj : Type u} (C : CategoryOps.{u,v} Obj)
    (E : HomEquiv C) : Prop where
  comp : ∀ {a b c} {g g' : C.Hom b c} {f f' : C.Hom a b},
    E.Rel g g' → E.Rel f f' → E.Rel (C.comp g f) (C.comp g' f')

structure CategoryLaws {Obj : Type u} (C : CategoryOps.{u,v} Obj)
    (E : HomEquiv C) : Prop where
  id_comp : ∀ {a b} (f : C.Hom a b), E.Rel (C.comp C.ident f) f
  comp_id : ∀ {a b} (f : C.Hom a b), E.Rel (C.comp f C.ident) f
  assoc : ∀ {a b c d} (h : C.Hom c d) (g : C.Hom b c) (f : C.Hom a b),
    E.Rel (C.comp (C.comp h g) f) (C.comp h (C.comp g f))

structure TerminalOps {Obj : Type u} (C : CategoryOps.{u,v} Obj) where
  unit : Obj
  terminal : {a : Obj} → C.Hom a unit

structure ProductOps {Obj : Type u} (C : CategoryOps.{u,v} Obj) where
  prod : Obj → Obj → Obj
  fst : {a b : Obj} → C.Hom (prod a b) a
  snd : {a b : Obj} → C.Hom (prod a b) b
  pair : {a b c : Obj} → C.Hom a b → C.Hom a c → C.Hom a (prod b c)

structure TerminalLaws {Obj : Type u} {C : CategoryOps.{u,v} Obj}
    (E : HomEquiv C) (T : TerminalOps C) : Prop where
  unique : ∀ {a} (f : C.Hom a T.unit), E.Rel f T.terminal

structure ProductCongr {Obj : Type u} {C : CategoryOps.{u,v} Obj}
    (E : HomEquiv C) (P : ProductOps C) : Prop where
  pair : ∀ {a b c} {f f' : C.Hom a b} {g g' : C.Hom a c},
    E.Rel f f' → E.Rel g g' → E.Rel (P.pair f g) (P.pair f' g')

structure ProductLaws {Obj : Type u} {C : CategoryOps.{u,v} Obj}
    (E : HomEquiv C) (P : ProductOps C) : Prop where
  fst_pair : ∀ {a b c} (f : C.Hom a b) (g : C.Hom a c),
    E.Rel (C.comp P.fst (P.pair f g)) f
  snd_pair : ∀ {a b c} (f : C.Hom a b) (g : C.Hom a c),
    E.Rel (C.comp P.snd (P.pair f g)) g
  pair_eta : ∀ {a b c} (f : C.Hom a (P.prod b c)),
    E.Rel (P.pair (C.comp P.fst f) (C.comp P.snd f)) f

/-- Equality-lawful models use Mathlib's category instance. -/
def ofCategory (Obj : Type u) [CategoryTheory.Category.{v} Obj] : CategoryOps Obj where
  Hom := Quiver.Hom
  ident := CategoryTheory.CategoryStruct.id _
  comp g f := CategoryTheory.CategoryStruct.comp f g

def equality {Obj : Type u} (C : CategoryOps.{u,v} Obj) : HomEquiv C where
  homSetoid _ _ := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩

theorem equalityCongr {Obj : Type u} (C : CategoryOps.{u,v} Obj) :
    CategoryCongr C (equality C) where
  comp := by intros; subst_vars; rfl

theorem ofCategoryLaws (Obj : Type u) [CategoryTheory.Category.{v} Obj] :
    CategoryLaws (ofCategory Obj) (equality (ofCategory Obj)) where
  id_comp := CategoryTheory.Category.comp_id
  comp_id := CategoryTheory.Category.id_comp
  assoc h g f := (CategoryTheory.Category.assoc f g h).symm

/-- Object wrapper prevents installing a quotient instance on the raw objects. -/
structure HomQuotient {Obj : Type u} (C : CategoryOps.{u,v} Obj) (E : HomEquiv C) where
  as : Obj

namespace HomQuotient
variable {Obj : Type u} {C : CategoryOps.{u,v} Obj} {E : HomEquiv C}

abbrev Hom (a b : HomQuotient C E) := Quotient (E.homSetoid a.as b.as)

def classOf {a b : Obj} (f : C.Hom a b) : Hom (⟨a⟩ : HomQuotient C E) ⟨b⟩ :=
  Quotient.mk _ f

@[simp] theorem mk_eq_iff {a b : Obj} (f g : C.Hom a b) :
    classOf (E := E) f = classOf g ↔ E.Rel f g := Quotient.eq

def comp (K : CategoryCongr C E) {a b c : HomQuotient C E}
    (g : Hom b c) (f : Hom a b) : Hom a c :=
  Quotient.liftOn₂ g f (fun g f => Quotient.mk _ (C.comp g f))
    (fun _ _ _ _ hg hf => Quotient.sound (K.comp hg hf))

@[instance_reducible] def category (K : CategoryCongr C E) (L : CategoryLaws C E) :
    CategoryTheory.Category (HomQuotient C E) where
  Hom := Hom
  id _ := Quotient.mk _ C.ident
  comp f g := comp K g f
  id_comp f := Quotient.inductionOn f (fun f => Quotient.sound (L.comp_id f))
  comp_id f := Quotient.inductionOn f (fun f => Quotient.sound (L.id_comp f))
  assoc f g h := Quotient.inductionOn₃ f g h
    (fun f g h => (Quotient.sound (L.assoc h g f)).symm)

@[simp] theorem mk_ident (K : CategoryCongr C E) (L : CategoryLaws C E) (a : Obj) :
    classOf (E := E) (C.ident (a := a)) =
      @CategoryTheory.CategoryStruct.id _ (category K L).toCategoryStruct ⟨a⟩ := rfl

@[simp] theorem mk_comp (K : CategoryCongr C E) {a b c : Obj}
    (g : C.Hom b c) (f : C.Hom a b) :
    classOf (E := E) (C.comp g f) = comp K (classOf g) (classOf f) := rfl

/-- The quotient's raw operations are the operations of its Mathlib category. -/
def ops (K : CategoryCongr C E) (L : CategoryLaws C E) :
    CategoryOps (HomQuotient C E) := @ofCategory _ (category K L)

def terminal (K : CategoryCongr C E) (L : CategoryLaws C E) (T : TerminalOps C) :
    TerminalOps (ops K L) where
  unit := ⟨T.unit⟩
  terminal := Quotient.mk _ T.terminal

def products (K : CategoryCongr C E) (L : CategoryLaws C E)
    (P : ProductOps C) (PC : ProductCongr E P) : ProductOps (ops K L) where
  prod a b := ⟨P.prod a.as b.as⟩
  fst := Quotient.mk _ P.fst
  snd := Quotient.mk _ P.snd
  pair f g := Quotient.liftOn₂ f g (fun f g => Quotient.mk _ (P.pair f g))
    (fun _ _ _ _ hf hg => Quotient.sound (PC.pair hf hg))

theorem terminalLaws (K : CategoryCongr C E) (L : CategoryLaws C E)
    (T : TerminalOps C) (TL : TerminalLaws E T) :
    TerminalLaws (equality (ops K L)) (terminal K L T) where
  unique f := Quotient.inductionOn f (fun f => Quotient.sound (TL.unique f))

theorem productLaws (K : CategoryCongr C E) (L : CategoryLaws C E)
    (P : ProductOps C) (PC : ProductCongr E P) (PL : ProductLaws E P) :
    ProductLaws (equality (ops K L)) (products K L P PC) where
  fst_pair f g := Quotient.inductionOn₂ f g (fun f g => Quotient.sound (PL.fst_pair f g))
  snd_pair f g := Quotient.inductionOn₂ f g (fun f g => Quotient.sound (PL.snd_pair f g))
  pair_eta f := Quotient.inductionOn f (fun f => Quotient.sound (PL.pair_eta f))

@[simp] theorem mk_terminal (K : CategoryCongr C E) (L : CategoryLaws C E)
    (T : TerminalOps C) (a : Obj) :
    classOf (E := E) (T.terminal (a := a)) = (terminal K L T).terminal (a := ⟨a⟩) := rfl

@[simp] theorem mk_fst (K : CategoryCongr C E) (L : CategoryLaws C E)
    (P : ProductOps C) (PC : ProductCongr E P) (a b : Obj) :
    classOf (E := E) (P.fst (a := a) (b := b)) =
      (products K L P PC).fst (a := ⟨a⟩) (b := ⟨b⟩) := rfl

@[simp] theorem mk_snd (K : CategoryCongr C E) (L : CategoryLaws C E)
    (P : ProductOps C) (PC : ProductCongr E P) (a b : Obj) :
    classOf (E := E) (P.snd (a := a) (b := b)) =
      (products K L P PC).snd (a := ⟨a⟩) (b := ⟨b⟩) := rfl

@[simp] theorem mk_pair (K : CategoryCongr C E) (L : CategoryLaws C E)
    (P : ProductOps C) (PC : ProductCongr E P) {a b c : Obj}
    (f : C.Hom a b) (g : C.Hom a c) :
    classOf (E := E) (P.pair f g) = (products K L P PC).pair (classOf f) (classOf g) := rfl
end HomQuotient
end SquareKit
