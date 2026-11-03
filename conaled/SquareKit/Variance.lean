import SquareKit.FunctionCategory

/-! Variance of homs uses only composition. Designation and coherence are
additional contracts, not properties of every mathematical function. -/
namespace SquareKit
universe u v u' v' u'' v''

namespace HomVariance
variable {O : Type u} {C : CategoryOps.{u,v} O}

def map {a a' b b'} (i : C.Hom a' a) (j : C.Hom b b')
    (f : C.Hom a b) : C.Hom a' b' := C.comp j (C.comp f i)

theorem congr {E : HomEquiv C} (CC : CategoryCongr C E)
    {a a' b b'} {i i' : C.Hom a' a} {j j' : C.Hom b b'} {f f' : C.Hom a b}
    (hi : E.Rel i i') (hj : E.Rel j j') (hf : E.Rel f f') :
    E.Rel (map i j f) (map i' j' f') := CC.comp hj (CC.comp hf hi)

theorem ident {E : HomEquiv C} (CL : CategoryLaws C E)
    {a b} (f : C.Hom a b) : E.Rel (map C.ident C.ident f) f :=
  E.trans (CL.id_comp _) (CL.comp_id _)

theorem comp {E : HomEquiv C} (CC : CategoryCongr C E) (CL : CategoryLaws C E)
    {a a' a'' b b' b''} (i : C.Hom a' a) (i' : C.Hom a'' a')
    (j : C.Hom b b') (j' : C.Hom b' b'') (f : C.Hom a b) :
    E.Rel (map i' j' (map i j f)) (map (C.comp i i') (C.comp j' j) f) := by
  unfold map
  apply E.trans (CC.comp (E.refl _) (CL.assoc _ _ _))
  apply E.trans (CC.comp (E.refl _) (CC.comp (E.refl _) (CL.assoc _ _ _)))
  exact E.symm (CL.assoc _ _ _)

/-- A lawful interpretation preserves this variance without closed structure. -/
theorem interpret {Q : Type u'} {D : CategoryOps.{u',v'} Q}
    {E : HomEquiv C} {V : HomEquiv D} (F : RawMap C D) (L : MapLaws F E V)
    (DC : CategoryCongr D V) {a a' b b'} (i : C.Hom a' a) (j : C.Hom b b')
    (f : C.Hom a b) :
    V.Rel (F.map (map i j f)) (map (F.map i) (F.map j) (F.map f)) :=
  V.trans (L.comp _ _) (DC.comp (V.refl _) (L.comp _ _))
end HomVariance

/-- A designated class of arrows. Membership does not assert injectivity,
proof irrelevance, zero runtime cost, or uniqueness of parallel arrows. -/
structure Designated {O : Type u} (C : CategoryOps.{u,v} O) where
  admits : {a b : O} → C.Hom a b → Prop

structure DesignatedLaws {O : Type u} {C : CategoryOps.{u,v} O}
    (S : Designated C) : Prop where
  ident : ∀ {a}, S.admits (C.ident (a := a))
  comp : ∀ {a b c} {g : C.Hom b c} {f : C.Hom a b},
    S.admits g → S.admits f → S.admits (C.comp g f)

namespace Designated
variable {O : Type u} {C : CategoryOps.{u,v} O} (S : Designated C)

abbrev Evidence (a b : O) := {f : C.Hom a b // S.admits f}

def ops (L : DesignatedLaws S) : CategoryOps O where
  Hom := S.Evidence
  ident := ⟨C.ident, L.ident⟩
  comp g f := ⟨C.comp g.val f.val, L.comp g.property f.property⟩

def forget (L : DesignatedLaws S) : RawMap (S.ops L) C where
  obj := id
  map := Subtype.val

/-- Evidence inherits precisely the selected semantic equivalence. -/
def equiv (L : DesignatedLaws S) (E : HomEquiv C) : HomEquiv (S.ops L) :=
  (S.forget L).induced E

theorem forget_laws (L : DesignatedLaws S) (E : HomEquiv C) :
    MapLaws (S.forget L) (S.equiv L E) E :=
  (S.forget L).inducedLaws E (E.refl _) (fun _ _ => E.refl _)

theorem laws (L : DesignatedLaws S) {E : HomEquiv C}
    (CC : CategoryCongr C E) (CL : CategoryLaws C E) :
    CategoryLaws (S.ops L) (S.equiv L E) :=
  RawMap.transportLaws (S.forget_laws L E) ((S.forget L).induced_reflects E) CC CL

def all (C : CategoryOps.{u,v} O) : Designated C := ⟨fun _ => True⟩
theorem all_laws : DesignatedLaws (all C) := ⟨True.intro, fun _ _ => True.intro⟩

/-- Function-constructor closure is a separate optional obligation. -/
def FunctionClosed (S : Designated FunctionCategory.ops.{u}) : Prop :=
  ∀ {A A' B B' : Type u} (i : A' → A) (j : B → B'),
    S.admits i → S.admits j → S.admits (HomVariance.map (C := FunctionCategory.ops) i j)

theorem all_functionClosed : FunctionClosed (all FunctionCategory.ops.{u}) :=
  fun _ _ _ _ => True.intro
/-- A semantic functor need not preserve a separately chosen designation. -/
def PreservedBy {Q : Type u'} {D : CategoryOps.{u',v'} Q}
    (T : Designated D) (F : RawMap C D) : Prop :=
  ∀ {a b} (f : C.Hom a b), S.admits f → T.admits (F.map f)

theorem preserved_id : S.PreservedBy S (RawMap.id C) := fun _ h => h

theorem preserved_comp {Q : Type u'} {R : Type u''}
    {D : CategoryOps.{u',v'} Q} {K : CategoryOps.{u'',v''} R}
    {T : Designated D} {U : Designated K} {F : RawMap C D} {G : RawMap D K}
    (hF : S.PreservedBy T F) (hG : T.PreservedBy U G) :
    S.PreservedBy U (F.comp G) := fun f h => hG (F.map f) (hF f h)
end Designated

/-- Coherence is an explicit equation on a bounded pair of routes. -/
structure CoercionDiamond {O : Type u} (C : CategoryOps.{u,v} O)
    (a b c d : O) where
  ab : C.Hom a b
  bd : C.Hom b d
  ac : C.Hom a c
  cd : C.Hom c d

namespace CoercionDiamond
variable {O : Type u} {C : CategoryOps.{u,v} O} {a b c d : O}

def left (r : CoercionDiamond C a b c d) := C.comp r.bd r.ab
def right (r : CoercionDiamond C a b c d) := C.comp r.cd r.ac
def Coherent (E : HomEquiv C) (r : CoercionDiamond C a b c d) := E.Rel r.left r.right

/-- The bounded assistant requires a coherence certificate before selecting a route. -/
def resolve (E : HomEquiv C) (r : CoercionDiamond C a b c d)
    (_ : r.Coherent E) : C.Hom a d := r.left

theorem resolve_right (E : HomEquiv C) (r : CoercionDiamond C a b c d)
    (h : r.Coherent E) : E.Rel (r.resolve E h) r.right := h

theorem interpret {Q : Type u'} {D : CategoryOps.{u',v'} Q}
    {E : HomEquiv C} {V : HomEquiv D} (F : RawMap C D) (L : MapLaws F E V)
    (r : CoercionDiamond C a b c d) (h : r.Coherent E) :
    V.Rel (D.comp (F.map r.bd) (F.map r.ab))
      (D.comp (F.map r.cd) (F.map r.ac)) :=
  V.trans (V.symm (L.comp _ _)) (V.trans (L.congr h) (L.comp _ _))
end CoercionDiamond
end SquareKit
