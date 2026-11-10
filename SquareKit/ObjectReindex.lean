import SquareKit.ObjectReindexBasic
import SquareKit.CartesianMap
import SquareKit.CoproductMap
import SquareKit.Initial
import Mathlib.CategoryTheory.InducedCategory

namespace SquareKit.ObjectReindex
universe u v r
variable {O : Type u} {J : Type r} {C : CategoryOps.{u,v} O} (F : J → O)

def terminal (T : TerminalOps C) (unit : J) (i : Comparison C (F unit) T.unit) :
    TerminalOps (ops C F) := ⟨unit,C.comp i.inv T.terminal⟩
def products (P : ProductOps C) (p : J → J → J)
    (i : ∀ a b, Comparison C (F (p a b)) (P.prod (F a) (F b))) : ProductOps (ops C F) where
  prod := p
  fst := C.comp P.fst (i _ _).hom
  snd := C.comp P.snd (i _ _).hom
  pair f g := C.comp (i _ _).inv (P.pair f g)
def initial (T : InitialOps C) (zero : J) (i : Comparison C (F zero) T.zero) :
    InitialOps (ops C F) := ⟨zero,C.comp T.initial i.hom⟩
def coproducts (S : CoproductOps C) (s : J → J → J)
    (i : ∀ a b, Comparison C (F (s a b)) (S.sum (F a) (F b))) : CoproductOps (ops C F) where
  sum := s
  inl := C.comp (i _ _).inv S.inl
  inr := C.comp (i _ _).inv S.inr
  copair f g := C.comp (S.copair f g) (i _ _).hom

variable {E : HomEquiv C}
theorem terminal_preserves (T : TerminalOps C) (unit : J) (i : Comparison C (F unit) T.unit) :
    TerminalMapLaws (F := forget C F) (T := terminal F T unit i) E i := ⟨E.refl _⟩
theorem products_preserve (P : ProductOps C) (p : J → J → J)
    (i : ∀ a b, Comparison C (F (p a b)) (P.prod (F a) (F b))) :
    ProductMapLaws (F := forget C F) (S := products F P p i) E i :=
  ⟨E.refl _,E.refl _,fun _ _ => E.refl _⟩
theorem initial_preserves (T : InitialOps C) (zero : J) (i : Comparison C (F zero) T.zero) :
    InitialMapLaws (F := forget C F) (T := initial F T zero i) E i := ⟨E.refl _⟩
theorem coproducts_preserve (S : CoproductOps C) (s : J → J → J)
    (i : ∀ a b, Comparison C (F (s a b)) (S.sum (F a) (F b))) :
    CoproductMapLaws (F := forget C F) (S := coproducts F S s i) E i :=
  ⟨E.refl _,E.refl _,fun _ _ => E.refl _⟩

variable (CC : CategoryCongr C E) (CL : CategoryLaws C E)
include CC CL in
theorem terminal_laws (T : TerminalOps C) (unit : J) (i : Comparison C (F unit) T.unit)
    (I : ComparisonLaws E i) (TL : TerminalLaws E T) :
    TerminalLaws (equiv F E) (terminal F T unit i) :=
  TerminalMap.transportLaws ((forget C F).induced_reflects E) CC CL I
    (terminal_preserves F T unit i) TL

include CC in
theorem product_congr (P : ProductOps C) (p : J → J → J)
    (i : ∀ a b, Comparison C (F (p a b)) (P.prod (F a) (F b))) (PC : ProductCongr E P) :
    ProductCongr (equiv F E) (products F P p i) :=
  ProductMap.transportCongr (forget_laws F E) ((forget C F).induced_reflects E) CC
    (products_preserve F P p i) PC

include CC CL in
theorem product_laws (P : ProductOps C) (p : J → J → J)
    (i : ∀ a b, Comparison C (F (p a b)) (P.prod (F a) (F b)))
    (I : ∀ a b, ComparisonLaws E (i a b)) (PC : ProductCongr E P) (PL : ProductLaws E P) :
    ProductLaws (equiv F E) (products F P p i) :=
  ProductMap.transportLaws (forget_laws F E) ((forget C F).induced_reflects E) CC CL I
    (products_preserve F P p i) PC PL

include CC CL in
theorem initial_laws (T : InitialOps C) (zero : J) (i : Comparison C (F zero) T.zero)
    (I : ComparisonLaws E i) (TL : InitialLaws E T) :
    InitialLaws (equiv F E) (initial F T zero i) :=
  InitialMap.transportLaws ((forget C F).induced_reflects E) CC CL I.inv_hom
    (initial_preserves F T zero i) TL

include CC in
theorem coproduct_congr (S : CoproductOps C) (s : J → J → J)
    (i : ∀ a b, Comparison C (F (s a b)) (S.sum (F a) (F b))) (SC : CoproductCongr C E S) :
    CoproductCongr (ops C F) (equiv F E) (coproducts F S s i) :=
  CoproductMap.transportCongr (forget_laws F E) ((forget C F).induced_reflects E) CC
    (coproducts_preserve F S s i) SC

include CC CL in
theorem coproduct_laws (S : CoproductOps C) (s : J → J → J)
    (i : ∀ a b, Comparison C (F (s a b)) (S.sum (F a) (F b)))
    (I : ∀ a b, ComparisonLaws E (i a b)) (SC : CoproductCongr C E S) (SL : CoproductLaws C E S) :
    CoproductLaws (ops C F) (equiv F E) (coproducts F S s i) :=
  CoproductMap.transportLaws (forget_laws F E) ((forget C F).induced_reflects E) CC CL I
    (coproducts_preserve F S s i) SC SL

/-- Mathlib's wrapper adds no condition on the object map. -/
def toInduced [CategoryTheory.Category.{v} O] (F : J → O) :
    RawMap (ops (ofCategory O) F) (ofCategory (CategoryTheory.InducedCategory O F)) :=
  ⟨id,CategoryTheory.InducedCategory.homMk⟩
def fromInduced [CategoryTheory.Category.{v} O] (F : J → O) :
    RawMap (ofCategory (CategoryTheory.InducedCategory O F)) (ops (ofCategory O) F) :=
  ⟨id,fun f => f.hom⟩
theorem toInduced_laws [CategoryTheory.Category.{v} O] (F : J → O) :
    MapLaws (toInduced F) (equiv F (equality _)) (equality _) := by
  constructor
  · intro a b f g h; exact congrArg CategoryTheory.InducedCategory.homMk h
  · intro; rfl
  · intros; rfl
theorem fromInduced_laws [CategoryTheory.Category.{v} O] (F : J → O) :
    MapLaws (fromInduced F) (equality _) (equiv F (equality _)) := by
  constructor
  · intro a b f g h; exact congrArg CategoryTheory.InducedCategory.Hom.hom h
  · intro; rfl
  · intros; rfl
@[simp] theorem mathlib_roundtrip [CategoryTheory.Category.{v} O] (F : J → O)
    {a b : CategoryTheory.InducedCategory O F} (f : (ofCategory _).Hom a b) :
    (toInduced F).map ((fromInduced F).map f) = f := rfl
@[simp] theorem roundtrip [CategoryTheory.Category.{v} O] (F : J → O) {a b : J}
    (f : (ops (ofCategory O) F).Hom a b) : (fromInduced F).map ((toInduced F).map f) = f := rfl
end SquareKit.ObjectReindex
