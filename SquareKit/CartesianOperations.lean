import SquareKit.Optional
import SquareKit.CartesianMap

/-! Derived raw operations require no category or product laws. -/
namespace SquareKit
universe u v w
namespace CategoryOps
variable {O : Type u} (C : CategoryOps.{u,v} O)

def sub {I : Sort w} (F : I → O) {a b : I} (h : a = b) : C.Hom (F a) (F b) :=
  h ▸ C.ident

def subEq {a b : O} (h : a = b) : C.Hom a b := C.sub id h

@[simp] theorem sub_refl {I : Sort w} (F : I → O) (a : I) :
    C.sub F (rfl : a = a) = C.ident := rfl

@[simp] theorem subEq_refl (a : O) : C.subEq (rfl : a = a) = C.ident := rfl

/-- Equalities between equality witnesses cannot affect the transported arrow. -/
theorem sub_equiv (E : HomEquiv C) {I : Sort w} (F : I → O) {a b : I}
    (h k : a = b) : E.Rel (C.sub F h) (C.sub F k) := by cases h; exact E.refl _
end CategoryOps

namespace CoproductOps
variable {O : Type u} {C : CategoryOps.{u,v} O}
def jam (S : CoproductOps C) {a : O} : C.Hom (S.sum a a) a := S.copair C.ident C.ident
end CoproductOps

namespace Cartesian
variable {O : Type u} {C : CategoryOps.{u,v} O} (P : ProductOps C)

def dup {a : O} : C.Hom a (P.prod a a) := P.pair C.ident C.ident

def tensor {a b c d : O} (f : C.Hom a c) (g : C.Hom b d) :
    C.Hom (P.prod a b) (P.prod c d) := P.pair (C.comp f P.fst) (C.comp g P.snd)

def first {a b c : O} (f : C.Hom a c) : C.Hom (P.prod a b) (P.prod c b) := tensor P f C.ident

def second {a b d : O} (g : C.Hom b d) : C.Hom (P.prod a b) (P.prod a d) := tensor P C.ident g

def twice {a c : O} (f : C.Hom a c) := tensor P f f

def unitLeft (T : TerminalOps C) {a : O} : C.Hom (P.prod T.unit a) a := P.snd

def unitRight (T : TerminalOps C) {a : O} : C.Hom (P.prod a T.unit) a := P.fst

def insertLeft (T : TerminalOps C) {a : O} : C.Hom a (P.prod T.unit a) := P.pair T.terminal C.ident

def insertRight (T : TerminalOps C) {a : O} : C.Hom a (P.prod a T.unit) := P.pair C.ident T.terminal

def constLeft (T : TerminalOps C) {a b : O} (f : C.Hom T.unit a) : C.Hom b (P.prod a b) :=
  C.comp (first P f) (insertLeft P T)

def constRight (T : TerminalOps C) {a b : O} (f : C.Hom T.unit b) : C.Hom a (P.prod a b) :=
  C.comp (second P f) (insertRight P T)

def assocLeft {a b c : O} : C.Hom (P.prod a (P.prod b c)) (P.prod (P.prod a b) c) :=
  P.pair (second P P.fst) (C.comp P.snd P.snd)

def assocRight {a b c : O} : C.Hom (P.prod (P.prod a b) c) (P.prod a (P.prod b c)) :=
  P.pair (C.comp P.fst P.fst) (first P P.snd)

def inAssocLeft' {a b c a' b' c' : O}
    (f : C.Hom (P.prod (P.prod a b) c) (P.prod (P.prod a' b') c')) :
    C.Hom (P.prod a (P.prod b c)) (P.prod a' (P.prod b' c')) :=
  C.comp (assocRight P) (C.comp f (assocLeft P))

def inAssocLeft {a b c a' b' : O} (f : C.Hom (P.prod a b) (P.prod a' b')) :
    C.Hom (P.prod a (P.prod b c)) (P.prod a' (P.prod b' c)) := inAssocLeft' P (first P f)

def inAssocRight' {a b c a' b' c' : O}
    (f : C.Hom (P.prod a (P.prod b c)) (P.prod a' (P.prod b' c'))) :
    C.Hom (P.prod (P.prod a b) c) (P.prod (P.prod a' b') c') :=
  C.comp (assocLeft P) (C.comp f (assocRight P))

def inAssocRight {a b c b' c' : O} (f : C.Hom (P.prod b c) (P.prod b' c')) :
    C.Hom (P.prod (P.prod a b) c) (P.prod (P.prod a b') c') := inAssocRight' P (second P f)

def swap {a b : O} : C.Hom (P.prod a b) (P.prod b a) := P.pair P.snd P.fst

def inSwap {a b a' b' : O} (f : C.Hom (P.prod b a) (P.prod b' a')) :
    C.Hom (P.prod a b) (P.prod a' b') := C.comp (swap P) (C.comp f (swap P))

def transpose {a b c d : O} : C.Hom (P.prod (P.prod a b) (P.prod c d))
    (P.prod (P.prod a c) (P.prod b d)) :=
  P.pair (P.pair (C.comp P.fst P.fst) (C.comp P.fst P.snd))
    (P.pair (C.comp P.snd P.fst) (C.comp P.snd P.snd))

def inTranspose {a b c d a' b' c' d' : O}
    (f : C.Hom (P.prod (P.prod a c) (P.prod b d)) (P.prod (P.prod a' c') (P.prod b' d'))) :
    C.Hom (P.prod (P.prod a b) (P.prod c d)) (P.prod (P.prod a' b') (P.prod c' d')) :=
  C.comp (transpose P) (C.comp f (transpose P))

def constants (T : TerminalOps C) {a b : O} (f : C.Hom T.unit a) (g : C.Hom T.unit b) :
    C.Hom T.unit (P.prod a b) := C.comp (tensor P f g) (insertLeft P T)
end Cartesian
end SquareKit
