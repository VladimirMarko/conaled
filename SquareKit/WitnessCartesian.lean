import SquareKit.WitnessStructure
import SquareKit.CartesianOperations

namespace SquareKit.WitnessEquivalence
universe u v w
variable {O : Type u} {C : CategoryOps.{u,v} O} {E : WitnessEquivalence.{u,v,w} C}
variable {P : ProductOps C}

namespace ProductLaws
variable (L : ProductLaws E P) (K : E.Congr) (A : E.Laws) (G : ProductCongr E P)

def projectionWitnesses {a b c} {f : C.Hom a b} {g : C.Hom a c} {k : C.Hom a (P.prod b c)}
    (h : E.Rel k (P.pair f g)) :
    E.Rel (C.comp P.fst k) f × E.Rel (C.comp P.snd k) g :=
  ⟨E.trans (K.comp (E.refl _) h) (L.fstPair _ _),
   E.trans (K.comp (E.refl _) h) (L.sndPair _ _)⟩

def pairWitness {a b c} {f : C.Hom a b} {g : C.Hom a c} {k : C.Hom a (P.prod b c)}
    (h : E.Rel (C.comp P.fst k) f × E.Rel (C.comp P.snd k) g) : E.Rel k (P.pair f g) :=
  E.trans (E.symm (L.pairEta _)) (G.pair h.1 h.2)

def pairComp {a b c x} (f : C.Hom a b) (g : C.Hom a c) (h : C.Hom x a) :
    E.Rel (C.comp (P.pair f g) h) (P.pair (C.comp f h) (C.comp g h)) :=
  L.pairWitness G ⟨E.trans (E.symm (A.assoc _ _ _)) (K.comp (L.fstPair _ _) (E.refl _)),
    E.trans (E.symm (A.assoc _ _ _)) (K.comp (L.sndPair _ _) (E.refl _))⟩

def pairProjections {a b} : E.Rel (P.pair (P.fst (a := a) (b := b)) P.snd) C.ident :=
  E.trans (G.pair (E.symm (A.compIdent _)) (E.symm (A.compIdent _))) (L.pairEta _)

end ProductLaws

namespace Cartesian
open SquareKit.Cartesian
variable (K : E.Congr) (A : E.Laws) (G : ProductCongr E P) (L : ProductLaws E P)

def tensorCongr {a b c d} {f f' : C.Hom a c} {g g' : C.Hom b d}
    (h : E.Rel f f') (k : E.Rel g g') : E.Rel (tensor P f g) (tensor P f' g') :=
  G.pair (K.comp h (E.refl _)) (K.comp k (E.refl _))

def fstTensor {a b c d} (f : C.Hom a c) (g : C.Hom b d) :
    E.Rel (C.comp P.fst (tensor P f g)) (C.comp f P.fst) := L.fstPair _ _
def sndTensor {a b c d} (f : C.Hom a c) (g : C.Hom b d) :
    E.Rel (C.comp P.snd (tensor P f g)) (C.comp g P.snd) := L.sndPair _ _

def tensorIdent (a b : O) :
    E.Rel (tensor P (C.ident (a := a)) (C.ident (a := b))) C.ident :=
  E.trans (G.pair (A.identComp _) (A.identComp _)) (L.pairProjections A G)

def tensorPair {a b c d x} (f : C.Hom a c) (g : C.Hom b d)
    (h : C.Hom x a) (k : C.Hom x b) :
    E.Rel (C.comp (tensor P f g) (P.pair h k)) (P.pair (C.comp f h) (C.comp g k)) :=
  E.trans (L.pairComp K A G _ _ _)
    (G.pair (E.trans (A.assoc _ _ _) (K.comp (E.refl _) (L.fstPair _ _)))
      (E.trans (A.assoc _ _ _) (K.comp (E.refl _) (L.sndPair _ _))))

def tensorComp {a b c d e f} (h : C.Hom c e) (k : C.Hom d f)
    (f : C.Hom a c) (g : C.Hom b d) :
    E.Rel (C.comp (tensor P h k) (tensor P f g)) (tensor P (C.comp h f) (C.comp k g)) :=
  E.trans (tensorPair K A G L _ _ _ _)
    (G.pair (E.symm (A.assoc _ _ _)) (E.symm (A.assoc _ _ _)))

def fstSwap (a b : O) : E.Rel (C.comp P.fst (swap P (a := a) (b := b))) P.snd :=
  L.fstPair _ _
def sndSwap (a b : O) : E.Rel (C.comp P.snd (swap P (a := a) (b := b))) P.fst :=
  L.sndPair _ _
def swapPair {a b x} (f : C.Hom x a) (g : C.Hom x b) :
    E.Rel (C.comp (swap P) (P.pair f g)) (P.pair g f) :=
  E.trans (L.pairComp K A G _ _ _) (G.pair (L.sndPair _ _) (L.fstPair _ _))
def swapSwap (a b : O) : E.Rel (C.comp (swap P (a := b) (b := a)) (swap P)) C.ident :=
  E.trans (swapPair K A G L _ _) (L.pairProjections A G)

def fstFirst {a b c} (f : C.Hom a c) :
    E.Rel (C.comp P.fst (first P (b := b) f)) (C.comp f P.fst) := L.fstPair _ _
def sndFirst {a b c} (f : C.Hom a c) :
    E.Rel (C.comp P.snd (first P (b := b) f)) P.snd :=
  E.trans (L.sndPair _ _) (A.identComp _)
def fstSecond {a b c} (f : C.Hom b c) :
    E.Rel (C.comp P.fst (second P (a := a) f)) P.fst :=
  E.trans (L.fstPair _ _) (A.identComp _)
def sndSecond {a b c} (f : C.Hom b c) :
    E.Rel (C.comp P.snd (second P (a := a) f)) (C.comp f P.snd) := L.sndPair _ _
def firstPair {a b c x} (f : C.Hom a c) (h : C.Hom x a) (k : C.Hom x b) :
    E.Rel (C.comp (first P f) (P.pair h k)) (P.pair (C.comp f h) k) :=
  E.trans (tensorPair K A G L _ _ _ _) (G.pair (E.refl _) (A.identComp _))
def secondPair {a b c x} (g : C.Hom b c) (h : C.Hom x a) (k : C.Hom x b) :
    E.Rel (C.comp (second P g) (P.pair h k)) (P.pair h (C.comp g k)) :=
  E.trans (tensorPair K A G L _ _ _ _) (G.pair (A.identComp _) (E.refl _))
def firstTensor {a b c d e} (h : C.Hom c e) (f : C.Hom a c) (g : C.Hom b d) :
    E.Rel (C.comp (first P h) (tensor P f g)) (tensor P (C.comp h f) g) :=
  E.trans (tensorComp K A G L _ _ _ _) (tensorCongr K G (E.refl _) (A.identComp _))
def tensorFirst {a b c d e} (h : C.Hom c d) (k : C.Hom b e) (f : C.Hom a c) :
    E.Rel (C.comp (tensor P h k) (first P f)) (tensor P (C.comp h f) k) :=
  E.trans (tensorComp K A G L _ _ _ _) (tensorCongr K G (E.refl _) (A.compIdent _))
def tensorSecond {a b c d e} (h : C.Hom a d) (k : C.Hom c e) (g : C.Hom b c) :
    E.Rel (C.comp (tensor P h k) (second P g)) (tensor P h (C.comp k g)) :=
  E.trans (tensorComp K A G L _ _ _ _) (tensorCongr K G (A.compIdent _) (E.refl _))
def secondTensor {a b c d e} (k : C.Hom d e) (f : C.Hom a c) (g : C.Hom b d) :
    E.Rel (C.comp (second P k) (tensor P f g)) (tensor P f (C.comp k g)) :=
  E.trans (tensorComp K A G L _ _ _ _) (tensorCongr K G (A.identComp _) (E.refl _))
def firstComp {a b c d} (h : C.Hom c d) (f : C.Hom a c) :
    E.Rel (C.comp (first P (b := b) h) (first P f)) (first P (C.comp h f)) :=
  E.trans (tensorComp K A G L _ _ _ _) (tensorCongr K G (E.refl _) (A.identComp _))
def secondComp {a b c d} (k : C.Hom c d) (g : C.Hom b c) :
    E.Rel (C.comp (second P (a := a) k) (second P g)) (second P (C.comp k g)) :=
  E.trans (tensorComp K A G L _ _ _ _) (tensorCongr K G (A.identComp _) (E.refl _))
def firstSecond {a b c d} (f : C.Hom a c) (g : C.Hom b d) :
    E.Rel (C.comp (first P f) (second P g)) (tensor P f g) :=
  E.trans (tensorComp K A G L _ _ _ _) (tensorCongr K G (A.compIdent _) (A.identComp _))
def secondFirst {a b c d} (f : C.Hom a c) (g : C.Hom b d) :
    E.Rel (C.comp (second P g) (first P f)) (tensor P f g) :=
  E.trans (tensorComp K A G L _ _ _ _) (tensorCongr K G (A.identComp _) (A.compIdent _))
def unitLeftInsertLeft (T : TerminalOps C) (a : O) :
    E.Rel (C.comp (unitLeft P T) (insertLeft P T (a := a))) C.ident := L.sndPair _ _
def unitRightInsertRight (T : TerminalOps C) (a : O) :
    E.Rel (C.comp (unitRight P T) (insertRight P T (a := a))) C.ident := L.fstPair _ _
def insertLeftUnitLeft (T : TerminalOps C) (TL : TerminalLaws E T) (a : O) :
    E.Rel (C.comp (insertLeft P T) (unitLeft P T (a := a))) C.ident :=
  E.trans (L.pairComp K A G _ _ _)
    (E.trans (G.pair (E.trans (TL.unique _) (E.symm (TL.unique _))) (A.identComp _))
      (L.pairProjections A G))
def insertRightUnitRight (T : TerminalOps C) (TL : TerminalLaws E T) (a : O) :
    E.Rel (C.comp (insertRight P T) (unitRight P T (a := a))) C.ident :=
  E.trans (L.pairComp K A G _ _ _)
    (E.trans (G.pair (A.identComp _) (E.trans (TL.unique _) (E.symm (TL.unique _))))
      (L.pairProjections A G))

def tensorLeftInverse {a b c d} {f : C.Hom a c} {fi : C.Hom c a}
    {g : C.Hom b d} {gi : C.Hom d b}
    (hf : E.Rel (C.comp fi f) C.ident) (hg : E.Rel (C.comp gi g) C.ident) :
    E.Rel (C.comp (tensor P fi gi) (tensor P f g)) C.ident :=
  E.trans (tensorComp K A G L _ _ _ _)
    (E.trans (tensorCongr K G hf hg) (tensorIdent A G L _ _))
def firstLeftInverse {a b c} {f : C.Hom a c} {fi : C.Hom c a}
    (h : E.Rel (C.comp fi f) C.ident) :
    E.Rel (C.comp (first P (b := b) fi) (first P f)) C.ident :=
  tensorLeftInverse K A G L h (A.identComp _)
def secondLeftInverse {a b c} {g : C.Hom b c} {gi : C.Hom c b}
    (h : E.Rel (C.comp gi g) C.ident) :
    E.Rel (C.comp (second P (a := a) gi) (second P g)) C.ident :=
  tensorLeftInverse K A G L (A.identComp _) h

end Cartesian
end SquareKit.WitnessEquivalence
