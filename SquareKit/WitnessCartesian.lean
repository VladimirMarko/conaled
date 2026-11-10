import SquareKit.WitnessStructure
import SquareKit.CartesianOperations

namespace SquareKit.WitnessEquivalence
universe u v w
variable {O : Type u} {C : CategoryOps.{u,v} O} {E : WitnessEquivalence.{u,v,w} C}
variable {P : ProductOps C}

namespace ProductLaws
variable (L : ProductLaws E P) (K : E.Congr) (A : E.Laws) (G : ProductCongr E P)

def forward {a b c} {f : C.Hom a b} {g : C.Hom a c} {k : C.Hom a (P.prod b c)}
    (h : E.Rel k (P.pair f g)) :
    E.Rel (C.comp P.fst k) f × E.Rel (C.comp P.snd k) g :=
  ⟨E.trans (K.comp (E.refl _) h) (L.fst_pair _ _),
   E.trans (K.comp (E.refl _) h) (L.snd_pair _ _)⟩

def backward {a b c} {f : C.Hom a b} {g : C.Hom a c} {k : C.Hom a (P.prod b c)}
    (h : E.Rel (C.comp P.fst k) f × E.Rel (C.comp P.snd k) g) : E.Rel k (P.pair f g) :=
  E.trans (E.symm (L.pair_eta _)) (G.pair h.1 h.2)

def pair_comp {a b c x} (f : C.Hom a b) (g : C.Hom a c) (h : C.Hom x a) :
    E.Rel (C.comp (P.pair f g) h) (P.pair (C.comp f h) (C.comp g h)) :=
  L.backward G ⟨E.trans (E.symm (A.assoc _ _ _)) (K.comp (L.fst_pair _ _) (E.refl _)),
    E.trans (E.symm (A.assoc _ _ _)) (K.comp (L.snd_pair _ _) (E.refl _))⟩

def projections {a b} : E.Rel (P.pair (P.fst (a := a) (b := b)) P.snd) C.ident :=
  E.trans (G.pair (E.symm (A.comp_id _)) (E.symm (A.comp_id _))) (L.pair_eta _)

end ProductLaws

namespace Cartesian
open SquareKit.Cartesian
variable (K : E.Congr) (A : E.Laws) (G : ProductCongr E P) (L : ProductLaws E P)

def tensor_congr {a b c d} {f f' : C.Hom a c} {g g' : C.Hom b d}
    (h : E.Rel f f') (k : E.Rel g g') : E.Rel (tensor P f g) (tensor P f' g') :=
  G.pair (K.comp h (E.refl _)) (K.comp k (E.refl _))

def fst_tensor {a b c d} (f : C.Hom a c) (g : C.Hom b d) :
    E.Rel (C.comp P.fst (tensor P f g)) (C.comp f P.fst) := L.fst_pair _ _
def snd_tensor {a b c d} (f : C.Hom a c) (g : C.Hom b d) :
    E.Rel (C.comp P.snd (tensor P f g)) (C.comp g P.snd) := L.snd_pair _ _

def tensor_ident (a b : O) :
    E.Rel (tensor P (C.ident (a := a)) (C.ident (a := b))) C.ident :=
  E.trans (G.pair (A.id_comp _) (A.id_comp _)) (L.projections A G)

def tensor_pair {a b c d x} (f : C.Hom a c) (g : C.Hom b d)
    (h : C.Hom x a) (k : C.Hom x b) :
    E.Rel (C.comp (tensor P f g) (P.pair h k)) (P.pair (C.comp f h) (C.comp g k)) :=
  E.trans (L.pair_comp K A G _ _ _)
    (G.pair (E.trans (A.assoc _ _ _) (K.comp (E.refl _) (L.fst_pair _ _)))
      (E.trans (A.assoc _ _ _) (K.comp (E.refl _) (L.snd_pair _ _))))

def tensor_comp {a b c d e f} (h : C.Hom c e) (k : C.Hom d f)
    (f : C.Hom a c) (g : C.Hom b d) :
    E.Rel (C.comp (tensor P h k) (tensor P f g)) (tensor P (C.comp h f) (C.comp k g)) :=
  E.trans (tensor_pair K A G L _ _ _ _)
    (G.pair (E.symm (A.assoc _ _ _)) (E.symm (A.assoc _ _ _)))

def fst_swap (a b : O) : E.Rel (C.comp P.fst (swap P (a := a) (b := b))) P.snd :=
  L.fst_pair _ _
def snd_swap (a b : O) : E.Rel (C.comp P.snd (swap P (a := a) (b := b))) P.fst :=
  L.snd_pair _ _
def swap_pair {a b x} (f : C.Hom x a) (g : C.Hom x b) :
    E.Rel (C.comp (swap P) (P.pair f g)) (P.pair g f) :=
  E.trans (L.pair_comp K A G _ _ _) (G.pair (L.snd_pair _ _) (L.fst_pair _ _))
def swap_swap (a b : O) : E.Rel (C.comp (swap P (a := b) (b := a)) (swap P)) C.ident :=
  E.trans (swap_pair K A G L _ _) (L.projections A G)

def fst_first {a b c} (f : C.Hom a c) :
    E.Rel (C.comp P.fst (first P (b := b) f)) (C.comp f P.fst) := L.fst_pair _ _
def snd_first {a b c} (f : C.Hom a c) :
    E.Rel (C.comp P.snd (first P (b := b) f)) P.snd :=
  E.trans (L.snd_pair _ _) (A.id_comp _)
def fst_second {a b c} (f : C.Hom b c) :
    E.Rel (C.comp P.fst (second P (a := a) f)) P.fst :=
  E.trans (L.fst_pair _ _) (A.id_comp _)
def snd_second {a b c} (f : C.Hom b c) :
    E.Rel (C.comp P.snd (second P (a := a) f)) (C.comp f P.snd) := L.snd_pair _ _
def first_pair {a b c x} (f : C.Hom a c) (h : C.Hom x a) (k : C.Hom x b) :
    E.Rel (C.comp (first P f) (P.pair h k)) (P.pair (C.comp f h) k) :=
  E.trans (tensor_pair K A G L _ _ _ _) (G.pair (E.refl _) (A.id_comp _))
def second_pair {a b c x} (g : C.Hom b c) (h : C.Hom x a) (k : C.Hom x b) :
    E.Rel (C.comp (second P g) (P.pair h k)) (P.pair h (C.comp g k)) :=
  E.trans (tensor_pair K A G L _ _ _ _) (G.pair (A.id_comp _) (E.refl _))
def first_tensor {a b c d e} (h : C.Hom c e) (f : C.Hom a c) (g : C.Hom b d) :
    E.Rel (C.comp (first P h) (tensor P f g)) (tensor P (C.comp h f) g) :=
  E.trans (tensor_comp K A G L _ _ _ _) (tensor_congr K G (E.refl _) (A.id_comp _))
def tensor_first {a b c d e} (h : C.Hom c d) (k : C.Hom b e) (f : C.Hom a c) :
    E.Rel (C.comp (tensor P h k) (first P f)) (tensor P (C.comp h f) k) :=
  E.trans (tensor_comp K A G L _ _ _ _) (tensor_congr K G (E.refl _) (A.comp_id _))
def tensor_second {a b c d e} (h : C.Hom a d) (k : C.Hom c e) (g : C.Hom b c) :
    E.Rel (C.comp (tensor P h k) (second P g)) (tensor P h (C.comp k g)) :=
  E.trans (tensor_comp K A G L _ _ _ _) (tensor_congr K G (A.comp_id _) (E.refl _))
def second_tensor {a b c d e} (k : C.Hom d e) (f : C.Hom a c) (g : C.Hom b d) :
    E.Rel (C.comp (second P k) (tensor P f g)) (tensor P f (C.comp k g)) :=
  E.trans (tensor_comp K A G L _ _ _ _) (tensor_congr K G (A.id_comp _) (E.refl _))
def first_comp {a b c d} (h : C.Hom c d) (f : C.Hom a c) :
    E.Rel (C.comp (first P (b := b) h) (first P f)) (first P (C.comp h f)) :=
  E.trans (tensor_comp K A G L _ _ _ _) (tensor_congr K G (E.refl _) (A.id_comp _))
def second_comp {a b c d} (k : C.Hom c d) (g : C.Hom b c) :
    E.Rel (C.comp (second P (a := a) k) (second P g)) (second P (C.comp k g)) :=
  E.trans (tensor_comp K A G L _ _ _ _) (tensor_congr K G (A.id_comp _) (E.refl _))
def first_second {a b c d} (f : C.Hom a c) (g : C.Hom b d) :
    E.Rel (C.comp (first P f) (second P g)) (tensor P f g) :=
  E.trans (tensor_comp K A G L _ _ _ _) (tensor_congr K G (A.comp_id _) (A.id_comp _))
def second_first {a b c d} (f : C.Hom a c) (g : C.Hom b d) :
    E.Rel (C.comp (second P g) (first P f)) (tensor P f g) :=
  E.trans (tensor_comp K A G L _ _ _ _) (tensor_congr K G (A.id_comp _) (A.comp_id _))
def unitLeft_insertLeft (T : TerminalOps C) (a : O) :
    E.Rel (C.comp (unitLeft P T) (insertLeft P T (a := a))) C.ident := L.snd_pair _ _
def unitRight_insertRight (T : TerminalOps C) (a : O) :
    E.Rel (C.comp (unitRight P T) (insertRight P T (a := a))) C.ident := L.fst_pair _ _
def insertLeft_unitLeft (T : TerminalOps C) (TL : TerminalLaws E T) (a : O) :
    E.Rel (C.comp (insertLeft P T) (unitLeft P T (a := a))) C.ident :=
  E.trans (L.pair_comp K A G _ _ _)
    (E.trans (G.pair (E.trans (TL.unique _) (E.symm (TL.unique _))) (A.id_comp _))
      (L.projections A G))
def insertRight_unitRight (T : TerminalOps C) (TL : TerminalLaws E T) (a : O) :
    E.Rel (C.comp (insertRight P T) (unitRight P T (a := a))) C.ident :=
  E.trans (L.pair_comp K A G _ _ _)
    (E.trans (G.pair (A.id_comp _) (E.trans (TL.unique _) (E.symm (TL.unique _))))
      (L.projections A G))

def tensor_inverse {a b c d} {f : C.Hom a c} {fi : C.Hom c a}
    {g : C.Hom b d} {gi : C.Hom d b}
    (hf : E.Rel (C.comp fi f) C.ident) (hg : E.Rel (C.comp gi g) C.ident) :
    E.Rel (C.comp (tensor P fi gi) (tensor P f g)) C.ident :=
  E.trans (tensor_comp K A G L _ _ _ _)
    (E.trans (tensor_congr K G hf hg) (tensor_ident A G L _ _))
def first_inverse {a b c} {f : C.Hom a c} {fi : C.Hom c a}
    (h : E.Rel (C.comp fi f) C.ident) :
    E.Rel (C.comp (first P (b := b) fi) (first P f)) C.ident :=
  tensor_inverse K A G L h (A.id_comp _)
def second_inverse {a b c} {g : C.Hom b c} {gi : C.Hom c b}
    (h : E.Rel (C.comp gi g) C.ident) :
    E.Rel (C.comp (second P (a := a) gi) (second P g)) C.ident :=
  tensor_inverse K A G L (A.id_comp _) h

end Cartesian
end SquareKit.WitnessEquivalence
