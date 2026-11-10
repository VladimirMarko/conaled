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

end Cartesian
end SquareKit.WitnessEquivalence
