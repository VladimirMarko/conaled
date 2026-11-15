import SquareKit.WitnessCoproductMap
import SquareKit.OptionalComparison

namespace SquareKit.WitnessEquivalence
universe u v
variable {O : Type u} {C : CategoryOps.{u,v} O} {E : WitnessEquivalence C}

namespace ProductOps
variable (P : ProductOps C)

def rightMap_congr (CC : Congr E) (PC : ProductCongr E P)
    {a b c} {f g : C.Hom b c} (h : E.Rel f g) :
    E.Rel (P.rightMap (a := a) f) (P.rightMap g) :=
  PC.pair (E.refl _) (CC.comp h (E.refl _))

def rightMap_comp (CC : Congr E) (CL : Laws E)
    (PC : ProductCongr E P) (PL : ProductLaws E P)
    {a b c d} (g : C.Hom c d) (f : C.Hom b c) :
    E.Rel (C.comp (P.rightMap (a := a) g) (P.rightMap f)) (P.rightMap (C.comp g f)) := by
  apply E.trans (PL.pair_comp CC CL PC _ _ _)
  apply PC.pair (PL.fst_pair _ _)
  exact E.trans (CL.assoc _ _ _) (E.trans (CC.comp (E.refl _) (PL.snd_pair _ _))
    (E.symm (CL.assoc _ _ _)))

def rightMap_pair (CC : Congr E) (CL : Laws E)
    (PC : ProductCongr E P) (PL : ProductLaws E P)
    {a b c d} (h : C.Hom b c) (f : C.Hom d a) (g : C.Hom d b) :
    E.Rel (C.comp (P.rightMap h) (P.pair f g)) (P.pair f (C.comp h g)) :=
  E.trans (PL.pair_comp CC CL PC _ _ _)
    (PC.pair (PL.fst_pair _ _) (E.trans (CL.assoc _ _ _)
      (CC.comp (E.refl _) (PL.snd_pair _ _))))

def rightMap_id (_CC : Congr E) (CL : Laws E)
    (PC : ProductCongr E P) (PL : ProductLaws E P) (a b : O) :
    E.Rel (P.rightMap (a := a) (C.ident (a := b))) C.ident :=
  E.trans (PC.pair (E.refl _) (CL.id_comp _))
    (E.trans (PC.pair (E.symm (CL.comp_id _)) (E.symm (CL.comp_id _))) (PL.pair_eta _))
end ProductOps

namespace CoproductOps
variable (S : CoproductOps C)

def map_congr (CC : Congr E) (SC : CoproductCongr E S)
    {a b c d} {f f' : C.Hom a c} {g g' : C.Hom b d} (hf : E.Rel f f') (hg : E.Rel g g') :
    E.Rel (S.map f g) (S.map f' g') :=
  SC.copair (CC.comp (E.refl _) hf) (CC.comp (E.refl _) hg)

def map_comp (CC : Congr E) (CL : Laws E)
    (SC : CoproductCongr E S) (SL : CoproductLaws E S)
    {a b c d e f} (g : C.Hom c e) (h : C.Hom d f) (i : C.Hom a c) (j : C.Hom b d) :
    E.Rel (C.comp (S.map g h) (S.map i j)) (S.map (C.comp g i) (C.comp h j)) := by
  apply E.trans (SL.comp_copair CC CL SC _ _ _)
  apply SC.copair
  · exact E.trans (E.symm (CL.assoc _ _ _))
      (E.trans (CC.comp (SL.left _ _) (E.refl _)) (CL.assoc _ _ _))
  · exact E.trans (E.symm (CL.assoc _ _ _))
      (E.trans (CC.comp (SL.right _ _) (E.refl _)) (CL.assoc _ _ _))

def map_id (_CC : Congr E) (CL : Laws E)
    (SC : CoproductCongr E S) (SL : CoproductLaws E S) (a b : O) :
    E.Rel (S.map (C.ident (a := a)) (C.ident (a := b))) C.ident :=
  E.trans (SC.copair (CL.comp_id _) (CL.comp_id _))
    (E.trans (SC.copair (E.symm (CL.id_comp _)) (E.symm (CL.id_comp _))) (SL.eta _))
end CoproductOps

namespace Comparison


def productRight_laws (CC : Congr E) (CL : Laws E)
    {P : ProductOps C} (PC : ProductCongr E P) (PL : ProductLaws E P)
    (a : O) {b c : O} {i : Comparison C b c} (I : ComparisonLaws E i) :
    ComparisonLaws E (SquareKit.Comparison.productRight P a i) where
  hom_inv := E.trans (ProductOps.rightMap_comp P CC CL PC PL _ _)
    (E.trans (ProductOps.rightMap_congr P CC PC I.hom_inv) (ProductOps.rightMap_id P CC CL PC PL _ _))
  inv_hom := E.trans (ProductOps.rightMap_comp P CC CL PC PL _ _)
    (E.trans (ProductOps.rightMap_congr P CC PC I.inv_hom) (ProductOps.rightMap_id P CC CL PC PL _ _))


def coproduct_laws (CC : Congr E) (CL : Laws E)
    {S : CoproductOps C} (SC : CoproductCongr E S) (SL : CoproductLaws E S)
    {a b c d : O} {i : Comparison C a b} {j : Comparison C c d}
    (I : ComparisonLaws E i) (J : ComparisonLaws E j) : ComparisonLaws E (SquareKit.Comparison.coproduct S i j) where
  hom_inv := E.trans (CoproductOps.map_comp S CC CL SC SL _ _ _ _)
    (E.trans (CoproductOps.map_congr S CC SC I.hom_inv J.hom_inv) (CoproductOps.map_id S CC CL SC SL _ _))
  inv_hom := E.trans (CoproductOps.map_comp S CC CL SC SL _ _ _ _)
    (E.trans (CoproductOps.map_congr S CC SC I.inv_hom J.inv_hom) (CoproductOps.map_id S CC CL SC SL _ _))
/-- Transport an arrow between independently chosen object presentations. -/

def conjugate_congr (CC : Congr E)
    {a a' b b' : O} (i : Comparison C a a') (j : Comparison C b b')
    {f g : C.Hom a' b'} (h : E.Rel f g) : E.Rel (SquareKit.Comparison.conjugate i j f) (SquareKit.Comparison.conjugate i j g) :=
  CC.comp (E.refl _) (CC.comp h (E.refl _))

def conjugate_comp (CC : Congr E) (CL : Laws E)
    {a a' b b' c c' : O} (i : Comparison C a a') (j : Comparison C b b')
    (k : Comparison C c c') (J : ComparisonLaws E j)
    (g : C.Hom b' c') (f : C.Hom a' b') :
    E.Rel (C.comp (SquareKit.Comparison.conjugate j k g) (SquareKit.Comparison.conjugate i j f)) (SquareKit.Comparison.conjugate i k (C.comp g f)) :=
  E.trans (CL.assoc _ _ _)
    (E.trans (CC.comp (E.refl _) (CL.cancel_middle CC J.hom_inv _ _))
      (CC.comp (E.refl _) (E.symm (CL.assoc _ _ _))))

def conjugate_id (CC : Congr E) (CL : Laws E)
    {a b : O} (i : Comparison C a b) (I : ComparisonLaws E i) :
    E.Rel (SquareKit.Comparison.conjugate i i C.ident) C.ident :=
  E.trans (CC.comp (E.refl _) (CL.id_comp _)) I.inv_hom

/-- A right inverse and a left inverse of the same arrow agree. -/
def inverse_unique (CC : Congr E) (CL : Laws E)
    {a b : O} {f g : C.Hom a b} {h : C.Hom b a}
    (hf : E.Rel (C.comp f h) C.ident) (hg : E.Rel (C.comp h g) C.ident) : E.Rel f g :=
  E.trans (E.symm (CL.comp_id _))
    (E.trans (CC.comp (E.refl _) (E.symm hg))
      (E.trans (E.symm (CL.assoc _ _ _))
        (E.trans (CC.comp hf (E.refl _)) (CL.id_comp _))))

end Comparison
namespace RawMap
universe u₂ v₂
variable {Q : Type u₂} {D : CategoryOps.{u₂,v₂} Q}

/-- Reflect inverse laws after comparing the source objects with the target
objects. The premises preserve the two arrows, not their final inverse laws. -/
def transportComparisonLaws {F : RawMap C D} {H : WitnessEquivalence D}
    (L : Preservation F E H) (R : Reflection F E H)
    (DC : Congr H) (DL : Laws H)
    {a b : O} {a' b' : Q} (p : Comparison D (F.obj a) a')
    (q : Comparison D (F.obj b) b') (P : ComparisonLaws H p) (Q : ComparisonLaws H q)
    (s : Comparison C a b) (t : Comparison D a' b') (T : ComparisonLaws H t)
    (hf : H.Rel (F.map s.hom) (Comparison.conjugate p q t.hom))
    (hg : H.Rel (F.map s.inv) (Comparison.conjugate q p t.inv)) : ComparisonLaws E s where
  hom_inv := R (H.trans (L.comp _ _) (H.trans (DC.comp hf hg)
    (H.trans (Comparison.conjugate_comp DC DL q p q P _ _)
      (H.trans (Comparison.conjugate_congr DC q q T.hom_inv)
        (H.trans (Comparison.conjugate_id DC DL q Q) (H.symm L.ident))))))
  inv_hom := R (H.trans (L.comp _ _) (H.trans (DC.comp hg hf)
    (H.trans (Comparison.conjugate_comp DC DL p q p Q _ _)
      (H.trans (Comparison.conjugate_congr DC p p T.inv_hom)
        (H.trans (Comparison.conjugate_id DC DL p P) (H.symm L.ident))))))
end RawMap

end SquareKit.WitnessEquivalence
