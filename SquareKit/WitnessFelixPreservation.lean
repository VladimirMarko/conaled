import SquareKit.WitnessCartesianPreservation
import SquareKit.WitnessInitialMap
import SquareKit.WitnessOptionalMap
import SquareKit.WitnessUniversal

namespace SquareKit.WitnessEquivalence
universe u v u' v' u'' v''
variable {O : Type u} {Q : Type u'} {C : CategoryOps.{u,v} O} {D : CategoryOps.{u',v'} Q}
variable {F : RawMap C D} {H : WitnessEquivalence D}

/-- Felix's primitive projection squares, before solving for the image arrow. -/
structure CartesianH {P : ProductOps C} {T : ProductOps D} (i : ProductMap F P T) where
  fst : ∀ a b, H.Rel (D.comp (F.map (P.fst (a := a) (b := b))) (i a b).inv) T.fst
  snd : ∀ a b, H.Rel (D.comp (F.map (P.snd (a := a) (b := b))) (i a b).inv) T.snd
  pair : ∀ {a b c} (f : C.Hom a b) (g : C.Hom a c),
    H.Rel (F.map (P.pair f g)) (D.comp (i b c).inv (T.pair (F.map f) (F.map g)))

def Comparison.solve_right (K : H.Congr) (L : H.Laws) {a b c : Q}
    {i : Comparison D a b} (I : ComparisonLaws H i) {f : D.Hom a c} {g : D.Hom b c}
    (h : H.Rel (D.comp f i.inv) g) : H.Rel f (D.comp g i.hom) :=
  H.trans (H.symm (H.trans (K.comp (H.refl _) I.inv_hom) (L.comp_id _)))
    (H.trans (H.symm (L.assoc _ _ _)) (K.comp h (H.refl _)))

def CartesianH.normalized {P : ProductOps C} {T : ProductOps D} {i : ProductMap F P T}
    (M : CartesianH (H := H) i) (K : H.Congr) (L : H.Laws)
    (I : ∀ a b, ComparisonLaws H (i a b)) : ProductMapLaws H i where
  fst := Comparison.solve_right K L (I _ _) (M.fst _ _)
  snd := Comparison.solve_right K L (I _ _) (M.snd _ _)
  pair := M.pair

def ProductMapLaws.felix {P : ProductOps C} {T : ProductOps D} {i : ProductMap F P T}
    (M : ProductMapLaws H i) (K : H.Congr) (L : H.Laws)
    (I : ∀ a b, ComparisonLaws H (i a b)) : CartesianH (H := H) i where
  fst a b := H.trans (K.comp M.fst (H.refl _))
    (H.trans (L.assoc _ _ _) (H.trans (K.comp (H.refl _) (I a b).hom_inv) (L.comp_id _)))
  snd a b := H.trans (K.comp M.snd (H.refl _))
    (H.trans (L.assoc _ _ _) (H.trans (K.comp (H.refl _) (I a b).hom_inv) (L.comp_id _)))
  pair := M.pair

def CartesianH.id {P : ProductOps C} {E : WitnessEquivalence C} (L : E.Laws) :
    CartesianH (H := E) (SquareKit.ProductMap.id P) where
  fst _ _ := L.comp_id _
  snd _ _ := L.comp_id _
  pair _ _ := E.symm (L.id_comp _)

def CartesianH.compose {R : Type u''} {K : CategoryOps.{u'',v''} R}
    {G : RawMap D K} {J : WitnessEquivalence K} (LG : Preservation G H J)
    (KC : J.Congr) (KL : J.Laws) {P : ProductOps C} {T : ProductOps D} {U : ProductOps K}
    {i : ProductMap F P T} {j : ProductMap G T U}
    (M : CartesianH (H := H) i) (N : CartesianH (H := J) j) :
    CartesianH (H := J) (SquareKit.ProductMap.comp i j) where
  fst _ _ := J.trans (J.symm (KL.assoc _ _ _))
    (J.trans (KC.comp (J.symm (LG.comp _ _)) (J.refl _))
      (J.trans (KC.comp (LG.congr (M.fst _ _)) (J.refl _)) (N.fst _ _)))
  snd _ _ := J.trans (J.symm (KL.assoc _ _ _))
    (J.trans (KC.comp (J.symm (LG.comp _ _)) (J.refl _))
      (J.trans (KC.comp (LG.congr (M.snd _ _)) (J.refl _)) (N.snd _ _)))
  pair f g := J.trans (LG.congr (M.pair f g)) (J.trans (LG.comp _ _)
    (J.trans (KC.comp (J.refl _) (N.pair _ _)) (J.symm (KL.assoc _ _ _))))

structure CocartesianH {S : CoproductOps C} {T : CoproductOps D} (i : CoproductMap F S T) where
  inl : ∀ a b, H.Rel (D.comp (i a b).hom (F.map (S.inl (a := a) (b := b)))) T.inl
  inr : ∀ a b, H.Rel (D.comp (i a b).hom (F.map (S.inr (a := a) (b := b)))) T.inr
  copair : ∀ {a b c} (f : C.Hom a c) (g : C.Hom b c),
    H.Rel (F.map (S.copair f g)) (D.comp (T.copair (F.map f) (F.map g)) (i a b).hom)

def CocartesianH.normalized {S : CoproductOps C} {T : CoproductOps D}
    {i : CoproductMap F S T} (M : CocartesianH (H := H) i) (K : H.Congr) (L : H.Laws)
    (I : ∀ a b, ComparisonLaws H (i a b)) : CoproductMapLaws H i where
  inl := H.trans (H.symm (L.cancel_left K (I _ _).inv_hom _)) (K.comp (H.refl _) (M.inl _ _))
  inr := H.trans (H.symm (L.cancel_left K (I _ _).inv_hom _)) (K.comp (H.refl _) (M.inr _ _))
  copair := M.copair

def CoproductMapLaws.felix {S : CoproductOps C} {T : CoproductOps D}
    {i : CoproductMap F S T} (M : CoproductMapLaws H i) (K : H.Congr) (L : H.Laws)
    (I : ∀ a b, ComparisonLaws H (i a b)) : CocartesianH (H := H) i where
  inl _ _ := H.trans (K.comp (H.refl _) M.inl) (L.cancel_left K (I _ _).hom_inv _)
  inr _ _ := H.trans (K.comp (H.refl _) M.inr) (L.cancel_left K (I _ _).hom_inv _)
  copair := M.copair

def Preservation.induced {E : WitnessEquivalence C} (L : Preservation F E H) :
    Preservation F (WitnessEquivalence.induced F H) H :=
  ⟨fun h => h, L.ident, L.comp⟩
def inducedReflection : Reflection F (WitnessEquivalence.induced F H) H := fun h => h

def lawfulCategoryInduced {E : WitnessEquivalence C} (L : Preservation F E H)
    (K : H.Congr) (A : H.Laws) :
    (WitnessEquivalence.induced F H).Congr × (WitnessEquivalence.induced F H).Laws :=
  ⟨transportCongr L.induced inducedReflection K, transportLaws L.induced inducedReflection K A⟩

def lawfulCartesianInduced {E : WitnessEquivalence C} (L : Preservation F E H)
    (K : H.Congr) (A : H.Laws) {P : ProductOps C} {T : ProductOps D}
    {S : TerminalOps C} {U : TerminalOps D} {i : ProductMap F P T} {j : TerminalMap F S U}
    (I : ∀ a b, ComparisonLaws H (i a b)) (J : ComparisonLaws H j)
    (M : CartesianH (H := H) i) (N : TerminalMapLaws H j)
    (PC : ProductCongr H T) (PL : ProductLaws H T) (UL : TerminalLaws H U) :
    TerminalLaws (WitnessEquivalence.induced F H) S ×
      ProductCongr (WitnessEquivalence.induced F H) P ×
      ProductUniversal (E := WitnessEquivalence.induced F H) P := by
  let normalized := M.normalized K A I
  let congr := ProductMap.transportCongr L.induced inducedReflection K normalized PC
  let laws := ProductMap.transportLaws L.induced inducedReflection K A I normalized PC PL
  exact ⟨TerminalMap.transportLaws inducedReflection K A J N UL, congr,
    laws.universal (transportCongr L.induced inducedReflection K) congr⟩

end SquareKit.WitnessEquivalence
