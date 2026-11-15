import SquareKit.WitnessCartesian

namespace SquareKit.WitnessEquivalence
universe u₁ v₁ u₂ v₂ u₃ v₃

structure ComparisonLaws {O : Type u₁} {C : CategoryOps.{u₁,v₁} O}
    (E : WitnessEquivalence C) {a b : O} (i : Comparison C a b) where
  hom_inv : E.Rel (C.comp i.hom i.inv) C.ident
  inv_hom : E.Rel (C.comp i.inv i.hom) C.ident

namespace Comparison
variable {O : Type u₁} {P : Type u₂}
variable {C : CategoryOps.{u₁,v₁} O} {D : CategoryOps.{u₂,v₂} P}




def id_laws {E : WitnessEquivalence C} (L : Laws E) (a : O) :
    ComparisonLaws E (SquareKit.Comparison.id C a) := ⟨L.id_comp _, L.id_comp _⟩

def map_laws {F : RawMap C D} {E : WitnessEquivalence C} {H : WitnessEquivalence D}
    (L : Preservation F E H) {a b} {i : Comparison C a b} (I : ComparisonLaws E i) :
    ComparisonLaws H (i.map F) where
  hom_inv := H.trans (H.symm (L.comp _ _)) (H.trans (L.congr I.hom_inv) L.ident)
  inv_hom := H.trans (H.symm (L.comp _ _)) (H.trans (L.congr I.inv_hom) L.ident)
end Comparison

namespace Laws
variable {O : Type u₁} {C : CategoryOps.{u₁,v₁} O} {E : WitnessEquivalence C}

def cancel_left (K : Congr E) (L : Laws E) {a b c} {i : C.Hom b c} {j : C.Hom c b}
    (h : E.Rel (C.comp i j) C.ident) (f : C.Hom a c) :
    E.Rel (C.comp i (C.comp j f)) f :=
  E.trans (E.symm (L.assoc _ _ _)) (E.trans (K.comp h (E.refl _)) (L.id_comp _))

def cancel_middle (K : Congr E) (L : Laws E) {a b c d} {i : C.Hom b c} {j : C.Hom c b}
    (h : E.Rel (C.comp i j) C.ident) (g : C.Hom c d) (f : C.Hom a c) :
    E.Rel (C.comp (C.comp g i) (C.comp j f)) (C.comp g f) :=
  E.trans (L.assoc _ _ _) (K.comp (E.refl _) (L.cancel_left K h f))
end Laws

namespace Comparison
variable {O : Type u₁} {C : CategoryOps.{u₁,v₁} O} {E : WitnessEquivalence C}
def comp_laws (K : Congr E) (L : Laws E)
    {a b c} {i : Comparison C a b} {j : Comparison C b c}
    (I : ComparisonLaws E i) (J : ComparisonLaws E j) : ComparisonLaws E (i.comp j) where
  hom_inv := E.trans (L.cancel_middle K I.hom_inv _ _) J.hom_inv
  inv_hom := E.trans (L.cancel_middle K J.inv_hom _ _) I.inv_hom
end Comparison



structure TerminalMapLaws {O : Type u₁} {P : Type u₂}
    {C : CategoryOps.{u₁,v₁} O} {D : CategoryOps.{u₂,v₂} P}
    {F : RawMap C D} {T : TerminalOps C} {U : TerminalOps D}
    (H : WitnessEquivalence D) (i : TerminalMap F T U) where
  terminal : ∀ {a}, H.Rel (F.map (T.terminal (a := a))) (D.comp i.inv U.terminal)

structure ProductMapLaws {O : Type u₁} {P : Type u₂}
    {C : CategoryOps.{u₁,v₁} O} {D : CategoryOps.{u₂,v₂} P}
    {F : RawMap C D} {S : ProductOps C} {T : ProductOps D}
    (H : WitnessEquivalence D) (i : ProductMap F S T) where
  fst : ∀ {a b}, H.Rel (F.map (S.fst (a := a) (b := b))) (D.comp T.fst (i a b).hom)
  snd : ∀ {a b}, H.Rel (F.map (S.snd (a := a) (b := b))) (D.comp T.snd (i a b).hom)
  pair : ∀ {a b c} (f : C.Hom a b) (g : C.Hom a c),
    H.Rel (F.map (S.pair f g)) (D.comp (i b c).inv (T.pair (F.map f) (F.map g)))

namespace TerminalMap
variable {O : Type u₁} {P : Type u₂} {Q : Type u₃}
variable {C : CategoryOps.{u₁,v₁} O} {D : CategoryOps.{u₂,v₂} P} {K : CategoryOps.{u₃,v₃} Q}



def id_laws {E : WitnessEquivalence C} (L : Laws E) (T : TerminalOps C) :
    TerminalMapLaws E (SquareKit.TerminalMap.id T) where
  terminal := E.symm (L.id_comp _)

def comp_laws {F : RawMap C D} {G : RawMap D K}
    {H : WitnessEquivalence D} {J : WitnessEquivalence K} (LG : Preservation G H J)
    (KC : Congr J) (KL : Laws J)
    {T : TerminalOps C} {U : TerminalOps D} {V : TerminalOps K}
    {i : TerminalMap F T U} {j : TerminalMap G U V}
    (I : TerminalMapLaws H i) (JJ : TerminalMapLaws J j) : TerminalMapLaws J (SquareKit.TerminalMap.comp i j) where
  terminal := J.trans (LG.congr I.terminal) (J.trans (LG.comp _ _)
    (J.trans (KC.comp (J.refl _) JJ.terminal) (J.symm (KL.assoc _ _ _))))

def transportLaws {F : RawMap C D} {E : WitnessEquivalence C} {H : WitnessEquivalence D}
    (R : Reflection F E H) (DC : Congr H) (DL : Laws H)
    {T : TerminalOps C} {U : TerminalOps D} {i : TerminalMap F T U}
    (I : ComparisonLaws H i) (M : TerminalMapLaws H i) (UL : TerminalLaws H U) :
    TerminalLaws E T where
  unique f := R (H.trans (H.symm (DL.cancel_left DC I.inv_hom (F.map f)))
    (H.trans (DC.comp (H.refl _) (UL.unique _)) (H.symm M.terminal)))
end TerminalMap


namespace ProductMap
variable {O : Type u₁} {P : Type u₂} {Q : Type u₃}
variable {C : CategoryOps.{u₁,v₁} O} {D : CategoryOps.{u₂,v₂} P} {K : CategoryOps.{u₃,v₃} Q}



def id_laws {E : WitnessEquivalence C} (L : Laws E) (S : ProductOps C) :
    ProductMapLaws E (SquareKit.ProductMap.id S) where
  fst := E.symm (L.comp_id _)
  snd := E.symm (L.comp_id _)
  pair _ _ := E.symm (L.id_comp _)

def comp_laws {F : RawMap C D} {G : RawMap D K}
    {H : WitnessEquivalence D} {J : WitnessEquivalence K} (LG : Preservation G H J)
    (KC : Congr J) (KL : Laws J)
    {S : ProductOps C} {T : ProductOps D} {U : ProductOps K}
    {i : ProductMap F S T} {j : ProductMap G T U}
    (I : ProductMapLaws H i) (JJ : ProductMapLaws J j) : ProductMapLaws J (SquareKit.ProductMap.comp i j) where
  fst := J.trans (LG.congr I.fst) (J.trans (LG.comp _ _)
    (J.trans (KC.comp JJ.fst (J.refl _)) (KL.assoc _ _ _)))
  snd := J.trans (LG.congr I.snd) (J.trans (LG.comp _ _)
    (J.trans (KC.comp JJ.snd (J.refl _)) (KL.assoc _ _ _)))
  pair f g := J.trans (LG.congr (I.pair f g)) (J.trans (LG.comp _ _)
    (J.trans (KC.comp (J.refl _) (JJ.pair _ _)) (J.symm (KL.assoc _ _ _))))

def transportCongr {F : RawMap C D} {E : WitnessEquivalence C} {H : WitnessEquivalence D}
    (L : Preservation F E H) (R : Reflection F E H) (DC : Congr H)
    {S : ProductOps C} {T : ProductOps D} {i : ProductMap F S T}
    (M : ProductMapLaws H i) (TC : ProductCongr H T) : ProductCongr E S where
  pair hf hg := R (H.trans (M.pair _ _) (H.trans
    (DC.comp (H.refl _) (TC.pair (L.congr hf) (L.congr hg))) (H.symm (M.pair _ _))))

def transportLaws {F : RawMap C D} {E : WitnessEquivalence C} {H : WitnessEquivalence D}
    (L : Preservation F E H) (R : Reflection F E H)
    (DC : Congr H) (DL : Laws H)
    {S : ProductOps C} {T : ProductOps D} {i : ProductMap F S T}
    (I : ∀ a b, ComparisonLaws H (i a b)) (M : ProductMapLaws H i)
    (TC : ProductCongr H T) (TL : ProductLaws H T) : ProductLaws E S where
  fst_pair f g := R (H.trans (L.comp _ _) (H.trans (DC.comp M.fst (M.pair f g))
    (H.trans (DL.cancel_middle DC (I _ _).hom_inv _ _) (TL.fst_pair _ _))))
  snd_pair f g := R (H.trans (L.comp _ _) (H.trans (DC.comp M.snd (M.pair f g))
    (H.trans (DL.cancel_middle DC (I _ _).hom_inv _ _) (TL.snd_pair _ _))))
  pair_eta f := by
    apply R
    apply H.trans (M.pair _ _)
    apply H.trans (DC.comp (H.refl _) (TC.pair (L.comp _ _) (L.comp _ _)))
    apply H.trans (DC.comp (H.refl _) (TC.pair (DC.comp M.fst (H.refl _)) (DC.comp M.snd (H.refl _))))
    apply H.trans (DC.comp (H.refl _) (TC.pair (DL.assoc _ _ _) (DL.assoc _ _ _)))
    exact H.trans (DC.comp (H.refl _) (TL.pair_eta _)) (DL.cancel_left DC (I _ _).inv_hom _)
end ProductMap

variable {O : Type u₁} {Q : Type u₂} {R : Type u₃}
variable {C : CategoryOps.{u₁,v₁} O} {D : CategoryOps.{u₂,v₂} Q} {K : CategoryOps.{u₃,v₃} R}

def Preservation.id (E : WitnessEquivalence C) : Preservation (RawMap.id C) E E :=
  ⟨fun h => h, E.refl _, fun _ _ => E.refl _⟩
def Preservation.compose {E : WitnessEquivalence C} {H : WitnessEquivalence D}
    {J : WitnessEquivalence K} {F : RawMap C D} {G : RawMap D K}
    (L : Preservation F E H) (M : Preservation G H J) : Preservation (F.comp G) E J where
  congr h := M.congr (L.congr h)
  ident := J.trans (M.congr L.ident) M.ident
  comp g f := J.trans (M.congr (L.comp g f)) (M.comp _ _)

def transportCongr {F : RawMap C D} {E : WitnessEquivalence C} {H : WitnessEquivalence D}
    (L : Preservation F E H) (R : Reflection F E H) (K : H.Congr) : E.Congr where
  comp h k := R (H.trans (L.comp _ _)
    (H.trans (K.comp (L.congr h) (L.congr k)) (H.symm (L.comp _ _))))

theorem ComparisonLaws.erase {E : WitnessEquivalence C} {a b} {i : Comparison C a b}
    (L : ComparisonLaws E i) : SquareKit.ComparisonLaws E.erase i :=
  ⟨⟨L.hom_inv⟩, ⟨L.inv_hom⟩⟩
theorem TerminalMapLaws.erase {H : WitnessEquivalence D} {F : RawMap C D}
    {T : TerminalOps C} {U : TerminalOps D} {i : TerminalMap F T U}
    (L : TerminalMapLaws H i) : SquareKit.TerminalMapLaws H.erase i := ⟨⟨L.terminal⟩⟩
theorem ProductMapLaws.erase {H : WitnessEquivalence D} {F : RawMap C D}
    {S : ProductOps C} {T : ProductOps D} {i : ProductMap F S T}
    (L : ProductMapLaws H i) : SquareKit.ProductMapLaws H.erase i :=
  ⟨⟨L.fst⟩, ⟨L.snd⟩, fun f g => ⟨L.pair f g⟩⟩
end SquareKit.WitnessEquivalence
