import SquareKit.WitnessOptionalMap
import SquareKit.ClosedMap

namespace SquareKit.WitnessEquivalence
universe u₁ v₁ u₂ v₂ u₃ v₃

namespace ClosedOps
variable {O : Type u₁} {C : CategoryOps.{u₁,v₁} O} {E : WitnessEquivalence C}
variable {P : ProductOps C} (H : ClosedOps C P)

def uncurry_congr (CC : Congr E) (PC : ProductCongr E P)
    {x a b} {f g : C.Hom x (H.exp a b)} (h : E.Rel f g) :
    E.Rel (H.uncurry f) (H.uncurry g) :=
  CC.comp (E.refl _) (PC.pair (CC.comp h (E.refl _)) (E.refl _))

/-- Uncurrying commutes with substitution in the captured environment. -/
def uncurry_comp (CC : Congr E) (CL : Laws E)
    (PC : ProductCongr E P) (PL : ProductLaws E P)
    {x y a b} (f : C.Hom x (H.exp a b)) (g : C.Hom y x) :
    E.Rel (H.uncurry (C.comp f g))
      (C.comp (H.uncurry f) (P.pair (C.comp g P.fst) P.snd)) := by
  apply E.symm
  apply E.trans (CL.assoc _ _ _)
  apply CC.comp (E.refl _)
  apply E.trans (PL.pair_comp CC CL PC _ _ _)
  exact PC.pair
    (E.trans (CL.assoc _ _ _) (E.trans
      (CC.comp (E.refl _) (PL.fst_pair _ _)) (E.symm (CL.assoc _ _ _))))
    (PL.snd_pair _ _)
end ClosedOps

namespace ClosedLaws
variable {O : Type u₁} {C : CategoryOps.{u₁,v₁} O} {E : WitnessEquivalence C}
variable {P : ProductOps C} {H : ClosedOps C P}

/-- Beta and eta imply currying naturality; callers need no separate structural proof. -/
def ofBetaEta (CC : Congr E) (CL : Laws E)
    (PC : ProductCongr E P) (PL : ProductLaws E P) (HC : ClosedCongr E P H)
    (beta : ∀ {x a b} (f : C.Hom (P.prod x a) b), E.Rel (H.uncurry (H.curry f)) f)
    (eta : ∀ {x a b} (f : C.Hom x (H.exp a b)), E.Rel (H.curry (H.uncurry f)) f) :
    ClosedLaws E P H where
  beta := beta
  eta := eta
  natural f _g := E.trans (HC.curry (CC.comp (E.symm (beta f)) (E.refl _)))
    (E.trans (HC.curry (E.symm (ClosedOps.uncurry_comp H CC CL PC PL _ _))) (eta _))
end ClosedLaws

namespace ClosedMap
variable {O : Type u₁} {Q : Type u₂} {R : Type u₃}
variable {C : CategoryOps.{u₁,v₁} O} {D : CategoryOps.{u₂,v₂} Q}
variable {K : CategoryOps.{u₃,v₃} R}
variable {F : RawMap C D} {G : RawMap D K}
variable {P : ProductOps C} {T : ProductOps D} {U : ProductOps K}
variable {H : ClosedOps C P} {J : ClosedOps D T} {N : ClosedOps K U}
variable {E : WitnessEquivalence C} {V : WitnessEquivalence D}
variable {i : ProductMap F P T} {j : ClosedMap F H J}



def id_inverse (CL : Laws E) (a b : O) :
    ComparisonLaws E (SquareKit.ClosedMap.id H a b) := Comparison.id_laws CL _

def comp_inverse {W : WitnessEquivalence K} (LG : Preservation G V W)
    (KC : Congr W) (KL : Laws W)
    {k : ClosedMap G J N}
    (JJ : ∀ a b, ComparisonLaws V (j a b))
    (KK : ∀ a b, ComparisonLaws W (k a b)) (a b : O) :
    ComparisonLaws W (j.comp k a b) :=
  Comparison.comp_laws KC KL (Comparison.map_laws LG (JJ a b)) (KK _ _)

/-- Image of uncurrying, expressed on target product objects. -/
def uncurry (i : ProductMap F P T) (j : ClosedMap F H J) {x a b}
    (f : D.Hom (F.obj x) (F.obj (H.exp a b))) :=
  D.comp (J.uncurry (D.comp (j a b).hom f)) (i x a).hom

def transportCongr (L : Preservation F E V) (R : Reflection F E V)
    (DC : Congr V) (JC : ClosedCongr V T J) (M : ClosedMapLaws V i j) :
    ClosedCongr E P H where
  curry h := R (V.trans (M.curry _) (V.trans
    (DC.comp (V.refl _) (JC.curry (DC.comp (L.congr h) (V.refl _))))
    (V.symm (M.curry _))))

/-- Evaluation and product preservation already imply uncurrying preservation. -/
def map_uncurry (L : Preservation F E V)
    (DC : Congr V) (DL : Laws V)
    (TC : ProductCongr V T) (TL : ProductLaws V T)
    (I : ∀ a b, ComparisonLaws V (i a b))
    (PM : ProductMapLaws V i) (M : ClosedMapLaws V i j)
    {x a b} (f : C.Hom x (H.exp a b)) :
    V.Rel (F.map (H.uncurry f)) (j.uncurry i (F.map f)) := by
  apply V.trans (L.comp _ _)
  apply V.trans (DC.comp M.evaluation (PM.pair _ _))
  apply V.trans (DC.comp (V.symm (DL.assoc _ _ _)) (V.refl _))
  apply V.trans (DL.cancel_middle DC (I _ _).hom_inv _ _)
  apply V.trans (DL.assoc _ _ _)
  apply V.trans (DC.comp (V.refl _) (TL.pair_comp DC DL TC _ _ _))
  apply V.trans (DC.comp (V.refl _) (TC.pair
    (V.trans (DL.assoc _ _ _) (DC.comp (V.refl _) (TL.fst_pair _ _)))
    (TL.snd_pair _ _)))
  apply V.trans (DC.comp (V.refl _) (TC.pair
    (DC.comp (V.refl _) (V.trans (L.comp _ _) (DC.comp (V.refl _) PM.fst))) PM.snd))
  apply V.trans (DC.comp (V.refl _) (TC.pair
    (V.trans (V.symm (DL.assoc _ _ _)) (V.symm (DL.assoc _ _ _))) (V.refl _)))
  apply V.trans (DC.comp (V.refl _) (V.symm (TL.pair_comp DC DL TC _ _ _)))
  exact V.symm (DL.assoc _ _ _)

/-- Identity comparisons preserve the chosen operations modulo the selected laws. -/
def id_laws (CC : Congr E) (CL : Laws E)
    (PC : ProductCongr E P) (PL : ProductLaws E P) (HC : ClosedCongr E P H) :
    ClosedMapLaws E (ProductMap.id P) (SquareKit.ClosedMap.id H) where
  curry f := E.symm (E.trans (CL.id_comp _) (HC.curry (CL.comp_id f)))
  evaluation := by
    intro a b
    apply E.symm
    apply E.trans (CC.comp (E.refl _) (CL.comp_id _))
    apply E.trans (CC.comp (E.refl _) (PC.pair (CL.id_comp _) (E.refl _)))
    have h : E.Rel (P.pair (P.fst (a := H.exp a b) (b := a)) P.snd) C.ident :=
      E.trans (E.symm (PC.pair (CL.comp_id _) (CL.comp_id _))) (PL.pair_eta _)
    exact E.trans (CC.comp (E.refl _) h) (CL.comp_id _)

/-- Composition reuses the category and product comparisons, without source closed laws. -/
def comp_laws {W : WitnessEquivalence K} (LG : Preservation G V W)
    (KC : Congr W) (KL : Laws W)
    (UC : ProductCongr W U) (UL : ProductLaws W U) (NC : ClosedCongr W U N)
    {r : ProductMap G T U} {k : ClosedMap G J N}
    (RI : ∀ a b, ComparisonLaws W (r a b)) (RM : ProductMapLaws W r)
    (M : ClosedMapLaws V i j) (NN : ClosedMapLaws W r k) :
    ClosedMapLaws W (i.comp r) (j.comp k) where
  curry f := by
    apply W.trans (LG.congr (M.curry f))
    apply W.trans (LG.comp _ _)
    apply W.trans (KC.comp (W.refl _) (NN.curry _))
    apply W.trans (W.symm (KL.assoc _ _ _))
    apply KC.comp (W.refl _)
    apply NC.curry
    exact W.trans (KC.comp (LG.comp _ _) (W.refl _)) (KL.assoc _ _ _)
  evaluation := by
    intro a b
    apply W.trans (LG.congr M.evaluation)
    apply W.trans (LG.comp _ _)
    apply W.trans (KC.comp (W.refl _) (LG.comp _ _))
    apply W.trans (W.symm (KL.assoc _ _ _))
    apply W.trans (KC.comp (W.symm (LG.comp _ _)) (W.refl _))
    apply W.trans (KC.comp (map_uncurry LG KC KL UC UL RI RM NN _) (W.refl _))
    apply W.trans (KL.assoc _ _ _)
    apply W.trans (KL.assoc _ _ _)
    apply KC.comp (W.refl _)
    apply KC.comp _ (W.refl _)
    exact W.refl _

/-- The target curry/uncurry bijection survives conjugation by both comparisons. -/
def uncurry_curry (DC : Congr V) (DL : Laws V)
    (TC : ProductCongr V T) (JL : ClosedLaws V T J)
    (I : ∀ a b, ComparisonLaws V (i a b)) (JJ : ∀ a b, ComparisonLaws V (j a b))
    {x a b} (f : D.Hom (F.obj (P.prod x a)) (F.obj b)) :
    V.Rel (j.uncurry i (j.curry i f)) f := by
  apply V.trans (DC.comp
    (ClosedOps.uncurry_congr J DC TC (DL.cancel_left DC (JJ _ _).hom_inv _)) (V.refl _))
  apply V.trans (DC.comp (JL.beta _) (V.refl _))
  exact V.trans (DL.assoc _ _ _) (V.trans
    (DC.comp (V.refl _) (I _ _).inv_hom) (DL.comp_id _))

def curry_uncurry (DC : Congr V) (DL : Laws V)
    (JC : ClosedCongr V T J) (JL : ClosedLaws V T J)
    (I : ∀ a b, ComparisonLaws V (i a b)) (JJ : ∀ a b, ComparisonLaws V (j a b))
    {x a b} (f : D.Hom (F.obj x) (F.obj (H.exp a b))) :
    V.Rel (j.curry i (j.uncurry i f)) f := by
  apply V.trans (DC.comp (V.refl _) (JC.curry
    (V.trans (DL.assoc _ _ _) (V.trans
      (DC.comp (V.refl _) (I _ _).hom_inv) (DL.comp_id _)))))
  exact V.trans (DC.comp (V.refl _) (JL.eta _)) (DL.cancel_left DC (JJ _ _).inv_hom _)

def transportLaws (L : Preservation F E V) (R : Reflection F E V)
    (DC : Congr V) (DL : Laws V)
    (TC : ProductCongr V T) (TL : ProductLaws V T)
    (JC : ClosedCongr V T J) (JL : ClosedLaws V T J)
    (I : ∀ a b, ComparisonLaws V (i a b)) (JJ : ∀ a b, ComparisonLaws V (j a b))
    (PM : ProductMapLaws V i) (M : ClosedMapLaws V i j) : ClosedLaws E P H := by
  apply ClosedLaws.ofBetaEta
    (SquareKit.WitnessEquivalence.transportCongr L R DC) (SquareKit.WitnessEquivalence.transportLaws L R DC DL)
    (ProductMap.transportCongr L R DC PM TC)
    (ProductMap.transportLaws L R DC DL I PM TC TL) (transportCongr L R DC JC M)
  · intro x a b f
    apply R
    apply V.trans (map_uncurry L DC DL TC TL I PM M _)
    apply V.trans (DC.comp (ClosedOps.uncurry_congr J DC TC (DC.comp (V.refl _) (M.curry _))) (V.refl _))
    exact uncurry_curry DC DL TC JL I JJ (F.map f)
  · intro x a b f
    apply R
    apply V.trans (M.curry _)
    apply V.trans (DC.comp (V.refl _) (JC.curry
      (DC.comp (map_uncurry L DC DL TC TL I PM M _) (V.refl _))))
    exact curry_uncurry DC DL JC JL I JJ (F.map f)
end ClosedMap
end SquareKit.WitnessEquivalence
