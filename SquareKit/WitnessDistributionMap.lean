import SquareKit.WitnessOptionalComparison
import SquareKit.DistributionMap

namespace SquareKit.WitnessEquivalence
universe u v w z
namespace DistributionMap
variable {O : Type u} {Q : Type w}
variable {C : CategoryOps.{u,v} O} {D : CategoryOps.{w,z} Q}
variable {F : RawMap C D} {P : ProductOps C} {T : ProductOps D}
variable {S : CoproductOps C} {U : CoproductOps D}



variable {E : WitnessEquivalence C} {H : WitnessEquivalence D}
variable (DC : Congr H) (DL : Laws H)
variable (TC : ProductCongr H T) (TL : ProductLaws H T)
variable (UC : CoproductCongr H U) (UL : CoproductLaws H U)
variable {i : ProductMap F P T} {j : CoproductMap F S U}

include DC DL TC TL in
def domainComparison_laws (I : ∀ a b, ComparisonLaws H (i a b))
    (J : ∀ a b, ComparisonLaws H (j a b)) (a b c : O) :
    ComparisonLaws H (SquareKit.DistributionMap.domainComparison i j a b c) :=
  Comparison.comp_laws DC DL (I _ _) (Comparison.productRight_laws DC DL TC TL _ (J _ _))

include DC DL UC UL in
def codomainComparison_laws (I : ∀ a b, ComparisonLaws H (i a b))
    (J : ∀ a b, ComparisonLaws H (j a b)) (a b c : O) :
    ComparisonLaws H (SquareKit.DistributionMap.codomainComparison i j a b c) :=
  Comparison.comp_laws DC DL (J _ _) (Comparison.coproduct_laws DC DL UC UL (I _ _) (I _ _))

include DL in
def distribute_preserved {d : DistributionOps C P S} {e : DistributionOps D T U}
    (M : DistributionMapLaws H i j d e) (a b c : O) :
    H.Rel (F.map (d.distribute (a := a) (b := b) (c := c)))
      (Comparison.conjugate (SquareKit.DistributionMap.domainComparison i j a b c) (SquareKit.DistributionMap.codomainComparison i j a b c)
        e.distribute) :=
  H.trans M.distribute (H.symm (DL.assoc _ _ _))

include DC DL TC TL in
def branch_normalize {a b c d x : Q} (k : D.Hom c d) (f : D.Hom b c)
    (h : D.Hom x (T.prod a b)) :
    H.Rel (D.comp (T.rightMap k) (D.comp (T.pair T.fst (D.comp f T.snd)) h))
      (T.pair (D.comp T.fst h) (D.comp k (D.comp f (D.comp T.snd h)))) := by
  apply H.trans (H.symm (DL.assoc _ _ _))
  apply H.trans (DC.comp (ProductOps.rightMap_pair T DC DL TC TL _ _ _) (H.refl _))
  apply H.trans (TL.pair_comp DC DL TC _ _ _)
  exact TC.pair (H.refl _) (H.trans (DL.assoc _ _ _) (DC.comp (H.refl _) (DL.assoc _ _ _)))

include DC DL TC TL in
def branch_preserved (L : Preservation F E H) (M : ProductMapLaws H i)
    {a b c : O} {c' : Q} (k : Comparison D (F.obj c) c')
    (f : C.Hom b c) (g : D.Hom (F.obj b) c')
    (h : H.Rel (F.map f) (D.comp k.inv g)) :
    H.Rel (F.map (P.pair (P.fst (a := a) (b := b)) (C.comp f P.snd)))
      (Comparison.conjugate (i a b)
        ((i a c).comp (Comparison.productRight T (F.obj a) k))
        (T.pair T.fst (D.comp g T.snd))) := by
  apply H.trans (M.pair _ _)
  apply H.trans (DC.comp (H.refl _) (TC.pair M.fst
    (H.trans (L.comp _ _) (H.trans (DC.comp h M.snd) (DL.assoc _ _ _)))))
  apply H.trans (DC.comp (H.refl _) (H.symm (branch_normalize DC DL TC TL _ _ _)))
  exact H.symm (DL.assoc _ _ _)

include DC DL UC UL in
def collect_map {a b c x y : Q} (f : D.Hom x (T.prod a b))
    (g : D.Hom y (T.prod a c)) :
    H.Rel (D.comp (collect D T U) (U.map f g))
      (U.copair (D.comp (T.pair T.fst (D.comp U.inl T.snd)) f)
        (D.comp (T.pair T.fst (D.comp U.inr T.snd)) g)) := by
  apply H.trans (UL.comp_copair DC DL UC _ _ _)
  apply UC.copair
  · exact H.trans (H.symm (DL.assoc _ _ _)) (DC.comp (UL.left _ _) (H.refl _))
  · exact H.trans (H.symm (DL.assoc _ _ _)) (DC.comp (UL.right _ _) (H.refl _))

include DC DL TC TL UC UL in
def collect_preserved (L : Preservation F E H) (M : ProductMapLaws H i)
    (N : CoproductMapLaws H j) (a b c : O) :
    H.Rel (F.map (collect C P S (a := a) (b := b) (c := c)))
      (Comparison.conjugate (SquareKit.DistributionMap.codomainComparison i j a b c) (SquareKit.DistributionMap.domainComparison i j a b c)
        (collect D T U)) := by
  apply H.trans (N.copair _ _)
  apply H.trans (DC.comp (UC.copair
    (branch_preserved DC DL TC TL L M (j b c) S.inl U.inl N.inl)
    (branch_preserved DC DL TC TL L M (j b c) S.inr U.inr N.inr)) (H.refl _))
  apply H.trans (DC.comp (H.symm (UL.comp_copair DC DL UC _ _ _)) (H.refl _))
  apply H.trans (DL.assoc _ _ _)
  apply DC.comp (H.refl _)
  apply H.trans (DC.comp (H.symm (collect_map DC DL UC UL _ _)) (H.refl _))
  exact DL.assoc _ _ _

include DC DL TC TL UC UL in
def transportLaws (L : Preservation F E H) (R : Reflection F E H)
    (M : ProductMapLaws H i) (N : CoproductMapLaws H j)
    (I : ∀ a b, ComparisonLaws H (i a b)) (J : ∀ a b, ComparisonLaws H (j a b))
    {d : DistributionOps C P S} {e : DistributionOps D T U}
    (K : DistributionMapLaws H i j d e) (V : DistributionLaws H T U e) :
    DistributionLaws E P S d := by
  have h (a b c : O) : ComparisonLaws E
      (⟨d.distribute (a := a) (b := b) (c := c), collect C P S⟩ : Comparison C _ _) :=
    RawMap.transportComparisonLaws L R DC DL (SquareKit.DistributionMap.domainComparison i j a b c)
      (SquareKit.DistributionMap.codomainComparison i j a b c)
      (domainComparison_laws DC DL TC TL I J a b c)
      (codomainComparison_laws DC DL UC UL I J a b c)
      _ ⟨e.distribute, collect D T U⟩
      ⟨V.distribute_collect _ _ _, V.collect_distribute _ _ _⟩
      (distribute_preserved DL K a b c) (collect_preserved DC DL TC TL UC UL L M N a b c)
  exact ⟨fun a b c => (h a b c).inv_hom, fun a b c => (h a b c).hom_inv⟩

include DC DL TC TL UC UL in
/-- For lawful distribution choices, structural preservation determines the
chosen inverse. Only one source inverse equation is used. -/
def of_laws (L : Preservation F E H) (M : ProductMapLaws H i)
    (N : CoproductMapLaws H j)
    (I : ∀ a b, ComparisonLaws H (i a b)) (J : ∀ a b, ComparisonLaws H (j a b))
    {d : DistributionOps C P S} {e : DistributionOps D T U}
    (V : ∀ a b c, E.Rel (C.comp (d.distribute (a := a) (b := b) (c := c))
      (collect C P S)) C.ident)
    (W : ∀ a b c, H.Rel (D.comp (collect D T U (a := a) (b := b) (c := c))
      e.distribute) D.ident) : DistributionMapLaws H i j d e where
  distribute := by
    intro a b c
    have hp := domainComparison_laws DC DL TC TL I J a b c
    have hq := codomainComparison_laws DC DL UC UL I J a b c
    have hg := collect_preserved DC DL TC TL UC UL L M N a b c
    have hinv : H.Rel (D.comp (F.map (collect C P S))
        (Comparison.conjugate (SquareKit.DistributionMap.domainComparison i j a b c)
          (SquareKit.DistributionMap.codomainComparison i j a b c) e.distribute)) D.ident :=
      H.trans (DC.comp hg (H.refl _))
        (H.trans (Comparison.conjugate_comp DC DL _ _ _ hq _ _)
          (H.trans (Comparison.conjugate_congr DC _ _ (W _ _ _))
            (Comparison.conjugate_id DC DL _ hp)))
    have heq := Comparison.inverse_unique DC DL
      (H.trans (H.symm (L.comp _ _)) (H.trans (L.congr (V a b c)) L.ident)) hinv
    exact H.trans heq (DL.assoc _ _ _)

include DC DL TC TL UC UL in
/-- Identity preserves arbitrary distribution choices; no inverse law is needed. -/
def id_laws (d : DistributionOps D T U) :
    DistributionMapLaws H (ProductMap.id T) (CoproductMap.id U) d d where
  distribute := by
    intro a b c
    apply H.symm
    apply H.trans (DL.id_comp _)
    apply H.trans (DC.comp (CoproductOps.map_id U DC DL UC UL _ _) (H.refl _))
    apply H.trans (DL.id_comp _)
    apply H.trans (DC.comp (H.refl _) (DL.comp_id _))
    apply H.trans (DC.comp (H.refl _) (ProductOps.rightMap_id T DC DL TC TL _ _))
    exact DL.comp_id _

section Composition
universe r s
variable {R : Type r} {K : CategoryOps.{r,s} R} {V : WitnessEquivalence K}
variable {G : RawMap D K} {W : ProductOps K} {X : CoproductOps K}
variable (LG : Preservation G H V) (KC : Congr V) (KL : Laws V)
variable (WC : ProductCongr V W) (WL : ProductLaws V W)
variable (XC : CoproductCongr V X) (XL : CoproductLaws V X)
variable {k : ProductMap G T W} {l : CoproductMap G U X}
variable (M : ProductMapLaws V k) (N : CoproductMapLaws V l)
variable (I : ∀ a b, V.Rel (K.comp (k a b).hom (k a b).inv) K.ident)
variable (J : ∀ a b, V.Rel (K.comp (l a b).hom (l a b).inv) K.ident)

include LG KC KL WC WL M in
/-- The derived map on the second product component is preserved. -/
def rightMap_preserved {a b c : Q} (f : D.Hom b c) :
    V.Rel (G.map (T.rightMap (a := a) f))
      (K.comp (k a c).inv (K.comp (W.rightMap (G.map f)) (k a b).hom)) := by
  apply V.trans (M.pair _ _)
  apply V.trans (KC.comp (V.refl _) (WC.pair M.fst
    (V.trans (LG.comp _ _) (V.trans (KC.comp (V.refl _) M.snd) (V.symm (KL.assoc _ _ _))))))
  exact KC.comp (V.refl _) (V.symm (WL.pair_comp KC KL WC _ _ _))

include LG KC KL XC XL N in
/-- The derived coproduct map is preserved. -/
def sumMap_preserved {a b c d : Q} (f : D.Hom a c) (g : D.Hom b d) :
    V.Rel (G.map (U.map f g))
      (K.comp (l c d).inv (K.comp (X.map (G.map f) (G.map g)) (l a b).hom)) := by
  apply V.trans (N.copair _ _)
  apply V.trans (KC.comp (XC.copair
    (V.trans (LG.comp _ _) (V.trans (KC.comp N.inl (V.refl _)) (KL.assoc _ _ _)))
    (V.trans (LG.comp _ _) (V.trans (KC.comp N.inr (V.refl _)) (KL.assoc _ _ _)))) (V.refl _))
  apply V.trans (KC.comp (V.symm (XL.comp_copair KC KL XC _ _ _)) (V.refl _))
  exact KL.assoc _ _ _

include LG KC KL WC WL M I in
def rightMap_natural {a b c : Q} (f : D.Hom b c) :
    V.Rel (K.comp (k a c).hom (G.map (T.rightMap (a := a) f)))
      (K.comp (W.rightMap (G.map f)) (k a b).hom) :=
  V.trans (KC.comp (V.refl _) (rightMap_preserved LG KC KL WC WL M f))
    (KL.cancel_left KC (I a c) _)

include LG KC KL XC XL N J in
def sumMap_natural_inv {a b c d : Q} (f : D.Hom a c) (g : D.Hom b d) :
    V.Rel (K.comp (G.map (U.map f g)) (l a b).inv)
      (K.comp (l c d).inv (X.map (G.map f) (G.map g))) := by
  apply V.trans (KC.comp (sumMap_preserved LG KC KL XC XL N f g) (V.refl _))
  apply V.trans (KL.assoc _ _ _)
  apply KC.comp (V.refl _)
  exact V.trans (KL.assoc _ _ _) (V.trans (KC.comp (V.refl _) (J a b)) (KL.comp_id _))

include LG KC KL WC WL M I in
/-- The induced domain comparison agrees with composing the two induced comparisons. -/
def domainComparison_comp_hom (a b c : O) :
    V.Rel (K.comp (SquareKit.DistributionMap.domainComparison k l (F.obj a) (F.obj b) (F.obj c)).hom
      (G.map (SquareKit.DistributionMap.domainComparison i j a b c).hom))
      (SquareKit.DistributionMap.domainComparison (i.comp k) (j.comp l) a b c).hom := by
  change V.Rel (K.comp (K.comp _ _) (G.map (D.comp _ _))) _
  apply V.trans (KC.comp (V.refl _) (LG.comp _ _))
  apply V.trans (KL.assoc _ _ _)
  apply V.trans (KC.comp (V.refl _) (V.symm (KL.assoc _ _ _)))
  apply V.trans (KC.comp (V.refl _) (KC.comp (rightMap_natural LG KC KL WC WL M I _) (V.refl _)))
  apply V.trans (KC.comp (V.refl _) (KL.assoc _ _ _))
  apply V.trans (V.symm (KL.assoc _ _ _))
  exact KC.comp (ProductOps.rightMap_comp W KC KL WC WL _ _) (V.refl _)

include LG KC KL XC XL N J in
/-- The inverse codomain comparison agrees with composing the two induced comparisons. -/
def codomainComparison_comp_inv (a b c : O) :
    V.Rel (K.comp (G.map (SquareKit.DistributionMap.codomainComparison i j a b c).inv)
      (SquareKit.DistributionMap.codomainComparison k l (F.obj a) (F.obj b) (F.obj c)).inv)
      (SquareKit.DistributionMap.codomainComparison (i.comp k) (j.comp l) a b c).inv := by
  change V.Rel (K.comp (G.map (D.comp _ _)) (K.comp _ _)) _
  apply V.trans (KC.comp (LG.comp _ _) (V.refl _))
  apply V.trans (KL.assoc _ _ _)
  apply V.trans (KC.comp (V.refl _) (V.symm (KL.assoc _ _ _)))
  apply V.trans (KC.comp (V.refl _) (KC.comp (sumMap_natural_inv LG KC KL XC XL N J _ _) (V.refl _)))
  apply V.trans (KC.comp (V.refl _) (KL.assoc _ _ _))
  apply V.trans (V.symm (KL.assoc _ _ _))
  exact KC.comp (V.refl _) (CoproductOps.map_comp X KC KL XC XL _ _ _ _)

include LG KC KL WC WL XC XL M N I J in
/-- Forward distribution preservation composes without source inverse laws or reflection. -/
def comp_laws {d : DistributionOps C P S} {e : DistributionOps D T U}
    {f : DistributionOps K W X}
    (A : DistributionMapLaws H i j d e) (B : DistributionMapLaws V k l e f) :
    DistributionMapLaws V (i.comp k) (j.comp l) d f where
  distribute := by
    intro a b c
    apply V.trans (LG.congr A.distribute)
    apply V.trans (LG.comp _ _)
    apply V.trans (KC.comp (V.refl _) (LG.comp _ _))
    apply V.trans (V.symm (KL.assoc _ _ _))
    apply V.trans (KC.comp (V.symm (LG.comp _ _)) (V.refl _))
    apply V.trans (KC.comp (V.refl _) (LG.comp _ _))
    apply V.trans (KC.comp (V.refl _) (KC.comp (distribute_preserved KL B _ _ _) (V.refl _)))
    apply V.trans (KC.comp (V.refl _) (KL.assoc _ _ _))
    apply V.trans (V.symm (KL.assoc _ _ _))
    apply V.trans (KC.comp (codomainComparison_comp_inv LG KC KL XC XL N J a b c)
      (V.refl _))
    apply V.trans (KC.comp (V.refl _) (KL.assoc _ _ _))
    apply V.trans (KC.comp (V.refl _) (KC.comp (V.refl _)
      (domainComparison_comp_hom LG KC KL WC WL M I a b c)))
    exact KL.assoc _ _ _
end Composition

end DistributionMap
end SquareKit.WitnessEquivalence
