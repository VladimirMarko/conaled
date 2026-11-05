import SquareKit.OptionalComparison

/-! Distribution transport uses the induced product and coproduct comparisons.
The preservation of collect is derived from its constituent operations. -/
namespace SquareKit
universe u v w z
namespace DistributionMap
variable {O : Type u} {Q : Type w}
variable {C : CategoryOps.{u,v} O} {D : CategoryOps.{w,z} Q}
variable {F : RawMap C D} {P : ProductOps C} {T : ProductOps D}
variable {S : CoproductOps C} {U : CoproductOps D}

def domainComparison (i : ProductMap F P T) (j : CoproductMap F S U) (a b c : O) :
    Comparison D (F.obj (P.prod a (S.sum b c))) (T.prod (F.obj a) (U.sum (F.obj b) (F.obj c))) :=
  (i a (S.sum b c)).comp (Comparison.productRight T (F.obj a) (j b c))

def codomainComparison (i : ProductMap F P T) (j : CoproductMap F S U) (a b c : O) :
    Comparison D (F.obj (S.sum (P.prod a b) (P.prod a c)))
      (U.sum (T.prod (F.obj a) (F.obj b)) (T.prod (F.obj a) (F.obj c))) :=
  (j (P.prod a b) (P.prod a c)).comp (Comparison.coproduct U (i a b) (i a c))

variable {E : HomEquiv C} {H : HomEquiv D}
variable (DC : CategoryCongr D H) (DL : CategoryLaws D H)
variable (TC : ProductCongr H T) (TL : ProductLaws H T)
variable (UC : CoproductCongr D H U) (UL : CoproductLaws D H U)
variable {i : ProductMap F P T} {j : CoproductMap F S U}

include DC DL TC TL in
theorem domainComparison_laws (I : ∀ a b, ComparisonLaws H (i a b))
    (J : ∀ a b, ComparisonLaws H (j a b)) (a b c : O) :
    ComparisonLaws H (domainComparison i j a b c) :=
  Comparison.comp_laws DC DL (I _ _) (Comparison.productRight_laws DC DL TC TL _ (J _ _))

include DC DL UC UL in
theorem codomainComparison_laws (I : ∀ a b, ComparisonLaws H (i a b))
    (J : ∀ a b, ComparisonLaws H (j a b)) (a b c : O) :
    ComparisonLaws H (codomainComparison i j a b c) :=
  Comparison.comp_laws DC DL (J _ _) (Comparison.coproduct_laws DC DL UC UL (I _ _) (I _ _))

include DL in
theorem distribute_preserved {d : DistributionOps C P S} {e : DistributionOps D T U}
    (M : DistributionMapLaws H i j d e) (a b c : O) :
    H.Rel (F.map (d.distribute (a := a) (b := b) (c := c)))
      (Comparison.conjugate (domainComparison i j a b c) (codomainComparison i j a b c)
        e.distribute) :=
  H.trans M.distribute (H.symm (DL.assoc _ _ _))

include DC DL TC TL in
theorem branch_normalize {a b c d x : Q} (k : D.Hom c d) (f : D.Hom b c)
    (h : D.Hom x (T.prod a b)) :
    H.Rel (D.comp (T.rightMap k) (D.comp (T.pair T.fst (D.comp f T.snd)) h))
      (T.pair (D.comp T.fst h) (D.comp k (D.comp f (D.comp T.snd h)))) := by
  apply H.trans (H.symm (DL.assoc _ _ _))
  apply H.trans (DC.comp (T.rightMap_pair DC DL TC TL _ _ _) (H.refl _))
  apply H.trans (TL.pair_comp DC DL TC _ _ _)
  exact TC.pair (H.refl _) (H.trans (DL.assoc _ _ _) (DC.comp (H.refl _) (DL.assoc _ _ _)))

include DC DL TC TL in
theorem branch_preserved (L : MapLaws F E H) (M : ProductMapLaws H i)
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
theorem collect_map {a b c x y : Q} (f : D.Hom x (T.prod a b))
    (g : D.Hom y (T.prod a c)) :
    H.Rel (D.comp (collect D T U) (U.map f g))
      (U.copair (D.comp (T.pair T.fst (D.comp U.inl T.snd)) f)
        (D.comp (T.pair T.fst (D.comp U.inr T.snd)) g)) := by
  apply H.trans (UL.comp_copair DC DL UC _ _ _)
  apply UC.copair
  · exact H.trans (H.symm (DL.assoc _ _ _)) (DC.comp (UL.left _ _) (H.refl _))
  · exact H.trans (H.symm (DL.assoc _ _ _)) (DC.comp (UL.right _ _) (H.refl _))

include DC DL TC TL UC UL in
theorem collect_preserved (L : MapLaws F E H) (M : ProductMapLaws H i)
    (N : CoproductMapLaws H j) (a b c : O) :
    H.Rel (F.map (collect C P S (a := a) (b := b) (c := c)))
      (Comparison.conjugate (codomainComparison i j a b c) (domainComparison i j a b c)
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
theorem transportLaws (L : MapLaws F E H) (R : F.Reflects E H)
    (M : ProductMapLaws H i) (N : CoproductMapLaws H j)
    (I : ∀ a b, ComparisonLaws H (i a b)) (J : ∀ a b, ComparisonLaws H (j a b))
    {d : DistributionOps C P S} {e : DistributionOps D T U}
    (K : DistributionMapLaws H i j d e) (V : DistributionLaws D H T U e) :
    DistributionLaws C E P S d := by
  have h (a b c : O) : ComparisonLaws E
      (⟨d.distribute (a := a) (b := b) (c := c), collect C P S⟩ : Comparison C _ _) :=
    F.transportComparisonLaws L R DC DL (domainComparison i j a b c)
      (codomainComparison i j a b c)
      (domainComparison_laws DC DL TC TL I J a b c)
      (codomainComparison_laws DC DL UC UL I J a b c)
      _ ⟨e.distribute, collect D T U⟩
      ⟨V.distribute_collect _ _ _, V.collect_distribute _ _ _⟩
      (distribute_preserved DL K a b c) (collect_preserved DC DL TC TL UC UL L M N a b c)
  exact ⟨fun a b c => (h a b c).inv_hom, fun a b c => (h a b c).hom_inv⟩

include DC DL TC TL UC UL in
/-- For lawful distribution choices, structural preservation determines the
chosen inverse. Only one source inverse equation is used. -/
theorem of_laws (L : MapLaws F E H) (M : ProductMapLaws H i)
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
        (Comparison.conjugate (domainComparison i j a b c)
          (codomainComparison i j a b c) e.distribute)) D.ident :=
      H.trans (DC.comp hg (H.refl _))
        (H.trans (Comparison.conjugate_comp DC DL _ _ _ hq _ _)
          (H.trans (Comparison.conjugate_congr DC _ _ (W _ _ _))
            (Comparison.conjugate_id DC DL _ hp)))
    have heq := Comparison.inverse_unique DC DL
      (H.trans (H.symm (L.comp _ _)) (H.trans (L.congr (V a b c)) L.ident)) hinv
    exact H.trans heq (DL.assoc _ _ _)

include DC DL TC TL UC UL in
/-- Identity preserves arbitrary distribution choices; no inverse law is needed. -/
theorem id_laws (d : DistributionOps D T U) :
    DistributionMapLaws H (ProductMap.id T) (CoproductMap.id U) d d where
  distribute := by
    intro a b c
    apply H.symm
    apply H.trans (DL.id_comp _)
    apply H.trans (DC.comp (U.map_id DC DL UC UL _ _) (H.refl _))
    apply H.trans (DL.id_comp _)
    apply H.trans (DC.comp (H.refl _) (DL.comp_id _))
    apply H.trans (DC.comp (H.refl _) (T.rightMap_id DC DL TC TL _ _))
    exact DL.comp_id _

end DistributionMap
end SquareKit
