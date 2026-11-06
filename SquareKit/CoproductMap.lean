import SquareKit.OptionalMap

/-! Coproduct law transport through explicit comparisons and reflection. -/
namespace SquareKit
universe u₁ v₁ u₂ v₂ u₃ v₃

namespace CoproductLaws
variable {O : Type u₁} {C : CategoryOps.{u₁,v₁} O} {E : HomEquiv C}
variable {S : CoproductOps C}

theorem hom_ext (SC : CoproductCongr C E S) (SL : CoproductLaws C E S)
    {a b c} {f g : C.Hom (S.sum a b) c}
    (hl : E.Rel (C.comp f S.inl) (C.comp g S.inl))
    (hr : E.Rel (C.comp f S.inr) (C.comp g S.inr)) : E.Rel f g :=
  E.trans (E.symm (SL.eta f)) (E.trans (SC.copair hl hr) (SL.eta g))

theorem comp_copair (CC : CategoryCongr C E) (CL : CategoryLaws C E)
    (SC : CoproductCongr C E S) (SL : CoproductLaws C E S)
    {a b c d} (h : C.Hom c d) (f : C.Hom a c) (g : C.Hom b c) :
    E.Rel (C.comp h (S.copair f g)) (S.copair (C.comp h f) (C.comp h g)) := by
  apply SL.hom_ext SC
  · exact E.trans (CL.assoc _ _ _)
      (E.trans (CC.comp (E.refl _) (SL.left _ _)) (E.symm (SL.left _ _)))
  · exact E.trans (CL.assoc _ _ _)
      (E.trans (CC.comp (E.refl _) (SL.right _ _)) (E.symm (SL.right _ _)))
end CoproductLaws

namespace CoproductMap
variable {O : Type u₁} {P : Type u₂} {Q : Type u₃}
variable {C : CategoryOps.{u₁,v₁} O} {D : CategoryOps.{u₂,v₂} P} {K : CategoryOps.{u₃,v₃} Q}

def id (S : CoproductOps C) : CoproductMap (RawMap.id C) S S :=
  fun a b => Comparison.id C (S.sum a b)

def comp {F : RawMap C D} {G : RawMap D K}
    {S : CoproductOps C} {T : CoproductOps D} {U : CoproductOps K}
    (i : CoproductMap F S T) (j : CoproductMap G T U) : CoproductMap (F.comp G) S U :=
  fun a b => ((i a b).map G).comp (j (F.obj a) (F.obj b))

theorem id_laws {E : HomEquiv C} (L : CategoryLaws C E) (S : CoproductOps C) :
    CoproductMapLaws E (id S) where
  inl := E.symm (L.id_comp _)
  inr := E.symm (L.id_comp _)
  copair _ _ := E.symm (L.comp_id _)

theorem comp_laws {F : RawMap C D} {G : RawMap D K}
    {H : HomEquiv D} {J : HomEquiv K} (LG : MapLaws G H J)
    (KC : CategoryCongr K J) (KL : CategoryLaws K J)
    {S : CoproductOps C} {T : CoproductOps D} {U : CoproductOps K}
    {i : CoproductMap F S T} {j : CoproductMap G T U}
    (I : CoproductMapLaws H i) (JJ : CoproductMapLaws J j) : CoproductMapLaws J (comp i j) where
  inl := J.trans (LG.congr I.inl) (J.trans (LG.comp _ _)
    (J.trans (KC.comp (J.refl _) JJ.inl) (J.symm (KL.assoc _ _ _))))
  inr := J.trans (LG.congr I.inr) (J.trans (LG.comp _ _)
    (J.trans (KC.comp (J.refl _) JJ.inr) (J.symm (KL.assoc _ _ _))))
  copair f g := J.trans (LG.congr (I.copair f g)) (J.trans (LG.comp _ _)
    (J.trans (KC.comp (JJ.copair _ _) (J.refl _)) (KL.assoc _ _ _)))

theorem comp_inverse {F : RawMap C D} {G : RawMap D K}
    {H : HomEquiv D} {J : HomEquiv K} (LG : MapLaws G H J)
    (KC : CategoryCongr K J) (KL : CategoryLaws K J)
    {S : CoproductOps C} {T : CoproductOps D} {U : CoproductOps K}
    {i : CoproductMap F S T} {j : CoproductMap G T U}
    (I : ∀ a b, ComparisonLaws H (i a b)) (JJ : ∀ a b, ComparisonLaws J (j a b)) (a b : O) :
    ComparisonLaws J (comp i j a b) :=
  Comparison.comp_laws KC KL (Comparison.map_laws LG (I a b)) (JJ _ _)

theorem transportCongr {F : RawMap C D} {E : HomEquiv C} {H : HomEquiv D}
    (L : MapLaws F E H) (R : F.Reflects E H) (DC : CategoryCongr D H)
    {S : CoproductOps C} {T : CoproductOps D} {i : CoproductMap F S T}
    (M : CoproductMapLaws H i) (TC : CoproductCongr D H T) : CoproductCongr C E S where
  copair hf hg := R (H.trans (M.copair _ _) (H.trans
    (DC.comp (TC.copair (L.congr hf) (L.congr hg)) (H.refl _)) (H.symm (M.copair _ _))))

theorem transportLaws {F : RawMap C D} {E : HomEquiv C} {H : HomEquiv D}
    (L : MapLaws F E H) (R : F.Reflects E H)
    (DC : CategoryCongr D H) (DL : CategoryLaws D H)
    {S : CoproductOps C} {T : CoproductOps D} {i : CoproductMap F S T}
    (I : ∀ a b, ComparisonLaws H (i a b)) (M : CoproductMapLaws H i)
    (TC : CoproductCongr D H T) (TL : CoproductLaws D H T) : CoproductLaws C E S where
  left f g := R (H.trans (L.comp _ _) (H.trans (DC.comp (M.copair f g) M.inl)
    (H.trans (DL.cancel_middle DC (I _ _).hom_inv _ _) (TL.left _ _))))
  right f g := R (H.trans (L.comp _ _) (H.trans (DC.comp (M.copair f g) M.inr)
    (H.trans (DL.cancel_middle DC (I _ _).hom_inv _ _) (TL.right _ _))))
  eta f := by
    apply R
    apply H.trans (M.copair _ _)
    apply H.trans (DC.comp (TC.copair (L.comp _ _) (L.comp _ _)) (H.refl _))
    apply H.trans (DC.comp (TC.copair (DC.comp (H.refl _) M.inl)
      (DC.comp (H.refl _) M.inr)) (H.refl _))
    apply H.trans (DC.comp (TC.copair (H.symm (DL.assoc _ _ _))
      (H.symm (DL.assoc _ _ _))) (H.refl _))
    apply H.trans (DC.comp (TL.eta _) (H.refl _))
    exact H.trans (DL.assoc _ _ _) (H.trans (DC.comp (H.refl _) (I _ _).inv_hom) (DL.comp_id _))

end CoproductMap
end SquareKit
