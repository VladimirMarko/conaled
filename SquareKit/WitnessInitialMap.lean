import SquareKit.WitnessCartesianMap

namespace SquareKit.WitnessEquivalence
universe u v w z r s

structure InitialMapLaws {O : Type u} {Q : Type w}
    {C : CategoryOps.{u,v} O} {D : CategoryOps.{w,z} Q}
    {F : RawMap C D} {T : InitialOps C} {U : InitialOps D}
    (H : WitnessEquivalence D) (i : InitialMap F T U) where
  initial : ∀ {a}, H.Rel (F.map (T.initial (a := a))) (D.comp U.initial i.hom)

namespace InitialMap
variable {O : Type u} {Q : Type w} {R : Type r}
variable {C : CategoryOps.{u,v} O} {D : CategoryOps.{w,z} Q} {K : CategoryOps.{r,s} R}



def id_laws {E : WitnessEquivalence C} (L : Laws E) (T : InitialOps C) :
    InitialMapLaws E (SquareKit.InitialMap.id T) := ⟨E.symm (L.comp_id _)⟩

def comp_laws {F : RawMap C D} {G : RawMap D K}
    {H : WitnessEquivalence D} {J : WitnessEquivalence K} (LG : Preservation G H J)
    (KC : Congr J) (KL : Laws J)
    {T : InitialOps C} {U : InitialOps D} {V : InitialOps K}
    {i : InitialMap F T U} {j : InitialMap G U V}
    (I : InitialMapLaws H i) (JJ : InitialMapLaws J j) : InitialMapLaws J (SquareKit.InitialMap.comp i j) where
  initial := J.trans (LG.congr I.initial) (J.trans (LG.comp _ _)
    (J.trans (KC.comp JJ.initial (J.refl _)) (KL.assoc _ _ _)))

def comp_inverse {F : RawMap C D} {G : RawMap D K}
    {H : WitnessEquivalence D} {J : WitnessEquivalence K} (LG : Preservation G H J)
    (KC : Congr J) (KL : Laws J)
    {T : InitialOps C} {U : InitialOps D} {V : InitialOps K}
    {i : InitialMap F T U} {j : InitialMap G U V}
    (I : ComparisonLaws H i) (JJ : ComparisonLaws J j) : ComparisonLaws J (SquareKit.InitialMap.comp i j) :=
  Comparison.comp_laws KC KL (Comparison.map_laws LG I) JJ

/-- Reflection is needed only for the separately selected source relation.
Only the inverse equation at the interpreted source initial object is used. -/
def transportLaws {F : RawMap C D} {E : WitnessEquivalence C} {H : WitnessEquivalence D}
    (R : Reflection F E H) (DC : Congr H) (DL : Laws H)
    {T : InitialOps C} {U : InitialOps D} {i : InitialMap F T U}
    (I : H.Rel (D.comp i.inv i.hom) D.ident)
    (M : InitialMapLaws H i) (UL : InitialLaws H U) : InitialLaws E T where
  unique f := by
    apply R
    apply H.trans (H.symm (DL.comp_id _))
    apply H.trans (DC.comp (H.refl _) (H.symm I))
    apply H.trans (H.symm (DL.assoc _ _ _))
    exact H.trans (DC.comp (UL.unique _) (H.refl _)) (H.symm M.initial)
end InitialMap

end SquareKit.WitnessEquivalence
