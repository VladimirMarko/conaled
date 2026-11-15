import SquareKit.WitnessCartesianMap
import SquareKit.OptionalMap

namespace SquareKit.WitnessEquivalence
universe u v w z
variable {O : Type u} {Q : Type w} {C : CategoryOps.{u,v} O} {D : CategoryOps.{w,z} Q}

structure CoproductMapLaws {F : RawMap C D} {S : CoproductOps C} {T : CoproductOps D}
    (E : WitnessEquivalence D) (i : CoproductMap F S T) where
  inl : ∀ {a b}, E.Rel (F.map (S.inl (a := a) (b := b))) i.inl
  inr : ∀ {a b}, E.Rel (F.map (S.inr (a := a) (b := b))) i.inr
  copair : ∀ {a b c} (f : C.Hom a c) (g : C.Hom b c),
    E.Rel (F.map (S.copair f g)) (i.copair (F.map f) (F.map g))


structure ClosedMapLaws {F : RawMap C D} {P : ProductOps C} {Q : ProductOps D}
    {H : ClosedOps C P} {J : ClosedOps D Q} (E : WitnessEquivalence D)
    (i : ProductMap F P Q) (j : ClosedMap F H J) where
  curry : ∀ {x a b} (f : C.Hom (P.prod x a) b),
    E.Rel (F.map (H.curry f)) (j.curry i (F.map f))
  evaluation : ∀ {a b}, E.Rel (F.map (H.evaluation (a := a) (b := b))) (j.evaluation i)


structure DistributionMapLaws {F : RawMap C D} {P : ProductOps C} {Q : ProductOps D}
    {S : CoproductOps C} {T : CoproductOps D} (E : WitnessEquivalence D)
    (i : ProductMap F P Q) (j : CoproductMap F S T)
    (d : DistributionOps C P S) (e : DistributionOps D Q T) where
  distribute : ∀ {a b c}, E.Rel (F.map (d.distribute (a := a) (b := b) (c := c)))
    (imageDistribution i j e)
end SquareKit.WitnessEquivalence
