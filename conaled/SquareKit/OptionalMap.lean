import SquareKit.Optional
import SquareKit.CartesianMap

/-! Scoped preservation of chosen optional operations. Comparison arrows are
supplied independently of inverse equations and operation coherence. -/
namespace SquareKit
universe u v w z
variable {O : Type u} {Q : Type w} {C : CategoryOps.{u,v} O} {D : CategoryOps.{w,z} Q}

abbrev CoproductMap (F : RawMap C D) (S : CoproductOps C) (T : CoproductOps D) :=
  (a b : O) → Comparison D (F.obj (S.sum a b)) (T.sum (F.obj a) (F.obj b))

abbrev ClosedMap (F : RawMap C D) {P : ProductOps C} {Q : ProductOps D}
    (H : ClosedOps C P) (J : ClosedOps D Q) :=
  (a b : O) → Comparison D (F.obj (H.exp a b)) (J.exp (F.obj a) (F.obj b))

namespace CoproductMap
variable {F : RawMap C D} {S : CoproductOps C} {T : CoproductOps D}
def inl (i : CoproductMap F S T) {a b : O} := D.comp (i a b).inv T.inl
def inr (i : CoproductMap F S T) {a b : O} := D.comp (i a b).inv T.inr
def copair (i : CoproductMap F S T) {a b c : O}
    (f : D.Hom (F.obj a) (F.obj c)) (g : D.Hom (F.obj b) (F.obj c)) :=
  D.comp (T.copair f g) (i a b).hom
end CoproductMap

structure CoproductMapLaws {F : RawMap C D} {S : CoproductOps C} {T : CoproductOps D}
    (E : HomEquiv D) (i : CoproductMap F S T) : Prop where
  inl : ∀ {a b}, E.Rel (F.map (S.inl (a := a) (b := b))) i.inl
  inr : ∀ {a b}, E.Rel (F.map (S.inr (a := a) (b := b))) i.inr
  copair : ∀ {a b c} (f : C.Hom a c) (g : C.Hom b c),
    E.Rel (F.map (S.copair f g)) (i.copair (F.map f) (F.map g))

namespace ClosedMap
variable {F : RawMap C D} {P : ProductOps C} {Q : ProductOps D}
variable {H : ClosedOps C P} {J : ClosedOps D Q}
def curry (i : ProductMap F P Q) (j : ClosedMap F H J) {x a b : O}
    (f : D.Hom (F.obj (P.prod x a)) (F.obj b)) :=
  D.comp (j a b).inv (J.curry (D.comp f (i x a).inv))
def evaluation (i : ProductMap F P Q) (j : ClosedMap F H J) {a b : O} :=
  D.comp J.evaluation (D.comp
    (Q.pair (D.comp (j a b).hom Q.fst) Q.snd) (i (H.exp a b) a).hom)
end ClosedMap

structure ClosedMapLaws {F : RawMap C D} {P : ProductOps C} {Q : ProductOps D}
    {H : ClosedOps C P} {J : ClosedOps D Q} (E : HomEquiv D)
    (i : ProductMap F P Q) (j : ClosedMap F H J) : Prop where
  curry : ∀ {x a b} (f : C.Hom (P.prod x a) b),
    E.Rel (F.map (H.curry f)) (j.curry i (F.map f))
  evaluation : ∀ {a b}, E.Rel (F.map (H.evaluation (a := a) (b := b))) (j.evaluation i)

/-- Reassociate the image of a distributed environment using both comparisons. -/
def imageDistribution {F : RawMap C D} {P : ProductOps C} {Q : ProductOps D}
    {S : CoproductOps C} {T : CoproductOps D}
    (i : ProductMap F P Q) (j : CoproductMap F S T) (d : DistributionOps D Q T) {a b c : O} :=
  D.comp (j (P.prod a b) (P.prod a c)).inv
    (D.comp (T.copair (D.comp T.inl (i a b).inv) (D.comp T.inr (i a c).inv))
      (D.comp d.distribute
        (D.comp (Q.pair Q.fst (D.comp (j b c).hom Q.snd)) (i a (S.sum b c)).hom)))

structure DistributionMapLaws {F : RawMap C D} {P : ProductOps C} {Q : ProductOps D}
    {S : CoproductOps C} {T : CoproductOps D} (E : HomEquiv D)
    (i : ProductMap F P Q) (j : CoproductMap F S T)
    (d : DistributionOps C P S) (e : DistributionOps D Q T) : Prop where
  distribute : ∀ {a b c}, E.Rel (F.map (d.distribute (a := a) (b := b) (c := c)))
    (imageDistribution i j e)
end SquareKit
