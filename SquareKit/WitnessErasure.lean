import SquareKit.WitnessFelixPreservation
import SquareKit.WitnessUniversal

namespace SquareKit.WitnessEquivalence
universe u v u' v'
variable {O : Type u} {Q : Type u'} {C : CategoryOps.{u,v} O} {D : CategoryOps.{u',v'} Q}
variable {F : RawMap C D} {H : WitnessEquivalence D}

theorem InitialMapLaws.erase {T : InitialOps C} {U : InitialOps D} {i : InitialMap F T U}
    (L : InitialMapLaws H i) : SquareKit.InitialMapLaws H.erase i := ⟨⟨L.initial⟩⟩
theorem CoproductMapLaws.erase {S : CoproductOps C} {T : CoproductOps D}
    {i : CoproductMap F S T} (L : CoproductMapLaws H i) : SquareKit.CoproductMapLaws H.erase i :=
  ⟨⟨L.inl⟩, ⟨L.inr⟩, fun f g => ⟨L.copair f g⟩⟩
theorem ClosedMapLaws.erase {P : ProductOps C} {T : ProductOps D}
    {A : ClosedOps C P} {B : ClosedOps D T} {i : ProductMap F P T} {j : ClosedMap F A B}
    (L : ClosedMapLaws H i j) : SquareKit.ClosedMapLaws H.erase i j :=
  ⟨fun f => ⟨L.curry f⟩, ⟨L.evaluation⟩⟩
theorem DistributionMapLaws.erase {P : ProductOps C} {T : ProductOps D}
    {S : CoproductOps C} {U : CoproductOps D} {i : ProductMap F P T} {j : CoproductMap F S U}
    {d : DistributionOps C P S} {e : DistributionOps D T U}
    (L : DistributionMapLaws H i j d e) : SquareKit.DistributionMapLaws H.erase i j d e :=
  ⟨⟨L.distribute⟩⟩

variable {E : WitnessEquivalence C}
def Congr.left (K : E.Congr) {a b c} {f g : C.Hom b c} (h : E.Rel f g) (k : C.Hom a b) :
    E.Rel (C.comp f k) (C.comp g k) := K.comp h (E.refl _)
def Congr.right (K : E.Congr) {a b c} (k : C.Hom b c) {f g : C.Hom a b} (h : E.Rel f g) :
    E.Rel (C.comp k f) (C.comp k g) := K.comp (E.refl _) h
def Laws.assoc_reverse (L : E.Laws) {a b c d} (h : C.Hom c d) (g : C.Hom b c) (f : C.Hom a b) :
    E.Rel (C.comp h (C.comp g f)) (C.comp (C.comp h g) f) := E.symm (L.assoc h g f)
def ProductCongr.left {P : ProductOps C} (K : ProductCongr E P)
    {a b c} {f g : C.Hom a b} (h : E.Rel f g) (k : C.Hom a c) :
    E.Rel (P.pair f k) (P.pair g k) := K.pair h (E.refl _)
def ProductCongr.right {P : ProductOps C} (K : ProductCongr E P)
    {a b c} (k : C.Hom a b) {f g : C.Hom a c} (h : E.Rel f g) :
    E.Rel (P.pair k f) (P.pair k g) := K.pair (E.refl _) h

def Cartesian.tensor_congr_left {P : ProductOps C} (K : E.Congr) (G : ProductCongr E P)
    {a b c d} {f f' : C.Hom a c} (g : C.Hom b d) (h : E.Rel f f') :
    E.Rel (SquareKit.Cartesian.tensor P f g) (SquareKit.Cartesian.tensor P f' g) :=
  Cartesian.tensor_congr K G h (E.refl _)
def Cartesian.tensor_congr_right {P : ProductOps C} (K : E.Congr) (G : ProductCongr E P)
    {a b c d} (f : C.Hom a c) {g g' : C.Hom b d} (h : E.Rel g g') :
    E.Rel (SquareKit.Cartesian.tensor P f g) (SquareKit.Cartesian.tensor P f g') :=
  Cartesian.tensor_congr K G (E.refl _) h

def InitialLaws.universal {T : InitialOps C} (L : InitialLaws E T) {a} (f : C.Hom T.zero a) :
    E.Rel T.initial f := E.symm (L.unique f)
def InitialLaws.ofUniversal {T : InitialOps C}
    (U : ∀ {a} (f : C.Hom T.zero a), E.Rel T.initial f) : InitialLaws E T :=
  ⟨fun f => E.symm (U f)⟩

end SquareKit.WitnessEquivalence
