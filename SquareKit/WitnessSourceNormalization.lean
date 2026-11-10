import SquareKit.WitnessErasure

namespace SquareKit.WitnessEquivalence
universe u v w
variable {O : Type u} {C : CategoryOps.{u,v} O} {E : WitnessEquivalence.{u,v,w} C}
variable {P : ProductOps C} {S : CoproductOps C}

/-- The pinned source writes distribution's canonical arrow using `second`. -/
def sourceCollect (P : ProductOps C) (S : CoproductOps C) {a b c : O} :
    C.Hom (S.sum (P.prod a b) (P.prod a c)) (P.prod a (S.sum b c)) :=
  S.copair (SquareKit.Cartesian.second P S.inl) (SquareKit.Cartesian.second P S.inr)

def sourceCollect_normalizes (A : E.Laws) (G : ProductCongr E P) (SC : CoproductCongr E S)
    (a b c : O) : E.Rel (sourceCollect P S (a := a) (b := b) (c := c)) (collect C P S) :=
  SC.copair (G.pair (A.id_comp _) (E.refl _)) (G.pair (A.id_comp _) (E.refl _))

def sourceCollectRight (P : ProductOps C) (S : CoproductOps C) {a b c : O} :
    C.Hom (S.sum (P.prod b a) (P.prod c a)) (P.prod (S.sum b c) a) :=
  S.copair (SquareKit.Cartesian.first P S.inl) (SquareKit.Cartesian.first P S.inr)

def sourceCollectRight_normalizes (A : E.Laws) (G : ProductCongr E P)
    (SC : CoproductCongr E S) (a b c : O) :
    E.Rel (sourceCollectRight P S (a := a) (b := b) (c := c)) (collectRight P S) :=
  SC.copair (G.pair (E.refl _) (A.id_comp _)) (G.pair (E.refl _) (A.id_comp _))

/-- Transport both selected inverse witnesses along a selected arrow comparison. -/
def ComparisonLaws.replace_inverse (K : E.Congr) {a b} {f : C.Hom a b} {g g' : C.Hom b a}
    (L : ComparisonLaws E (⟨f, g⟩ : Comparison C a b)) (h : E.Rel g g') :
    ComparisonLaws E (⟨f, g'⟩ : Comparison C a b) :=
  ⟨E.trans (K.comp (E.refl _) (E.symm h)) L.hom_inv,
    E.trans (K.comp (E.symm h) (E.refl _)) L.inv_hom⟩

def DistributionLaws.source (K : E.Congr) (A : E.Laws) (G : ProductCongr E P)
    (SC : CoproductCongr E S) {d : DistributionOps C P S} (L : DistributionLaws E P S d)
    (a b c : O) : ComparisonLaws E
      (⟨d.distribute (a := a) (b := b) (c := c), sourceCollect P S⟩ : Comparison C _ _) :=
  ComparisonLaws.replace_inverse K ⟨L.distribute_collect a b c, L.collect_distribute a b c⟩
    (E.symm (sourceCollect_normalizes A G SC a b c))

def DistributionLaws.ofSource (K : E.Congr) (A : E.Laws) (G : ProductCongr E P)
    (SC : CoproductCongr E S) {d : DistributionOps C P S}
    (L : ∀ a b c, ComparisonLaws E
      (⟨d.distribute (a := a) (b := b) (c := c), sourceCollect P S⟩ : Comparison C _ _)) :
    DistributionLaws E P S d where
  collect_distribute a b c :=
    (ComparisonLaws.replace_inverse K (L a b c) (sourceCollect_normalizes A G SC a b c)).inv_hom
  distribute_collect a b c :=
    (ComparisonLaws.replace_inverse K (L a b c) (sourceCollect_normalizes A G SC a b c)).hom_inv

def ProductCongr.reverse (G : ProductCongr E P) : ProductCongr E P.reverse :=
  ⟨fun h k => G.pair k h⟩
def ProductLaws.reverse (L : ProductLaws E P) : ProductLaws E P.reverse :=
  ⟨fun f g => L.snd_pair g f, fun f g => L.fst_pair g f, L.pair_eta⟩

def RightDistributionLaws.source (K : E.Congr) (A : E.Laws) (G : ProductCongr E P)
    (SC : CoproductCongr E S) {d : RightDistributionOps P S}
    (L : RightDistributionLaws (E := E) P S d) (a b c : O) : ComparisonLaws E
      (⟨d.distribute (a := a) (b := b) (c := c), sourceCollectRight P S⟩ : Comparison C _ _) :=
  DistributionLaws.source K A G.reverse SC L a b c

def RightDistributionLaws.ofSource (K : E.Congr) (A : E.Laws) (G : ProductCongr E P)
    (SC : CoproductCongr E S) {d : RightDistributionOps P S}
    (L : ∀ a b c, ComparisonLaws E
      (⟨d.distribute (a := a) (b := b) (c := c), sourceCollectRight P S⟩ : Comparison C _ _)) :
    RightDistributionLaws (E := E) P S d :=
  DistributionLaws.ofSource K A G.reverse SC L

def sourceUncurry (H : ClosedOps C P) {x a b} (g : C.Hom x (H.exp a b)) : C.Hom (P.prod x a) b :=
  C.comp H.evaluation (SquareKit.Cartesian.first P g)

def sourceUncurry_normalizes (K : E.Congr) (A : E.Laws) (G : ProductCongr E P)
    (H : ClosedOps C P) {x a b} (g : C.Hom x (H.exp a b)) :
    E.Rel (sourceUncurry H g) (H.uncurry g) :=
  K.comp (E.refl _) (G.pair (E.refl _) (A.id_comp _))

structure SourceClosedUniversal (H : ClosedOps C P) where
  forward : ∀ {x a b} {f : C.Hom (P.prod x a) b} {g : C.Hom x (H.exp a b)},
    E.Rel g (H.curry f) → E.Rel f (sourceUncurry H g)
  backward : ∀ {x a b} {f : C.Hom (P.prod x a) b} {g : C.Hom x (H.exp a b)},
    E.Rel f (sourceUncurry H g) → E.Rel g (H.curry f)

def SourceClosedUniversal.normalized {H : ClosedOps C P} (U : SourceClosedUniversal (E := E) H)
    (K : E.Congr) (A : E.Laws) (G : ProductCongr E P) : ClosedUniversal (E := E) H where
  forward h := E.trans (U.forward h) (sourceUncurry_normalizes K A G _ _)
  backward h := U.backward (E.trans h (E.symm (sourceUncurry_normalizes K A G _ _)))
def ClosedUniversal.source {H : ClosedOps C P} (U : ClosedUniversal (E := E) H)
    (K : E.Congr) (A : E.Laws) (G : ProductCongr E P) : SourceClosedUniversal (E := E) H where
  forward h := E.trans (U.forward h) (E.symm (sourceUncurry_normalizes K A G _ _))
  backward h := U.backward (E.trans h (sourceUncurry_normalizes K A G _ _))

end SquareKit.WitnessEquivalence
