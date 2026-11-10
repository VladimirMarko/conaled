import SquareKit.WitnessClosedMap
import SquareKit.WitnessCoproductMap
import SquareKit.RightDistribution

namespace SquareKit.WitnessEquivalence
universe u v w
variable {O : Type u} {C : CategoryOps.{u,v} O} {E : WitnessEquivalence.{u,v,w} C}

structure ProductUniversal (P : ProductOps C) where
  forward : ∀ {a b c} {f : C.Hom a b} {g : C.Hom a c} {k : C.Hom a (P.prod b c)},
    E.Rel k (P.pair f g) → E.Rel (C.comp P.fst k) f × E.Rel (C.comp P.snd k) g
  backward : ∀ {a b c} {f : C.Hom a b} {g : C.Hom a c} {k : C.Hom a (P.prod b c)},
    E.Rel (C.comp P.fst k) f × E.Rel (C.comp P.snd k) g → E.Rel k (P.pair f g)

def ProductUniversal.laws {P : ProductOps C} (U : ProductUniversal (E := E) P) : ProductLaws E P where
  fst_pair _ _ := (U.forward (E.refl _)).1
  snd_pair _ _ := (U.forward (E.refl _)).2
  pair_eta _ := E.symm (U.backward ⟨E.refl _, E.refl _⟩)
def ProductLaws.universal {P : ProductOps C} (L : ProductLaws E P)
    (K : E.Congr) (G : ProductCongr E P) : ProductUniversal (E := E) P :=
  ⟨L.forward K, L.backward G⟩

structure CoproductUniversal (S : CoproductOps C) where
  forward : ∀ {a b c} {f : C.Hom a c} {g : C.Hom b c} {k : C.Hom (S.sum a b) c},
    E.Rel k (S.copair f g) → E.Rel (C.comp k S.inl) f × E.Rel (C.comp k S.inr) g
  backward : ∀ {a b c} {f : C.Hom a c} {g : C.Hom b c} {k : C.Hom (S.sum a b) c},
    E.Rel (C.comp k S.inl) f × E.Rel (C.comp k S.inr) g → E.Rel k (S.copair f g)

def CoproductUniversal.laws {S : CoproductOps C} (U : CoproductUniversal (E := E) S) :
    CoproductLaws E S := ⟨fun _ _ => (U.forward (E.refl _)).1,
      fun _ _ => (U.forward (E.refl _)).2, fun _ => E.symm (U.backward ⟨E.refl _, E.refl _⟩)⟩
def CoproductLaws.universal {S : CoproductOps C} (L : CoproductLaws E S)
    (K : E.Congr) (G : CoproductCongr E S) : CoproductUniversal (E := E) S where
  forward h := ⟨E.trans (K.comp h (E.refl _)) (L.left _ _),
    E.trans (K.comp h (E.refl _)) (L.right _ _)⟩
  backward h := E.trans (E.symm (L.eta _)) (G.copair h.1 h.2)

structure ClosedUniversal {P : ProductOps C} (H : ClosedOps C P) where
  forward : ∀ {x a b} {f : C.Hom (P.prod x a) b} {g : C.Hom x (H.exp a b)},
    E.Rel g (H.curry f) → E.Rel f (H.uncurry g)
  backward : ∀ {x a b} {f : C.Hom (P.prod x a) b} {g : C.Hom x (H.exp a b)},
    E.Rel f (H.uncurry g) → E.Rel g (H.curry f)

def ClosedUniversal.laws {P : ProductOps C} {H : ClosedOps C P}
    (U : ClosedUniversal (E := E) H) (K : E.Congr) (A : E.Laws)
    (G : ProductCongr E P) (L : ProductLaws E P) (HC : ClosedCongr E P H) : ClosedLaws E P H :=
  ClosedLaws.ofBetaEta K A G L HC
    (fun _ => E.symm (U.forward (E.refl _))) (fun _ => E.symm (U.backward (E.refl _)))
def ClosedLaws.universal {P : ProductOps C} {H : ClosedOps C P}
    (L : ClosedLaws E P H) (K : E.Congr) (G : ProductCongr E P)
    (HC : ClosedCongr E P H) : ClosedUniversal (E := E) H where
  forward h := E.symm (E.trans (ClosedOps.uncurry_congr H K G h) (L.beta _))
  backward h := E.symm (E.trans (HC.curry h) (L.eta _))

def ClosedLaws.curry_evaluation {P : ProductOps C} {H : ClosedOps C P}
    (L : ClosedLaws E P H) (K : E.Congr) (A : E.Laws) (G : ProductCongr E P)
    (PL : ProductLaws E P) (HC : ClosedCongr E P H) (a b : O) :
    E.Rel (C.ident (a := H.exp a b)) (H.curry H.evaluation) :=
  E.trans (E.symm (L.eta _)) (HC.curry
    (E.trans (K.comp (E.refl _)
      (E.trans (G.pair (A.id_comp _) (E.refl _)) (PL.projections A G))) (A.comp_id _)))

abbrev RightDistributionLaws (P : ProductOps C) (S : CoproductOps C)
    (d : RightDistributionOps P S) := DistributionLaws E P.reverse S d

end SquareKit.WitnessEquivalence
