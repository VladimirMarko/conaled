import SquareKit.WitnessEquivalence
import SquareKit.Initial
import SquareKit.Optional

namespace SquareKit.WitnessEquivalence
universe u v w
variable {Obj : Type u} {C : CategoryOps.{u,v} Obj}

structure TerminalLaws {Obj : Type u} {C : CategoryOps.{u,v} Obj}
    (E : WitnessEquivalence C) (T : TerminalOps C) where
  unique : ∀ {a} (f : C.Hom a T.unit), E.Rel f T.terminal

structure ProductCongr {Obj : Type u} {C : CategoryOps.{u,v} Obj}
    (E : WitnessEquivalence C) (P : ProductOps C) where
  pair : ∀ {a b c} {f f' : C.Hom a b} {g g' : C.Hom a c},
    E.Rel f f' → E.Rel g g' → E.Rel (P.pair f g) (P.pair f' g')

structure ProductLaws {Obj : Type u} {C : CategoryOps.{u,v} Obj}
    (E : WitnessEquivalence C) (P : ProductOps C) where
  fst_pair : ∀ {a b c} (f : C.Hom a b) (g : C.Hom a c),
    E.Rel (C.comp P.fst (P.pair f g)) f
  snd_pair : ∀ {a b c} (f : C.Hom a b) (g : C.Hom a c),
    E.Rel (C.comp P.snd (P.pair f g)) g
  pair_eta : ∀ {a b c} (f : C.Hom a (P.prod b c)),
    E.Rel (P.pair (C.comp P.fst f) (C.comp P.snd f)) f

structure CoproductCongr (E : WitnessEquivalence C) (S : CoproductOps C) where
  copair : ∀ {a b c} {f f' : C.Hom a c} {g g' : C.Hom b c},
    E.Rel f f' → E.Rel g g' → E.Rel (S.copair f g) (S.copair f' g')

structure CoproductLaws (E : WitnessEquivalence C) (S : CoproductOps C) where
  left : ∀ {a b c} (f : C.Hom a c) (g : C.Hom b c), E.Rel (C.comp (S.copair f g) S.inl) f
  right : ∀ {a b c} (f : C.Hom a c) (g : C.Hom b c), E.Rel (C.comp (S.copair f g) S.inr) g
  eta : ∀ {a b c} (f : C.Hom (S.sum a b) c),
    E.Rel (S.copair (C.comp f S.inl) (C.comp f S.inr)) f

structure DistributionLaws (E : WitnessEquivalence C) (P : ProductOps C) (S : CoproductOps C)
    (D : DistributionOps C P S) where
  collect_distribute : ∀ a b c, E.Rel (C.comp (collect C P S (a := a) (b := b) (c := c)) D.distribute) C.ident
  distribute_collect : ∀ a b c, E.Rel (C.comp (D.distribute (a := a) (b := b) (c := c)) (collect C P S)) C.ident

structure ClosedCongr (E : WitnessEquivalence C) (P : ProductOps C) (H : ClosedOps C P) where
  curry : ∀ {x a b} {f g : C.Hom (P.prod x a) b}, E.Rel f g → E.Rel (H.curry f) (H.curry g)

structure ClosedLaws (E : WitnessEquivalence C) (P : ProductOps C) (H : ClosedOps C P) where
  beta : ∀ {x a b} (f : C.Hom (P.prod x a) b), E.Rel (H.uncurry (H.curry f)) f
  eta : ∀ {x a b} (f : C.Hom x (H.exp a b)), E.Rel (H.curry (H.uncurry f)) f
  natural : ∀ {x y a b} (f : C.Hom (P.prod x a) b) (g : C.Hom y x),
    E.Rel (H.curry (C.comp f (P.pair (C.comp g P.fst) P.snd))) (C.comp (H.curry f) g)

structure InitialLaws {O : Type u} {C : CategoryOps.{u,v} O}
    (E : WitnessEquivalence C) (T : InitialOps C) where
  unique : ∀ {a} (f : C.Hom T.zero a), E.Rel f T.initial

variable {E : WitnessEquivalence C}

theorem TerminalLaws.erase {T : TerminalOps C} (L : TerminalLaws E T) :
    SquareKit.TerminalLaws E.erase T := ⟨fun f => ⟨L.unique f⟩⟩
theorem InitialLaws.erase {T : InitialOps C} (L : InitialLaws E T) :
    SquareKit.InitialLaws E.erase T := ⟨fun f => ⟨L.unique f⟩⟩
theorem ProductCongr.erase {P : ProductOps C} (L : ProductCongr E P) :
    SquareKit.ProductCongr E.erase P := ⟨fun ⟨h⟩ ⟨k⟩ => ⟨L.pair h k⟩⟩
theorem ProductLaws.erase {P : ProductOps C} (L : ProductLaws E P) :
    SquareKit.ProductLaws E.erase P :=
  ⟨fun f g => ⟨L.fst_pair f g⟩, fun f g => ⟨L.snd_pair f g⟩, fun f => ⟨L.pair_eta f⟩⟩
theorem CoproductCongr.erase {S : CoproductOps C} (L : CoproductCongr E S) :
    SquareKit.CoproductCongr C E.erase S := ⟨fun ⟨h⟩ ⟨k⟩ => ⟨L.copair h k⟩⟩
theorem CoproductLaws.erase {S : CoproductOps C} (L : CoproductLaws E S) :
    SquareKit.CoproductLaws C E.erase S :=
  ⟨fun f g => ⟨L.left f g⟩, fun f g => ⟨L.right f g⟩, fun f => ⟨L.eta f⟩⟩
theorem DistributionLaws.erase {P : ProductOps C} {S : CoproductOps C}
    {D : DistributionOps C P S} (L : DistributionLaws E P S D) :
    SquareKit.DistributionLaws C E.erase P S D :=
  ⟨fun a b c => ⟨L.collect_distribute a b c⟩, fun a b c => ⟨L.distribute_collect a b c⟩⟩
theorem ClosedCongr.erase {P : ProductOps C} {H : ClosedOps C P} (L : ClosedCongr E P H) :
    SquareKit.ClosedCongr E.erase P H := ⟨fun ⟨h⟩ => ⟨L.curry h⟩⟩
theorem ClosedLaws.erase {P : ProductOps C} {H : ClosedOps C P} (L : ClosedLaws E P H) :
    SquareKit.ClosedLaws E.erase P H :=
  ⟨fun f => ⟨L.beta f⟩, fun f => ⟨L.eta f⟩, fun f g => ⟨L.natural f g⟩⟩

end SquareKit.WitnessEquivalence
