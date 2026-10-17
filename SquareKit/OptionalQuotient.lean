import SquareKit.Optional

namespace SquareKit.HomQuotient
universe u v
variable {Obj : Type u} {C : CategoryOps.{u,v} Obj} {E : HomEquiv C}
variable (K : CategoryCongr C E) (L : CategoryLaws C E)

def coproducts (S : CoproductOps C) (SC : CoproductCongr C E S) : CoproductOps (ops K L) where
  sum a b := ⟨S.sum a.as b.as⟩
  inl := Quotient.mk _ S.inl
  inr := Quotient.mk _ S.inr
  copair f g := Quotient.liftOn₂ f g (fun f g => Quotient.mk _ (S.copair f g))
    (fun _ _ _ _ hf hg => Quotient.sound (SC.copair hf hg))

theorem coproductLaws (S : CoproductOps C) (SC : CoproductCongr C E S) (SL : CoproductLaws C E S) :
    CoproductLaws (ops K L) (equality _) (coproducts K L S SC) where
  left f g := Quotient.inductionOn₂ f g (fun f g => Quotient.sound (SL.left f g))
  right f g := Quotient.inductionOn₂ f g (fun f g => Quotient.sound (SL.right f g))
  eta f := Quotient.inductionOn f (fun f => Quotient.sound (SL.eta f))

def distribution (P : ProductOps C) (PC : ProductCongr E P)
    (S : CoproductOps C) (SC : CoproductCongr C E S) (D : DistributionOps C P S) :
    DistributionOps (ops K L) (products K L P PC) (coproducts K L S SC) where
  distribute := Quotient.mk _ D.distribute

theorem distributionLaws (P : ProductOps C) (PC : ProductCongr E P)
    (S : CoproductOps C) (SC : CoproductCongr C E S) (D : DistributionOps C P S)
    (DL : DistributionLaws C E P S D) :
    DistributionLaws (ops K L) (equality _) (products K L P PC) (coproducts K L S SC)
      (distribution K L P PC S SC D) where
  collect_distribute a b c := Quotient.sound (DL.collect_distribute a.as b.as c.as)
  distribute_collect a b c := Quotient.sound (DL.distribute_collect a.as b.as c.as)

def closed (P : ProductOps C) (PC : ProductCongr E P) (H : ClosedOps C P)
    (HC : ClosedCongr E P H) : ClosedOps (ops K L) (products K L P PC) where
  exp a b := ⟨H.exp a.as b.as⟩
  evaluation := Quotient.mk _ H.evaluation
  curry f := Quotient.liftOn f (fun f => Quotient.mk _ (H.curry f))
    (fun _ _ h => Quotient.sound (HC.curry h))

theorem closedLaws (P : ProductOps C) (PC : ProductCongr E P) (H : ClosedOps C P)
    (HC : ClosedCongr E P H) (HL : ClosedLaws E P H) :
    ClosedLaws (equality _) (products K L P PC) (closed K L P PC H HC) where
  beta f := Quotient.inductionOn f (fun f => Quotient.sound (HL.beta f))
  eta f := Quotient.inductionOn f (fun f => Quotient.sound (HL.eta f))
  natural f g := Quotient.inductionOn₂ f g (fun f g => Quotient.sound (HL.natural f g))

@[simp] theorem mk_inl (S : CoproductOps C) (SC : CoproductCongr C E S) (a b : Obj) :
    classOf (E := E) (S.inl (a := a) (b := b)) = (coproducts K L S SC).inl (a := ⟨a⟩) (b := ⟨b⟩) := rfl
@[simp] theorem mk_inr (S : CoproductOps C) (SC : CoproductCongr C E S) (a b : Obj) :
    classOf (E := E) (S.inr (a := a) (b := b)) = (coproducts K L S SC).inr (a := ⟨a⟩) (b := ⟨b⟩) := rfl
@[simp] theorem mk_copair (S : CoproductOps C) (SC : CoproductCongr C E S)
    {a b c : Obj} (f : C.Hom a c) (g : C.Hom b c) :
    classOf (E := E) (S.copair f g) = (coproducts K L S SC).copair (classOf f) (classOf g) := rfl
@[simp] theorem mk_distribute (P : ProductOps C) (PC : ProductCongr E P)
    (S : CoproductOps C) (SC : CoproductCongr C E S) (D : DistributionOps C P S) (a b c : Obj) :
    classOf (E := E) (D.distribute (a := a) (b := b) (c := c)) =
      (distribution K L P PC S SC D).distribute (a := ⟨a⟩) (b := ⟨b⟩) (c := ⟨c⟩) := rfl
@[simp] theorem mk_evaluation (P : ProductOps C) (PC : ProductCongr E P)
    (H : ClosedOps C P) (HC : ClosedCongr E P H) (a b : Obj) :
    classOf (E := E) (H.evaluation (a := a) (b := b)) =
      (closed K L P PC H HC).evaluation (a := ⟨a⟩) (b := ⟨b⟩) := rfl
@[simp] theorem mk_curry (P : ProductOps C) (PC : ProductCongr E P)
    (H : ClosedOps C P) (HC : ClosedCongr E P H) {x a b : Obj} (f : C.Hom (P.prod x a) b) :
    classOf (E := E) (H.curry f) = (closed K L P PC H HC).curry (classOf f) := rfl
@[simp] theorem mk_uncurry (P : ProductOps C) (PC : ProductCongr E P)
    (H : ClosedOps C P) (HC : ClosedCongr E P H) {x a b : Obj} (f : C.Hom x (H.exp a b)) :
    classOf (E := E) (H.uncurry f) = (closed K L P PC H HC).uncurry (classOf f) := rfl
end SquareKit.HomQuotient
