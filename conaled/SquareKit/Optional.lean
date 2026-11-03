import SquareKit.Category

/-! Optional operations do not enlarge category or product clients. -/
namespace SquareKit
universe u v
variable {Obj : Type u} (C : CategoryOps.{u,v} Obj)

structure CoproductOps where
  sum : Obj → Obj → Obj
  inl : {a b : Obj} → C.Hom a (sum a b)
  inr : {a b : Obj} → C.Hom b (sum a b)
  copair : {a b c : Obj} → C.Hom a c → C.Hom b c → C.Hom (sum a b) c

structure CoproductCongr (E : HomEquiv C) (S : CoproductOps C) : Prop where
  copair : ∀ {a b c} {f f' : C.Hom a c} {g g' : C.Hom b c},
    E.Rel f f' → E.Rel g g' → E.Rel (S.copair f g) (S.copair f' g')

structure CoproductLaws (E : HomEquiv C) (S : CoproductOps C) : Prop where
  left : ∀ {a b c} (f : C.Hom a c) (g : C.Hom b c), E.Rel (C.comp (S.copair f g) S.inl) f
  right : ∀ {a b c} (f : C.Hom a c) (g : C.Hom b c), E.Rel (C.comp (S.copair f g) S.inr) g
  eta : ∀ {a b c} (f : C.Hom (S.sum a b) c),
    E.Rel (S.copair (C.comp f S.inl) (C.comp f S.inr)) f

/-- The canonical map exists without distributivity; distribution chooses its inverse. -/
def collect (P : ProductOps C) (S : CoproductOps C) {a b c : Obj} :
    C.Hom (S.sum (P.prod a b) (P.prod a c)) (P.prod a (S.sum b c)) :=
  S.copair (P.pair P.fst (C.comp S.inl P.snd)) (P.pair P.fst (C.comp S.inr P.snd))

structure DistributionOps (P : ProductOps C) (S : CoproductOps C) where
  distribute : {a b c : Obj} → C.Hom (P.prod a (S.sum b c)) (S.sum (P.prod a b) (P.prod a c))

/-- Distribution has no arrow arguments, hence requires no extra congruence field. -/
structure DistributionLaws (E : HomEquiv C) (P : ProductOps C) (S : CoproductOps C)
    (D : DistributionOps C P S) : Prop where
  collect_distribute : ∀ a b c, E.Rel (C.comp (collect C P S (a := a) (b := b) (c := c)) D.distribute) C.ident
  distribute_collect : ∀ a b c, E.Rel (C.comp (D.distribute (a := a) (b := b) (c := c)) (collect C P S)) C.ident

structure ClosedOps (P : ProductOps C) where
  exp : Obj → Obj → Obj
  evaluation : {a b : Obj} → C.Hom (P.prod (exp a b) a) b
  curry : {x a b : Obj} → C.Hom (P.prod x a) b → C.Hom x (exp a b)

variable {C}
def ClosedOps.uncurry {P : ProductOps C} (H : ClosedOps C P)
    {x a b : Obj} (f : C.Hom x (H.exp a b)) : C.Hom (P.prod x a) b :=
  C.comp H.evaluation (P.pair (C.comp f P.fst) P.snd)

structure ClosedCongr (E : HomEquiv C) (P : ProductOps C) (H : ClosedOps C P) : Prop where
  curry : ∀ {x a b} {f g : C.Hom (P.prod x a) b}, E.Rel f g → E.Rel (H.curry f) (H.curry g)

structure ClosedLaws (E : HomEquiv C) (P : ProductOps C) (H : ClosedOps C P) : Prop where
  beta : ∀ {x a b} (f : C.Hom (P.prod x a) b), E.Rel (H.uncurry (H.curry f)) f
  eta : ∀ {x a b} (f : C.Hom x (H.exp a b)), E.Rel (H.curry (H.uncurry f)) f
  natural : ∀ {x y a b} (f : C.Hom (P.prod x a) b) (g : C.Hom y x),
    E.Rel (H.curry (C.comp f (P.pair (C.comp g P.fst) P.snd))) (C.comp (H.curry f) g)
end SquareKit
