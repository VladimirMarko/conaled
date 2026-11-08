import SquareKit.AdjointModes.Translation

/-! A terminating big-step semantics for this finite combinator fragment only.
It models selected payload evaluation, not allocation, garbage collection, or
the abstract machine of Adjoint Natural Deduction. -/
namespace SquareKit.AdjointModes
set_option backward.isDefEq.respectTransparency false

inductive Eval {P} (v : Atoms) (p : PayloadMeaning v P) :
    {m : Mode} → {A B : Ty m} → Term P A B → A.Payload v → B.Payload v → Prop
  | prim {m} {A B : Ty m} (a : P A B) (x) : Eval v p (.prim a) x (p a x)
  | id {m} {A : Ty m} (x) : Eval v p (Term.id (A := A)) x x
  | comp {m} {A B C : Ty m} {f : Term P A B} {g : Term P B C} {x y z} :
      Eval v p f x y → Eval v p g y z → Eval v p (.comp g f) x z
  | times {m} {A B C D : Ty m} {f : Term P A B} {g : Term P C D} {x y u w} :
      Eval v p f x y → Eval v p g u w → Eval v p (.times f g) (x,u) (y,w)
  | swap {m} {A B : Ty m} (x : A.Payload v) (y : B.Payload v) : Eval v p (Term.swap (A := A) (B := B)) (x,y) (y,x)
  | assoc {m} {A B C : Ty m} (x : A.Payload v) (y : B.Payload v) (z : C.Payload v) :
      Eval v p (Term.assoc (A := A) (B := B) (C := C)) ((x,y),z) (x,(y,z))
  | unassoc {m} {A B C : Ty m} (x : A.Payload v) (y : B.Payload v) (z : C.Payload v) :
      Eval v p (Term.unassoc (A := A) (B := B) (C := C)) (x,(y,z)) ((x,y),z)
  | unitor {m} {A : Ty m} (x : A.Payload v) : Eval v p (Term.unitor (A := A)) ((),x) x
  | ununitor {m} {A : Ty m} (x : A.Payload v) : Eval v p (Term.ununitor (A := A)) x ((),x)
  | copy {A : Ty .unrestricted} (x : A.Payload v) : Eval v p (Term.copy (A := A)) x (x,x)
  | discard {A : Ty .unrestricted} (x : A.Payload v) : Eval v p (Term.discard (A := A)) x ()
  | downMap {A B} {f : Term P A B} {x y} : Eval v p f x y → Eval v p (.downMap f) x y
  | upMap {A B} {f : Term P A B} {x y} : Eval v p f x y → Eval v p (.upMap f) x y
  | unit {A : Ty .unrestricted} (x : A.Payload v) : Eval v p (Term.unit (A := A)) x x
  | counit {A : Ty .linear} (x : A.Payload v) : Eval v p (Term.counit (A := A)) x x
  | downTimes {A B : Ty .unrestricted} (x : A.Payload v) (y : B.Payload v) : Eval v p (Term.downTimes (A := A) (B := B)) (x,y) (x,y)
  | timesDown {A B : Ty .unrestricted} (x : A.Payload v) (y : B.Payload v) : Eval v p (Term.timesDown (A := A) (B := B)) (x,y) (x,y)
  | downOne : Eval v p .downOne () ()
  | oneDown : Eval v p .oneDown () ()

theorem Eval.sound {P} {v : Atoms} {p : PayloadMeaning v P} {m} {A B : Ty m}
    {t : Term P A B} {x y} (h : Eval v p t x y) : t.denote v p x = y := by
  induction h <;> simp_all [Term.denote]

theorem Eval.complete {P} (v : Atoms) (p : PayloadMeaning v P) {m} {A B : Ty m}
    (t : Term P A B) (x) : Eval v p t x (t.denote v p x) := by
  induction t with
  | prim a => exact .prim a x
  | id => exact .id x
  | comp g f ihg ihf => exact .comp (ihf x) (ihg _)
  | times f g ihf ihg => exact .times (ihf x.1) (ihg x.2)
  | swap => exact .swap x.1 x.2
  | assoc => exact .assoc x.1.1 x.1.2 x.2
  | unassoc => exact .unassoc x.1 x.2.1 x.2.2
  | unitor => cases x.1; exact .unitor x.2
  | ununitor => exact .ununitor x
  | copy => exact .copy x
  | discard => exact .discard x
  | downMap f ih => exact .downMap (ih x)
  | upMap f ih => exact .upMap (ih x)
  | unit => exact .unit x
  | @counit A => exact Eval.counit (A := A) x
  | downTimes => exact .downTimes x.1 x.2
  | timesDown => exact .timesDown x.1 x.2
  | downOne => cases x; exact .downOne
  | oneDown => cases x; exact .oneDown

theorem Eval.deterministic {P} {v : Atoms} {p : PayloadMeaning v P} {m} {A B : Ty m}
    {t : Term P A B} {x y z} (h : Eval v p t x y) (k : Eval v p t x z) : y = z :=
  h.sound.symm.trans k.sound

/-- Compiler adequacy for selected payload big-step evaluation. Primitive
implementations must additionally respect the resource model. -/
theorem Term.compile_evaluates {P} (v : Atoms) (p : PrimitiveMeaning v P)
    (q : PayloadMeaning v P)
    (primitive_correct : ∀ {m} {A B : Ty m} (a : P A B) x,
      B.forget v ((p a).run x) = q a (A.forget v x))
    {m} {A B : Ty m} (t : Term P A B) (x) :
    Eval v q t (A.forget v x) (B.forget v ((t.compile v p).run x)) := by
  rw [t.compile_preserves v p q primitive_correct]
  exact Eval.complete v q t _

end SquareKit.AdjointModes
