import SquareKit.AdjointModes.Compiler

/-! Primitive compiler passes extend through the entire mode fragment. The
passes cannot change resource permission by replacing a linear primitive with
an untyped ordinary function. -/
namespace SquareKit.AdjointModes
set_option backward.isDefEq.respectTransparency false

abbrev Translation (P Q : Signature) := {m : Mode} → {A B : Ty m} → P A B → Term Q A B

def Term.translate {P Q} (f : Translation P Q) :
    {m : Mode} → {A B : Ty m} → Term P A B → Term Q A B
  | _, _, _, .prim a => f a
  | _, _, _, .id => .id
  | _, _, _, .comp g h => .comp (g.translate f) (h.translate f)
  | _, _, _, .times g h => .times (g.translate f) (h.translate f)
  | _, _, _, .swap => .swap
  | _, _, _, .assoc => .assoc
  | _, _, _, .unassoc => .unassoc
  | _, _, _, .unitor => .unitor
  | _, _, _, .ununitor => .ununitor
  | _, _, _, .copy => .copy
  | _, _, _, .discard => .discard
  | _, _, _, .downMap g => .downMap (g.translate f)
  | _, _, _, .upMap g => .upMap (g.translate f)
  | _, _, _, .unit => .unit
  | _, _, _, .counit => .counit
  | _, _, _, .downTimes => .downTimes
  | _, _, _, .timesDown => .timesDown
  | _, _, _, .downOne => .downOne
  | _, _, _, .oneDown => .oneDown

def Translation.identity (P) : Translation P P := fun a => .prim a
def Translation.comp {P Q R} (g : Translation Q R) (f : Translation P Q) : Translation P R :=
  fun a => (f a).translate g

theorem Term.translate_identity {P m} {A B : Ty m} (t : Term P A B) :
    t.translate (Translation.identity P) = t := by
  induction t <;> simp_all [Term.translate, Translation.identity]

theorem Term.translate_comp {P Q R} (f : Translation P Q) (g : Translation Q R)
    {m} {A B : Ty m} (t : Term P A B) :
    t.translate (g.comp f) = (t.translate f).translate g := by
  induction t <;> simp_all [Term.translate, Translation.comp]

theorem Term.translate_preserves {P Q} (v : Atoms)
    (p : PayloadMeaning v P) (q : PayloadMeaning v Q) (f : Translation P Q)
    (primitive_correct : ∀ {m} {A B : Ty m} (a : P A B) x,
      (f a).denote v q x = p a x)
    {m} {A B : Ty m} (t : Term P A B) (x) :
    (t.translate f).denote v q x = t.denote v p x := by
  induction t with
  | prim a => exact primitive_correct a x
  | comp g h ihg ihh => exact (ihg _).trans (congrArg (g.denote v p) (ihh x))
  | times g h ihg ihh => exact congrArg₂ Prod.mk (ihg x.1) (ihh x.2)
  | downMap g ih | upMap g ih => exact ih x
  | id | swap | assoc | unassoc | unitor | ununitor | copy | discard | unit | counit |
      downTimes | timesDown | downOne | oneDown => rfl

/-- Reuse the library square interface for the compiler's full selected payload. -/
def Term.square {P} (v : Atoms) (p : PrimitiveMeaning v P) (q : PayloadMeaning v P)
    (primitive_correct : ∀ {m} {A B : Ty m} (a : P A B) x,
      B.forget v ((p a).run x) = q a (A.forget v x))
    {m} {A B : Ty m} (t : Term P A B) :
    Squares.Square ⟨(A.meaning v).Carrier, A.Payload v, A.forget v⟩
      ⟨(B.meaning v).Carrier, B.Payload v, B.forget v⟩ :=
  ⟨(t.compile v p).run, t.denote v q, t.compile_preserves v p q primitive_correct⟩

theorem Term.square_identity {P} (v : Atoms) (p : PrimitiveMeaning v P) (q : PayloadMeaning v P)
    (h : ∀ {m} {A B : Ty m} (a : P A B) x, B.forget v ((p a).run x) = q a (A.forget v x))
    {m} (A : Ty m) :
    (Term.id (P := P) (A := A)).square v p q h = Squares.identity _ := rfl

theorem Term.square_comp {P} (v : Atoms) (p : PrimitiveMeaning v P) (q : PayloadMeaning v P)
    (h : ∀ {m} {A B : Ty m} (a : P A B) x, B.forget v ((p a).run x) = q a (A.forget v x))
    {m} {A B C : Ty m} (f : Term P A B) (g : Term P B C) :
    (Term.comp g f).square v p q h = Squares.compose (g.square v p q h) (f.square v p q h) := rfl

end SquareKit.AdjointModes
