import SquareKit.AdjointModes.Syntax
import Squares

/-! Local resource and payload certificates extend to every construction of the
source fragment. A payload interpretation is independent of the resource model. -/
namespace SquareKit.AdjointModes
set_option backward.isDefEq.respectTransparency false

abbrev PayloadMeaning (v : Atoms) (P : Signature) :=
  {m : Mode} → {A B : Ty m} → P A B → A.Payload v → B.Payload v

def Term.denote {P} (v : Atoms) (p : PayloadMeaning v P) :
    {m : Mode} → {A B : Ty m} → Term P A B → A.Payload v → B.Payload v
  | _, _, _, .prim a => p a
  | _, _, _, .id => _root_.id
  | _, _, _, .comp g f => g.denote v p ∘ f.denote v p
  | _, _, _, .times f g => fun x => (f.denote v p x.1, g.denote v p x.2)
  | _, _, _, .swap => fun x => (x.2,x.1)
  | _, _, _, .assoc => fun x => (x.1.1,(x.1.2,x.2))
  | _, _, _, .unassoc => fun x => ((x.1,x.2.1),x.2.2)
  | _, _, _, .unitor => Prod.snd
  | _, _, _, .ununitor => fun x => ((),x)
  | _, _, _, .copy => fun x => (x,x)
  | _, _, _, .discard => fun _ => ()
  | _, _, _, .downMap f => f.denote v p
  | _, _, _, .upMap f => f.denote v p
  | _, _, _, .unit => _root_.id
  | _, _, _, .counit => _root_.id
  | _, _, _, .downTimes => _root_.id
  | _, _, _, .timesDown => _root_.id
  | _, _, _, .downOne => _root_.id
  | _, _, _, .oneDown => _root_.id

def Term.compile {P} (v : Atoms) (p : PrimitiveMeaning v P) :
    {m : Mode} → {A B : Ty m} → Term P A B → Map (A.meaning v) (B.meaning v)
  | _, _, _, .prim a => p a
  | _, _, _, .id => Map.identity _
  | _, _, _, .comp g f => (g.compile v p).comp (f.compile v p)
  | _, _, _, .times f g =>
      ⟨fun x => ((f.compile v p).run x.1, (g.compile v p).run x.2),
        fun x => congrArg₂ (· + ·) ((f.compile v p).preserves x.1) ((g.compile v p).preserves x.2)⟩
  | _, _, _, .swap => ⟨fun x => (x.2,x.1), fun x => Nat.add_comm _ _⟩
  | _, _, _, .assoc => ⟨fun x => (x.1.1,(x.1.2,x.2)), fun _ => (Nat.add_assoc _ _ _).symm⟩
  | _, _, _, .unassoc => ⟨fun x => ((x.1,x.2.1),x.2.2), fun _ => Nat.add_assoc _ _ _⟩
  | _, _, _, .unitor => ⟨Prod.snd, fun _ => (Nat.zero_add _).symm⟩
  | _, _, _, .ununitor => ⟨fun x => ((),x), fun _ => Nat.zero_add _⟩
  | _, A, _, .copy => ⟨fun x => (x,x), fun x => by
      change (A.meaning v).degree x + (A.meaning v).degree x = (A.meaning v).degree x
      rw [A.unrestricted_zero v x]⟩
  | _, A, _, .discard => ⟨fun _ => (), fun x => (A.unrestricted_zero v x).symm⟩
  | _, _, _, .downMap f => AdjointModes.downMap (f.compile v p).run
  | _, _, _, .upMap f => AdjointModes.downMap (AdjointModes.upMap (f.compile v p))
  | _, A, _, .unit => ⟨fun x => ⟨x, rfl⟩, fun x => (A.unrestricted_zero v x).symm⟩
  | _, _, _, .counit => AdjointModes.counit _
  | _, _, _, .downTimes => ⟨_root_.id, fun _ => rfl⟩
  | _, _, _, .timesDown => ⟨_root_.id, fun _ => rfl⟩
  | _, _, _, .downOne => ⟨_root_.id, fun _ => rfl⟩
  | _, _, _, .oneDown => ⟨_root_.id, fun _ => rfl⟩

/-- Only primitive payload agreement is supplied; the compiler derives the
whole-program commuting square by structural induction. -/
theorem Term.compile_preserves {P} (v : Atoms) (p : PrimitiveMeaning v P)
    (q : PayloadMeaning v P)
    (primitive_correct : ∀ {m} {A B : Ty m} (a : P A B) x,
      B.forget v ((p a).run x) = q a (A.forget v x))
    {m} {A B : Ty m} (t : Term P A B) (x : (A.meaning v).Carrier) :
    B.forget v ((t.compile v p).run x) = t.denote v q (A.forget v x) := by
  induction t with
  | prim a => exact primitive_correct a x
  | id => rfl
  | comp g f ihg ihf => exact (ihg _).trans (congrArg (g.denote v q) (ihf x))
  | times f g ihf ihg => exact congrArg₂ Prod.mk (ihf x.1) (ihg x.2)
  | downMap f ih => exact ih x
  | upMap f ih => exact ih x.val
  | swap | assoc | unassoc | unitor | ununitor | copy | discard | unit | counit |
      downTimes | timesDown | downOne | oneDown => rfl

/-- Resource preservation is exact, not merely an upper bound on consumption. -/
theorem Term.resource_sound {P} (v : Atoms) (p : PrimitiveMeaning v P)
    {m} {A B : Ty m} (t : Term P A B) (x) :
    (B.meaning v).degree ((t.compile v p).run x) = (A.meaning v).degree x :=
  (t.compile v p).preserves x

abbrev EmptySignature : Signature := fun _ _ => Empty

def emptyMeaning (v : Atoms) : PrimitiveMeaning v EmptySignature := fun e => nomatch e

def tokenAtoms : Atoms := ⟨Nat, atom⟩

theorem no_generic_linear_copy : ¬Nonempty
    (Term EmptySignature (.atom .linear) (.times (.atom .linear) (.atom .linear))) := by
  rintro ⟨t⟩
  exact atom_no_copy ⟨t.compile tokenAtoms (emptyMeaning tokenAtoms)⟩

theorem no_generic_linear_discard : ¬Nonempty
    (Term EmptySignature (.atom .linear) (.one .linear)) := by
  rintro ⟨t⟩
  exact atom_no_discard ⟨t.compile tokenAtoms (emptyMeaning tokenAtoms)⟩

/-- The source-level transpose uses only the restricted unit and functorial upshift. -/
def Term.transpose {P} {A : Ty .unrestricted} {B : Ty .linear}
    (f : Term P (.down A) B) : Term P A (.up B) := .comp (.upMap f) .unit

def Term.untranspose {P} {A : Ty .unrestricted} {B : Ty .linear}
    (g : Term P A (.up B)) : Term P (.down A) B := .comp .counit (.downMap g)

theorem Term.transpose_compiles {P} (v : Atoms) (p : PrimitiveMeaning v P)
    {A : Ty .unrestricted} {B : Ty .linear} (f : Term P (.down A) B) :
    (f.transpose.compile v p).run =
      shiftAdjunction (A.meaning v).Carrier (B.meaning v) (show Map (down (A.meaning v).Carrier) (B.meaning v) from @Term.compile P v p .linear (.down A) B f) := rfl

theorem Term.transpose_roundtrip {P} (v : Atoms) (p : PrimitiveMeaning v P)
    {A : Ty .unrestricted} {B : Ty .linear} (f : Term P (.down A) B) :
    (f.transpose.untranspose).compile v p = f.compile v p := by
  apply Map.ext
  intro x
  rfl

theorem Term.untranspose_roundtrip {P} (v : Atoms) (p : PrimitiveMeaning v P)
    {A : Ty .unrestricted} {B : Ty .linear} (g : Term P A (.up B)) :
    (g.untranspose.transpose).compile v p = g.compile v p := by
  apply Map.ext
  intro x
  rfl

end SquareKit.AdjointModes
