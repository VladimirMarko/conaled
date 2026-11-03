import SquareKit.CommaExact

/-! Vertical pasting needs only target congruence and associativity. The middle
arrows agree after interpretation, modulo the target hom equivalence. Felix's
`Construct/Comma/Vertical.agda` at 6f36d28097db7ea5f5df3263db3e8be08f74e490
uses equality of interpreted arrows and notes this weaker alternative. No
source laws, interpretation preservation, or injectivity is required here. -/
namespace SquareKit.Comma
universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {T : Type u₄}
variable {CA : CategoryOps.{u₁,v₁} A} {CB : CategoryOps.{u₂,v₂} B}
variable {CC : CategoryOps.{u₃,v₃} C} {K : CategoryOps.{u₄,v₄} T}
variable {F : RawMap CA K} {G : RawMap CB K} {I : RawMap CC K}

/-- Follow a connector by a second interpretation stage. -/
def after (a : Obj F G) (c : C) (k : K.Hom (G.obj a.right) (I.obj c)) : Obj F I :=
  ⟨a.left, c, K.comp k a.connector⟩

/-- Keep the outer arrows; compose the two vertical connectors. -/
def vertical {H : HomEquiv K} (KC : CategoryCongr K H) (KL : CategoryLaws K H)
    {a b : Obj F G} {c d : C}
    {k : K.Hom (G.obj a.right) (I.obj c)} {l : K.Hom (G.obj b.right) (I.obj d)}
    (f : Hom H a b) (g : Hom H (Obj.mk a.right c k : Obj G I) (Obj.mk b.right d l))
    (middle : H.Rel (G.map f.right) (G.map g.left)) :
    Hom H (after a c k) (after b d l) where
  left := f.left
  right := g.right
  commutes := H.trans (KL.assoc _ _ _)
    (H.trans (KC.comp (H.refl _) f.commutes)
    (H.trans (H.symm (KL.assoc _ _ _))
    (H.trans (KC.comp (KC.comp (H.refl _) middle) (H.refl _))
    (H.trans (KC.comp g.commutes (H.refl _)) (KL.assoc _ _ _)))))

namespace Exact
@[simp] theorem ofRep_after (a : Squares.Rep.{u₁}) {T : Type u₁} (d : a.S → T) :
    ofRep (a.after d) = after (I := interpretation) (ofRep a) T d := rfl

@[simp] theorem ofSquare_vertical {a b : Squares.Rep.{u₁}} {AS BS : Type u₁}
    (da : a.S → AS) (db : b.S → BS) (f : Squares.Square a b)
    (g : Squares.Square ⟨a.S, AS, da⟩ ⟨b.S, BS, db⟩)
    (middle : ∀ x, f.spec x = g.impl x) :
    ofSquare (Squares.vertical da db f g middle) =
      vertical (equalityCongr FunctionCategory.ops) FunctionCategory.laws
        (ofSquare f) (ofSquare g) (funext middle) := rfl
end Exact
end SquareKit.Comma
