import SquareKit.WitnessSetoids

namespace SquareKit.WitnessSetoids
universe u v

/-- Exponentials use the common carrier/witness universe of the pinned source. -/
def exponential (A B : Obj.{u,u}) : Obj.{u,u} where
  Carrier := Hom A B
  Rel f g := ∀ x, B.Rel (f.toFun x) (g.toFun x)
  refl f x := B.refl (f.toFun x)
  symm := fun h x => B.symm (h x)
  trans := fun h k x => B.trans (h x) (k x)

def closed : ClosedOps ops.{u,u} products where
  exp := exponential
  evaluation {_ b} := ⟨fun p => p.1.toFun p.2,fun {_ y} h =>
    b.trans (h.1 _) (y.1.congr h.2)⟩
  curry {x a _} f := ⟨fun z => ⟨fun y => f.toFun (z,y),fun h => f.congr ⟨x.refl _,h⟩⟩,
    fun h y => f.congr ⟨h,a.refl y⟩⟩
def closed_congr : WitnessEquivalence.ClosedCongr equiv products closed.{u} := ⟨fun h x a => h (x,a)⟩
def closed_laws : WitnessEquivalence.ClosedLaws equiv products closed.{u} :=
  ⟨fun {_ _ b} _ _ => b.refl _,fun {_ _ b} _ _ _ => b.refl _,
    fun {_ _ _ b} _ _ _ _ => b.refl _⟩


end SquareKit.WitnessSetoids
