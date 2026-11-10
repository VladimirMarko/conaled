import SquareKit.WitnessSetoidsClosed
import SquareKit.WitnessUniversal

namespace SquareKit.WitnessSetoids
universe u v

def distribution : DistributionOps ops.{u,v} products coproducts where
  distribute := ⟨fun p => match p.2 with
    | .inl b => .inl (p.1,b)
    | .inr c => .inr (p.1,c), by
      intro x y h
      rcases x with ⟨x₁,x₂⟩; rcases y with ⟨y₁,y₂⟩
      cases x₂ <;> cases y₂
      · exact h
      · exact h.2.elim
      · exact h.2.elim
      · exact h⟩

def rightDistribution : RightDistributionOps products coproducts.{u,v} where
  distribute := ⟨fun p => match p.1 with
    | .inl b => .inl (b,p.2)
    | .inr c => .inr (c,p.2), by
      intro x y h
      rcases x with ⟨x₁,x₂⟩; rcases y with ⟨y₁,y₂⟩
      cases x₁ <;> cases y₁
      · exact h
      · exact h.1.elim
      · exact h.1.elim
      · exact h⟩

def distribution_laws : WitnessEquivalence.DistributionLaws equiv products coproducts distribution.{u,v} := by
  constructor
  · intro a b c x; rcases x with ⟨x,y⟩; cases y <;> exact (prod a (sum b c)).refl _
  · intro a b c x; cases x <;> exact (sum (prod a b) (prod a c)).refl _

def rightDistribution_laws : WitnessEquivalence.RightDistributionLaws (E := equiv)
    products coproducts rightDistribution.{u,v} := by
  constructor
  · intro a b c x; rcases x with ⟨y,x⟩; cases y <;> exact (prod (sum b c) a).refl _
  · intro a b c x; cases x <;> exact (sum (prod b a) (prod c a)).refl _

/-- Source universal-product witnesses are projected and paired without normalization. -/
def product_universal : WitnessEquivalence.ProductUniversal (E := equiv) products.{u,v} where
  forward h := ⟨fun x => (h x).1, fun x => (h x).2⟩
  backward h x := ⟨h.1 x,h.2 x⟩

def coproduct_universal : WitnessEquivalence.CoproductUniversal (E := equiv) coproducts.{u,v} where
  forward h := ⟨fun x => h (.inl x), fun x => h (.inr x)⟩
  backward h := fun x => match x with
    | .inl x => h.1 x
    | .inr x => h.2 x

/-- Felix's chosen closed universal witnesses use symmetry directly. -/
def closed_universal : WitnessEquivalence.ClosedUniversal (E := equiv) closed.{u} where
  forward := fun {_ _ B} {_ _} h x => B.symm (h x.1 x.2)
  backward := fun {_ _ B} {_ _} h x y => B.symm (h (x,y))

end SquareKit.WitnessSetoids
