import SquareKit.WitnessSetoidsClosed

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

end SquareKit.WitnessSetoids
