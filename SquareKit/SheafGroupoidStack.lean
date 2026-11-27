import SquareKit.SheafGroupoidBundleStackDescent
import SquareKit.StackObjectPropertyDescent

/-! The stack of principal groupoid bundles and the prestack of represented objects. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.SheafGroupoid.Bundle
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (G : Operations J) [G.Laws]
namespace Stack

instance isPrestack : (pseudofunctor G).IsPrestack (SheafCover.topology (J := J)) where
  isSheaf {S} M N := by
    apply Presheaf.IsSheaf.of_le (SheafCover.over_topology_le S)
    rw [isSheaf_iff_isSheaf_of_type, Presieve.isSheaf_coverage]
    rintro X R ⟨Y, f, rfl, hf⟩
    rw [Presieve.isSheafFor_iff_generate]
    apply Pseudofunctor.IsPrestackFor.isSheafFor'
    rw [Sieve.overEquiv_generate, ← Sieve.arrows_generate_map_eq_functorPushforward,
      Sieve.generate_sieve]
    simp only [Presieve.map_singleton]
    rw [← Presieve.ofArrows_pUnit.{0}]
    apply (Pseudofunctor.IsPrestackFor_generate_iff _ _).mpr
    exact (isStackFor_cover (G := G) f.left).isPrestackFor

instance isStack : (pseudofunctor G).IsStack (SheafCover.topology (J := J)) := by
  apply Pseudofunctor.IsStack.of_isStackFor
  rintro X R ⟨Y, f, hf, hR⟩
  apply Pseudofunctor.IsStackFor.of_le (pseudofunctor G) (isStackFor_cover (G := G) f) (J := SheafCover.topology (J := J))
  · exact ⟨Y, f, hf, Sieve.ofArrows_mk _ _ ()⟩
  · intro Z g hg
    cases hg
    exact hR

end Stack

/-- Full faithfulness into the constructed stack proves descent of source arrows. -/
instance sourceIsPrestack : G.pseudofunctor.IsPrestack (SheafCover.topology (J := J)) :=
  StackObjectPropertyDescent.isPrestack_of_fullyFaithful (unit G)
    (fun _ => regularFullyFaithful G) _

end SquareKit.SheafGroupoid.Bundle
