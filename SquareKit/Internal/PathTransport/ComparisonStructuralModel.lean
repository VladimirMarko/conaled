import SquareKit.Internal.PathTransport.ComparisonIdentity
import SquareKit.Internal.PathTransport.ComparisonSignature

/-! A constructed structural model of ordinary-groupoid comparisons. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Comparison
open CategoryTheory
universe u

/-- Structural operations use the two direct interpretations; every comparison
component and preservation law is constructed from the signature map. -/
def structuralModel (S : Signature.{u}) : Typed.StructuralModel.{u+1} where
  Context := Context.{u}
  Family := Family
  Section _ := Section
  Substitution := Substitution
  empty := ⟨@Grpd.of (Discrete PUnit) Groupoid.ofIsGroupoid,
    @Grpd.of (Discrete PUnit) Groupoid.ofIsGroupoid, 𝟭 _⟩
  extend _ := Family.extend
  idSub := Substitution.id
  compSub := Substitution.comp
  subTy := Family.reindex
  subTm := Section.reindex
  weaken _ := Family.weaken
  genericVariable _ := Family.variable
  pairSub := Family.pair
  base := S.baseFamily
  fiber := S.fiber
  identity := Family.identity
  reflexivity := Family.reflexivity
  comp_id_left := Substitution.comp_id_left
  comp_id_right := Substitution.comp_id_right
  comp_assoc := Substitution.comp_assoc
  subTy_id := Family.reindex_id
  subTy_comp := Family.reindex_comp
  subTm_id := Section.reindex_id
  subTm_comp := Section.reindex_comp
  base_sub := S.base_sub
  fiber_sub := S.fiber_sub
  identity_sub := Family.identity_sub
  refl_sub := Family.refl_sub
  weaken_pair := Family.weaken_pair
  variable_pair := Family.variable_pair
  pair_eta := Family.pair_eta

end SquareKit.Internal.PathTransport.GroupoidModel.Comparison
