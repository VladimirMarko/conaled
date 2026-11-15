import Examples.AssemblyCertificateFamily
import SquareKit.AssemblyBoundedFamily

/-! The certificate comparison retains arbitrary contexts and joint tracking. -/
namespace AssemblyCertificateFamily
open VaryingPartialCertificates UniformCertificateStates
open Realizability Realizability.Assembly CategoryTheory

/-- Context and state realizers travel together. An arrow into this family must
produce both uniformly from its input realizer. -/
def contextualStates {Γ : Assembly} (capacity : Hom Γ (encoded Nat)) : Assembly where
  Carrier := (γ : Γ.Carrier) × (stateAssembly (capacity.toFun γ)).Carrier
  realizes e q := Γ.realizes e.unpair.1 q.1 ∧ StateRealizer e.unpair.2 q.2.val
  inhabited q := by
    obtain ⟨r, hr⟩ := Γ.inhabited q.1
    obtain ⟨e, he⟩ := q.2.property
    exact ⟨Nat.pair r e, by simpa using And.intro hr he⟩

noncomputable def familyToStates {Γ : Assembly} (capacity : Hom Γ (encoded Nat)) :
    Hom (boundedFamily capacity) (contextualStates capacity) where
  toFun q := ⟨q.val.1, (toStates (capacity.toFun q.val.1)).toFun ⟨q.val.2,q.property⟩⟩
  tracked := by
    refine ⟨Part.some, Nat.Partrec.some, ?_⟩
    intro q e he
    refine ⟨e, by simp, he.1, ?_⟩
    exact (recover_realizer_iff ⟨q.val.2,q.property⟩).mpr he.2

noncomputable def familyFromStates {Γ : Assembly} (capacity : Hom Γ (encoded Nat)) :
    Hom (contextualStates capacity) (boundedFamily capacity) where
  toFun q := ⟨(q.1, stateSequence q.2.val q.2.property),
    stateSequence_bounded q.2.val q.2.property⟩
  tracked := by
    refine ⟨Part.some, Nat.Partrec.some, ?_⟩
    intro q e he
    refine ⟨e, by simp, he.1, ?_⟩
    intro k r hr
    change r = k at hr
    subst r
    obtain ⟨c, hc, hs⟩ := he.2 k
    refine ⟨c, hc, liftNat_realizes_iff.mpr ?_⟩
    intro v
    exact (hs v).trans (coordinate_eq_some q.2.val k v).symm

noncomputable def familyComparison {Γ : Assembly} (capacity : Hom Γ (encoded Nat)) :
    boundedFamily capacity ≅ contextualStates capacity where
  hom := familyToStates capacity
  inv := familyFromStates capacity
  hom_inv_id := by
    apply Hom.ext
    intro q
    apply Subtype.ext
    exact Prod.ext rfl (congrArg Subtype.val
      (congrArg (fun f => f.toFun (⟨q.val.2,q.property⟩ :
        (boundedSequences (capacity.toFun q.val.1)).Carrier))
        (stateComparison (capacity.toFun q.val.1)).hom_inv_id))
  inv_hom_id := by
    apply Hom.ext
    rintro ⟨γ,q⟩
    exact congrArg (fun z => Sigma.mk γ z)
      (congrArg (fun f => f.toFun q) (stateComparison (capacity.toFun γ)).inv_hom_id)

/-- Coordinate evaluation and reassembly preserve the complete selected record. -/
theorem familyComparison_coordinate {Γ : Assembly} (capacity : Hom Γ (encoded Nat))
    (q : (boundedFamily capacity).Carrier) (k : Nat) :
    coordinate ((familyComparison capacity).hom.toFun q).2.val k = q.val.2.toFun k :=
  recover_coordinate ⟨q.val.2,q.property⟩ k

end AssemblyCertificateFamily
