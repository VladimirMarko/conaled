import SquareKit.Internal.Cubical.EquivalenceFamilies

/-! Native equivalence sections retain Boolean transposition and its selected
fiber contractions. The witness comparison is a native path. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalEquivalenceFamilies
open CategoryTheory SquareKit.Cubical.Presheaf
open EquivalenceFamilies
variable {Γ : Context.{0}}

def boolIso : constantFamily Γ Bool ≅ constantFamily Γ Bool :=
  NatIso.ofComponents (fun _ => (show Bool ≃ Bool from
    ⟨Bool.not, Bool.not, by intro b; cases b <;> rfl,
      by intro b; cases b <;> rfl⟩).toIso) (by intro x y f; rfl)

def unitIndex : Term (constantFamily Γ Unit) where
  val _ := ()
  property _ := rfl

def boolFilling : Filling (constantFamily Γ Bool) := discreteFilling unitIndex (fun _ => Bool)
theorem boolFilling_lawful : (boolFilling (Γ := Γ)).Lawful :=
  discreteFilling_lawful unitIndex (fun _ => Bool)

/-- The full roundtrip recovers the selected contractions as well as the Boolean map. -/
theorem flip_roundtrip (e : HomotopyEquivalence (boolIso (Γ := Γ)).hom) :
    (equivSections _ _).symm ((equivSections _ _) ⟨boolIso.hom,e⟩) = ⟨boolIso.hom,e⟩ :=
  (equivSections _ _).left_inv _

noncomputable def flipSection : Term (equiv (constantFamily Γ Bool) (constantFamily Γ Bool)) :=
  (equivSections _ _) ⟨boolIso.hom,HomotopyEquivalence.ofIso boolIso⟩

theorem flip_action : decodeMap (sigmaFst (flipSection (Γ := Γ))) = boolIso.hom := rfl

/-- A native comparison retains arbitrary chosen witnesses for the same map. -/
noncomputable def flipWitnessPath
    (e d : HomotopyEquivalence (boolIso (Γ := Γ)).hom) :
    Term (homogeneousPath (isEquiv boolIso.hom) (encodeIsEquiv e) (encodeIsEquiv d)) :=
  isEquivPath _ boolFilling boolFilling_lawful boolFilling boolFilling_lawful _ _

theorem flip_substitution {Δ : Context.{0}} (σ : Δ ⟶ Γ)
    (e : HomotopyEquivalence (boolIso (Γ := Γ)).hom) :
    isEquivReindexSections boolIso.hom σ (e.reindex σ) = (encodeIsEquiv e).reindex σ :=
  isEquivReindexSections_reindex e σ

/-- The native proposition construction also applies to genuinely varying families. -/
noncomputable def varyingIdentityWitnessPath (A : Family Γ) (F : Filling A) (hF : F.Lawful)
    (e : HomotopyEquivalence (𝟙 A)) :
    Term (homogeneousPath (isEquiv (𝟙 A))
      (encodeIsEquiv (HomotopyEquivalence.ofIso (Iso.refl A))) (encodeIsEquiv e)) :=
  isEquivPath (𝟙 A) F hF F hF _ _

end Examples.CubicalEquivalenceFamilies
