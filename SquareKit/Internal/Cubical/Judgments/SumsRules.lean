import SquareKit.Internal.Cubical.Judgments.SumsAlgebra

namespace SquareKit.Cubical.Source.Sums
set_option backward.isDefEq.respectTransparency false
open GuardedTheory Presheaf CategoryTheory
universe u

theorem formation_valid : Satisfies algebra.{u} formationRule := by
  apply formationSchema_valid
  intro Γ A B
  exact ⟨Γ,Presheaf.sigma A B,rfl,extra_sigma Γ A B⟩

theorem pack_valid : Satisfies algebra.{u} packRule := by
  apply formationSchema_valid
  intro Γ A B
  refine ⟨total B,total (Presheaf.sigma A B),sigmaPack A B,?_,?_,extra_pack Γ A B⟩
  · change Source.operation .extend ![Source.operation .extend ![.context Γ,.family Γ A],.family (total A) B] = _
    simp [Source.operation]
  · change Source.operation .extend ![.context Γ,extraOperation .sigma ![.family Γ A,.family (total A) B]] = _
    rw [extra_sigma]
    simp [Source.operation]

theorem unpack_valid : Satisfies algebra.{u} unpackRule := by
  apply formationSchema_valid
  intro Γ A B
  refine ⟨total (Presheaf.sigma A B),total B,sigmaUnpack A B,?_,?_,extra_unpack Γ A B⟩
  · change Source.operation .extend ![.context Γ,extraOperation .sigma ![.family Γ A,.family (total A) B]] = _
    rw [extra_sigma]
    simp [Source.operation]
  · change Source.operation .extend ![Source.operation .extend ![.context Γ,.family Γ A],.family (total A) B] = _
    simp [Source.operation]

theorem beta_valid : Satisfies algebra.{u} betaRule := by
  apply formationSchema_valid
  intro Γ A B
  change Source.operation .comp ![extraOperation .unpack ![.family Γ A,.family (total A) B],
    extraOperation .pack ![.family Γ A,.family (total A) B]] =
    Source.operation .id ![Source.operation .extend ![Source.operation .extend ![.context Γ,.family Γ A],.family (total A) B]]
  rw [extra_unpack,extra_pack]
  simp [Source.operation]

theorem eta_valid : Satisfies algebra.{u} etaRule := by
  apply formationSchema_valid
  intro Γ A B
  change Source.operation .comp ![extraOperation .pack ![.family Γ A,.family (total A) B],
    extraOperation .unpack ![.family Γ A,.family (total A) B]] =
    Source.operation .id ![Source.operation .extend ![.context Γ,extraOperation .sigma ![.family Γ A,.family (total A) B]]]
  rw [extra_pack,extra_unpack,extra_sigma]
  simp [Source.operation]

theorem sigmaSub_valid : Satisfies algebra.{u} sigmaSubRule := by
  apply substitutionSchema_valid
  intro Γ Δ A B σ
  have hl := lifted_eval Γ Δ A B σ
  change Source.operation .subTy ![extraOperation .sigma ![.family Γ A,.family (total A) B],.substitution Δ Γ σ] =
    extraOperation .sigma ![Source.operation .subTy ![.family Γ A,.substitution Δ Γ σ],
      Source.operation .subTy ![.family (total A) B,
        lifted.eval algebra ![.context Γ,.context Δ,.family Γ A,.family (total A) B,.substitution Δ Γ σ]]]
  rw [hl,extra_sigma]
  simp only [Source.operation,Matrix.cons_val_zero,Matrix.cons_val_one,
    Value.familyAt_family]
  exact (extra_sigma Δ (reindex A σ) (reindex B (liftSub A σ))).symm

end SquareKit.Cubical.Source.Sums
