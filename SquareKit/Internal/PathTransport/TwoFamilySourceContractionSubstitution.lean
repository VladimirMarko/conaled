import SquareKit.Internal.PathTransport.TwoFamilySourceContraction
import SquareKit.Internal.PathTransport.TwoFamilyModelSquareLift
import SquareKit.Internal.PathTransport.TwoFamilyContractionHomotopySubstitution
/-! Substitution of normalized contractions along the exact source telescope
squares preserves the selected branch and its transported family. -/
namespace SquareKit.Internal.PathTransport.HigherInterpretation.SourceContraction
open CategoryTheory Bicategory
open TwoFamily
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
variable {Γ Δ : Context.{u}} {i : StrictPseudofunctor Δ Γ}
structure Square {Γ Δ Γ' Δ' : Context.{u}}
    {i : StrictPseudofunctor Δ Γ} {i' : StrictPseudofunctor Δ' Γ'}
    (c : SourceContraction i) (d : SourceContraction i')
    (σ : StrictPseudofunctor Γ' Γ) (τ : StrictPseudofunctor Δ' Δ) : Prop where
  inclusion : i'.comp σ = τ.comp i
  retraction : d.retraction.comp τ = σ.comp c.retraction
  homotopy : HEq (strongPostcomp d.homotopy σ) (strongPrecomp c.homotopy σ)

variable {Γ' Δ' : Context.{u}} {i' : StrictPseudofunctor Δ' Γ'}
theorem Square.cast {c : SourceContraction i} {d : SourceContraction i'}
    {σ : StrictPseudofunctor Γ' Γ} {τ : StrictPseudofunctor Δ' Δ}
    (h : Square c d σ τ) {j : StrictPseudofunctor Δ Γ} {j' : StrictPseudofunctor Δ' Γ'}
    {σ' : StrictPseudofunctor Γ' Γ} {τ' : StrictPseudofunctor Δ' Δ}
    (hi : i = j) (hi' : i' = j') (hσ : σ = σ') (hτ : τ = τ') :
    Square (c.cast hi) (d.cast hi') σ' τ' := by
  cases hi; cases hi'; cases hσ; cases hτ
  exact h

theorem Square.extendRaw {c : SourceContraction i} {d : SourceContraction i'}
    {σ : StrictPseudofunctor Γ' Γ} {τ : StrictPseudofunctor Δ' Δ}
    (h : Square c d σ τ) (A : Family Γ) :
    Square (Γ := A.total) (Δ := (A.reindex i).total)
      (Γ' := (A.reindex σ).total) (Δ' := ((A.reindex σ).reindex i').total)
      (c.extendRaw A) (d.extendRaw (A.reindex σ)) (reindexHigher A.data σ)
      (contractionBranchSubstitution i i' σ τ h.inclusion A.data) := by
  let : ∀x, IsIso (c.homotopy.app x) := fun _ => IsGroupoid.all_isIso _
  let : ∀x, IsIso (d.homotopy.app x) := fun _ => IsGroupoid.all_isIso _
  have h1 := contractionInclusion_reindex i i' σ τ h.inclusion A.data
  have h2 := contractionRetraction_reindex i c.retraction i' d.retraction σ τ h.inclusion
      h.retraction c.homotopy d.homotopy h.homotopy A.data
  have h3 := contractionRetractionHomotopy_reindex i c.retraction i' d.retraction σ τ h.inclusion
      h.retraction c.homotopy d.homotopy h.homotopy A.data
  constructor
  · set_option backward.dsimp.instances true in
      dsimp only [SourceContraction.extendRaw, Family.total, Family.reindex, instBicategoryCarrier, instStrictCarrier] at *
    set_option backward.isDefEq.respectTransparency true in
      set_option backward.isDefEq.respectTransparency.types true in
        set_option backward.defeqAttrib.useBackward false in
          with_reducible exact h1
  · set_option backward.dsimp.instances true in
      dsimp only [SourceContraction.extendRaw, Family.total, Family.reindex, instBicategoryCarrier, instStrictCarrier] at *
    set_option backward.isDefEq.respectTransparency true in
      set_option backward.isDefEq.respectTransparency.types true in
        set_option backward.defeqAttrib.useBackward false in
          with_reducible exact h2
  · set_option backward.dsimp.instances true in
      dsimp only [SourceContraction.extendRaw, Family.total, Family.reindex, instBicategoryCarrier, instStrictCarrier] at *
    set_option backward.isDefEq.respectTransparency true in
      set_option backward.isDefEq.respectTransparency.types true in
        set_option backward.defeqAttrib.useBackward false in
          with_reducible exact h3


variable (C D : Context.{u})
local notation "M" => structuralModel C D
theorem Square.extend {Γ Δ Γ' Δ' : (M).Context}
    (F : (M).Substitution Δ Γ) (F' : (M).Substitution Δ' Γ')
    (K : (M).Substitution Γ' Γ) (L : (M).Substitution Δ' Δ)
    (h : (M).compSub K F' = (M).compSub F L)
    {c : SourceContraction F.down} {d : SourceContraction F'.down}
    (hc : Square c d K.down L.down) (A : (M).Family Γ) :
    Square (c.extend C D A) (d.extend C D ((M).subTy A K))
      ((M).lift A K).down ((M).squareLift F F' K L h A).down :=
  (hc.extendRaw A).cast (lift_down_eq_reindexHigher C D A F).symm
    (lift_down_eq_reindexHigher C D ((M).subTy A K) F').symm
    (lift_down_eq_reindexHigher C D A K).symm
    (squareLift_down_eq C D F F' K L h A).symm

theorem Square.telescope {Γ Δ Γ' Δ' : (M).Context} {n}
    (T : Typed.StructuralModel.Telescope M Γ n)
    (F : (M).Substitution Δ Γ) (F' : (M).Substitution Δ' Γ')
    (K : (M).Substitution Γ' Γ) (L : (M).Substitution Δ' Δ)
    (h : (M).compSub K F' = (M).compSub F L)
    (c : {c : SourceContraction F.down // c.Normalized})
    (d : {d : SourceContraction F'.down // d.Normalized})
    (hc : Square c.val d.val K.down L.down) :
    Square (SourceContraction.telescope C D T F c).val
      (SourceContraction.telescope C D (T.pullback M K) F' d).val
      (T.liftSub M K).down ((T.square M F F' K L h).val).down :=
  match T with
  | .nil => by
    simpa only [Typed.StructuralModel.Telescope.square, SourceContraction.telescope,
      Typed.StructuralModel.Telescope.pullback, Typed.StructuralModel.Telescope.reindex,
      Typed.StructuralModel.Telescope.liftSub] using hc
  | .cons A tail => by
    have hi := Square.telescope tail
      ((M).lift A F) ((M).lift ((M).subTy A K) F')
      ((M).lift A K) ((M).squareLift F F' K L h A)
      ((M).squareLift_forward F F' K L h A)
      ⟨c.val.extend C D A, c.val.extend_normalized C D A c.property⟩
      ⟨d.val.extend C D ((M).subTy A K),
        d.val.extend_normalized C D ((M).subTy A K) d.property⟩
      (hc.extend C D F F' K L h A)
    simpa only [Typed.StructuralModel.Telescope.square, SourceContraction.telescope,
      Typed.StructuralModel.Telescope.pullback, Typed.StructuralModel.Telescope.reindex,
      Typed.StructuralModel.Telescope.liftSub] using hi

noncomputable def branchReindex {Γ Δ Γ' Δ' : (M).Context} {n}
    (T : Typed.StructuralModel.Telescope M Γ n)
    (F : (M).Substitution Δ Γ) (F' : (M).Substitution Δ' Γ')
    (K : (M).Substitution Γ' Γ) (L : (M).Substitution Δ' Δ)
    (h : (M).compSub K F' = (M).compSub F L)
    (E : (M).Family (T.total M))
    (b : (M).Section _ ((M).subTy E (T.liftSub M F))) :
    (M).Section _ ((M).subTy ((M).subTy E (T.liftSub M K))
      ((T.pullback M K).liftSub M F')) :=
  _root_.cast (congrArg ((M).Section _)
    ((M).square_type (T.liftSub M F) ((T.pullback M K).liftSub M F') (T.liftSub M K)
      (T.square M F F' K L h).val (T.square M F F' K L h).property E).symm)
    ((M).subTm b (T.square M F F' K L h).val)

theorem branchReindex_down {Γ Δ Γ' Δ' : (M).Context} {n}
    (T : Typed.StructuralModel.Telescope M Γ n)
    (F : (M).Substitution Δ Γ) (F' : (M).Substitution Δ' Γ')
    (K : (M).Substitution Γ' Γ) (L : (M).Substitution Δ' Δ)
    (h : (M).compSub K F' = (M).compSub F L)
    (E : (M).Family (T.total M))
    (b : (M).Section _ ((M).subTy E (T.liftSub M F))) :
    (branchReindex C D T F F' K L h E b).down =
      retractionBranchReindex (T.liftSub M F).down ((T.pullback M K).liftSub M F').down
        (T.liftSub M K).down (T.square M F F' K L h).val.down
        (congrArg ULift.down (T.square M F F' K L h).property) E.data b.down := by
  exact sectionCast_down
    ((M).square_type (T.liftSub M F) ((T.pullback M K).liftSub M F') (T.liftSub M K)
      (T.square M F F' K L h).val (T.square M F F' K L h).property E).symm
    ((M).subTm b (T.square M F F' K L h).val)

theorem eliminate_reindex {Γ Δ Γ' Δ' : (M).Context} {n}
    (T : Typed.StructuralModel.Telescope M Γ n)
    (F : (M).Substitution Δ Γ) (F' : (M).Substitution Δ' Γ')
    (K : (M).Substitution Γ' Γ) (L : (M).Substitution Δ' Δ)
    (h : (M).compSub K F' = (M).compSub F L)
    (c : {c : SourceContraction F.down // c.Normalized})
    (d : {d : SourceContraction F'.down // d.Normalized})
    (hc : Square c.val d.val K.down L.down)
    (E : (M).Family (T.total M))
    (b : (M).Section _ ((M).subTy E (T.liftSub M F))) :
    (M).subTm (SourceContraction.eliminate C D T F c E b) (T.liftSub M K) =
      SourceContraction.eliminate C D (T.pullback M K) F' d ((M).subTy E (T.liftSub M K))
        (branchReindex C D T F F' K L h E b) := by
  apply ULift.ext
  change _ = retractionJ _ _ _ _ (branchReindex C D T F F' K L h E b).down
  rw [branchReindex_down]
  have hs := hc.telescope C D T F F' K L h c d
  exact retractionJ_reindex _ _ _ _ _ _ hs.inclusion hs.retraction _ _ hs.homotopy E.data b.down

end SquareKit.Internal.PathTransport.HigherInterpretation.SourceContraction
