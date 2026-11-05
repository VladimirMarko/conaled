import SquareKit.Internal.PathTransport.InterpretationMaps
import Mathlib.Logic.Equiv.Basic

/-! Native equality gives a lower-truncated full contextual model. Its J is
constructed by extending sections along the reflexive-root equivalence. -/
namespace SquareKit.Internal.DependentJudgments.NativeType
open PathTransport.Typed StructuralModel
set_option backward.isDefEq.respectTransparency false
universe u

variable (Base : Type u) (Fiber : Base → Type u)

def structuralModel : StructuralModel.{u+1} where
  Context := Type u
  Family Γ := Γ → Type u
  Section Γ A := ULift.{u+1} ((γ : Γ) → A γ)
  Substitution Δ Γ := ULift.{u+1} (Δ → Γ)
  empty := PUnit
  extend Γ A := (γ : Γ) × A γ
  idSub _ := ⟨id⟩
  compSub σ τ := ⟨σ.down ∘ τ.down⟩
  subTy A σ := A ∘ σ.down
  subTm t σ := ⟨fun δ => t.down (σ.down δ)⟩
  weaken _ _ := ⟨Sigma.fst⟩
  genericVariable _ _ := ⟨Sigma.snd⟩
  pairSub _ σ t := ⟨fun δ => ⟨σ.down δ, t.down δ⟩⟩
  base _ := fun _ => Base
  fiber x := fun γ => Fiber (x.down γ)
  identity _ x y := fun γ => ULift.{u} (PLift (x.down γ = y.down γ))
  reflexivity _ _ := ⟨fun _ => ⟨⟨rfl⟩⟩⟩
  comp_id_left _ := rfl
  comp_id_right _ := rfl
  comp_assoc _ _ _ := rfl
  subTy_id _ := rfl
  subTy_comp _ _ _ := rfl
  subTm_id _ := HEq.rfl
  subTm_comp _ _ _ := HEq.rfl
  base_sub _ := rfl
  fiber_sub _ _ := rfl
  identity_sub _ _ _ _ := rfl
  refl_sub _ _ _ := HEq.rfl
  weaken_pair _ _ _ := rfl
  variable_pair _ _ _ := HEq.rfl
  pair_eta _ σ := by cases σ; rfl

local notation "M" => structuralModel Base Fiber

def rootEquiv {Γ : (M).Context} (A : (M).Family Γ) (x : (M).Section Γ A) :
    Γ ≃ (M).pathContext A x where
  toFun := ((M).rootSub A x).down
  invFun p := p.1.1
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨γ, y⟩, ⟨⟨p⟩⟩⟩
    change x.down γ = y at p
    cases p
    rfl

def telescopeEquiv {Γ Δ : (M).Context} {n} (T : Telescope M Γ n) (e : Δ ≃ Γ) :
    (Telescope.pullback M T ⟨e⟩).total ≃ T.total :=
  match T with
  | .nil => e
  | .cons _ T => telescopeEquiv T (Equiv.sigmaCongrLeft e)

theorem telescopeEquiv_apply {Γ Δ : (M).Context} {n} (T : Telescope M Γ n) (e : Δ ≃ Γ) :
    (telescopeEquiv Base Fiber T e).toFun = (Telescope.liftSub M T ⟨e⟩).down := by
  induction T generalizing Δ with
  | nil => rfl
  | cons A T ih => exact ih (Equiv.sigmaCongrLeft e)

def rootTailEquiv {Γ : (M).Context} {n} (A : (M).Family Γ) (x : (M).Section Γ A)
    (T : Telescope M ((M).pathContext A x) n) :
    (Telescope.pullback M T ((M).rootSub A x)).total ≃ T.total where
  toFun := ((M).rootTail A x T).down
  invFun := (telescopeEquiv Base Fiber T (rootEquiv Base Fiber A x)).symm
  left_inv r :=
    (congrArg (telescopeEquiv Base Fiber T (rootEquiv Base Fiber A x)).symm
      (congrFun (telescopeEquiv_apply Base Fiber T (rootEquiv Base Fiber A x)) r)).symm.trans
      (Equiv.symm_apply_apply _ _)
  right_inv r :=
    (congrFun (telescopeEquiv_apply Base Fiber T (rootEquiv Base Fiber A x))
      ((telescopeEquiv Base Fiber T (rootEquiv Base Fiber A x)).symm r)).symm.trans
      (Equiv.apply_symm_apply _ _)

theorem rootTailEquiv_apply {Γ : (M).Context} {n} (A : (M).Family Γ) (x : (M).Section Γ A)
    (T : Telescope M ((M).pathContext A x) n) :
    (rootTailEquiv Base Fiber A x T).toFun = ((M).rootTail A x T).down := rfl

def contextualJ {Γ : (M).Context} {n} (A : (M).Family Γ) (x : (M).Section Γ A)
    (T : Telescope M ((M).pathContext A x) n) (D : (M).Family T.total)
    (d : (M).Section (Telescope.pullback M T ((M).rootSub A x)).total
      ((M).subTy D ((M).rootTail A x T))) : (M).Section T.total D :=
  ⟨Equiv.piCongrLeft D (rootTailEquiv Base Fiber A x T) d.down⟩

theorem contextualJ_beta {Γ : (M).Context} {n} (A : (M).Family Γ) (x : (M).Section Γ A)
    (T : Telescope M ((M).pathContext A x) n) (D : (M).Family T.total)
    (d : (M).Section (Telescope.pullback M T ((M).rootSub A x)).total
      ((M).subTy D ((M).rootTail A x T))) :
    HEq ((M).subTm (contextualJ Base Fiber A x T D d) ((M).rootTail A x T)) d := by
  apply heq_of_eq
  apply ULift.ext
  funext r
  exact Equiv.piCongrLeft_apply_apply D (rootTailEquiv Base Fiber A x T) d.down r

theorem subTm_injective {Γ Δ : (M).Context} {A : (M).Family Γ}
    (σ : (M).Substitution Δ Γ) (hs : Function.Surjective σ.down)
    {t s : (M).Section Γ A} (h : HEq ((M).subTm t σ) ((M).subTm s σ)) : t = s := by
  apply ULift.ext
  funext γ
  obtain ⟨δ, rfl⟩ := hs γ
  exact congrArg (fun z => z.down δ) (eq_of_heq h)

theorem contextualJ_sub {Γ Δ : (M).Context} {n} (A : (M).Family Γ) (x : (M).Section Γ A)
    (T : Telescope M ((M).pathContext A x) n) (D : (M).Family T.total)
    (d : (M).Section (Telescope.pullback M T ((M).rootSub A x)).total
      ((M).subTy D ((M).rootTail A x T))) (σ : (M).Substitution Δ Γ) :
    HEq ((M).subTm (contextualJ Base Fiber A x T D d) ((M).pathTailMap A x T σ))
      (contextualJ Base Fiber ((M).subTy A σ) ((M).subTm x σ) ((M).pathTail A x T σ)
        ((M).subTy D ((M).pathTailMap A x T σ)) ((M).reindexBranch A x T σ D d)) := by
  apply heq_of_eq
  apply subTm_injective Base Fiber
    ((M).rootTail ((M).subTy A σ) ((M).subTm x σ) ((M).pathTail A x T σ))
  · rw [← rootTailEquiv_apply]
    exact Equiv.surjective _
  · apply ((M).subTm_comp _ _ _).trans
    rw [(M).branchMap_square]
    apply ((M).subTm_comp _ _ _).symm.trans
    apply ((M).subTm_congr rfl
      (contextualJ_beta Base Fiber A x T D d) _).trans
    apply (cast_heq _ _).symm.trans
    exact (contextualJ_beta Base Fiber _ _ _ _ _).symm

def model : Model.{u+1} where
  toStructuralModel := M
  j := contextualJ Base Fiber
  j_beta := contextualJ_beta Base Fiber
  j_sub := contextualJ_sub Base Fiber

end SquareKit.Internal.DependentJudgments.NativeType
