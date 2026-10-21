import SquareKit.Internal.PathTransport.JNaturality
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Types.Basic
import SquareKit.Internal.PathTransport.ContextualModel
import SquareKit.Internal.PathTransport.GroupoidElimination
import SquareKit.Internal.PathTransport.SplitFamily

/-! The constructed ordinary-groupoid instance of every supported model rule.
Normalized path-context equivalences give contextual J. The exact structural
branch map is used in its repeated-tail substitution proof. A universe-lift
wrapper admits independent object, arrow and primitive-fiber universes. -/
noncomputable section
open CategoryTheory
open SquareKit.Internal.PathTransport
namespace SquareKit.Internal.PathTransport.GroupoidModel.Instance
open GroupoidModel
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u)
def structuralModel : SquareKit.Internal.PathTransport.Typed.StructuralModel.{u+1} where
  Context := Grpd.{u,u}
  Family Γ := Γ ⥤ Grpd.{u,u}
  Section _ A := ULift.{u+1} (Section A)
  Substitution Δ Γ := ULift.{u+1} (Δ ⥤ Γ)
  empty := @Grpd.of _ (Groupoid.ofIsGroupoid (C := Discrete PUnit))
  extend _ A := @Grpd.of _ (Groupoid.ofIsGroupoid (C := Extend A))
  idSub Γ := ⟨𝟭 Γ⟩
  compSub σ τ := ⟨τ.down ⋙ σ.down⟩
  subTy A σ := σ.down ⋙ A
  subTm t σ := ⟨t.down.reindex σ.down⟩
  weaken _ A := ⟨weaken A⟩
  genericVariable _ A := ⟨«variable» A⟩
  pairSub A σ t := ⟨pair A σ.down t.down⟩
  base _ := constant C
  fiber x := primitiveFiber B x.down
  identity A x y := identityFamily A x.down y.down
  reflexivity A x := ⟨reflexivitySection A x.down⟩
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
  pair_eta A σ := by
    apply ULift.ext
    fapply CategoryTheory.Functor.ext
    · intro a; rfl
    · intro a b f
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
      rfl
open SquareKit.Internal.PathTransport.Typed ContextualElimination
local notation "M" => structuralModel C B

local instance (Γ : Grpd.{u,u}) : IsGroupoid (Cat.of Γ) :=
  inferInstanceAs (IsGroupoid Γ)

def telescopeEquivalence {Γ Δ : Grpd.{u,u}} {n}
    (T : StructuralModel.Telescope M Γ n)
    (e : NormalizedEquivalence (Cat.of Δ) (Cat.of Γ)) :
    NormalizedEquivalence
      (Grpd.forgetToCat.obj (StructuralModel.Telescope.total M
        (StructuralModel.Telescope.pullback M T ⟨e.equiv.functor⟩)))
      (Grpd.forgetToCat.obj (StructuralModel.Telescope.total M T)) :=
  match T with
  | .nil => e
  | .cons A tail => telescopeEquivalence
      (Δ := @Grpd.of (Extend (e.equiv.functor ⋙ A)) Groupoid.ofIsGroupoid)
      tail (e.extend (A ⋙ Grpd.forgetToCat))

@[simp] theorem telescopeEquivalence_functor {Γ Δ : Grpd.{u,u}} {n}
    (T : StructuralModel.Telescope M Γ n)
    (e : NormalizedEquivalence (Cat.of Δ) (Cat.of Γ)) :
    (telescopeEquivalence C B T e).equiv.functor =
      (StructuralModel.Telescope.liftSub M T ⟨e.equiv.functor⟩).down :=
  match T with
  | .nil => rfl
  | .cons A tail => telescopeEquivalence_functor
      (Δ := @Grpd.of (Extend (e.equiv.functor ⋙ A)) Groupoid.ofIsGroupoid)
      tail (e.extend (A ⋙ Grpd.forgetToCat))
termination_by sizeOf T

def pathEquivalence {Γ : Grpd.{u,u}} (A : Γ ⥤ Grpd.{u,u}) (x : Section A) :
    NormalizedEquivalence (Cat.of Γ) (Grpd.forgetToCat.obj (StructuralModel.pathContext M A ⟨x⟩)) where
  equiv := PathComparison.pathEquivalence A x
  unit_obj _ := rfl
  unit_hom _ := rfl

@[simp] theorem pathEquivalence_functor {Γ : Grpd.{u,u}}
    (A : Γ ⥤ Grpd.{u,u}) (x : Section A) :
    (pathEquivalence C B A x).equiv.functor = (StructuralModel.rootSub M A ⟨x⟩).down := by
  fapply CategoryTheory.Functor.ext
  · intro γ; rfl
  · intro γ δ f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    fapply Grothendieck.ext
    · rfl
    · exact congrArg Discrete.Hom.mk rfl

def rootEquivalence {Γ : Grpd.{u,u}} (A : Γ ⥤ Grpd.{u,u}) (x : Section A) :
    NormalizedEquivalence (Cat.of Γ) (Grpd.forgetToCat.obj (StructuralModel.pathContext M A ⟨x⟩)) :=
  (pathEquivalence C B A x).changeFunctor (StructuralModel.rootSub M A ⟨x⟩).down
    (pathEquivalence_functor C B A x)

def rootTailEquivalence {Γ : Grpd.{u,u}} {n} (A : Γ ⥤ Grpd.{u,u}) (x : Section A)
    (T : StructuralModel.Telescope M (StructuralModel.pathContext M A ⟨x⟩) n) :
    NormalizedEquivalence
      (Grpd.forgetToCat.obj (StructuralModel.Telescope.total M
        (StructuralModel.Telescope.pullback M T (StructuralModel.rootSub M A ⟨x⟩))))
      (Grpd.forgetToCat.obj (StructuralModel.Telescope.total M T)) :=
  (telescopeEquivalence C B T (rootEquivalence C B A x)).changeFunctor
    (StructuralModel.rootTail M A ⟨x⟩ T).down
    (telescopeEquivalence_functor C B T (rootEquivalence C B A x))

def contextualJ {Γ : (M).Context} {n} (A : (M).Family Γ) (x : (M).Section Γ A)
    (T : StructuralModel.Telescope M (StructuralModel.pathContext M A x) n)
    (D : (M).Family (StructuralModel.Telescope.total M T))
    (d : (M).Section
      (StructuralModel.Telescope.total M
        (StructuralModel.Telescope.pullback M T (StructuralModel.rootSub M A x)))
      ((M).subTy D (StructuralModel.rootTail M A x T))) :
    (M).Section (StructuralModel.Telescope.total M T) D :=
  ⟨eliminateSection (rootTailEquivalence C B A x.down T) D d.down⟩

theorem contextualJ_beta {Γ : (M).Context} {n} (A : (M).Family Γ) (x : (M).Section Γ A)
    (T : StructuralModel.Telescope M (StructuralModel.pathContext M A x) n)
    (D : (M).Family (StructuralModel.Telescope.total M T))
    (d : (M).Section
      (StructuralModel.Telescope.total M
        (StructuralModel.Telescope.pullback M T (StructuralModel.rootSub M A x)))
      ((M).subTy D (StructuralModel.rootTail M A x T))) :
    HEq ((M).subTm (contextualJ C B A x T D d) (StructuralModel.rootTail M A x T)) d := by
  apply heq_of_eq
  apply ULift.ext
  exact eliminateSection_beta (rootTailEquivalence C B A x.down T) D d.down

end SquareKit.Internal.PathTransport.GroupoidModel.Instance

namespace SquareKit.Internal.PathTransport.GroupoidModel.Instance
open CategoryTheory GroupoidModel SquareKit.Internal.PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u)
local notation "M" => structuralModel C B

theorem down_cast {α β : Type u} (h : α = β) (a : ULift.{u+1} α) :
    (cast (congrArg ULift.{u+1} h) a).down = cast h a.down := by
  subst β
  rfl

theorem squareLift_eq {Γ Γ' Δ Δ' : Grpd.{u,u}}
    (F : Δ ⥤ Γ) (F' : Δ' ⥤ Γ') (K : Γ' ⥤ Γ) (L : Δ' ⥤ Δ)
    (h : F' ⋙ K = L ⋙ F) (A : Γ ⥤ Grpd.{u,u}) :
    (StructuralModel.squareLift M ⟨F⟩ ⟨F'⟩ ⟨K⟩ ⟨L⟩ (congrArg ULift.up h) A).down =
      Grothendieck.map (eqToHom (congrArg (· ⋙ A ⋙ Grpd.forgetToCat) h)) ⋙
        Grothendieck.pre (F ⋙ A ⋙ Grpd.forgetToCat) L := by
  change pair (F ⋙ A) (weaken (F' ⋙ K ⋙ A) ⋙ L)
    ((cast _ (ULift.up («variable» (F' ⋙ K ⋙ A))) : ULift.{u+1} (Section (weaken (F' ⋙ K ⋙ A) ⋙ L ⋙ F ⋙ A))).down) = _
  rw [down_cast]
  exact EquivalenceSquare.map_cast_pair (F ⋙ A) L (F' ⋙ K ⋙ A)
    (congrArg (· ⋙ A) h)
end SquareKit.Internal.PathTransport.GroupoidModel.Instance

namespace SquareKit.Internal.PathTransport.GroupoidModel.Instance
open CategoryTheory GroupoidModel ContextualElimination SquareKit.Internal.PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u)
local notation "M" => structuralModel C B
local instance (Γ : Grpd.{u,u}) : IsGroupoid (Cat.of Γ) := inferInstanceAs (IsGroupoid Γ)

theorem model_lift_eq {Γ Δ : Grpd.{u,u}} (A : Γ ⥤ Grpd.{u,u}) (σ : Δ ⥤ Γ) :
    StructuralModel.lift M A ⟨σ⟩ = ⟨Grothendieck.pre (A ⋙ Grpd.forgetToCat) σ⟩ := rfl

theorem telescopeModelSquare {Γ Δ Γ' Δ' : Grpd.{u,u}} {n}
    (T : StructuralModel.Telescope M Γ n)
    (e : NormalizedEquivalence (Cat.of Δ) (Cat.of Γ))
    (e' : NormalizedEquivalence (Cat.of Δ') (Cat.of Γ'))
    (K : Γ' ⥤ Γ) (L : Δ' ⥤ Δ) (sq : EquivalenceSquare.Square e.equiv e'.equiv K L) :
    EquivalenceSquare.Square (telescopeEquivalence C B T e).equiv
      (telescopeEquivalence C B (StructuralModel.Telescope.pullback M T ⟨K⟩) e').equiv
      (StructuralModel.Telescope.liftSub M T ⟨K⟩).down
      (StructuralModel.Telescope.square M ⟨e.equiv.functor⟩ ⟨e'.equiv.functor⟩ ⟨K⟩ ⟨L⟩
        (congrArg ULift.up sq.forward) T).val.down :=
  match T with
  | .nil => by
    simpa only [telescopeEquivalence, StructuralModel.Telescope.square,
      StructuralModel.Telescope.pullback, StructuralModel.Telescope.reindex,
      StructuralModel.Telescope.liftSub] using sq
  | .cons A tail => by
    have s : EquivalenceSquare.Square (e.extend (A ⋙ Grpd.forgetToCat)).equiv
        (e'.extend (K ⋙ A ⋙ Grpd.forgetToCat)).equiv
        (Grothendieck.pre (A ⋙ Grpd.forgetToCat) K)
        (StructuralModel.squareLift M ⟨e.equiv.functor⟩ ⟨e'.equiv.functor⟩ ⟨K⟩ ⟨L⟩
          (congrArg ULift.up sq.forward) A).down := by
      rw [squareLift_eq C B _ _ _ _ sq.forward A]
      exact EquivalenceSquare.liftSquare e.equiv e'.equiv K L sq (A ⋙ Grpd.forgetToCat)
    rw [StructuralModel.Telescope.square]
    exact telescopeModelSquare
      (Γ := @Grpd.of (Extend A) Groupoid.ofIsGroupoid)
      (Δ := @Grpd.of (Extend (e.equiv.functor ⋙ A)) Groupoid.ofIsGroupoid)
      (Γ' := @Grpd.of (Extend (K ⋙ A)) Groupoid.ofIsGroupoid)
      (Δ' := @Grpd.of (Extend (e'.equiv.functor ⋙ K ⋙ A)) Groupoid.ofIsGroupoid)
      tail (e.extend (A ⋙ Grpd.forgetToCat)) (e'.extend (K ⋙ A ⋙ Grpd.forgetToCat))
      (Grothendieck.pre (A ⋙ Grpd.forgetToCat) K)
      (StructuralModel.squareLift M ⟨e.equiv.functor⟩ ⟨e'.equiv.functor⟩ ⟨K⟩ ⟨L⟩
        (congrArg ULift.up sq.forward) A).down s
termination_by sizeOf T
end SquareKit.Internal.PathTransport.GroupoidModel.Instance

namespace SquareKit.Internal.PathTransport.GroupoidModel.Instance
open CategoryTheory GroupoidModel ContextualElimination SquareKit.Internal.PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u)
local notation "M" => structuralModel C B
local instance (Γ : Grpd.{u,u}) : IsGroupoid (Cat.of Γ) := inferInstanceAs (IsGroupoid Γ)

theorem rootTailModelSquare {Γ Δ : Grpd.{u,u}} {n}
    (A : Γ ⥤ Grpd.{u,u}) (x : Section A) (σ : Δ ⥤ Γ)
    (T : StructuralModel.Telescope M (StructuralModel.pathContext M A ⟨x⟩) n) :
    EquivalenceSquare.Square (rootTailEquivalence C B A x T).equiv
      (rootTailEquivalence C B (σ ⋙ A) (x.reindex σ)
        (StructuralModel.pathTail M A ⟨x⟩ T ⟨σ⟩)).equiv
      (StructuralModel.pathTailMap M A ⟨x⟩ T ⟨σ⟩).down
      (StructuralModel.branchMap M A ⟨x⟩ T ⟨σ⟩).down := by
  let sq := EquivalenceSquare.changeFunctorSquare
    (pathEquivalence C B A x) (pathEquivalence C B (σ ⋙ A) (x.reindex σ))
    (PathComparison.substitution A x σ) σ (EquivalenceSquare.rootSquare A x σ)
    (StructuralModel.rootSub M A ⟨x⟩).down
    (StructuralModel.rootSub M (σ ⋙ A) ⟨x.reindex σ⟩).down
    (pathEquivalence_functor C B A x)
    (pathEquivalence_functor C B (σ ⋙ A) (x.reindex σ))
  have t := telescopeModelSquare C B T (rootEquivalence C B A x)
    (rootEquivalence C B (σ ⋙ A) (x.reindex σ))
    (PathComparison.substitution A x σ) σ sq
  exact EquivalenceSquare.changeFunctorSquare
    (telescopeEquivalence C B T (rootEquivalence C B A x))
    (telescopeEquivalence C B (StructuralModel.pathTail M A ⟨x⟩ T ⟨σ⟩)
      (rootEquivalence C B (σ ⋙ A) (x.reindex σ)))
    (StructuralModel.pathTailMap M A ⟨x⟩ T ⟨σ⟩).down
    (StructuralModel.branchMap M A ⟨x⟩ T ⟨σ⟩).down t
    (StructuralModel.rootTail M A ⟨x⟩ T).down
    (StructuralModel.rootTail M (σ ⋙ A) ⟨x.reindex σ⟩
      (StructuralModel.pathTail M A ⟨x⟩ T ⟨σ⟩)).down
    (telescopeEquivalence_functor C B T (rootEquivalence C B A x))
    (telescopeEquivalence_functor C B _ (rootEquivalence C B (σ ⋙ A) (x.reindex σ)))
end SquareKit.Internal.PathTransport.GroupoidModel.Instance

namespace SquareKit.Internal.PathTransport.GroupoidModel.Instance
open CategoryTheory GroupoidModel ContextualElimination SquareKit.Internal.PathTransport.Typed
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u)
local notation "M" => structuralModel C B
local instance (Γ : Grpd.{u,u}) : IsGroupoid (Cat.of Γ) := inferInstanceAs (IsGroupoid Γ)

theorem contextualJ_sub {Γ Δ : (M).Context} {n}
    (A : (M).Family Γ) (x : (M).Section Γ A)
    (T : StructuralModel.Telescope M (StructuralModel.pathContext M A x) n)
    (σ : (M).Substitution Δ Γ)
    (D : (M).Family (StructuralModel.Telescope.total M T))
    (d : (M).Section
      (StructuralModel.Telescope.total M
        (StructuralModel.Telescope.pullback M T (StructuralModel.rootSub M A x)))
      ((M).subTy D (StructuralModel.rootTail M A x T))) :
    HEq ((M).subTm (contextualJ C B A x T D d) (StructuralModel.pathTailMap M A x T σ))
      (contextualJ C B ((M).subTy A σ) ((M).subTm x σ)
        (StructuralModel.pathTail M A x T σ) ((M).subTy D (StructuralModel.pathTailMap M A x T σ))
        (StructuralModel.reindexBranch M A x T σ D d)) := by
  apply heq_of_eq
  apply ULift.ext
  change (eliminateSection (rootTailEquivalence C B A x.down T) D d.down).reindex _ =
    eliminateSection (rootTailEquivalence C B (σ.down ⋙ A) (x.down.reindex σ.down)
      (StructuralModel.pathTail M A x T σ))
      ((StructuralModel.pathTailMap M A x T σ).down ⋙ D)
      (StructuralModel.reindexBranch M A x T σ D d).down
  unfold StructuralModel.reindexBranch
  rw [down_cast]
  exact (EquivalenceSquare.eliminateSection_substitution _ _ _ _
    (rootTailModelSquare C B A x.down σ.down T) D d.down).symm
end SquareKit.Internal.PathTransport.GroupoidModel.Instance

namespace SquareKit.Internal.PathTransport.GroupoidModel.Instance
open CategoryTheory
universe u
variable (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u)
local notation "M" => structuralModel C B
def fullModel : SquareKit.Internal.PathTransport.Typed.Model.{u+1} where
  toStructuralModel := M
  j := contextualJ C B
  j_beta := contextualJ_beta C B
  j_sub := fun A x T D d σ => contextualJ_sub C B A x T σ D d

end SquareKit.Internal.PathTransport.GroupoidModel.Instance

open CategoryTheory
noncomputable section
namespace SquareKit.Internal.PathTransport.GroupoidModel.Instance
universe u v w
variable (C : Type u) [Groupoid.{v} C] (B : C ⥤ Type w)
instance liftedGroupoid : Groupoid (AsSmall.{w} C) where
  inv f := ⟨inv f.down⟩
  inv_comp f := by apply ULift.ext; exact IsIso.inv_hom_id f.down
  comp_inv f := by apply ULift.ext; exact IsIso.hom_inv_id f.down

def liftedFamily : AsSmall.{w} C ⥤ Type (max u v w) :=
  AsSmall.down ⋙ B ⋙ uliftFunctor.{max u v}

def universeModel : Typed.Model.{max u v w + 1} :=
  fullModel (AsSmall.{w} C) (liftedFamily C B)

end SquareKit.Internal.PathTransport.GroupoidModel.Instance
