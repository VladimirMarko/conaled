import SquareKit.Internal.PathTransport.Comprehension
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! The category of display maps with all commuting squares. Fullness here
refers to these arrows; it does not assert fullness for cleavage-preserving maps. -/
namespace SquareKit.Internal.PathTransport.Typed.StructuralModel
open CategoryTheory CategoryTheory.Limits
universe u
variable (M : StructuralModel.{u})

/-- A wrapper keeps the category instance tied to its chosen model. -/
def ContextCat := M.Context
instance : Category (M.ContextCat) where
  Hom Γ Δ := M.Substitution Γ Δ
  id Γ := M.idSub Γ
  comp f g := M.compSub g f
  id_comp f := M.comp_id_right f
  comp_id f := M.comp_id_left f
  assoc f g h := (M.comp_assoc h g f).symm

abbrev Display := (Γ : M.Context) × M.Family Γ

def displayArrow (A : M.Display) : Arrow M.ContextCat :=
  Arrow.mk (X := M.extend A.1 A.2) (Y := A.1) (M.weaken A.1 A.2)

instance : Category M.Display where
  Hom A B := M.displayArrow A ⟶ M.displayArrow B
  id A := 𝟙 (M.displayArrow A)
  comp f g := f ≫ g

def comprehension : M.Display ⥤ Arrow M.ContextCat where
  obj := M.displayArrow
  map f := f

def comprehensionFullyFaithful : M.comprehension.FullyFaithful where
  preimage f := f

def displayBase : M.Display ⥤ M.ContextCat :=
  M.comprehension ⋙ Arrow.rightFunc

def displayReindex {Γ Δ : M.Context} (A : M.Family Γ) (σ : M.Substitution Δ Γ) :
    (⟨Δ, M.subTy A σ⟩ : M.Display) ⟶ ⟨Γ, A⟩ :=
  Arrow.homMk (M.lift A σ) σ (M.weaken_lift A σ)

/-- The chosen reindexing square is a categorical pullback. -/
theorem displayPullback {Γ Δ : M.Context} (A : M.Family Γ) (σ : M.Substitution Δ Γ) :
    IsPullback (C := M.ContextCat) (M.weaken Δ (M.subTy A σ))
      (M.lift A σ) σ (M.weaken Γ A) where
  w := (M.weaken_lift A σ).symm
  isLimit' := ⟨PullbackCone.isLimitAux _
    (fun s => M.pullbackFactor A σ s.fst s.snd s.condition)
    (fun s => M.pullbackFactor_projection A σ s.fst s.snd s.condition)
    (fun s => M.pullbackFactor_lift A σ s.fst s.snd s.condition)
    (fun s k hk => M.pullbackFactor_unique A σ s.fst s.snd s.condition k
      (hk WalkingCospan.left) (hk WalkingCospan.right))⟩

/-- Every square over a composite factors uniquely over the chosen reindexing.
This is the cartesian lifting property for the display-base functor. -/
theorem display_cartesian {Γ Δ Θ : M.Context} (A : M.Family Γ) (B : M.Family Θ)
    (σ : M.Substitution Δ Γ) (τ : M.Substitution Θ Δ)
    (g : (⟨Θ, B⟩ : M.Display) ⟶ ⟨Γ, A⟩)
    (hg : g.right = M.compSub σ τ) :
    ∃! k : (⟨Θ, B⟩ : M.Display) ⟶ ⟨Δ, M.subTy A σ⟩,
      k.right = τ ∧ k ≫ M.displayReindex A σ = g := by
  have h : M.compSub σ (M.compSub τ (M.weaken Θ B)) =
      M.compSub (M.weaken Γ A) g.left := by
    rw [← M.comp_assoc, ← hg]
    exact g.w.symm
  let k : (⟨Θ, B⟩ : M.Display) ⟶ ⟨Δ, M.subTy A σ⟩ :=
    Arrow.homMk (M.pullbackFactor A σ (M.compSub τ (M.weaken Θ B)) g.left h) τ
      (M.pullbackFactor_projection _ _ _ _ _)
  refine ⟨k, ⟨rfl, ?_⟩, ?_⟩
  · apply Arrow.hom_ext
    · exact M.pullbackFactor_lift A σ (M.compSub τ (M.weaken Θ B)) g.left h
    · exact hg.symm
  · intro l hl
    apply Arrow.hom_ext
    · apply M.pullbackFactor_unique A σ _ g.left h l.left
      · exact l.w.trans (congrArg (fun t => M.compSub t (M.weaken Θ B)) hl.1)
      · exact congrArg Arrow.Hom.left hl.2
    · exact hl.1

end SquareKit.Internal.PathTransport.Typed.StructuralModel
