import SquareKit.Internal.PresheafSetting
import Mathlib.CategoryTheory.Category.Preorder
import Lean.Elab.Tactic.Omega

/-! Walking-arrow specializations with a genuinely nonconstant parameter.
The two independent stage partitions do not determine a presheaf model. -/
namespace Examples.PresheafSetting
open CategoryTheory Opposite SquareKit.Internal
open SquareKit.Internal.PresheafSetting
set_option backward.isDefEq.respectTransparency false

abbrev Base := Fin 2
def fine : Baseᵒᵖ := op 1
def coarse : Baseᵒᵖ := op 0
def step : fine ⟶ coarse := (homOfLE (show (0 : Base) ≤ 1 by decide)).op

def terminal : Baseᵒᵖ ⥤ Type := (Functor.const _).obj Unit

def parameter : Presentation terminal where
  obj j _ := j.unop = 0
  map {j k} f := by
    intro x h
    have hk := leOfHom f.unop
    change j.unop = 0 at h
    change k.unop = 0
    apply Fin.ext
    have := congrArg Fin.val h
    change k.unop.val ≤ j.unop.val at hk
    omega

def finePoint : (total parameter).obj fine := ⟨(), .inr ()⟩
def coarseLeft : (total parameter).obj coarse := ⟨(), .inl ⟨rfl⟩⟩
def coarseRight : (total parameter).obj coarse := ⟨(), .inr ()⟩

theorem fine_unique (a : (total parameter).obj fine) : a = finePoint := by
  rcases a with ⟨x, a⟩; cases x
  cases a with
  | inl h => exact False.elim (by have := h.down; change (1 : Base) = 0 at this; exact (show (1 : Base) ≠ 0 by decide) this)
  | inr b => cases b; rfl

theorem coarse_two (a : (total parameter).obj coarse) : a = coarseLeft ∨ a = coarseRight := by
  rcases a with ⟨x, a⟩; cases x
  cases a with
  | inl h => left; rfl
  | inr b => right; cases b; rfl

theorem coarse_distinct : coarseLeft ≠ coarseRight := by
  intro h
  have := congrArg (fun a => a.2.isLeft) h
  contradiction

theorem restriction_right : (total parameter).map step finePoint = coarseRight := rfl

/-- A model at each stage, choosing left only at the coarse stage. -/
def separate (j : Baseᵒᵖ) : FiniteSetting.Section (stage parameter j) := fun _ =>
  if h : j.unop = 0 then .inl ⟨h⟩ else .inr ()

theorem separate_satisfies (j : Baseᵒᵖ) :
    FiniteSetting.Satisfies (stage parameter j) (separate j).toModel.P (separate j).toModel.Q :=
  (separate j).toModel.satisfies

/-- Fine-right cannot restrict to coarse-left. -/
theorem separate_not_natural : ¬ ∃ s : Section parameter, s.val = separate := by
  rintro ⟨s, hs⟩
  have h := s.natural step ()
  rw [hs] at h
  have ht := congrArg Sum.isLeft h
  simp [separate, fine, coarse, step, restrict] at ht

theorem separate_not_model : ¬ ∃ M : Model parameter,
    ∀ j, M.stage j = (separate j).toModel := by
  rintro ⟨M, hM⟩
  apply separate_not_natural
  refine ⟨modelSectionEquiv parameter M, ?_⟩
  funext j
  change (M.stage j).toSection = separate j
  rw [hM, FiniteSetting.Section.toModel_toSection]

def valid : Section parameter where
  val _ _ := .inr ()
  natural _ _ := rfl

theorem valid_correspondence : modelSectionEquiv parameter valid.toModel = valid :=
  (modelSectionEquiv parameter).apply_symm_apply valid

theorem valid_recovery : (genericModel parameter).subst valid.graph = valid.toModel := rfl

/-- Forget a Boolean label at both stages. This is not an invertible substitution. -/
def labelled : Baseᵒᵖ ⥤ Type := (Functor.const _).obj Bool

def forget : labelled ⟶ terminal where
  app _ := ↾fun _ => ()

def flip : labelled ⟶ labelled where
  app _ := ↾Bool.not

theorem forget_noninjective : ¬ Function.Injective (forget.app fine) := by
  intro h
  have := h (show forget.app fine false = forget.app fine true from rfl)
  contradiction

def labelledLeft : (total (subst parameter forget)).obj coarse := ⟨false, .inl ⟨rfl⟩⟩
def labelledRight : (total (subst parameter forget)).obj fine := ⟨true, .inr ()⟩

theorem substituted_restriction :
    (total (subst parameter forget)).map step labelledRight = ⟨true, .inr ()⟩ := rfl

theorem substituted_correspondence :
    modelSectionEquiv (subst parameter forget) (valid.toModel.subst forget) =
      (modelSectionEquiv parameter valid.toModel).subst forget :=
  correspondence_subst _ _

theorem labelled_graph :
    (∃ p : (pullback parameter forget).obj coarse,
      p = (comparison parameter forget).inv.app coarse labelledLeft ∧ true = p.original.2.isLeft) ∧
    (∃ p : (pullback parameter forget).obj fine,
      p = (comparison parameter forget).inv.app fine labelledRight ∧ false = p.original.2.isLeft) :=
  ⟨(graph_routes parameter forget coarse labelledLeft true).1.mpr rfl,
   (graph_routes parameter forget fine labelledRight false).1.mpr rfl⟩

theorem labelled_partition :
    (pullbackGeneric parameter forget).P.obj coarse
      ((comparison parameter forget).inv.app coarse labelledLeft) ∧
    (pullbackGeneric parameter forget).Q.obj fine
      ((comparison parameter forget).inv.app fine labelledRight) := by
  constructor
  · exact (pullback_partition parameter forget coarse _).1.mpr rfl
  · exact (pullback_partition parameter forget fine _).2.mpr rfl

theorem flipped_comparison :
    pullbackRebase parameter forget flip ≫ (comparison parameter (flip ≫ forget)).hom =
      (comparison (subst parameter forget) flip).hom := comparison_composition _ _ _

theorem flipped_generic :
    (pullbackGeneric parameter (flip ≫ forget)).subst (pullbackRebase parameter forget flip) =
      pullbackGeneric (subst parameter forget) flip := generic_composition _ _ _

end Examples.PresheafSetting
