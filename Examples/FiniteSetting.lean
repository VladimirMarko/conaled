import SquareKit.Internal.FiniteSetting

/-! Checked uses of the finite Set-family presentation, including invalid partitions. -/
namespace Examples.FiniteSetting
open SquareKit.Internal.FiniteSetting

/-- Bool's false point represents 0 and true represents 1. -/
def varying : Presentation Bool := ⟨fun x => x = false⟩

def varyingModel : Model varying where
  P x := x = false
  Q x := x = true
  satisfies := (satisfies_iff _ _ _).mpr (by
    refine ⟨?_, ?_, ?_⟩
    · intro x; cases x <;> simp
    · intro x; cases x <;> simp
    · exact fun _ h => h)

/-- Independently specified section: left at 0, right at 1. -/
def varyingSection : Section varying
  | false => .inl ⟨rfl⟩
  | true => .inr ()

theorem varying_correspondence : modelSectionEquiv varying varyingModel = varyingSection := by
  apply (modelSectionEquiv varying).symm.injective
  change varyingModel.toSection.toModel = varyingSection.toModel
  rw [Model.toSection_toModel]
  apply Model.ext <;> funext x <;> cases x <;> simp [varyingModel, varyingSection, Section.toModel]

theorem varying_left : (modelSectionEquiv varying varyingModel false).isLeft = true := by
  rw [varying_correspondence]; rfl

theorem varying_right : (modelSectionEquiv varying varyingModel true).isRight = true := by
  rw [varying_correspondence]; rfl

/-- At 0 both choices exist and differ; at 1 every fibre element is right. -/
theorem zero_two_choices :
    (Sum.inl ⟨rfl⟩ : Fiber varying false) ≠ Sum.inr () := by intro h; cases h

theorem one_only_right (a : Fiber varying true) : a = Sum.inr () := by
  cases a with
  | inl h => cases h.down
  | inr u => cases u; rfl

def allAllowed (X : Type) : Presentation X := ⟨fun _ => True⟩
def noneAllowed (X : Type) : Presentation X := ⟨fun _ => False⟩

def allLeft (X : Type) : Model (allAllowed X) where
  P _ := True
  Q _ := False
  satisfies := (satisfies_iff _ _ _).mpr ⟨fun _ => Or.inl trivial,
    fun _ h => h.2, fun _ _ => trivial⟩

def allRight (T : Presentation X) : Section T := fun _ => .inr ()

theorem true_left (x : X) : ((allLeft X).toSection x).isLeft = true := by
  simp [Model.toSection, allLeft]

theorem true_right (x : X) : ((allRight (allAllowed X)).toModel.Q x) := rfl

/-- With r=false the correspondence forces the unique everywhere-right section. -/
theorem false_section_unique (M : Model (noneAllowed X)) :
    modelSectionEquiv _ M = allRight (noneAllowed X) := by
  funext x
  change M.toSection x = .inr ()
  cases h : M.toSection x with
  | inl a => exact False.elim a.down
  | inr u => cases u; rfl

/-- A substitution exchanges the two fibres and the selected summands. -/
theorem substitute_not :
    (modelSectionEquiv _ (varyingModel.subst Bool.not)) true = .inl ⟨rfl⟩ ∧
    (modelSectionEquiv _ (varyingModel.subst Bool.not)) false = .inr () := by
  change (varyingModel.subst Bool.not).toSection true = _ ∧
    (varyingModel.subst Bool.not).toSection false = _
  rw [Model.toSection_subst]
  change (modelSectionEquiv _ varyingModel) false = _ ∧
    (modelSectionEquiv _ varyingModel) true = _
  rw [varying_correspondence]; exact ⟨rfl, rfl⟩

theorem varying_generic_recovery :
    (genericModel varying).subst varyingSection.graph = varyingModel := by
  rw [genericModel_recovery, ← varying_correspondence]
  exact varyingModel.toSection_toModel

/-- Coverage, disjointness and containment are independently necessary. -/
theorem rejects_uncovered : ¬ Satisfies (allAllowed Unit) (fun _ => False) (fun _ => False) := by
  intro h
  exact ((satisfies_iff _ _ _).mp h).1 () |>.elim id id

theorem rejects_overlap : ¬ Satisfies (allAllowed Unit) (fun _ => True) (fun _ => True) := by
  intro h
  exact ((satisfies_iff _ _ _).mp h).2.1 () ⟨trivial, trivial⟩

theorem rejects_forbidden_left :
    ¬ Satisfies varying (fun _ => True) (fun _ => False) := by
  intro h
  have hf := ((satisfies_iff _ _ _).mp h).2.2 true trivial
  cases hf

end Examples.FiniteSetting
