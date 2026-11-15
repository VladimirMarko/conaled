import SquareKit.OracleModalitySections

/-! Two persistent oracle requirements on a non-Boolean four-world model.
The section separator concerns the same answer objects as the modal forcing theorem. -/

namespace Examples.OracleModalities

open OracleModality OracleModality.Kripke
open CategoryTheory Opposite

abbrev p := leftAnswer
abbrev q := rightAnswer

theorem left_not_valid : p ≠ ⊤ := by
  intro h
  have : (false, false) ∈ p := by rw [h]; trivial
  exact Bool.false_ne_true this

theorem right_not_valid : q ≠ ⊤ := by
  intro h
  have : (false, false) ∈ q := by rw [h]; trivial
  exact Bool.false_ne_true this

theorem joint_inhabited : (true, true) ∈ p ⊓ q := ⟨rfl, rfl⟩

theorem joint_not_bottom : p ⊓ q ≠ ⊥ := by
  intro h
  have hh := joint_inhabited
  rw [h] at hh
  exact hh

theorem joint_not_valid : p ⊓ q ≠ ⊤ := by
  intro h
  exact left_not_valid (inf_eq_top_iff.mp h).1

/-- The future-stage implication law, not pointwise classical implication, computes this result. -/
theorem left_does_not_answer_right : p ⇨ q = q := by
  rw [← implication_eq_himp (W := World)]
  apply LowerSet.ext
  ext w
  change (∀ v : World, (show World from w) ≤ v → v.1 = true → v.2 = true) ↔ w.2 = true
  rcases w with ⟨a,b⟩
  cases a <;> cases b <;> simp [Prod.forall, Bool.forall_bool, Prod.le_def]

theorem right_does_not_answer_left : q ⇨ p = p := by
  rw [← implication_eq_himp (W := World)]
  apply LowerSet.ext
  ext w
  change (∀ v : World, (show World from w) ≤ v → v.2 = true → v.1 = true) ↔ w.1 = true
  rcases w with ⟨a,b⟩
  cases a <;> cases b <;> simp [Prod.forall, Bool.forall_bool, Prod.le_def]

theorem left_dense : p ⇨ (⊥ : Truth World) = ⊥ := by
  rw [← implication_eq_himp (W := World)]
  apply LowerSet.ext
  ext w
  change (∀ v : World, (show World from w) ≤ v → v.1 = true → False) ↔ False
  rcases w with ⟨a,b⟩
  cases a <;> cases b <;> simp [Prod.forall, Bool.forall_bool, Prod.le_def]

/-- The model's negation is not the complement supplied by the external classical metatheory. -/
theorem excluded_middle_fails : p ⊔ pᶜ ≠ ⊤ := by
  rw [← himp_bot, left_dense, sup_bot_eq]
  exact left_not_valid

theorem left_modal_answer : openNucleus p p = ⊤ := himp_self

theorem left_nonidentity : openNucleus p p ≠ p := by
  rw [left_modal_answer]
  exact Ne.symm left_not_valid

theorem left_nonchaotic : openNucleus p (⊥ : Truth World) = ⊥ := left_dense

/-- One query layer cannot supply both answers. -/
theorem first_step : step p q (p ⊓ q) (p ⊓ q) = p ⊔ q := by
  simp only [step, himp_inf_distrib, himp_self, top_inf_eq, inf_top_eq,
    left_does_not_answer_right, right_does_not_answer_left]
  rw [show p ⊓ q ⊔ q = q from sup_eq_right.mpr inf_le_right, sup_comm]

theorem first_step_not_valid : step p q (p ⊓ q) (p ⊓ q) ≠ ⊤ := by
  rw [first_step]
  intro h
  have : (false, false) ∈ p ⊔ q := by rw [h]; trivial
  exact this.elim Bool.false_ne_true Bool.false_ne_true

/-- Two return/ask layers attain the separately specified oracle interpretation. -/
theorem two_queries : step p q (p ⊓ q) (step p q (p ⊓ q) (p ⊓ q)) = ⊤ := by
  rw [two_steps]
  exact himp_self

theorem joint_modal_answer : oracle p q (p ⊓ q) = ⊤ := himp_self

theorem joint_least (j : Nucleus (Truth World)) :
    openNucleus (p ⊓ q) ≤ j ↔ j p = ⊤ ∧ j q = ⊤ := least_forcing p q j

theorem composed_answers (s : Truth World) :
    openNucleus p (openNucleus q s) = oracle p q s := open_comp p q s

/-- An actual local Type-valued answer exists at the tip. -/
def localJointAnswer : (answers (p ⊓ q)).obj.obj (op (show Site World from (true,true))) :=
  ⟨joint_inhabited⟩

/-- The same joint answer object has no global section despite its modal validity. -/
theorem modal_answer_without_section : oracle p q (p ⊓ q) = ⊤ ∧
    ¬ Nonempty (SquareKit.SheafSections.unit ⟶
      SquareKit.SheafSections.sections (display (p ⊓ q))) :=
  ⟨joint_modal_answer, fun h => joint_not_valid ((global_section_iff _).mp h)⟩

theorem each_answer_without_section :
    ¬ Nonempty (SquareKit.SheafSections.unit ⟶ SquareKit.SheafSections.sections (display p)) :=
  fun h => left_not_valid ((global_section_iff _).mp h)

/-- The positive ordinary section uses the constructed section-object naming map. -/
noncomputable def suppliedSection : SquareKit.SheafSections.unit ⟶
    SquareKit.SheafSections.sections (display (⊤ : Truth World)) := topSection

/-- Entailment and conjunction/implication observations concern actual sheaf maps. -/
theorem implication_representation (R U V : Truth World) :
    Nonempty (SquareKit.SheafRelation.product (answers R) (answers U) ⟶ answers V) ↔
      R ≤ U ⇨ V := parameterized_implication R U V

end Examples.OracleModalities
