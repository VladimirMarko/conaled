import SquareKit.Internal.DependentJudgments.LeftConcatGroupoidSemantics
import Examples.GroupoidTransport

/-! Checked consumers of the guarded first-path recipe. These known cases are
framework-authored regression evidence, not the independent author retest. -/
noncomputable section
namespace Examples.GuardedLeftConcatenation
open CategoryTheory SquareKit.Internal
open DependentJudgments DependentJudgments.Contextual
open DependentJudgments.Contextual.TelescopePresentation
open PathTransport.GroupoidModel
open Examples.GroupoidTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev G : Grpd := @Grpd.of (Discrete PUnit) (Groupoid.ofIsGroupoid (C := Discrete PUnit))
def base : Section (constant (Γ := G) C4) :=
  constantSection ((Functor.const G).obj point)

def labeled (n : ZMod 4) : Section (identityFamily (constant C4) base base) where
  obj _ := ⟨label n⟩
  map _ := eqToHom (by
    apply Discrete.ext
    change inv (𝟙 GroupoidTransport.point) ≫ label n ≫ 𝟙 GroupoidTransport.point = label n
    simp)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

def observed (B : C4 ⥤ Type) (m n : ZMod 4) : Option (GroupoidTransport.point ⟶ GroupoidTransport.point) :=
  Option.map (fun t : (Instance.fullModel C4 B).Section G
      (identityFamily (constant C4) base base) => (t.down.obj ⟨PUnit.unit⟩).as)
    ((LeftSemantics.Groupoid.recipe.eval (algebra (Instance.fullModel C4 B))
      (LeftSemantics.Groupoid.environment C4 B base base base (labeled m) (labeled n))).termAt G
        (identityFamily (constant C4) base base))

theorem observed_eq (B : C4 ⥤ Type) (m n : ZMod 4) :
    observed B m n = some (label m ≫ label n) :=
  LeftSemantics.Groupoid.recipe_action C4 B base base base (labeled m) (labeled n) ⟨PUnit.unit⟩

example : observed faithful 1 2 = some (label 3) := by
  rw [observed_eq]
  rfl

example : observed ineffective 1 2 = some (label 3) := by
  rw [observed_eq]
  rfl

/-- Ineffective arrows stay distinguishable even though every fiber action is
identity. This exercises interpretation of the source J recipe itself. -/
theorem ineffective_distinct : observed ineffective 1 0 ≠ observed ineffective 0 0 := by
  rw [observed_eq, observed_eq]
  intro h
  have h' : label 1 = label 0 := Option.some.inj h
  exact (by decide : (1 : ZMod 4) ≠ 0) (labels_injective h')

open SquareKit.GuardedTheory
abbrev inputs : List (Contextual.Judgment (Fin 7)) :=
  [term (.var 0) (.var 1) (.var 2), term (.var 0) (.var 1) (.var 3),
    term (.var 0) (.var 1) (.var 4),
    term (.var 0) (Contextual.identity (.var 1) (.var 2) (.var 3)) (.var 5),
    term (.var 0) (Contextual.identity (.var 1) (.var 3) (.var 4)) (.var 6)]

def source : TelescopePresentation.Tm (Ω := inputs) (.var 0) (Contextual.identity (.var 1) (.var 2) (.var 4))
    LeftSemantics.Groupoid.recipe :=
  TelescopePresentation.Tm.leftConcat (.hypothesis (by simp [inputs])) (.hypothesis (by simp [inputs]))
    (.hypothesis (by simp [inputs])) (.hypothesis (by simp [inputs]))
    (.hypothesis (by simp [inputs]))

/-- The generated judgment is interpreted by the existing guarded soundness
proof for every model, before specializing any groupoid observations. -/
theorem source_sound (M : PathTransport.Typed.Model) (ρ : Fin 7 → Value M.toStructuralModel)
    (hρ : ∀ a ∈ inputs, a.eval (TelescopePresentation.model M).toAlgebra ρ) :
    (term (.var 0) (Contextual.identity (.var 1) (.var 2) (.var 4))
      LeftSemantics.Groupoid.recipe).eval (TelescopePresentation.model M).toAlgebra ρ :=
  Derivation.sound (TelescopePresentation.model M) source ρ hρ

theorem inputs_valid (B : C4 ⥤ Type) (m n : ZMod 4) :
    ∀ a ∈ inputs, a.eval (TelescopePresentation.model (Instance.fullModel C4 B)).toAlgebra
      (LeftSemantics.Groupoid.environment C4 B base base base (labeled m) (labeled n)) := by
  intro a ha
  simp only [inputs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  all_goals
    change ∃ Γ A t, _ = Value.context Γ ∧ _ = Value.family Γ A ∧ _ = Value.term Γ A t
    first
    | exact ⟨G, constant C4, ⟨base⟩, rfl, rfl, rfl⟩
    | refine ⟨G, identityFamily (constant C4) base base, ⟨labeled m⟩, rfl, ?_, rfl⟩
    | refine ⟨G, identityFamily (constant C4) base base, ⟨labeled n⟩, rfl, ?_, rfl⟩
  all_goals
    simp [Term.eval, TelescopePresentation.model, Contextual.algebra, Contextual.operation, LeftSemantics.Groupoid.environment]
    rfl

/-- These concrete inputs satisfy every source assumption, including
nonreflexive choices of both path labels. Soundness therefore applies to the actual recipe. -/
theorem interpreted (B : C4 ⥤ Type) (m n : ZMod 4) :
    (term (.var 0) (Contextual.identity (.var 1) (.var 2) (.var 4))
      LeftSemantics.Groupoid.recipe).eval
      (TelescopePresentation.model (Instance.fullModel C4 B)).toAlgebra
      (LeftSemantics.Groupoid.environment C4 B base base base (labeled m) (labeled n)) :=
  source_sound _ _ (inputs_valid B m n)
end Examples.GuardedLeftConcatenation
