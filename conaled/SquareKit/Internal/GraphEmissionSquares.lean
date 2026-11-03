import SquareKit.Internal.GraphEmissionContract
import SquareKit.Internal.GraphEmissionTyping
import SquareKit.Relations

/-! Source preservation and emission compose through the shared relational
square interface. The artifact relation permits independently certified
producers; it does not require equality to the pure producer's output. -/
namespace SquareKit.Internal.GraphEmissionPure
open GraphTarget
universe v

def declarationRep : Relational.RelRep where
  R := GraphTarget.Declaration
  S := Prop
  Rel d P := Declaration.denote.{v} d = P

def artifactRep : Relational.RelRep where
  R := Lean.Expr × Lean.Expr
  S := Prop
  Rel a P := ArtifactTyped a ∧ ArtifactDenotes.{v} a P

def producerSquare : Relational.RelSquare declarationRep.{v} artifactRep.{v} where
  impl := emit
  spec := id
  preserves := by
    intro d P h
    cases h
    exact ⟨emit_typed d, emit_denotes d⟩

/-- The source proof lives in Prop; the chosen executable target certificate is
provided as data, rather than extracted by choice from translate_derivation. -/
structure SourceProgram where
  context : List Ty
  premise : SourceFormula context
  conclusion : SourceFormula context
  code : Code (translateFormula premise) (translateFormula conclusion)

def SourceProgram.target (s : SourceProgram) : GraphTarget.Declaration :=
  ⟨s.context, translateFormula s.premise, translateFormula s.conclusion, s.code⟩

def SourceProgram.denote (s : SourceProgram) : Prop :=
  ∀ (M : Interpretation.{0,v} Graph.Arrow) (ρ : Env M s.context),
    s.premise.eval M ρ → s.conclusion.eval M ρ

theorem SourceProgram.target_denote (s : SourceProgram) :
    Declaration.denote.{v} s.target ↔ s.denote.{v} := by
  constructor
  · intro h M ρ hp
    exact (formula_comparison M ρ s.conclusion).mp
      (h M ρ ((formula_comparison M ρ s.premise).mpr hp))
  · intro h M ρ hp
    exact (formula_comparison M ρ s.conclusion).mpr
      (h M ρ ((formula_comparison M ρ s.premise).mp hp))

def sourceRep : Relational.RelRep where
  R := SourceProgram
  S := Prop
  Rel s P := s.denote.{v} = P

def sourceSquare : Relational.RelSquare sourceRep.{v} declarationRep.{v} where
  impl := SourceProgram.target
  spec := id
  preserves := by
    intro s P h
    cases h
    exact propext s.target_denote

def sourceEmissionSquare : Relational.RelSquare sourceRep.{v} artifactRep.{v} :=
  Relational.compose producerSquare sourceSquare

theorem source_emission (s : SourceProgram) :
    ArtifactTyped (emit s.target) ∧ ArtifactDenotes.{v} (emit s.target) s.denote.{v} :=
  sourceEmissionSquare.preserves (r := s) rfl

end SquareKit.Internal.GraphEmissionPure
