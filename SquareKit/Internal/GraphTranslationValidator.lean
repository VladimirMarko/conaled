import SquareKit.Internal.GraphEmissionSquares
import SquareKit.Internal.GraphPrimitiveEnvironment
import SquareKit.Internal.GraphArtifactEquality

/-! A bounded replay validator for graph translations. Certificates contain
executable proof instructions, never semantic correctness or acceptance proofs.
The intended type is fixed by the source; the proof body may use another Code.
The environment input is the ordered projection of the host environment onto
all pinned primitives and helpers. Reading that projection is a driver task. -/
namespace SquareKit.Internal.GraphTranslationValidator
open Lean GraphTarget GraphEmissionPure GraphArtifactEquality
universe v

structure Certificate (s : SourceProgram) where
  version : Nat := 1
  code : Code (translateFormula s.premise) (translateFormula s.conclusion)

def Certificate.target (c : Certificate s) : GraphTarget.Declaration :=
  { s.target with code := c.code }

def Certificate.original (s : SourceProgram) : Certificate s := ⟨1, s.code⟩

def nodes : E → Nat
  | .bvar _ | .sort _ | .const _ _ => 1
  | .app a b | .lam a b | .all a b => 1 + nodes a + nodes b

inductive Error where
  | version | environment | kind | name | universes | mutual | type | body | limit
  deriving DecidableEq, Repr

/-- A size bound applies to the reconstructed type and body. It is a bound on
this accepted fragment, not a resource guarantee for an untrusted driver. -/
def check (limit : Nat) (s : SourceProgram) (name : Name)
    (environment : List ConstantInfo) (actual : ConstantInfo) (c : Certificate s) : Except Error Unit :=
  if c.version ≠ 1 then .error .version else
  if listEq constantEq environment GraphPrimitiveEnvironment.declarations ≠ true then .error .environment else
  match actual with
  | .thmInfo t =>
    if t.name ≠ name then .error .name else
    if t.levelParams ≠ [`v] then .error .universes else
    if t.all ≠ [name] then .error .mutual else
    let expected := emitCore c.target
    if CoreSyntax.Expr.ofLean t.type ≠ some (emitCore s.target).1 then .error .type else
    if CoreSyntax.Expr.ofLean t.value ≠ some expected.2 then .error .body else
    if nodes expected.1 + nodes expected.2 > limit then .error .limit else .ok ()
  | _ => .error .kind

private theorem context_type (Γ : List Ty) (m : Model)
    (f g : Model → Assignment Γ → E × E) (h : ∀ m a, (f m a).1 = (g m a).1) :
    (context m Γ f).1 = (context m Γ g).1 := by
  induction Γ with
  | nil => exact h _ _
  | cons s Γ ih =>
    apply ih
    intro m a
    dsimp only
    rw [h]

theorem Certificate.type_eq (c : Certificate s) :
    (emitCore c.target).1 = (emitCore s.target).1 := by
  simp only [emitCore]
  apply congrArg (closeParameters true)
  apply context_type
  intro m a
  rfl

/-- Source syntax and declaration identity remain in the contract in addition
to the shared semantic relation; truth of an unrelated proposition is insufficient. -/
structure Validated (s : SourceProgram) (name : Name) (environment : List ConstantInfo)
    (actual : ConstantInfo) : Prop where
  environment_eq : environment = GraphPrimitiveEnvironment.declarations
  theorem_record : ∃ t : TheoremVal, actual = .thmInfo t ∧ t.name = name ∧
    t.levelParams = [`v] ∧ t.all = [name] ∧
    CoreSyntax.Expr.ofLean t.type = some (emitCore s.target).1 ∧
    ArtifactTyped (t.type, t.value) ∧ ArtifactDenotes.{v} (t.type, t.value) s.denote.{v}

theorem check_sound (h : check limit s name environment actual c = .ok ()) :
    Validated.{v} s name environment actual := by
  unfold check at h
  split at h
  · contradiction
  split at h
  · contradiction
  rename_i he
  have heq := listEq_sound constantEq (@constantEq_sound) (by simpa using he)
  split at h
  · rename_i t
    repeat first | (split at h) | contradiction | (dsimp only at h)
    rename_i hn hu hm ht hb hl
    have ht : CoreSyntax.Expr.ofLean t.type = some (emitCore s.target).1 := by simpa using ht
    have hb : CoreSyntax.Expr.ofLean t.value = some (emitCore c.target).2 := by simpa using hb
    constructor
    · exact heq
    · refine ⟨t, rfl, (by simpa using hn), (by simpa using hu), (by simpa using hm), ht, ?_, ?_⟩
      · exact ⟨_, _, ht.trans (congrArg some c.type_eq.symm), hb, emitCore_typed c.target⟩
      · refine ⟨_, _, ht.trans (congrArg some c.type_eq.symm), hb, ?_⟩
        have hd := emitCore_denotes.{v} c.target
        have eqDenote : c.target.denote.{v} = s.denote.{v} := propext s.target_denote
        exact eqDenote ▸ hd
  · contradiction

/-- Success implies the source-to-core preservation claim without a semantic
premise on the certificate. -/
theorem Validated.source (h : Validated.{v} s name environment actual) : s.denote.{v} := by
  obtain ⟨t, _, _, _, _, _, _, hd⟩ := h.theorem_record
  exact hd.sound

theorem approvedEnvironment_checked :
    listEq constantEq GraphPrimitiveEnvironment.declarations GraphPrimitiveEnvironment.declarations = true := by
  decide

def payload (name : Name) (c : Certificate s) : ConstantInfo := constantInfo name c.target

theorem check_payload (c : Certificate s) (hv : c.version = 1)
    (hl : nodes (emitCore c.target).1 + nodes (emitCore c.target).2 ≤ limit) :
    check limit s name GraphPrimitiveEnvironment.declarations (payload name c) c = .ok () := by
  have hl' := hl
  rw [c.type_eq] at hl'
  simp [check, hv, approvedEnvironment_checked, payload, constantInfo, emit,
    CoreSyntax.Expr.ofLean_toLean, c.type_eq, Nat.not_lt.mpr hl']

/-- Both checked stages use the repository's shared relational square interface. -/
def checkedRep : Relational.RelRep where
  R := Σ _s : SourceProgram, Σ _name : Name, List ConstantInfo × ConstantInfo
  S := Prop
  Rel x P := Validated.{v} x.1 x.2.1 x.2.2.1 x.2.2.2 ∧ x.1.denote.{v} = P

def validatedSquare : Relational.RelSquare checkedRep.{v} sourceRep.{v} where
  impl := Sigma.fst
  spec := id
  preserves := fun h => h.2

def checkedTargetSquare : Relational.RelSquare checkedRep.{v} declarationRep.{v} :=
  Relational.compose sourceSquare validatedSquare

/-- The actual declaration payload, including the transformed body, maps to the
same artifact relation used by the producer. -/
def validatedArtifactSquare : Relational.RelSquare checkedRep.{v} artifactRep.{v} where
  impl x := (x.2.2.2.type, (x.2.2.2.value? true).getD (.sort .zero))
  spec := id
  preserves := by
    intro x P h
    obtain ⟨t, ha, _, _, _, _, ht, hd⟩ := h.1.theorem_record
    rcases x with ⟨s, name, env, actual⟩
    dsimp at ha ht hd
    cases ha
    cases h.2
    exact ⟨ht, hd⟩

/-- Cut composes certificates at a shared source formula. Its semantic proof
uses the separately validated source-to-core results at both stages. -/
def composeSource {Γ : List Ty} {p q r : SourceFormula Γ}
    (a : Code (translateFormula p) (translateFormula q))
    (b : Code (translateFormula q) (translateFormula r)) : SourceProgram :=
  ⟨Γ, p, r, .cut a b⟩

theorem compose_preserves {Γ : List Ty} {p q r : SourceFormula Γ}
    {a : Code (translateFormula p) (translateFormula q)}
    {b : Code (translateFormula q) (translateFormula r)}
    (ha : Validated.{v} ⟨Γ, p, q, a⟩ na ea aa)
    (hb : Validated.{v} ⟨Γ, q, r, b⟩ nb eb ab) : (composeSource a b).denote.{v} :=
  fun M ρ hp => hb.source M ρ (ha.source M ρ hp)

end SquareKit.Internal.GraphTranslationValidator
