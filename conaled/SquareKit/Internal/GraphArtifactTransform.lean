import SquareKit.Internal.GraphTranslationValidator

/-! An artifact transformation independent of proof-code construction. It reads
raw type/body syntax and inserts two Eq.symm applications at an equality leaf.
Its accepted output is connected to replay instructions by checked equations. -/
namespace SquareKit.Internal.GraphArtifactTransform
open Lean GraphEmissionPure GraphTranslationValidator

/-- Descend corresponding telescope binders. A malformed telescope or a
non-equality leaf is rejected. Variables are never permuted or erased. -/
def doubleSymmetry : E → E → Option E
  | .all a t, .lam b v =>
      if a = b then (.lam b) <$> doubleSymmetry t v else none
  | .app (.app (.app (.const n us) a) x) y, proof =>
      if n = ``Eq then
        some (.apps (.const ``Eq.symm us) [a, y, x,
          .apps (.const ``Eq.symm us) [a, x, y, proof]])
      else none
  | _, _ => none

/-- Decode the actual record, transform its body, and retain its declaration
name, universes and type verbatim. No Code value is an input to this strategy. -/
def transform (actual : ConstantInfo) : Option ConstantInfo := do
  let .thmInfo t := actual | none
  let ty ← CoreSyntax.Expr.ofLean t.type
  let body ← CoreSyntax.Expr.ofLean t.value
  let body' ← doubleSymmetry ty body
  return .thmInfo { t with value := body'.toLean }

/-- Alpha renaming changes only binder labels, not their indices or info flags. -/
def renameBinders (name : Name) : Lean.Expr → Lean.Expr
  | .app f a => .app (renameBinders name f) (renameBinders name a)
  | .lam _ a b i => .lam name (renameBinders name a) (renameBinders name b) i
  | .forallE _ a b i => .forallE name (renameBinders name a) (renameBinders name b) i
  | e => e

theorem renameBinders_decodes (name : Name) (e : Lean.Expr) :
    CoreSyntax.Expr.ofLean (renameBinders name e) = CoreSyntax.Expr.ofLean e := by
  induction e <;> simp_all [renameBinders, CoreSyntax.Expr.ofLean]
  all_goals rename_i info _ _
  all_goals cases info <;> simp_all [CoreSyntax.Expr.ofLean]

def renameDeclaration (name : Name) : ConstantInfo → ConstantInfo
  | .thmInfo t => .thmInfo { t with type := renameBinders name t.type, value := renameBinders name t.value }
  | ci => ci

/-- Validator acceptance transports along alpha renaming for every request,
certificate and diagnostic result. Exact environment records are unaffected. -/
theorem check_rename (binderName : Name) (actual : ConstantInfo) :
    check limit s name environment (renameDeclaration binderName actual) c =
      check limit s name environment actual c := by
  cases actual <;> simp only [check, renameDeclaration, renameBinders_decodes]

end SquareKit.Internal.GraphArtifactTransform
