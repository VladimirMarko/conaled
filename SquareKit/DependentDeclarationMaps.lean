import SquareKit.DependentDeclarationSubstitution

/-! The pair-template translation fixes the independently typed declarations. -/
namespace SquareKit.DependentPairDeclarations
open DependentTheoryMaps DependentPairPresentations DependentPairJudgments

@[simp] theorem projectionToElimination_operation (decl : Declaration)
    (args : (i : Fin (signature.arity decl)) → PExpr (Fin (signature.binds decl i) ⊕ V)) :
    projectionToElimination.act (projection.operation decl args) =
      elimination.operation decl (fun i => projectionToElimination.act (args i)) := rfl

@[simp] theorem projectionToElimination_N : projectionToElimination.act (Terms.N (V := V) projection) = Terms.N elimination := by
  rw [Terms.N, projectionToElimination_operation]
  congr 1
  funext i
  nomatch i

@[simp] theorem projectionToElimination_B (n : PExpr V) :
    projectionToElimination.act (Terms.B projection n) = Terms.B elimination (projectionToElimination.act n) := by
  rw [Terms.B, projectionToElimination_operation]
  congr 1
  funext i
  change Fin 1 at i
  fin_cases i
  exact projectionToElimination.rename Sum.inr n

@[simp] theorem projectionToElimination_C (n y : PExpr V) :
    projectionToElimination.act (Terms.C projection n y) = Terms.C elimination (projectionToElimination.act n) (projectionToElimination.act y) := by
  rw [Terms.C, projectionToElimination_operation]
  congr 1
  funext i
  change Fin 2 at i
  fin_cases i <;> exact projectionToElimination.rename Sum.inr _

@[simp] theorem projectionToElimination_s (m : PExpr V) :
    projectionToElimination.act (Terms.s projection m) = Terms.s elimination (projectionToElimination.act m) := by
  rw [Terms.s, projectionToElimination_operation]
  congr 1
  funext i
  change Fin 1 at i
  fin_cases i
  exact projectionToElimination.rename Sum.inr m

@[simp] theorem projectionToElimination_d (m : PExpr V) :
    projectionToElimination.act (Terms.d projection m) = Terms.d elimination (projectionToElimination.act m) := by
  rw [Terms.d, projectionToElimination_operation]
  congr 1
  funext i
  change Fin 1 at i
  fin_cases i
  exact projectionToElimination.rename Sum.inr m

@[simp] theorem projectionToElimination_t (m : PExpr V) :
    projectionToElimination.act (Terms.t projection m) = Terms.t elimination (projectionToElimination.act m) := by
  rw [Terms.t, projectionToElimination_operation]
  congr 1
  funext i
  change Fin 1 at i
  fin_cases i
  exact projectionToElimination.rename Sum.inr m

@[simp] theorem projectionToElimination_u (m : PExpr V) :
    projectionToElimination.act (Terms.u projection m) = Terms.u elimination (projectionToElimination.act m) := by
  rw [Terms.u, projectionToElimination_operation]
  congr 1
  funext i
  change Fin 1 at i
  fin_cases i
  exact projectionToElimination.rename Sum.inr m

def Rule.map (F : SyntaxMap S T) : Rule S → Rule T
  | .N Γ => .N (Γ.map F)
  | .B Γ n => .B (Γ.map F) (F.act n)
  | .C Γ n y => .C (Γ.map F) (F.act n) (F.act y)
  | .s Γ m => .s (Γ.map F) (F.act m)
  | .d Γ m => .d (Γ.map F) (F.act m)
  | .t Γ m => .t (Γ.map F) (F.act m)
  | .u Γ m => .u (Γ.map F) (F.act m)

@[simp] theorem Rule.projectionToElimination_schema (r : Rule projectionSignature) :
    (r.map projectionToElimination).schema elimination = (r.schema projection).map projectionToElimination := by
  cases r <;> simp [Rule.map, Rule.schema, Schema.map, Judgment.map, Judgment.mapForm,
    Judgment.ctx, Judgment.type, Judgment.term]

def gDeclarations : TheoryMap (rulesOf (Rule.schema projection))
    (rulesOf (Rule.schema elimination)) (Judgment.map projectionToElimination) :=
  replayMap _ _ projectionToElimination (Rule.map projectionToElimination) Rule.projectionToElimination_schema

def Congruence.map (F : SyntaxMap S T) : Congruence S → Congruence T
  | .B Γ n n' => .B (Γ.map F) (F.act n) (F.act n')
  | .C Γ n n' y y' => .C (Γ.map F) (F.act n) (F.act n') (F.act y) (F.act y')
  | .s Γ m m' => .s (Γ.map F) (F.act m) (F.act m')
  | .d Γ m m' => .d (Γ.map F) (F.act m) (F.act m')
  | .t Γ m m' => .t (Γ.map F) (F.act m) (F.act m')
  | .u Γ m m' => .u (Γ.map F) (F.act m) (F.act m')

@[simp] theorem Congruence.projectionToElimination_schema (r : Congruence projectionSignature) :
    (r.map projectionToElimination).schema elimination = (r.schema projection).map projectionToElimination := by
  cases r <;> simp [Congruence.map, Congruence.schema, Schema.map, Judgment.map, Judgment.mapForm,
    Judgment.ctx, Judgment.term, Judgment.typeEq, Judgment.termEq]

def gDeclarationCongruence : TheoryMap (rulesOf (Congruence.schema projection))
    (rulesOf (Congruence.schema elimination)) (Judgment.map projectionToElimination) :=
  replayMap _ _ projectionToElimination (Congruence.map projectionToElimination) Congruence.projectionToElimination_schema

end SquareKit.DependentPairDeclarations
