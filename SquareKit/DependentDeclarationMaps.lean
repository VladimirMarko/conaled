import SquareKit.DependentDeclarationSubstitution

/-! The pair-template translation fixes the independently typed declarations. -/
namespace SquareKit.DependentPairDeclarations
open DependentTheoryMaps DependentPairPresentations DependentPairJudgments

@[simp] theorem G_operation (decl : Declaration)
    (args : (i : Fin (signature.arity decl)) → PExpr (Fin (signature.binds decl i) ⊕ V)) :
    G.act (projection.operation decl args) =
      elimination.operation decl (fun i => G.act (args i)) := rfl

@[simp] theorem G_N : G.act (Terms.N (V := V) projection) = Terms.N elimination := by
  rw [Terms.N, G_operation]
  congr 1
  funext i
  nomatch i

@[simp] theorem G_B (n : PExpr V) :
    G.act (Terms.B projection n) = Terms.B elimination (G.act n) := by
  rw [Terms.B, G_operation]
  congr 1
  funext i
  change Fin 1 at i
  fin_cases i
  exact G.rename Sum.inr n

@[simp] theorem G_C (n y : PExpr V) :
    G.act (Terms.C projection n y) = Terms.C elimination (G.act n) (G.act y) := by
  rw [Terms.C, G_operation]
  congr 1
  funext i
  change Fin 2 at i
  fin_cases i <;> exact G.rename Sum.inr _

@[simp] theorem G_s (m : PExpr V) :
    G.act (Terms.s projection m) = Terms.s elimination (G.act m) := by
  rw [Terms.s, G_operation]
  congr 1
  funext i
  change Fin 1 at i
  fin_cases i
  exact G.rename Sum.inr m

@[simp] theorem G_d (m : PExpr V) :
    G.act (Terms.d projection m) = Terms.d elimination (G.act m) := by
  rw [Terms.d, G_operation]
  congr 1
  funext i
  change Fin 1 at i
  fin_cases i
  exact G.rename Sum.inr m

@[simp] theorem G_t (m : PExpr V) :
    G.act (Terms.t projection m) = Terms.t elimination (G.act m) := by
  rw [Terms.t, G_operation]
  congr 1
  funext i
  change Fin 1 at i
  fin_cases i
  exact G.rename Sum.inr m

@[simp] theorem G_u (m : PExpr V) :
    G.act (Terms.u projection m) = Terms.u elimination (G.act m) := by
  rw [Terms.u, G_operation]
  congr 1
  funext i
  change Fin 1 at i
  fin_cases i
  exact G.rename Sum.inr m

def Rule.map (F : SyntaxMap S T) : Rule S → Rule T
  | .N Γ => .N (Γ.map F)
  | .B Γ n => .B (Γ.map F) (F.act n)
  | .C Γ n y => .C (Γ.map F) (F.act n) (F.act y)
  | .s Γ m => .s (Γ.map F) (F.act m)
  | .d Γ m => .d (Γ.map F) (F.act m)
  | .t Γ m => .t (Γ.map F) (F.act m)
  | .u Γ m => .u (Γ.map F) (F.act m)

@[simp] theorem Rule.G_schema (r : Rule projectionSignature) :
    (r.map G).schema elimination = (r.schema projection).map G := by
  cases r <;> simp [Rule.map, Rule.schema, Schema.map, Judgment.map, Judgment.mapForm,
    Judgment.ctx, Judgment.type, Judgment.term]

def G_declarations : TheoryMap (rulesOf (Rule.schema projection))
    (rulesOf (Rule.schema elimination)) (Judgment.map G) :=
  replayMap _ _ G (Rule.map G) Rule.G_schema

def Congruence.map (F : SyntaxMap S T) : Congruence S → Congruence T
  | .B Γ n n' => .B (Γ.map F) (F.act n) (F.act n')
  | .C Γ n n' y y' => .C (Γ.map F) (F.act n) (F.act n') (F.act y) (F.act y')
  | .s Γ m m' => .s (Γ.map F) (F.act m) (F.act m')
  | .d Γ m m' => .d (Γ.map F) (F.act m) (F.act m')
  | .t Γ m m' => .t (Γ.map F) (F.act m) (F.act m')
  | .u Γ m m' => .u (Γ.map F) (F.act m) (F.act m')

@[simp] theorem Congruence.G_schema (r : Congruence projectionSignature) :
    (r.map G).schema elimination = (r.schema projection).map G := by
  cases r <;> simp [Congruence.map, Congruence.schema, Schema.map, Judgment.map, Judgment.mapForm,
    Judgment.ctx, Judgment.term, Judgment.typeEq, Judgment.termEq]

def G_declarationCongruence : TheoryMap (rulesOf (Congruence.schema projection))
    (rulesOf (Congruence.schema elimination)) (Judgment.map G) :=
  replayMap _ _ G (Congruence.map G) Congruence.G_schema

end SquareKit.DependentPairDeclarations
