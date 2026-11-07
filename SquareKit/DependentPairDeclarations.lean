import SquareKit.DependentPairStructuralMaps

/-! Ordered declarations shared by the independently specified test clients. -/
namespace SquareKit.DependentPairDeclarations
open DependentTheoryMaps DependentPairPresentations DependentPairJudgments

abbrev signature := fromBindings Declaration Declaration.bindings

def projection : OperationMap signature projectionSignature where
  operation := fun decl args => .app (.declaration decl) args
  natural := fun _ _ _ => rfl

def elimination : OperationMap signature eliminationSignature where
  operation := fun decl args => .app (.declaration decl) args
  natural := fun _ _ _ => rfl

namespace Terms
variable (D : OperationMap signature S)
def N : Expr S V := D.operation .N (fun i => nomatch i)
def B (n : Expr S V) : Expr S V :=
  D.operation .B (Fin.cases (zero n) (fun i => nomatch i))
def C (n y : Expr S V) : Expr S V :=
  D.operation .C (Fin.cases (zero n) (Fin.cases (zero y) (fun i => nomatch i)))
def s (m : Expr S V) : Expr S V :=
  D.operation .s (Fin.cases (zero m) (fun i => nomatch i))
def d (k : Expr S V) : Expr S V :=
  D.operation .d (Fin.cases (zero k) (fun i => nomatch i))
def t (m : Expr S V) : Expr S V :=
  D.operation .t (Fin.cases (zero m) (fun i => nomatch i))
def u (m : Expr S V) : Expr S V :=
  D.operation .u (Fin.cases (zero m) (fun i => nomatch i))
end Terms

namespace Projection
abbrev N : PExpr V := Terms.N projection
abbrev B (n : PExpr V) := Terms.B projection n
abbrev C (n y : PExpr V) := Terms.C projection n y
abbrev s (m : PExpr V) := Terms.s projection m
abbrev d (m : PExpr V) := Terms.d projection m
abbrev t (m : PExpr V) := Terms.t projection m
abbrev u (m : PExpr V) := Terms.u projection m
end Projection
namespace Elimination
abbrev N : EExpr V := Terms.N elimination
abbrev B (n : EExpr V) := Terms.B elimination n
abbrev C (n y : EExpr V) := Terms.C elimination n y
abbrev s (m : EExpr V) := Terms.s elimination m
abbrev d (m : EExpr V) := Terms.d elimination m
abbrev t (m : EExpr V) := Terms.t elimination m
abbrev u (m : EExpr V) := Terms.u elimination m
end Elimination

/-- Each declaration is admitted only at its typed argument telescope. -/
inductive Rule (S : Signature) where
  | N {V} (Γ : Context S V)
  | B {V} (Γ : Context S V) (n : Expr S V)
  | C {V} (Γ : Context S V) (n y : Expr S V)
  | s {V} (Γ : Context S V) (m : Expr S V)
  | d {V} (Γ : Context S V) (k : Expr S V)
  | t {V} (Γ : Context S V) (m : Expr S V)
  | u {V} (Γ : Context S V) (m : Expr S V)

def Rule.schema (D : OperationMap signature S) : Rule S → Schema S
  | .N Γ => ⟨[.ctx Γ], .type Γ (Terms.N D)⟩
  | .B Γ n => ⟨[.ctx Γ, .term Γ n (Terms.N D)], .type Γ (Terms.B D n)⟩
  | .C Γ n y => ⟨[.ctx Γ, .term Γ n (Terms.N D), .term Γ y (Terms.B D n)],
      .type Γ (Terms.C D n y)⟩
  | .s Γ m => ⟨[.ctx Γ, .term Γ m (Terms.N D)], .term Γ (Terms.s D m) (Terms.N D)⟩
  | .d Γ k => ⟨[.ctx Γ, .term Γ k (Terms.N D)], .term Γ (Terms.d D k) (Terms.N D)⟩
  | .t Γ m => ⟨[.ctx Γ, .term Γ m (Terms.N D)],
      .term Γ (Terms.t D m) (Terms.B D (Terms.s D m))⟩
  | .u Γ m => ⟨[.ctx Γ, .term Γ m (Terms.N D)],
      .term Γ (Terms.u D m) (Terms.C D (Terms.s D m) (Terms.t D m))⟩

end SquareKit.DependentPairDeclarations
