import EmittedGraph
import GraphEnvironment
import SquareKit.Internal.GraphPrimitiveEnvironment

/-! Native helper records are translated from the exact producer environment.
ConLeche erases binder names and binder-info flags in its expression grammar.
Its checked primitive blocks compute their own recursor and projection metadata.
-/
namespace EmittedEnvironment
open ConLeche SquareKit.Internal EmissionEncoding

def expression : Lean.Expr → Option ConLeche.Expr
  | .bvar i => some (.bvar i)
  | .sort u => return .sort (← U.encode u)
  | .const n us => return .const (N.encode n) (← levels us)
  | .app f a => return .app (← expression f) (← expression a)
  | .lam _ a b _ => return .lam (← expression a) (← expression b)
  | .forallE _ a b _ => return .forallE (← expression a) (← expression b)
  | .proj n i e => return .proj (N.encode n) i (← expression e)
  | _ => none

theorem expression_core (e : CoreSyntax.Expr) : expression e.toLean = encode e := by
  induction e <;> simp_all [CoreSyntax.Expr.toLean, expression, encode]

def value (c : Lean.ConstantVal) : Option ConLeche.ConstantVal := do
  return ⟨N.encode c.name, c.levelParams.map N.encode, ← expression c.type⟩

def hint : Lean.ReducibilityHints → ConLeche.ReducibilityHint
  | .opaque => .opaque
  | .abbrev => .abbrev
  | .regular n => .regular n.toNat

def helper : Lean.ConstantInfo → Option ConLeche.Declaration
  | .thmInfo c => return .thmDecl (← value c.toConstantVal) (← expression c.value)
  | .defnInfo c => return .defnDecl (← value c.toConstantVal) (← expression c.value) (hint c.hints)
  | _ => none

/-- Dependency order, with the native private matcher before Exists.elim. -/
def helperNames : List Lean.Name :=
  [``rfl, ``Eq.symm, ``Eq.trans, ``congrArg, ``And.left, ``And.right,
    ``Exists.casesOn,
    Lean.Name.str (Lean.Name.str (Lean.Name.str (.num `_private.Init.Core 0) "Exists") "elim") "match_1_1",
    ``Exists.elim]

def helpers : List ConLeche.Declaration := helperNames.filterMap fun n =>
  (GraphPrimitiveEnvironment.declarations.find? (fun c => c.name == n)).bind helper

def graphDeclarations : List ConLeche.Declaration :=
  [.thmDecl ⟨N.encode `graph_forward, [N.encode `v], EmittedGraph.forwardType⟩ EmittedGraph.forwardProof,
   .thmDecl ⟨N.encode `graph_backward, [N.encode `v], EmittedGraph.backwardType⟩ EmittedGraph.backwardProof]

def declarations : List ConLeche.Declaration :=
  GraphEnvironment.declarations.toList ++ helpers ++ graphDeclarations

def stored : ConLeche.Declaration → Option ConLeche.ConstantInfo
  | .thmDecl c _ => some (.thmInfo c)
  | .defnDecl c v h => some (.defnInfo c v h)
  | _ => none

def environment : ConLeche.Env :=
  ⟨((helpers ++ graphDeclarations).filterMap stored).reverse ++ GraphEnvironment.environment.consts,
    GraphEnvironment.environment.tables⟩


theorem helpers_complete : helpers.length = helperNames.length := rfl

/-- Universe parameter names are canonicalized by their declared positions. -/
def nativeSignature (n : Lean.Name) : Option ConLeche.ConstantVal :=
  ((GraphPrimitiveEnvironment.declarations.find? (fun c => c.name == n)).bind
    (fun c => value c.toConstantVal)).map ConstantVal.canon

def relativeSignature (n : Lean.Name) : Option ConLeche.ConstantVal :=
  (GraphEnvironment.environment.find? (N.encode n)).map (fun c => c.toConstantVal.canon)

theorem primitive_signatures :
    ([``Eq, ``Eq.refl, ``Eq.rec, ``And, ``And.intro, ``Exists, ``Exists.intro, ``Exists.rec].map
      nativeSignature) =
    ([``Eq, ``Eq.refl, ``Eq.rec, ``And, ``And.intro, ``Exists, ``Exists.intro, ``Exists.rec].map
      relativeSignature) := by rfl

end EmittedEnvironment
#audit_graph_module
