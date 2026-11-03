import ArtifactAudit
import GraphEnvironment
import GraphAdapter

namespace GraphDeclarations
open ConLeche ConLeche.BasisDSL
open GraphEnvironment (existsName existsIntroName existsRecName)

def carrierLevel : Level := .succ v
private def A := Expr.fvar 0 (srt carrierLevel)
private def B := Expr.fvar 1 (srt carrierLevel)
private def C := Expr.fvar 2 (srt carrierLevel)
private def F := Expr.fvar 3 (.forallE A B)
private def G := Expr.fvar 4 (.forallE B C)
private def x := Expr.fvar 5 A
private def z := Expr.fvar 6 C
private def eq (T a b : Expr) := ap3 (cnst eqName [carrierLevel]) T a b
private def and (p q : Expr) := ap2 (cnst andName) p q
private def bind (i : Nat) (T body : Expr) := Expr.lam T (body.abstract1 i)
private def all (i : Nat) (T body : Expr) := Expr.forallE T (body.abstract1 i)
private def y := Expr.fvar 7 B
private def left := eq B y (.app F x)
private def right := eq C z (.app G y)
private def predicate := bind 7 B (and left right)
private def premise := ap2 (cnst existsName [carrierLevel]) B predicate
private def conclusion := eq C z (.app G (.app F x))
private def h := Expr.fvar 8 premise
private def hy := Expr.fvar 9 (and left right)
private def y' := Expr.fvar 10 B
private def he := Expr.fvar 11 (eq B y y')
private def motiveEq := bind 10 B (bind 11 (eq B y y') (eq C z (.app G y')))
private def forwardAtWitness : Expr :=
  .app (.app (ap4 (cnst (eqName.str "rec") [.zero, carrierLevel])
    B y motiveEq (.proj andName 1 hy)) (.app F x)) (.proj andName 0 hy)
private def forwardBody : Expr :=
  .app (ap4 (cnst existsRecName [carrierLevel]) B predicate
    (bind 8 premise conclusion)
    (bind 7 B (bind 9 (and left right) forwardAtWitness))) h
private def backwardHyp := Expr.fvar 8 conclusion
private def fx := Expr.app F x
private def reflexive := ap2 (cnst eqReflName [carrierLevel]) B fx
private def backwardBody :=
  ap4 (cnst existsIntroName [carrierLevel]) B predicate fx
    (ap4 (cnst andIntroName) (eq B fx fx) conclusion reflexive backwardHyp)
private def close (constructor : Nat → Expr → Expr → Expr) (body : Expr) :=
  constructor 0 (srt carrierLevel) <| constructor 1 (srt carrierLevel) <|
  constructor 2 (srt carrierLevel) <| constructor 3 (.forallE A B) <|
  constructor 4 (.forallE B C) <| constructor 5 A <| constructor 6 C body

def forwardType := close all (all 8 premise conclusion)
def backwardType := close all (all 8 conclusion premise)
def forwardProof := close bind (bind 8 premise forwardBody)
def backwardProof := close bind (bind 8 conclusion backwardBody)
def forwardName := bn "graph_forward"
def backwardName := bn "graph_backward"
def declarations : Array Declaration := GraphEnvironment.declarations ++
  #[.thmDecl ⟨forwardName, [BasisDSL.vN], forwardType⟩ forwardProof,
    .thmDecl ⟨backwardName, [BasisDSL.vN], backwardType⟩ backwardProof]

def environment : Env :=
  ⟨[.thmInfo ⟨backwardName, [BasisDSL.vN], backwardType⟩,
    .thmInfo ⟨forwardName, [BasisDSL.vN], forwardType⟩] ++ GraphEnvironment.environment.consts,
    GraphEnvironment.environment.tables⟩

end GraphDeclarations

#audit_graph_module
