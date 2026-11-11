import SquareKit.InterpretationDiagnostics
import SquareKit.DiagonalCoverage
import Examples.RecursiveCompilation
import SquareKit.InterpretationAssistance

/-! Common supplied data for the prospective #462 comparison.
Required certificates and final applications are author obligations. -/
namespace Tasks462
namespace H1
open SquareKit.DiagonalConstruction

def sourceEval (c _ : Bool) : Bool := c
def sourceStep (_ : Bool) : Bool := false
def targetEval (c _ : Option Bool) : Bool := c.getD true
def targetStep (_ : Bool) : Bool := false

def source : Selected sourceEval sourceStep where
  code := false
  represents _ := rfl

def changeCodes : Map sourceEval sourceStep targetEval targetStep where
  code := some
  value := id
  evaluation _ _ := rfl
  step _ := rfl

end H1
namespace H2
open FirstOrderCompiler Examples.RecursiveCompilation

def productWeight (n : Nat) : Nat × Nat := (n, 2*n)
def finalWeight (p : Nat × Nat) : Nat := p.1 + 3*p.2

def compiledSeed : Resources.Measured Int Nat :=
  FirstOrderCompiler.compile counted.scalar seed ()

def transition (x acc : Int) : Resources.Measured Int Nat :=
  let r := FirstOrderCompiler.compile counted.scalar addBody (((),acc),x)
  (r.1,1+r.2)

def shifted (n : Nat) : Nat := n+1

end H2
end Tasks462

#transport_audit Tasks462.H1.source
