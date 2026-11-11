import SquareKit.InterpretationDiagnostics
import TaskSetup462

import TaskSetup462
namespace AssistedH1
open Tasks462.H1 SquareKit.DiagonalConstruction
theorem extension : changeCodes.Extension source := by
  intro b _
  rfl
end AssistedH1

namespace Requested
def selectedSource := Tasks462.H1.source
def route := Tasks462.H1.changeCodes
def requirement_0 : Prop := SquareKit.DiagonalConstruction.Map.Extension route selectedSource
#transport_requirement Requested.requirement_0
def requestPresent : Unit := ()
#check selectedSource.code
#check selectedSource.witness
#check route.code selectedSource.code
#check route.value selectedSource.witness
#transport_audit Requested.requestPresent

end Requested
