import Examples.WeakCanonicity

open SquareKit.WeakHigherOrder SquareKit.WeakMachine Examples.WeakCanonicity

def check (label : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError label)

def opaqueObservation : OpaqueControl.Result .ground → String
  | .terminal (.lit n) => s!"numeral {n}"
  | .terminal _ => "other terminal"
  | .stuck _ => "stuck"
  | .timeout _ => "timeout"

def main : IO Unit := do
  check "value at zero fuel" (Examples.WeakMachine.numeral (execute 0 (.lit 7)) == some 7)
  check "two steps insufficient" (Examples.WeakMachine.numeral (execute 2 twice) == none)
  for fuel in [3, 4, 20] do
    check "duplicated argument returns seven" (Examples.WeakMachine.numeral (execute fuel twice) == some 7)
  check "unforced omega body" (Examples.WeakMachine.numeral (execute 1 ignoredOmega) == some 0)
  check "demanded omega" (Examples.WeakMachine.numeral (execute 20 Examples.WeakMachine.discardLoop) == none)
  check "opaque primitive stuck" (opaqueObservation (OpaqueControl.execute 20 .kappa) == "stuck")
  check "demanded opaque argument stuck" (opaqueObservation (OpaqueControl.execute 20 OpaqueControl.demanded) == "stuck")
  check "ignored opaque function insufficient fuel" (opaqueObservation (OpaqueControl.execute 0 OpaqueControl.ignored) == "timeout")
  check "ignored opaque function returns" (opaqueObservation (OpaqueControl.execute 1 OpaqueControl.ignored) == "numeral 0")
  IO.println "canonicity controls passed: returning, timeout, unforced bodies, and demanded opaque stuckness"
