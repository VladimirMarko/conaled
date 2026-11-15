import Examples.DependentFunctionConversion
open SquareKit.Internal.DependentFunctions
open Examples.DependentFunctionConversion

private def verdict {P : Prop} : Except ConversionFailure (PLift P) → Option ConversionFailure
  | .ok _ => none
  | .error e => some e

private def check (label : String) (actual expected : Option ConversionFailure) : IO Unit :=
  unless actual = expected do throw (IO.userError s!"{label}: {repr actual}")

def main : IO Unit := do
  check "generated dependent beta" (verdict (generated.check (.neg (.neg (.var 0))) expected)) none
  check "wrong expected index" (verdict (generated.check .zero expected)) (some .leftIndex)
  check "changed right index" (verdict (generated.check (.neg (.neg (.var 0)))
    (.app parameter (.neg (.var 0))))) (some .rightIndex)
  check "same index different free function" (verdict (newest.check (.var 0) older))
    (some .notConvertible)
  check "eta of free parameter" (verdict
    ((Func.lam (.app ((Ren.weaken Γ).funcMap parameter) (.var 0))).check (.var 0) parameter)) none
  let left := negate.depSub (negate.depSub generated)
  let right := negate.depSub (negate.depSub expected)
  check "two nonidentity substitutions" (verdict (left.check
    (.neg (.neg (.neg (.neg (.var 0))))) right)) none
  check "dependent index repaired" (verdict (repairedTerm.val.check
    (.neg (.neg (.var 0))) generatedTerm.val)) none
  -- Unary negation remains literal syntax: no Boolean-model reflection.
  check "semantic double-negation is not source conversion"
    (verdict (generated.check (.neg (.neg (.var 0))) (.app parameter (.var 0))))
    (some .rightIndex)
  check "repair accepts changed free dependency"
    (verdict (dependentRepair.check (.neg (.neg (.var 1))) repairedExpected)) none
  check "repair rejects obsolete constant annotation"
    (verdict (dependentRepair.check (.neg (.neg .zero)) repairedExpected)) (some .leftIndex)
  check "weakening retains free variable identity"
    (verdict (((Ren.weaken Γ).depMap generated).check (.neg (.neg (.var 1)))
      ((Ren.weaken Γ).depMap expected))) none
  check "nested eta with intervening beta and two substitutions"
    (verdict (generatedFunction.check (.var 0)
      (negate.funcSub (negate.funcSub parameter)))) none
  IO.println "dependent conversion: twelve public-service fixtures passed"
