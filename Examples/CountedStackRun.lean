import Examples.CountedStack

/-! Executable controls with expected values fixed independently of the executor. -/
namespace Examples.CountedStackRun
open FirstOrderCompiler StackMachine Examples.CountedStack

def check (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError ("counted stack control failed: " ++ name))

def controls : IO Unit := do
  let add : Program Arithmetic.Prim (.prod .base .base) [.base] .base [.base] :=
    .cons (.primitive .add) .nil
  let x := (((3 : ℚ),4),((99 : ℚ),()))
  check "primitive value, nonempty tail, unit tariff"
    (runMeasured Arithmetic.meaning add x == ((7,(99,())),1))
  check "empty program"
    (runMeasured Arithmetic.meaning (.nil : Program Arithmetic.Prim (.prod .base .base) [.base] (.prod .base .base) [.base]) x == (x,0))
  check "padding preserves full state, adds four"
    (runMeasured Arithmetic.meaning (add.append padding) x == ((7,(99,())),5))
  check "value equality does not preserve exact cost"
    ((runMeasured Arithmetic.meaning add x).2 !=
      (runMeasured Arithmetic.meaning (add.append padding) x).2)
  check "linear composition order and tariff"
    (runMeasured (MatrixCompiler.meaning ℕ) (linearThenTriple.code [.base])
      (((),(3,4)),(99,())) == ((54,(99,())),15))
  check "arithmetic composition and tariff"
    (runMeasured Arithmetic.meaning (sharedThenNegate.code [.base])
      (((),((3 : ℚ),2)),((99 : ℚ),())) == ((-39,(99,())),41))
  check "arithmetic padded changed-client control"
    (runMeasured Arithmetic.meaning ((sharedThenNegate.code [.base]).append padding)
      (((),((3 : ℚ),2)),((99 : ℚ),())) == ((-39,(99,())),45))
  IO.println "counted stack controls passed"

#eval controls
end Examples.CountedStackRun
