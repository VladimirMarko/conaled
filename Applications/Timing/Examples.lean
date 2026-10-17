import Applications.Timing.Adders

/-! # Exact, executable timing calculations and proof-dependency checks -/

namespace Applications.Timing.Examples

open Adders

/-- `some` displays a finite bound; `none` means the corresponding infinity. -/
def bounds (I : Interval) : WithTop (OrderDual Time) × WithTop Time :=
  (MinTropical.untrop I.1, MinTropical.untrop I.2)

def halfAdderRows :=
  [ [ bounds (halfAdder.digital.matrix sumPort sumPort),
      bounds (halfAdder.digital.matrix sumPort carryPort) ],
    [ bounds (halfAdder.digital.matrix carryPort sumPort),
      bounds (halfAdder.digital.matrix carryPort carryPort) ] ]

def fullAdderRows :=
  [ [ bounds (compiledFullAdder.digital.matrix sumPort inputA),
      bounds (compiledFullAdder.digital.matrix sumPort inputB),
      bounds (compiledFullAdder.digital.matrix sumPort inputC) ],
    [ bounds (compiledFullAdder.digital.matrix carryPort inputA),
      bounds (compiledFullAdder.digital.matrix carryPort inputB),
      bounds (compiledFullAdder.digital.matrix carryPort inputC) ] ]

def carryWaveform : List (Time × Bool) :=
  ([0, 1 / 2, 7 / 10, 9 / 10, 1] : List Time).map
    (fun t => (t, (compiledFullAdder.digital.analog hazardInput).2 t))

/-- Two inversions delayed by one and two units preserve the input value on
exactly the input bounds shifted by three. Inputs need only be stable there. -/
theorem delayed_double_not {s : Signal} {lo hi : Time} {v : Bool}
    (h : Stable .base s (fun _ => Interval.finite lo hi) v) :
    Stable .base
      ((Digital.compose (Digital.unary 2 Bool.not) (Digital.unary 1 Bool.not)).analog s)
      (fun _ => Interval.finite (3 + lo) (3 + hi)) v := by
  have hc := (Digital.compose (Digital.unary 2 Bool.not)
    (Digital.unary 1 Bool.not)).correct h
  norm_num [Digital.compose, Digital.unary, Interval.point, Interval.finite_mul,
    ← add_assoc] at hc ⊢
  exact hc

/-- The composed contract has admissible inputs and a nonempty output window. -/
theorem delayed_double_not_constant :
    Stable .base
      ((Digital.compose (Digital.unary 2 Bool.not) (Digital.unary 1 Bool.not)).analog
        (fun _ => true))
      (fun _ => Interval.finite 3 4) true := by
  have h : Stable .base (fun _ => true) (fun _ => Interval.finite 0 1) true :=
    fun _ _ => rfl
  convert delayed_double_not h using 1 <;> norm_num

#eval halfAdderRows
#eval fullAdderRows
#eval carryWaveform

#print axioms Interval.empty_product_counterexample
#print axioms Digital.square_compose
#print axioms Digital.timingMatrixSquare
#print axioms Applications.Circuits.Circuit.compile_matrix_stable
#print axioms compiled_fullAdder
#print axioms fullAdder_addition
#print axioms fullAdder_matrix
#print axioms hazard_at_seven_tenths
#print axioms carry_path_nonempty_iff

end Applications.Timing.Examples
