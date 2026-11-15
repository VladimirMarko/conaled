import Applications.Incremental.MappedAggregate
import SquareKit.Arithmetic

/-! Ordinary polynomial specifications use the same compiled repair path.
The tariff counts every scalar primitive once, including literals. -/
namespace Examples.MappedAggregate
open FirstOrderCompiler Incremental Incremental.MappedAggregate
open Incremental.VectorSum (Values Patch applyPatch)
open scoped BigOperators

private def input : Term Arithmetic.Prim [.base] .base := .var .here

def square : Scalar Int where
  Prim := Arithmetic.Prim
  meaning := Arithmetic.meaning
  charge _ := 1
  body := .prim .mul (.pair input input)

def quadratic : Scalar Int where
  Prim := Arithmetic.Prim
  meaning := Arithmetic.meaning
  charge _ := 1
  body := .prim .add (.pair (.prim .mul (.pair input input)) input)

def downstream : Scalar Int where
  Prim := Arithmetic.Prim
  meaning := Arithmetic.meaning
  charge _ := 1
  body := .prim .add (.pair (.prim .mul (.pair input input)) (.prim (.literal 1) .unit))

/-- Independent mathematical specifications, without compiler definitions. -/
def squares (v : Values Int n) : Int := ∑ i, v i * v i
def quadratics (v : Values Int n) : Int := ∑ i, (v i * v i + v i)
def report (x : Int) : Int := x * x + 1

@[simp] theorem square_eval (x : Int) : square.eval x = x * x := rfl
@[simp] theorem quadratic_eval (x : Int) : quadratic.eval x = x * x + x := rfl
@[simp] theorem downstream_eval (x : Int) : downstream.eval x = report x := rfl

@[simp] theorem square_spec (v : Values Int n) : specification square.eval v = squares v := rfl
@[simp] theorem quadratic_spec (v : Values Int n) : specification quadratic.eval v = quadratics v := rfl

theorem squares_workload (v : Values Int n) (ps : List (Patch Int n)) :
    (Cost.workload square downstream v ps).1.2.2 = report (squares (ps.foldl applyPatch v)) :=
  Cost.workload_output square downstream v ps

theorem quadratics_workload (v : Values Int n) (ps : List (Patch Int n)) :
    (Cost.workload quadratic downstream v ps).1.2.2 = report (quadratics (ps.foldl applyPatch v)) :=
  Cost.workload_output quadratic downstream v ps

theorem squares_after_patch (v : Values Int n) (p : Patch Int n) :
    (Cost.repair square (Cost.init square v).1 p).1.1.sum = squares (applyPatch v p) :=
  Cost.repair_after_init_output square v p

theorem quadratics_after_patch (v : Values Int n) (p : Patch Int n) :
    (Cost.repair quadratic (Cost.init quadratic v).1 p).1.1.sum = quadratics (applyPatch v p) :=
  Cost.repair_after_init_output quadratic v p

def initial : Values Int 3 := ![1, 2, 3]
def repeated : Patch Int 3 := [(1, 5), (1, -1)]
def later : Patch Int 3 := [(0, 0)]

theorem initial_outputs :
    (Cost.workload square downstream initial []).1.2.2 = 197 ∧
    (Cost.workload quadratic downstream initial []).1.2.2 = 401 := by
  rw [squares_workload, quadratics_workload]
  decide

theorem single_outputs :
    (Cost.workload square downstream initial [[(1, 5)]]).1.2.2 = 1226 ∧
    (Cost.workload quadratic downstream initial [[(1, 5)]]).1.2.2 = 1937 := by
  rw [squares_workload, quadratics_workload]
  decide

theorem repeated_outputs :
    (Cost.workload square downstream initial [repeated]).1.2.2 = 122 ∧
    (Cost.workload quadratic downstream initial [repeated]).1.2.2 = 197 := by
  rw [squares_workload, quadratics_workload]
  decide

theorem consecutive_outputs :
    (Cost.workload square downstream initial [[], repeated, later]).1.2.2 = 101 ∧
    (Cost.workload quadratic downstream initial [[], repeated, later]).1.2.2 = 145 := by
  rw [squares_workload, quadratics_workload]
  decide

/-- Repeated writes retain the last actual contribution. -/
theorem retained_after_repetition :
    (Cost.workload square downstream initial [repeated]).1.1.values 1 = 1 := by
  have h := Cost.workload_valid square downstream initial [repeated]
  exact congrFun h.1.1 1

theorem empty_patch_outputs :
    (Cost.workload square downstream initial [[]]).1.2.2 = 197 ∧
    (Cost.workload quadratic downstream initial [[]]).1.2.2 = 401 := by
  rw [squares_workload, quadratics_workload]
  decide

theorem zero_patch (p : Patch Int 0) : p = [] := by
  cases p with
  | nil => rfl
  | cons a _ => exact Fin.elim0 a.1

theorem zero_size (v : Values Int 0) :
    (Cost.workload square downstream v []).1.2.2 = 1 ∧
    (Cost.workload square downstream v []).2 = 8 := by
  rw [squares_workload, Cost.workload_cost]
  simp [squares, report, VectorSum.Cost.assignments, downstream, square, Scalar.cost,
    Resources.FoldCompiler.bodyCost, input]

theorem repeated_bills :
    (Cost.workload square downstream initial [repeated, later]).2 = 61 ∧
    (Cost.recompute square downstream initial [repeated, later]).2 = 55 := by
  rw [Cost.workload_cost, Cost.recompute_cost]
  decide

theorem quadratic_bills :
    (Cost.workload quadratic downstream initial [repeated, later]).2 = 67 ∧
    (Cost.recompute quadratic downstream initial [repeated, later]).2 = 64 := by
  rw [Cost.workload_cost, Cost.recompute_cost]
  decide

/-- A larger input with few assignments amortizes the retained setup. -/
def sparse : List (Patch Int 100) := [[(0, 7)], [(0, -2)], [(1, 4)]]

theorem sparse_bills (v : Values Int 100) :
    (Cost.workload square downstream v sparse).2 = 556 ∧
    (Cost.recompute square downstream v sparse).2 = 1429 := by
  rw [Cost.workload_cost, Cost.recompute_cost]
  decide

theorem sparse_repair_cheaper (v : Values Int 100) :
    (Cost.workload square downstream v sparse).2 ≤ (Cost.recompute square downstream v sparse).2 := by
  rw [Cost.repair_le_recompute_iff]
  decide

theorem setup_prevents_blanket_advantage (v : Values Int n) :
    (Cost.recompute square downstream v []).2 < (Cost.workload square downstream v []).2 := by
  rw [Cost.recompute_cost, Cost.workload_cost]
  simp [VectorSum.Cost.assignments]

theorem zero_empty_patch_bill (v : Values Int 0) :
    (Cost.workload square downstream v [[]]).2 = 18 ∧
    (Cost.recompute square downstream v [[]]).2 = 12 := by
  rw [Cost.workload_cost, Cost.recompute_cost]
  decide

/-- Naming this term does not insert a source-level let binding. -/
private def shifted : Term Arithmetic.Prim [.base] .base :=
  .prim .add (.pair input (.prim (.literal 2) .unit))

def shiftedSquare : Scalar Int where
  Prim := Arithmetic.Prim
  meaning := Arithmetic.meaning
  charge _ := 1
  body := .prim .mul (.pair shifted shifted)

def shiftedSquares (v : Values Int n) : Int := ∑ i, (v i + 2) * (v i + 2)

@[simp] theorem shiftedSquare_eval (x : Int) : shiftedSquare.eval x = (x + 2) * (x + 2) := rfl

@[simp] theorem shiftedSquare_spec (v : Values Int n) :
    specification shiftedSquare.eval v = shiftedSquares v := rfl

theorem shiftedSquares_after_patch (v : Values Int n) (p : Patch Int n) :
    (Cost.repair shiftedSquare (Cost.init shiftedSquare v).1 p).1.1.sum =
      shiftedSquares (applyPatch v p) :=
  Cost.repair_after_init_output shiftedSquare v p

theorem shiftedSquares_workload (v : Values Int n) (ps : List (Patch Int n)) :
    (Cost.workload shiftedSquare downstream v ps).1.2.2 =
      report (shiftedSquares (ps.foldl applyPatch v)) :=
  Cost.workload_output shiftedSquare downstream v ps

theorem shifted_repeated_outputs :
    (Cost.repair shiftedSquare (Cost.init shiftedSquare initial).1 repeated).1.1.sum = 35 ∧
    (Cost.workload shiftedSquare downstream initial [repeated]).1.2.2 = 1226 := by
  rw [shiftedSquares_after_patch, shiftedSquares_workload]
  decide

/-- Two literals and two additions execute before the multiplication. Reusing
`shifted` as a Lean name does not memoize its execution. -/
theorem shiftedSquare_exec_cost (x : Int) : (shiftedSquare.exec x).2 = 5 := by
  rw [Scalar.exec_cost]
  rfl

end Examples.MappedAggregate
