import Applications.Resources.FoldCompiler
import Applications.Progress.Streams
import SquareKit.Arithmetic
import Mathlib.Algebra.Ring.Int.Defs

namespace Examples.RecursiveCompilation
open FirstOrderCompiler
open ListFoldCompiler

abbrev meaning {a b : Ty} : Arithmetic.Prim a b → Val Int a → Val Int b := Arithmetic.meaning (R := Int)
def charge {a b : Ty} (_ : Arithmetic.Prim a b) : Nat := 1
abbrev ordinary := functionTarget meaning
abbrev counted := Resources.FoldCompiler.target meaning charge
abbrev ordinarySound := functionSound meaning
abbrev countedSound := Resources.FoldCompiler.sound meaning charge

def seed : Term Arithmetic.Prim [] .base := .prim (.literal 0) .unit
def addBody : Term Arithmetic.Prim [.base,.base] .base :=
  .prim .add (.pair (.var (.there .here)) (.var .here))
/-- The square is bound once, then reused as a value by the accumulator body. -/
def squareBody : Term Arithmetic.Prim [.base,.base] .base :=
  .letE (.prim .mul (.pair (.var .here) (.var .here)))
    (.prim .add (.pair (.var (.there (.there .here))) (.var .here)))
def total : Program Arithmetic.Prim .base .base := .fold seed addBody
def squares : Program Arithmetic.Prim .base .base := .fold seed squareBody

def twice : Term Arithmetic.Prim [.base] .base := .prim .add (.pair (.var .here) (.var .here))
def twiceAdd : Term Arithmetic.Prim [.base,.base] .base :=
  .prim .add (.pair (.var (.there .here)) (.prim .add (.pair (.var .here) (.var .here))))
def twiceSquare : Term Arithmetic.Prim [.base,.base] .base :=
  .letE (.prim .mul (.pair (.var .here) (.var .here)))
    (.prim .add (.pair (.var (.there (.there .here)))
      (.prim .add (.pair (.var .here) (.var .here)))))

theorem fold_add_map (f : Int → Int) (xs : List Int) (s : Int) :
    xs.foldl (fun acc x => acc + f x) s = s + (xs.map f).sum := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih => simp [ih,Int.add_assoc]

theorem total_meaning (xs : List Int) : ListFoldCompiler.eval meaning total xs = xs.sum := by
  simp only [ListFoldCompiler.eval,total,iterate_eq_foldl]
  change xs.foldl (fun acc x => acc+x) 0 = xs.sum
  simpa using fold_add_map id xs 0

theorem squares_meaning (xs : List Int) :
    ListFoldCompiler.eval meaning squares xs = (xs.map (fun x => x*x)).sum := by
  simp only [ListFoldCompiler.eval,squares,iterate_eq_foldl]
  change xs.foldl (fun acc x => acc+x*x) 0 = _
  simpa using fold_add_map (fun x => x*x) xs 0

/-- Source evaluation visits exactly the input cells, independently of compilation. -/
example (xs : List Int) : Executes meaning squareBody xs 0
    (iterate meaning squareBody 0 xs) xs.length := iterate_executes _ _ _ _
/-- The compiled fold is one operation applied to compiled seed/body, for every target. -/
example (K : ListFoldCompiler.Target Arithmetic.Prim) :
    ListFoldCompiler.compile K squares = K.fold (FirstOrderCompiler.compile K.scalar seed)
      (FirstOrderCompiler.compile K.scalar squareBody) := compile_fold K _ _

theorem total_compiled (xs : List Int) : ListFoldCompiler.compile ordinary total xs = xs.sum :=
  (ListFoldCompiler.compile_sound ordinary ordinarySound total xs).trans (total_meaning xs)
theorem squares_compiled (xs : List Int) :
    ListFoldCompiler.compile ordinary squares xs = (xs.map (fun x => x*x)).sum :=
  (ListFoldCompiler.compile_sound ordinary ordinarySound squares xs).trans (squares_meaning xs)

theorem total_counted (xs : List Int) :
    ListFoldCompiler.compile counted total xs = (xs.sum,1+2*xs.length) := by
  apply Prod.ext
  · exact ((Resources.FoldCompiler.erasure meaning charge total).commutes xs).trans (total_meaning xs)
  · simpa [Resources.FoldCompiler.programCost,Resources.FoldCompiler.bodyCost,seed,addBody,total,charge,Nat.mul_comm] using
      Resources.FoldCompiler.compile_cost meaning charge total xs

theorem squares_counted (xs : List Int) :
    ListFoldCompiler.compile counted squares xs = ((xs.map (fun x => x*x)).sum,1+3*xs.length) := by
  apply Prod.ext
  · exact ((Resources.FoldCompiler.erasure meaning charge squares).commutes xs).trans (squares_meaning xs)
  · simpa [Resources.FoldCompiler.programCost,Resources.FoldCompiler.bodyCost,seed,squareBody,squares,charge,Nat.mul_comm] using
      Resources.FoldCompiler.compile_cost meaning charge squares xs

/-- Both clients consume the same compiled fusion theorem, across both targets.
The observation on counted code is value erasure; cost equality is not claimed. -/
theorem total_fusion (K L : ListFoldCompiler.Target Arithmetic.Prim)
    (SK : ListFoldCompiler.Sound Int K meaning) (SL : ListFoldCompiler.Sound Int L meaning)
    (xs : List Int) :
    SK.denote (ListFoldCompiler.compile K (.post total twice)) xs =
      SL.denote (ListFoldCompiler.compile L (.fold seed twiceAdd)) xs := by
  apply compiled_fusion meaning K L SK SL seed addBody twice seed twiceAdd
    (fun _ => True) True.intro (fun _ _ _ => True.intro)
  · rfl
  · intro s x _
    change (s+x)+(s+x) = (s+s)+(x+x)
    ac_rfl

theorem squares_fusion (K L : ListFoldCompiler.Target Arithmetic.Prim)
    (SK : ListFoldCompiler.Sound Int K meaning) (SL : ListFoldCompiler.Sound Int L meaning)
    (xs : List Int) :
    SK.denote (ListFoldCompiler.compile K (.post squares twice)) xs =
      SL.denote (ListFoldCompiler.compile L (.fold seed twiceSquare)) xs := by
  apply compiled_fusion meaning K L SK SL seed squareBody twice seed twiceSquare
    (fun _ => True) True.intro (fun _ _ _ => True.intro)
  · rfl
  · intro s x _
    change (s+x*x)+(s+x*x) = (s+s)+(x*x+x*x)
    ac_rfl

example (xs : List Int) : (ListFoldCompiler.compile counted (.post total twice) xs).1 =
    ListFoldCompiler.compile ordinary (.fold seed twiceAdd) xs :=
  total_fusion counted ordinary countedSound ordinarySound xs
example (xs : List Int) : ListFoldCompiler.compile ordinary (.post squares twice) xs =
    (ListFoldCompiler.compile counted (.fold seed twiceSquare) xs).1 :=
  squares_fusion ordinary counted ordinarySound countedSound xs

example : ListFoldCompiler.compile counted total [] = (0,1) := total_counted []
example : ListFoldCompiler.compile counted squares [] = (0,1) := squares_counted []
example : ListFoldCompiler.compile counted total [2,-1,3] = (4,7) := total_counted _
example : ListFoldCompiler.compile counted squares [2,-1,3] = (14,10) := squares_counted _
example : (ListFoldCompiler.compile counted (.post total twice) [1,2]).2 = 6 ∧
    (ListFoldCompiler.compile counted (.fold seed twiceAdd) [1,2]).2 = 7 := by decide

/-- Shared resource reweighting operates on the actual fold transitions. -/
example (xs : List Int) (s : Int) (h : Nat →+ Nat) :
    Resources.reweight h (Resources.run
      (fun x acc => let r := FirstOrderCompiler.compile counted.scalar squareBody (((),acc),x)
        ; (r.1,1+r.2)) xs s) =
    Resources.run (fun x acc => Resources.reweight h
      (let r := FirstOrderCompiler.compile counted.scalar squareBody (((),acc),x)
        ; (r.1,1+r.2))) xs s := Resources.reweight_run h _ xs s

/-- Same scalar interpretation, but deliberately missing the fold-preservation law. -/
def badTarget : ListFoldCompiler.Target Arithmetic.Prim :=
  { ordinary with fold := fun seed _ _ => seed () }
example : FirstOrderCompiler.Sound Int badTarget.scalar meaning := functionScalarSound meaning
example : ListFoldCompiler.compile badTarget total [1] = 0 ∧
    ListFoldCompiler.compile ordinary total [1] = 1 := by decide

theorem bad_fold_law : ¬ ∃ S : ListFoldCompiler.Sound Int badTarget meaning,
    ∀ {a b} (f : badTarget.Hom a b) xs, S.denote f xs = f xs := by
  rintro ⟨S,denotes⟩
  have h := ListFoldCompiler.compile_sound badTarget S total [1]
  rw [denotes] at h
  change (0 : Int) = 1 at h
  omega

/-- Doubling only the accumulator does not commute with adding an unchanged input. -/
example : ¬ (∀ s x : Int, (s+x)+(s+x) = (s+s)+x) := by
  intro h
  have := h 0 1
  omega
example : (2 : Int) * ListFoldCompiler.compile ordinary total [1] ≠
    ListFoldCompiler.compile ordinary total [1] := by decide

/-- General silent recursion has no finite evaluation and is not a fold body
constructor. This uses the existing operational model, not an opaque primitive. -/
example : ¬ Progress.Terminates (fun n : Nat => .inr (n+1) : Progress.Machine Nat Nat) 0 := by
  rintro ⟨a,k,h⟩
  exact Progress.silent_no_evaluation _ h

#eval ListFoldCompiler.compile counted total [2,-1,3]
#eval ListFoldCompiler.compile counted squares [2,-1,3]
end Examples.RecursiveCompilation
