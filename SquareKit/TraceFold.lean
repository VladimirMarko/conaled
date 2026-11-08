import SquareKit.ListFusion

/-! Identify a native trace-producing recursion with a finite left fold.
This supplies a proof adapter, not a replacement runtime. -/
namespace SquareKit.TraceFold
universe u v w
variable {I : Type u} {S : Type v} {O : Type w}
def accumulate (step : S → I → S × O) (a : S × List O) (i : I) : S × List O :=
  let next := step a.1 i
  (next.1,a.2 ++ [next.2])

theorem identifies (step : S → I → S × O) (run : S → List I → S × List O)
    (nil : ∀ s, run s [] = (s,[]))
    (cons : ∀ s i is, run s (i::is) =
      let next := step s i
      let rest := run next.1 is
      (rest.1,next.2::rest.2)) (is : List I) (s : S) (outputs : List O) :
    is.foldl (accumulate step) (s,outputs) =
      ((run s is).1,outputs ++ (run s is).2) := by
  induction is generalizing s outputs with
  | nil => simp [nil]
  | cons i is ih =>
    simp only [List.foldl_cons, accumulate, ih, cons]
    simp [List.append_assoc]

theorem identifies_empty (step : S → I → S × O) (run : S → List I → S × List O)
    (nil : ∀ s, run s [] = (s,[]))
    (cons : ∀ s i is, run s (i::is) =
      let next := step s i
      let rest := run next.1 is
      (rest.1,next.2::rest.2)) (is : List I) (s : S) :
    is.foldl (accumulate step) (s,[]) = run s is := by
  simpa using identifies step run nil cons is s []
end SquareKit.TraceFold
