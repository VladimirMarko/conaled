import Examples.RecursiveCompilation
import Examples.GuardedStreamCompiler
import SquareKit.SelectedFeedback

/-! Practical consumers retain their native existence and observation contracts.
The investigation and independently frozen contracts are recorded in
`docs/research/construction-transport-contracts.md`. -/
namespace Examples.ConstructionTransport
namespace Fold
open FirstOrderCompiler
open Examples.RecursiveCompilation

theorem native (xs : List Int) :
    ListFoldCompiler.compile counted squares xs =
      ((xs.map (fun x => x*x)).sum, 1 + 3 * xs.length) := squares_counted xs

def scale (k : Nat) : Nat →+ Nat where
  toFun n := k*n
  map_zero' := Nat.mul_zero k
  map_add' := Nat.mul_add k

/-- Includes the visit charge, not just the scalar primitive charges. -/
def transition (x acc : Int) : Resources.Measured Int Nat :=
  let r := FirstOrderCompiler.compile counted.scalar squareBody (((),acc),x)
  (r.1, 1+r.2)

theorem composed_transitions (xs : List Int) (s : Int) :
    Resources.reweight (scale 3) (Resources.reweight (scale 2)
      (Resources.run transition xs s)) =
    Resources.run (fun x s => Resources.reweight ((scale 3).comp (scale 2))
      (transition x s)) xs s := by
  change Resources.reweight ((scale 3).comp (scale 2))
    (Resources.run transition xs s) = _
  exact Resources.reweight_run _ _ _ _

/-- Push a resource interpretation through the compiled seed and every executed
transition. This connects reweighting to code execution, not just its final pair. -/
theorem compiled_reweighted_run (h : Nat →+ Nat) (xs : List Int) :
    Resources.reweight h (ListFoldCompiler.compile counted squares xs) =
    Resources.bind (Resources.reweight h
      (FirstOrderCompiler.compile counted.scalar seed ()))
      (fun s => Resources.run (fun x acc => Resources.reweight h (transition x acc)) xs s) := by
  change Resources.reweight h (Resources.bind
    (FirstOrderCompiler.compile counted.scalar seed ())
    (fun s => Resources.run transition xs s)) = _
  rw [Resources.reweight_bind]
  congr 1
  funext s
  exact Resources.reweight_run h transition xs s

theorem recovery (xs : List Int) :
    Resources.reweight (AddMonoidHom.id Nat) (ListFoldCompiler.compile counted squares xs) =
      ((xs.map (fun x => x*x)).sum, 1 + 3 * xs.length) := native xs

theorem visits (xs : List Int) : ListFoldCompiler.Executes meaning squareBody xs 0
    (ListFoldCompiler.iterate meaning squareBody 0 xs) xs.length :=
  ListFoldCompiler.iterate_executes _ _ _ _

/-- The compiled seed is charged too; this is the full result observation. -/
theorem composed_result (xs : List Int) :
    Resources.reweight (scale 3) (Resources.reweight (scale 2)
      (ListFoldCompiler.compile counted squares xs)) =
    ((xs.map (fun x => x*x)).sum, 6*(1+3*xs.length)) := by
  rw [native]
  apply Prod.ext
  · rfl
  · change 3*(2*(1+3*xs.length)) = 6*(1+3*xs.length)
    omega

example : Resources.reweight (scale 3) (Resources.reweight (scale 2)
    (ListFoldCompiler.compile counted squares [2,-1,3])) = (14,60) := composed_result _
example : scale 2 1 ≠ 1 ∧ scale 3 1 ≠ 1 := by decide

/-- Existing fusion observes values; the unchanged costs separate that contract. -/
example : (ListFoldCompiler.compile counted (.post total twice) [1,2]).1 =
    (ListFoldCompiler.compile counted (.fold seed twiceAdd) [1,2]).1 :=
  total_fusion counted counted countedSound countedSound _
example : (ListFoldCompiler.compile counted (.post total twice) [1,2]).2 ≠
    (ListFoldCompiler.compile counted (.fold seed twiceAdd) [1,2]).2 := by decide
end Fold

namespace Feedback
open SquareKit GuardedStreams GuardedStreamCompiler
open GuardedStreamCompiler.Examples

theorem native : compiledTriangular = triangular := compiledTriangular_eq

def body : Stream Nat → Stream Nat := denote
  (model (fun _ => 0) compiledSums) triangularBody

theorem body_guarded : Guarded body := denote_guarded _ _ rfl

def selected : FunctionFeedback.Witness
    (fun p : Unit × Stream Nat => (p.2, body p.2)) :=
  FunctionFeedback.guardedWitness (fun _ => body) (fun _ s => s)
    (fun _ => body_guarded) 0

theorem selected_native : FunctionFeedback.trace _ selected () = triangular := by
  change solve body 0 = triangular
  have fixed : compiledTriangular = body compiledTriangular :=
    solution_fixed _ _ _ triangularBody rfl 0
  exact (unique body_guarded 0 compiledTriangular fixed).symm.trans native

theorem every_selected (w : FunctionFeedback.Witness
    (fun p : Unit × Stream Nat => (p.2, body p.2))) :
    FunctionFeedback.trace _ w () = triangular := by
  rw [FunctionFeedback.guarded_trace_unique (fun _ => body) (fun _ s => s)
    (fun _ => body_guarded) 0 w]
  exact selected_native

/-- The selected state is exactly the existing compiled result. -/
theorem selected_compiled : (selected ()).2.val = compiledTriangular := by
  change solve body 0 = compiledTriangular
  exact selected_native.trans native.symm

def modFour : Nat →+ ZMod 4 := (Nat.castRingHom (ZMod 4)).toAddMonoidHom
def modTwo : ZMod 4 →+ ZMod 2 := (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)).toAddMonoidHom

theorem quotient_chain :
    modTwo ∘ modFour ∘ triangular =
      run (modTwo ∘ modFour ∘ (fun n => n+1)) (fun _ => 0) parameterBody rfl := by
  rw [← parameter_triangular]
  have first := run_interpretation modFour (by rfl) (fun n => n+1) (fun _ => 0)
    (modFour ∘ (fun n => n+1)) (fun _ => 0) rfl
    (by funext n; exact map_zero modFour) parameterBody rfl
  have second := run_interpretation modTwo (by rfl) (modFour ∘ (fun n => n+1))
    (fun _ => 0) (modTwo ∘ modFour ∘ (fun n => n+1)) (fun _ => 0) rfl
    (by funext n; exact map_zero modTwo) parameterBody rfl
  exact (congrArg (fun s => modTwo ∘ s) first).trans second

theorem chain_parity (n : Nat) : modTwo (modFour n) = GuardedStreams.Examples.parity n := by
  change (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)) (n : ZMod 4) = (n : ZMod 2)
  exact map_natCast _ n

theorem selected_quotient :
    modTwo ∘ modFour ∘ FunctionFeedback.trace _ selected () =
      run (modTwo ∘ modFour ∘ (fun n => n+1)) (fun _ => 0) parameterBody rfl := by
  rw [selected_native]
  exact quotient_chain

/-- The composed interpretation agrees with the existing direct parity route. -/
theorem quotient_direct :
    run (modTwo ∘ modFour ∘ (fun n => n+1)) (fun _ => 0) parameterBody rfl =
      run (GuardedStreams.Examples.parity ∘ (fun n => n+1))
        (fun _ => 0) parameterBody rfl := by
  congr 1
  funext n
  exact chain_parity (n+1)

example : modFour 4 = 0 ∧ modTwo 2 = 0 := by decide
example : modTwo (modFour (triangular 4)) = 0 := by decide
example : ¬ Function.Injective (modTwo ∘ modFour) := by
  intro h
  have bad := h (show (modTwo ∘ modFour) 0 = (modTwo ∘ modFour) 2 by decide)
  omega
end Feedback
end Examples.ConstructionTransport
