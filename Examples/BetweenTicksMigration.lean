import Applications.FRP.MigrationSafety

/-! Between-tick continuation, phase and rejection clients. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.BetweenTicksMigration
open FRPSpec.Migration

def tick (x : Bool) : List Command := [.accept x,.evaluate none,.sink true,.tickCommit]
def transfer (k : Kind) : List Command := [.request k,.prepare 128 true true,.ownershipCommit]
def schedule : List Command := tick true ++ transfer .redundant ++ transfer .delay ++
  tick false ++ tick true ++ transfer .redundant ++ tick true ++ transfer .delay ++ tick false

example : (execute (initial .delay) schedule).2.1 = [true,false,true,true,false] := rfl
example : (execute (initial .delay) schedule).2.2 = [false,true,false,true,true] :=
  (congrArg Prod.fst (completed_schedule .delay schedule rfl)).symm
example : (execute (initial .delay) schedule).1.active.logical = false := rfl
example : (execute (initial .redundant) (tick true ++ transfer .delay ++ tick false)).2.2 =
    [false,true] :=
  (congrArg Prod.fst (completed_schedule .redundant (tick true ++ transfer .delay ++ tick false) rfl)).symm
example (s : Session) (commands : List Command) :
    outstanding s ++ (Progress.Feedback.run FRPSpec.Indefinite.delay.machine.mealy
      (future s) (execute s commands).2.1).1 =
    (execute s commands).2.2 ++ outstanding (execute s commands).1 :=
  (execute_balance s commands).1

example : (execute (initial .delay) [.query,.accept true,.query,.evaluate none,
    .sink true,.query,.tickCommit,.query,.accept true,.evaluate none,.sink true,.tickCommit]).2.2 =
    [false,true] := rfl

/-- Each wait retains its accepted input and eventual unique publication. -/
example : (execute (initial .delay) [.accept true,.request .redundant,.accept false,
    .prepare 128 true true,.evaluate none,.sink false,.query,.cancel,.sink true,
    .sink true,.tickCommit,.accept false,.evaluate none,.sink true,.tickCommit]).2 =
      ([true,false],[false,true]) := rfl
example : (execute (initial .delay) [.accept true,.evaluate none,.sink true,
    .request .redundant,.prepare 128 true true,.cancel,.tickCommit]).1.active.logical = true := rfl

example (s : Session) : HEq (step s .cancel).session.flight s.flight :=
  (cancellation_preserves_work s).2
example (s : Session) : (step s (.sink false)).session = s := refusal_preserves s
example (s : Session) : stateSlots s ≤ 89 := state_slots_bound s
example (s : Session) : peakSlots s ≤ 137 := peak_slots_bound s
example (s : Session) (n : Nat) (a v : Bool)
    (h : (step s (.prepare n a v)).status = .prepared) :
    stateSlots (step s (.prepare n a v)).session + 2 ≤ n := admitted_preparation_fits s n a v h

example : (step (initial .delay) (.request .delay)).status = .sameBackend := rfl
example : (step (initial .delay) .unsupported).status = .unsupported := rfl
example : FRPSpec.MigrationPair.validate (false,false) = false ∧
    FRPSpec.MigrationPair.reverse (true,true) = none := by decide
example : (execute (initial .delay) (tick true ++ [.request .redundant,
    .prepare 128 false true] ++ tick false)).2.2 = [false,true] := rfl
example : (execute (initial .delay) (tick true ++ [.request .redundant,
    .prepare 128 true true,.cancel] ++ tick false)).1.active.kind = .delay := rfl
example : (step (execute (initial .delay) (transfer .redundant)).1
    (.evaluate (some .delay))).status = .wrongOwner := rfl
example : (step (execute (initial .delay) (tick true)).1 (.sink true)).business = none := rfl

example (commands : List Command) : Safe (execute (initial .delay) commands).1 :=
  execute_safe _ _ (initial_safe _)
example (old : Backend) (flight : Flight old) (last : Option Bool) (target : Kind) :
    let s : Session := ⟨old,flight,last,some target,none⟩
    let drained := (execute s (drain s)).1
    (execute drained [.prepare 128 true true,.ownershipCommit]).1.active =
      realize target (future s) := drain_then_migrate old flight last target

/-- A retained protocol pair directly supplies the existing infinite transport
contract, rebased to its current logical state rather than the original seed. -/
example (p : PairState) (input : Progress.Stream Bool) :
    ∀ n, Progress.Feedback.output ⟨FRPSpec.Indefinite.delay.machine.step,p.first⟩ input n =
      Progress.Feedback.output ⟨FRPSpec.MigrationPair.redundant.machine.step,(p.first,p.second)⟩ input n :=
  (FRPSpec.MigrationPair.infinite_suffix p.first (p.first,p.second)
    (Prod.ext rfl p.valid) input).2

end Examples.BetweenTicksMigration
