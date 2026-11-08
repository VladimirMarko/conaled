import Examples.MeasuredFRPTrace
import Examples.MeasuredNumericalMotion

private def check (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError name)

def main : IO Unit := do
  let s := Examples.MeasuredFRPTrace.initialState
  let a := Examples.MeasuredFRPTrace.accepted
  let r := Examples.MeasuredFRPTrace.rejected
  let later := Examples.MeasuredFRPTrace.later
  let frp := FRPSpec.Frontier.Trace.Measured.run [a,r,later] s
  check "FRP continues after rejection" (decide (frp =
    (Examples.MeasuredFRPTrace.expected,(3,(2,1)))))
  check "FRP empty execution" (decide (FRPSpec.Frontier.Trace.Measured.run [] s = (s,0)))
  check "FRP accepted stutter is labelled accepted" (decide
    (FRPSpec.Frontier.Trace.Measured.step ⟨2,[]⟩ s = (s,Resources.acceptedAttempt)))
  check "FRP tariffs share one recorded execution" (decide
    (Resources.attemptTariff frp.2 = 3 ∧ Resources.branchTariff frp.2 = 11))
  for m in [a,r,later] do
    for n in [a,r,later] do
      let observed := FRPSpec.Frontier.Trace.Measured.run [m,n] s
      check "FRP native erasure across branches" (decide
        (observed.1 = ([m,n].foldl FRPSpec.Frontier.Trace.process s)))
      check "FRP event conservation" (decide
        (observed.2.1 = 2 ∧ observed.2.2.1+observed.2.2.2 = 2))
  let q := Examples.NumericalMotion.initial
  let move := Examples.NumericalMotion.moveTick
  let turn := Examples.NumericalMotion.turnTick
  let bad := Examples.MeasuredNumericalMotion.badTick
  let measured := Orbifold.DiskTransport.Numerical.Measured.run
  let native := Orbifold.DiskTransport.Numerical.run
  check "numerical empty execution" (decide (measured [] q = (some ⟨q,[],0⟩,0)))
  let word := Examples.NumericalMotion.word
  let success := measured word q
  check "numerical exact final packet, samples and elapsed" (decide (success.1 = native word q))
  check "numerical successful word branches" (decide (success.2 = (3,(3,0))))
  let failed := measured [move,bad,turn] q
  check "numerical whole-run failure retains spent work" (decide (failed = (none,(2,(1,1)))))
  check "numerical failure ignores long suffix" (decide
    (measured (move::bad::List.replicate 10000 turn) q = failed))
  check "numerical equal failures retain different counts" (decide
    ((measured [bad] q).1 = failed.1 ∧ (measured [bad] q).2 ≠ failed.2))
  check "numerical tariffs share one recorded execution" (decide
    (Resources.attemptTariff failed.2 = 2 ∧ Resources.branchTariff failed.2 = 8))
  for c in [move,turn,bad,Examples.NumericalMotion.zeroTick] do
    for d in [move,turn,bad,Examples.NumericalMotion.zeroTick] do
      let observed := measured [c,d] q
      check "numerical native erasure across branches" (decide (observed.1 = native [c,d] q))
      check "numerical first-failure bounds" (decide
        (observed.2.1 ≤ 2 ∧ observed.2.2.2 ≤ 1 ∧ observed.2.1 = observed.2.2.1+observed.2.2.2))
  IO.println "Measured FRP/numerical execution runtime checks passed"
