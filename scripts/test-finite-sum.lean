import Examples.FiniteSumReactive

/-! Executable checks use the actual circuit evaluator and admission path.
The oracle is the independently specified plain Lean transition. -/
open FRPSpec.FiniteSum Examples.FiniteSumReactive Progress.Feedback

def ensure (b : Bool) (message : String) : IO Unit :=
  unless b do throw (IO.userError message)

def words : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => (words n).map (false :: ·) ++ (words n).map (true :: ·)

def delayedNot : Bool → List Bool → List Bool
  | _, [] => []
  | previous, x::xs => previous :: delayedNot (!x) xs

def main : IO Unit := do
  let states : List NativeState := [.inl false,.inl true,.inr (false,false),
    .inr (false,true),.inr (true,false),.inr (true,true)]
  let mut admitted := 0
  for tag in [false,true] do
    for l in [false,true] do
      for u in [false,true] do
        for v in [false,true] do
          let raw := (tag,(l,(u,v)))
          -- This policy is the frozen plain representation oracle.
          let expected := if tag then l == false else (u == false && v == false)
          ensure ((validator S).execute raw == expected) "validator differs from independent policy"
          ensure ((checkedAdmit S raw).isSome == expected) "decoder accepted malformed bits"
          for x in [false,true] do
            ensure ((source.tick x raw).isSome == expected) "checked tick bypassed state admission"
          ensure ((sumInputSource.tick raw ()).isSome == expected) "checked tick bypassed input admission"
          if expected then admitted := admitted + 1
  ensure (admitted == 6) "expected six canonical states among sixteen raw representations"
  let trials := (List.range 6).flatMap words
  for st in states do
    for xs in trials do
      let actual := run source.program.machine.mealy (encode (a := S) st) xs
      let expected := run reference.mealy st xs
      ensure (actual.1 == expected.1) "lowered output order differs from oracle"
      ensure (actual.2 == encode (a := S) expected.2) "lowered final state differs from oracle"
  for xs in trials do
    let actual := run pipeline.machine.mealy pipeline.initial xs
    let expected := delayedNot false (run reference.mealy reference.initial xs).1
    ensure (actual.1 == expected) "compiled first-order region/delay changed output order"
  ensure ((source.tick false (true,(true,(true,false)))).isNone) "invalid inactive payload admitted"
  ensure ((checkedAdmit (.sum S .bool) (false,((false,(true,(true,false))),false))).isNone)
    "malformed nested active payload admitted"
  ensure ((caseCircuit leftArm rightArm).work == 55) "eager branch/mux work changed"
  IO.println s!"PASS: 16 raw encodings; 6 states x {trials.length} traces; {trials.length} downstream traces"
