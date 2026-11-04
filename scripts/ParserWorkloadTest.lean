import Examples.ParserWorkload

open LanguageWitnesses ParserWorkload RetainedSnapshot ParserWorkloadExamples

def check (name : String) (ok : Bool) : IO Unit :=
  unless ok do throw (IO.userError name)

def observe : Option (Decision Payload) → Option (List Bool)
  | some (.yes x) => some x.1
  | _ => none

def main : IO Unit := do
  check "repeated metrics" (metrics source repeated ==
    [(5180,3380,202), (1361,808,822), (2326,1307,124), (868,436,450)])
  check "short setup loss" (metrics source short ==
    [(173,110,143), (1226,789,822), (144,81,114), (733,417,450)])
  check "already simple overhead" (metrics (.base [true,false]) repeated ==
    [(380,180,18), (225,72,62), (846,483,36), (324,132,122)])
  check "heavy payload" (metrics heavy repeated ==
    [(52220,34740,1966), (17825,11784,11994), (49366,32667,1888), (17332,11412,11622)])
  check "map work retained" (policies.map (fun p => (execute p heavy 2 repeated).count .map) ==
    [16480,5736,16380,5729])
  check "closure work retained" (policies.map (fun p => (execute p source 2 repeated).count .closure) ==
    [320,48,49,15])
  -- Exercise every policy, both witness parities, bounds and several prefix paths.
  for n in List.range 5 do
    for policy in policies do
      let p := chain n (.base [true,false])
      let qs := [(0,[]), (1,[true]), (2,[false,true]), (2,[true,false]),
        (1,[true,true]), (3,[])]
      let expected := if n % 2 == 0 then [true,false] else [false,true]
      check "exact selected witnesses and rejected views"
        ((execute policy p 2 qs).answers.map observe ==
          [some expected, some expected, some expected, some expected, none, none])
  let b := setup .combined source 2
  check "retained queries do not parse"
    ((b.query (2,[true,true])).2.count .derivative == 0 &&
     (b.query (2,[true,true])).2.count .nullable == 0 &&
     (b.query (2,[true,true])).2.count .map == 0)
  check "empty batch still pays setup" ((execute .combined source 2 []).cumulative > 0)
  check "rejection still validates" ((directQuery source 2 (3,[])).2.count .validation == 2)
  IO.println "Parser workload runtime checks passed"
