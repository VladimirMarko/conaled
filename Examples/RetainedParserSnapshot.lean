import Applications.Languages.RetainedSnapshot

namespace RetainedParserSnapshotExamples
open LanguageWitnesses RetainedSnapshot

/-- Nullable operand, with selected empty-star witness and nonempty derivatives. -/
def parser : Parser (Star (fun w : List Bool => epsilon w ⊕ atom true w)) :=
  .star (.union .epsilon (.atom true))

def workload : List Request :=
  [(2,[true,true]), (2,[true,false]), (1,[true]), (0,[]),
   (2,[true,true]), (1,[true]), (2,[true,true]), (1,[true]),
   (2,[true,true]), (2,[true,false])]

example (q : Request) : query (build parser 2).1 q.1 q.2 =
    if q.1 ≤ 2 ∧ q.2.length ≤ q.1 then some (parser.parse q.2) else none :=
  query_build parser 2 q.1 q.2

example : (build parser 2).2 = 6 := rfl
example : (build parser 2).1.size = 7 := Tree.size_eq _
example : baselineDerivatives 2 workload = 15 := rfl
example : (batch (build parser 2).1 workload).2 = ⟨10,0,15,20⟩ := rfl

example : (build parser 2).2 < baselineDerivatives 2 (List.replicate 4 (2,[true,true])) :=
  repeated_saves parser 2 4 (2,[true,true]) (by decide) (by decide)

/-- With a single word, the eager tree performs more derivatives than parsing. -/
example : baselineDerivatives 2 [(2,[true,true])] < (build parser 2).2 := by decide

example : query (build parser 0).1 0 [] = some (.yes ⟨[],rfl⟩) := rfl
example : query (build parser 2).1 1 [true,true] = none := rfl
example : query (build parser 1).1 2 [true] = none := rfl
example : query (build parser 2).1 2 [true,true] = some (parser.parse [true,true]) :=
  query_build parser 2 2 [true,true]

example : query (build parser 2).1 1 [true] =
    some ((WitnessTrie.truncate 1 (by decide) (build parser 2).1.toTrie).lookup [true] (by decide)) :=
  query_restricted _ 1 (by decide) [true] (by decide)

example : WitnessTrie.truncate 0 (by decide)
    (WitnessTrie.truncate 1 (by decide) (build parser 2).1.toTrie) =
    WitnessTrie.truncate 0 (by decide) (build parser 2).1.toTrie :=
  WitnessTrie.truncate_comp 0 1 (by decide) (by decide) _

/-- Different retained selected witnesses must not share a Boolean cache key. -/
def selected (b : Bool) : Parser (fun _ : List Bool => Bool × PUnit) :=
  .scale (.yes b) .universal

example : query (build (selected true) 0).1 0 [] ≠
    query (build (selected false) 0).1 0 [] := by
  intro h
  cases h

example : ((build (selected true) 0).1.lookup [] (by decide)).test =
    ((build (selected false) 0).1.lookup [] (by decide)).test := rfl

end RetainedParserSnapshotExamples
