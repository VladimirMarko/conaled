import Applications.Languages.ParserWorkload
import Examples.RetainedParserSnapshot

namespace ParserWorkloadExamples
open LanguageWitnesses ParserWorkload RetainedSnapshot

def chain : Nat → Spine → Spine
  | 0, p => p
  | n+1, p => .transport .flip (chain n p)

def repeated : List Request := List.replicate 20 (2, [true,true])
def short : List Request := [(1,[true])]
def source : Spine := chain 8 (.base [true,false])
def heavy : Spine := chain 8 (.base (List.replicate 100 true))
def policies : List Policy := [.ordinary, .retained, .normalized, .combined]
def metrics (p : Spine) (qs : List Request) : List (Nat × Nat × Nat) :=
  policies.map fun policy =>
    let r := execute policy p 2 qs
    (r.work, r.cumulative, r.peak)

-- Independent witness expectation: three pointwise flips complement the input.
example : (execute .combined (chain 3 (.base [true,false])) 2 [(2,[false,true])]).answers =
    [some (.yes ([false,true], ⟨⟩))] := by
  rw [execute_exact]
  rfl

-- The generic composition also retains the selected nullable-star witness.
example : session .combined RetainedParserSnapshotExamples.parser 2 (0,[]) =
    some (.yes ⟨[],rfl⟩) := by
  rw [session_exact]
  rfl
example (policy : Policy) :
    session policy RetainedParserSnapshotExamples.parser 2 (2,[true,true]) =
      some (RetainedParserSnapshotExamples.parser.parse [true,true]) := by
  rw [session_exact]
  rfl
example : session .combined RetainedParserSnapshotExamples.parser 1 (2,[true]) = none := by
  rw [session_exact]
  rfl
example : session .combined RetainedParserSnapshotExamples.parser 2 (1,[true,true]) = none := by
  rw [session_exact]
  rfl

-- Recognition-equivalent selected witnesses still belong to different instances.
example : session .combined (.scale (.yes true) .universal) 0 (0,[]) ≠
    session .combined (.scale (.yes false) .universal) 0 (0,[]) := by
  simp only [session_exact]
  intro h
  cases h

example :
    (session .combined (.scale (.yes true) .universal) 0 (0,[])).map Decision.test =
    (session .combined (.scale (.yes false) .universal) 0 (0,[])).map Decision.test := by
  simp only [session_exact]
  rfl

set_option maxRecDepth 100000 in
example : metrics source repeated =
    [(5180,3380,202), (1361,808,822), (2326,1307,124), (868,436,450)] := by decide
set_option maxRecDepth 100000 in
example : metrics source short =
    [(173,110,143), (1226,789,822), (144,81,114), (733,417,450)] := by decide
set_option maxRecDepth 100000 in
example : metrics (.base [true,false]) repeated =
    [(380,180,18), (225,72,62), (846,483,36), (324,132,122)] := by decide
set_option maxRecDepth 100000 in
example : metrics heavy repeated =
    [(52220,34740,1966), (17825,11784,11994), (49366,32667,1888), (17332,11412,11622)] := by decide
set_option maxRecDepth 100000 in
example : (execute .combined source 2 repeated).work <
    (execute .retained source 2 repeated).work := by decide
set_option maxRecDepth 100000 in
example : (execute .ordinary source 2 short).work <
    (execute .combined source 2 short).work := by decide
set_option maxRecDepth 100000 in
example : (execute .retained (.base [true,false]) 2 repeated).work <
    (execute .combined (.base [true,false]) 2 repeated).work := by decide

-- Public repeated-query composition separates setup from the exact per-query tariff.
set_option maxRecDepth 100000 in
example (k : Nat) : (execute .combined source 2 (List.replicate k (2,[true,true]))).count .map =
    241 := by
  rw [execute_count_repeated]
  change 241 + k * 0 = 241
  omega

end ParserWorkloadExamples
