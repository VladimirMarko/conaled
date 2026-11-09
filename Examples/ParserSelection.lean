import Applications.Languages.ParserSelection
import Examples.ParserWorkload

namespace ParserSelectionExamples
open LanguageWitnesses ParserWorkload ParserSelection Resources.Prepared
open ParserWorkloadExamples (source heavy repeated short)

-- Preparation depth two; the public envelope additionally admits both rejection modes.
def unitTariff : Tariff := fun _ => 1

def roomy : Requirements :=
  {deadline := 10000, maintenance := 0, capacity := 20000, peak := 20000}

def offline (req : Requirements) (p : Spine) (qs : List RetainedSnapshot.Request) :=
  choose 2 3 3 unitTariff req p (offlineObjective 2 unitTariff (offlineInput p qs))

def online (req : Requirements) (p : Spine) (count : Nat) :=
  choose 2 3 3 unitTariff req p (upperObjective 2 3 3 unitTariff p count)

def observations (p : Spine) : List (Nat × Nat × Nat × Nat) :=
  catalog.map fun c => let b := profile 2 3 3 unitTariff c
                      (b.preparation p,b.query p,b.retained p,b.peak p)

-- Expectations derive from all-category work and the declared live arenas.
set_option maxRecDepth 100000 in
example : observations source =
    [(0,259,33,202), (1221,7,821,822), (66,113,60,124), (728,7,449,450)] := by decide

set_option maxRecDepth 100000 in
theorem repeated_choice : offline roomy source repeated = some .combined := by decide
set_option maxRecDepth 100000 in
theorem short_choice : offline roomy source short = some .normalized := by decide
set_option maxRecDepth 100000 in
theorem simple_choice : offline roomy (.base [true,false]) repeated = some .retained := by decide
set_option maxRecDepth 100000 in
theorem heavy_choice : offline roomy heavy repeated = some .combined := by decide
set_option maxRecDepth 100000 in
theorem storage_choice : offline {roomy with capacity := 200, peak := 200} source repeated =
    some .normalized := by decide
set_option maxRecDepth 100000 in
theorem deadline_choice : offline {roomy with deadline := 7} source short =
    some .combined := by decide
set_option maxRecDepth 100000 in
theorem impossible_choice : offline {roomy with deadline := 2} source repeated = none := by decide
set_option maxRecDepth 100000 in
theorem empty_choice : offline roomy source [] = some .ordinary := by decide
set_option maxRecDepth 100000 in
example : online roomy source 20 = some .combined := by decide
set_option maxRecDepth 100000 in
example : online roomy source 0 = some .ordinary := by decide

-- The chosen result is the original selected payload, not just successful recognition.
def q : ParserSelection.Request 3 3 := Request.ofRaw (2,[true,true]) (by decide) (by decide)
example : ((ops 2 3 3 unitTariff .combined).answer
    ((ops 2 3 3 unitTariff .combined).prepare source).1 q).1 =
      some (.yes ([true,false], ⟨⟩)) := by
  rw [chosen_correct repeated_choice]
  rfl

example (request : ParserSelection.Request 3 3) :
    ((ops 2 3 3 unitTariff .combined).answer
      ((ops 2 3 3 unitTariff .combined).prepare source).1 request).2 ≤ 7 :=
  chosen_deadline deadline_choice request

example : ¬ Feasible {roomy with capacity := 200, peak := 200}
    (profile 2 3 3 unitTariff .combined) source := by decide
example : ¬ Feasible {roomy with deadline := 7}
    (profile 2 3 3 unitTariff .normalized) source := by decide

-- The generic tagged adapter preserves the nullable-star fiber and chosen empty parse.
example (c : Policy) : semanticAnswer c RetainedParserSnapshotExamples.parser 2 (0,[]) =
    ⟨[],some (.yes ⟨[],rfl⟩)⟩ := by
  rw [semanticAnswer_exact]
  rfl
example (c : Policy) : semanticAnswer c RetainedParserSnapshotExamples.parser 2 (2,[true,true]) =
    ⟨[true,true],some (RetainedParserSnapshotExamples.parser.parse [true,true])⟩ := by
  rw [semanticAnswer_exact]
  rfl

example : (execute .ordinary source 2 []).peak = 33 := by decide
example : (execute .combined source 2 []).peak = 449 := by decide
example : (setup .combined source 2).events.count .allocation = 416 := by decide

-- Rejections are inside the envelope, and their validation traversal is charged.
example : (ops 2 3 3 unitTariff .ordinary).answer
    ((ops 2 3 3 unitTariff .ordinary).prepare source).1
    (Request.ofRaw (3,[]) (by decide) (by decide)) = (none,3) := by rfl
example : (ops 2 3 3 unitTariff .combined).answer
    ((ops 2 3 3 unitTariff .combined).prepare source).1
    (Request.ofRaw (1,[true,true,true]) (by decide) (by decide)) = (none,6) := by rfl

set_option maxRecDepth 100000 in
example : chooseOffline 2 3 3 unitTariff roomy
    (offlineInput source (List.replicate 20 q)) = some .combined := by decide

example : ¬ Valid 2 .combined (.base [false])
    ⟨.base [true], setup .combined (.base [true]) 2⟩ := by
  intro h
  have bad : Spine.base [true] = Spine.base [false] := valid_source h
  cases bad

-- Same recognition does not identify the selected witness in the tagged answer.
example : semanticAnswer .combined (.scale (.yes true) .universal) 0 (0,[]) ≠
    semanticAnswer .combined (.scale (.yes false) .universal) 0 (0,[]) := by
  simp only [semanticAnswer_exact]
  intro h
  cases h

end ParserSelectionExamples
