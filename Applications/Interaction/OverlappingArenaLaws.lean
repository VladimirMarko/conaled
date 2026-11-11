import Applications.Interaction.OverlappingStrategies

/-! Boundary legality for the finite-slot Boolean arenas. -/
namespace Interaction.OverlappingStrategies
open FiniteStrategies
variable {A : Arena}

/-- `true` means this slot has an outstanding question. Answers may carry either
Boolean, but require an outstanding question. -/
def questionStep : Bool → FiniteQueries.Move → Option Bool
  | false,.ask => some true
  | true,.reply _ => some false
  | _,_ => none

def Arena.Legal (A : Arena) (xs : List (Event A FiniteQueries.Move)) : Prop :=
  ∀ i, ∃ pending, Path questionStep false (project i xs) pending

def clientBoundary : RelayMove → List FiniteQueries.Move
  | .leftAsk => [.ask]
  | .leftReply b => [.reply b]
  | _ => []
def serviceBoundary : RelayMove → List FiniteQueries.Move
  | .rightAsk => [.ask]
  | .rightReply b => [.reply b]
  | _ => []

def clientPending : Phase → Bool
  | .idle => false
  | _ => true
def servicePending : Phase → Bool
  | .waiting => true
  | _ => false

private theorem client_local (h : relayStep f p m = some q) :
    Path questionStep (clientPending p) (clientBoundary m) (clientPending q) := by
  cases p <;> cases m <;> cases q <;> simp_all [relayStep, clientPending, clientBoundary]
  all_goals first | exact .nil | exact .cons rfl .nil
private theorem service_local (h : relayStep f p m = some q) :
    Path questionStep (servicePending p) (serviceBoundary m) (servicePending q) := by
  cases p <;> cases m <;> cases q <;> simp_all [relayStep, servicePending, serviceBoundary]
  all_goals first | exact .nil | exact .cons rfl .nil

/-- Both arena boundaries of every strategy position obey per-slot question and
answer discipline. Several distinct slots may be pending at once. -/
theorem Strategy.boundaries (s : Strategy A) (h : s.Play xs) :
    A.Legal (translate (fun _ => clientBoundary) xs) ∧
    A.Legal (translate (fun _ => serviceBoundary) xs) := by
  constructor
  · intro i
    rw [project_translate]
    obtain ⟨q,hq⟩ := h i
    exact ⟨_, hq.project clientPending clientBoundary (fun _ _ _ => client_local)⟩
  · intro i
    rw [project_translate]
    obtain ⟨q,hq⟩ := h i
    exact ⟨_, hq.project servicePending serviceBoundary (fun _ _ _ => service_local)⟩

theorem Arena.empty (A : Arena) : A.Legal [] := fun _ => ⟨false,.nil⟩
theorem Arena.prefix (h : A.Legal (xs ++ ys)) : A.Legal xs := by
  intro i
  obtain ⟨q,hq⟩ := h i
  rw [project_append] at hq
  exact hq.take_prefix

/-- Player's response within a slot is determined. Scheduling between distinct
slots remains observable and is deliberately not forced to be deterministic. -/
theorem Strategy.local_deterministic (s : Strategy A) (i : Fin A.slots)
    (hp : p = .requested ∨ ∃ b, p = .answered b)
    (hm : relayStep (s.response i) p m = some q)
    (hn : relayStep (s.response i) p n = some r) : m = n :=
  player_deterministic hp hm hn

end Interaction.OverlappingStrategies
