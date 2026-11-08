import SquareKit.RetainedException

/-! Independent bounded query/response specification and native handler comparison. -/
namespace Interaction.FiniteQueries
inductive Move where
  | ask | reply (b : Bool)
  deriving DecidableEq, Repr

/-- Complete rounds, optionally followed by one outstanding query. -/
inductive Legal : List Move → Prop where
  | nil : Legal []
  | pending : Legal [.ask]
  | round (b : Bool) : Legal t → Legal (.ask :: .reply b :: t)

abbrev Environment := List Bool → Option Bool
abbrev Outcome := Option Bool × List Move

/-- Direct finite loop. An environment sees all previous replies. -/
def native (env : Environment) : Nat → Bool → List Bool → Outcome
  | 0, last, _ => (some last, [])
  | n+1, _, h => match env h with
    | none => (none, [.ask])
    | some b => let out := native env n b (h ++ [b])
                (out.1, .ask :: .reply b :: out.2)

theorem native_legal (env : Environment) (n : Nat) (last : Bool) (h : List Bool) :
    Legal (native env n last h).2 := by
  induction n generalizing last h with
  | zero => exact .nil
  | succ n ih =>
    simp only [native]
    split
    · exact .pending
    · exact .round _ (ih _ _)

def once (env : Environment) := native env 1 false []
def twice (env : Environment) := native env 2 false []
def constant (b : Bool) : Environment := fun _ => some b
def changing : Environment := fun h => some (!h.isEmpty)
def silent : Environment := fun _ => none

theorem constant_once (b : Bool) : once (constant b) = (some b, [.ask, .reply b]) := rfl
theorem constant_twice (b : Bool) :
    twice (constant b) = (some b, [.ask, .reply b, .ask, .reply b]) := rfl

theorem changing_distinguishes : (once changing).1 = some false ∧
    (twice changing).1 = some true := by decide

theorem silent_pending : twice silent = (none, [.ask]) := rfl

/-- Returned-value observation is intentionally coarser than exact history. -/
theorem no_history_recovery : ¬ ∃ recover : Option Bool → List Move,
    recover (once (constant false)).1 = (once (constant false)).2 ∧
    recover (twice (constant false)).1 = (twice (constant false)).2 := by
  rintro ⟨recover, h, k⟩
  have bad := h.symm.trans k
  contradiction

open RetainedException
abbrev State := List Bool × List Move

def query (env : Environment) (_ : Unit) (s : State) : Option Bool × State :=
  match env s.1 with
  | none => (none, (s.1, s.2 ++ [.ask]))
  | some b => (some b, (s.1 ++ [b], s.2 ++ [.ask, .reply b]))

def body : Nat → Bool → Tree Unit Unit (Option Bool) Unit Bool
  | 0, last => .ret last
  | n+1, _ => .act () (fun answer => match answer with
      | none => .raise ()
      | some b => body n b)

def result (x : Except Unit Bool) : Option Bool :=
  match x with | .ok b => some b | .error _ => none

def handler (env : Environment) (n : Nat) (last : Bool) (h : List Bool)
    (pre : List Move) : Outcome :=
  let out := fold (algebra (S := Unit) (E := Unit) (query env)) (body n last) () (h,pre)
  (result out.1.1, out.2.2)

theorem handler_native (env : Environment) (n : Nat) (last : Bool)
    (h : List Bool) (pre : List Move) :
    handler env n last h pre = ((native env n last h).1, pre ++ (native env n last h).2) := by
  induction n generalizing last h pre with
  | zero => simp [handler, body, fold, algebra, Run.ret, result, native]
  | succ n ih =>
    cases he : env h with
    | none => simp [handler, body, fold, algebra, query, he, Run.raise, result, native]
    | some b =>
      have ihere := ih b (h ++ [b]) (pre ++ [.ask, .reply b])
      simpa [handler, body, fold, algebra, query, he, native, List.append_assoc] using ihere
end Interaction.FiniteQueries
