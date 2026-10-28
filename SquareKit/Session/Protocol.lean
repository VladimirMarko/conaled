import SquareKit.Session.Process
import SquareKit.InteractionContracts

namespace Session

/-- Finite selecting protocols; their duals are offering endpoints. -/
inductive Protocol where
  | finish
  | choose (left right : Protocol)
  deriving DecidableEq, Repr

def Protocol.formula : Protocol → Formula
  | .finish => .one
  | .choose a b => .plus a.formula b.formula

/-- Independent trace specification derived only from the protocol type. -/
inductive Accepts (x : Nat) : Protocol → List Event → Prop where
  | finish : Accepts x .finish [.closed x]
  | left : Accepts x a es → Accepts x (.choose a b) (.label x false :: es)
  | right : Accepts x b es → Accepts x (.choose a b) (.label x true :: es)

def Event.channel : Event → Nat
  | .label x _ => x
  | .closed x => x

theorem Accepts.channels (h : Accepts x a es) : ∀ e ∈ es, e.channel = x := by
  induction h with
  | finish => simp [Event.channel]
  | left _ ih => simpa [Event.channel] using ih
  | right _ ih => simpa [Event.channel] using ih

inductive Selection : Protocol → Type where
  | finish : Selection .finish
  | left : Selection a → Selection (.choose a b)
  | right : Selection b → Selection (.choose a b)

def Selection.proof (x : Nat) : Selection a → Proof [(x,a.formula)]
  | .finish => .close x
  | .left p => .left (p.proof x)
  | .right p => .right (p.proof x)

def Selection.events (x : Nat) : Selection a → List Event
  | .finish => [.closed x]
  | .left p => .label x false :: p.events x
  | .right p => .label x true :: p.events x

theorem Selection.accepts (p : Selection a) (x : Nat) : Accepts x a (p.events x) := by
  induction p with
  | finish => exact .finish
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih

/-- Each offered branch has its own typed continuation at the same linear interface. -/
inductive Receiver (Γ : Context) : Protocol → Type where
  | finish : Proof Γ → Receiver Γ .finish
  | choose : Receiver Γ a → Receiver Γ b → Receiver Γ (.choose a b)

theorem Receiver.valid : Receiver Γ a → Valid Γ
  | .finish p => p.typed.valid
  | .choose p _ => p.valid

def Receiver.proof (x : Nat) (fresh : x ∉ Γ.map Prod.fst) :
    Receiver Γ a → Proof ((x,a.formula.dual) :: Γ)
  | .finish p => .wait x (by simpa [Valid] using And.intro fresh p.typed.valid) p
  | .choose p q => .offer (p.proof x fresh) (q.proof x fresh)

def Receiver.follow (r : Receiver Γ a) (p : Selection a) : Proof Γ :=
  match r, p with
  | .finish q, .finish => q
  | .choose r _, .left p => r.follow p
  | .choose _ r, .right p => r.follow p

/-- Cut really connects two separately translated, dual endpoints. -/
def connect (x : Nat) (fresh : x ∉ Γ.map Prod.fst) (p : Selection a) (r : Receiver Γ a) : Proof Γ :=
  .cut x a.formula (Γ := []) r.valid (p.proof x) (r.proof x fresh)

/-- Completion stops at the selected residual component, not at a fictitious closed world. -/
theorem completes (x : Nat) (fresh : x ∉ Γ.map Prod.fst) (p : Selection a) (r : Receiver Γ a) :
    Steps (connect x fresh p r).erase (p.events x) (r.follow p).erase := by
  induction p with
  | finish => cases r with
    | finish q => exact .cons .close .nil
  | left p ih => cases r with
    | choose r s => exact .cons .left (ih r)
  | right p ih => cases r with
    | choose r s => exact .cons .right (ih s)

/-- There is a next communication in every focused network, without a fairness premise. -/
theorem progress (x : Nat) (fresh : x ∉ Γ.map Prod.fst) (p : Selection a) (r : Receiver Γ a) :
    ∃ e q, Step (connect x fresh p r).erase e q := by
  cases p with
  | finish => cases r with | finish q => exact ⟨_,_,.close⟩
  | left p => cases r with | choose r s => exact ⟨_,_,.left⟩
  | right p => cases r with | choose r s => exact ⟨_,_,.right⟩

/-- Typed component composition concatenates actual communication traces. -/
theorem completes_then (x : Nat) (fresh : x ∉ Γ.map Prod.fst) (p : Selection a) (r : Receiver Γ a)
    (next : Steps (r.follow p).erase es q) :
    Steps (connect x fresh p r).erase (p.events x ++ es) q :=
  (completes x fresh p r).append next

theorem Step.deterministic (h : Step p e q) (k : Step p f r) : e = f ∧ q = r := by
  cases h <;> cases k <;> exact ⟨rfl,rfl⟩

/-- Equal-length executions of this principal-step relation have identical observations. -/
theorem Steps.same_length (h : Steps p es q) (k : Steps p fs r) (len : es.length = fs.length) :
    es = fs ∧ q = r := by
  induction h generalizing fs r with
  | nil => cases k with
    | nil => exact ⟨rfl,rfl⟩
    | cons => simp at len
  | cons hs ht ih => cases k with
    | nil => simp at len
    | cons ks kt =>
      obtain ⟨rfl,rfl⟩ := hs.deterministic ks
      obtain ⟨rfl,rfl⟩ := ih kt (Nat.succ.inj len)
      exact ⟨rfl,rfl⟩

/-- Every actual execution through this phase's communication boundary satisfies
its independent protocol contract. Longer executions may belong to the continuation. -/
theorem trace_refines (x : Nat) (fresh : x ∉ Γ.map Prod.fst) (p : Selection a) (r : Receiver Γ a) :
    Interaction.Refines Eq {es | Accepts x a es}
      {es | ∃ q, Steps (connect x fresh p r).erase es q ∧ es.length = (p.events x).length} := by
  rintro es ⟨q,run,len⟩
  have eq := ((completes x fresh p r).same_length run len.symm).1
  exact ⟨p.events x, p.accepts x, eq⟩

/-- Finite type depth bounds one phase, regardless of selected branches. -/
def Protocol.bound : Protocol → Nat
  | .finish => 1
  | .choose a b => 1 + max a.bound b.bound

theorem Selection.length_le (p : Selection a) (x : Nat) : (p.events x).length ≤ a.bound := by
  induction p with
  | finish => exact Nat.le_refl 1
  | @left a b p ih =>
    simpa [Selection.events, Protocol.bound, Nat.add_comm] using Nat.succ_le_succ (ih.trans (Nat.le_max_left a.bound b.bound))
  | @right a b p ih =>
    simpa [Selection.events, Protocol.bound, Nat.add_comm] using Nat.succ_le_succ (ih.trans (Nat.le_max_right b.bound a.bound))

end Session
