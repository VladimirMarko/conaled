import Applications.Optimization.Relations

/-!
# Finite evaluation and certificate checking

A deterministic atomic transition either returns a value or continues in a
state. One transition has unit cost. This model does not account for the host
cost of computing that transition, or environmental scheduling. `Evaluates`
is an inductive operational judgment, independent of fuel search.
-/
namespace Progress
universe u
variable {S T A B : Type u}

abbrev Machine (S A : Type u) := S → Sum A S

inductive Evaluates (step : Machine S A) : S → A → Nat → Prop
  | done {s a} : step s = .inl a → Evaluates step s a 1
  | next {s t a k} : step s = .inr t → Evaluates step t a k →
      Evaluates step s a (k + 1)

/-- Runtime termination at one state. No checker or search bound occurs here. -/
def Terminates (step : Machine S A) (s : S) : Prop :=
  ∃ a k, Evaluates step s a k

/-- Totality on a domain, with a postcondition retaining the initial state. -/
def TotalOn (step : Machine S A) (pre : S → Prop) (post : S → A → Prop) : Prop :=
  ∀ s, pre s → ∃ a k, Evaluates step s a k ∧ post s a

theorem Evaluates.unique {step : Machine S A} {s a b k l}
    (h : Evaluates step s a k) (j : Evaluates step s b l) : a = b ∧ k = l := by
  induction h generalizing b l with
  | done e =>
    cases j with
    | done f => exact ⟨Sum.inl.inj (e.symm.trans f), rfl⟩
    | next f _ => simp [e] at f
  | next e h ih =>
    cases j with
    | done f => simp [e] at f
    | next f j =>
      have eq := Sum.inr.inj (e.symm.trans f)
      subst eq
      obtain ⟨rfl, rfl⟩ := ih j
      exact ⟨rfl, rfl⟩

/-- `none` means unknown. Search always terminates, even on a silent loop. -/
def search (step : Machine S A) : Nat → S → Option (A × Nat)
  | 0, _ => none
  | fuel + 1, s => match step s with
    | .inl a => some (a, 1)
    | .inr t => (search step fuel t).map (fun (a, k) => (a, k + 1))

theorem search_sound {step : Machine S A} {fuel s a k}
    (h : search step fuel s = some (a, k)) : Evaluates step s a k := by
  induction fuel generalizing s a k with
  | zero => simp [search] at h
  | succ fuel ih =>
    simp only [search] at h
    split at h
    next e => cases h; exact .done e
    next t e =>
      cases hs : search step fuel t with
      | none => simp [hs] at h
      | some p =>
        simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        rcases p with ⟨v, n⟩
        rcases h with ⟨rfl, rfl⟩
        exact .next e (ih hs)

/-- Completeness only for finite derivations with sufficient supplied fuel. -/
theorem search_complete {step : Machine S A} {s a k}
    (h : Evaluates step s a k) {fuel} (bound : k ≤ fuel) :
    search step fuel s = some (a, k) := by
  induction h generalizing fuel with
  | done e =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [search, e]
  | next e h ih =>
    cases fuel with
    | zero => omega
    | succ fuel => simp [search, e, ih (fuel := fuel) (by omega)]

/-- A certificate is proposed fuel and a claimed result/cost, not a proof field. -/
abbrev Certificate (A : Type u) := Nat × A × Nat

def check [DecidableEq A] (step : Machine S A) (s : S) (c : Certificate A) : Bool :=
  decide (search step c.1 s = some c.2)

theorem check_sound [DecidableEq A] {step : Machine S A} {s c}
    (h : check step s c = true) : Evaluates step s c.2.1 c.2.2 := by
  exact search_sound (of_decide_eq_true h)

/-- Set-valued specifications retain unknown without treating it as divergence. -/
def admissible (step : Machine S A) (s : S) : Set (Option (A × Nat)) :=
  {r | ∀ a k, r = some (a, k) → Evaluates step s a k}

/-- Reuse #112's indexed membership relation for the search implementation. -/
def searchSquare (step : Machine S A) (fuel : Nat) :
    Relational.RelSquare (Optimization.inputRep S)
      (Optimization.membershipRep (I := S) (id : Option (A × Nat) → Option (A × Nat))) where
  impl s := (s, search step fuel s)
  spec s := (s, admissible step s)
  preserves := by
    rintro s _ rfl
    exact ⟨rfl, fun _ _ h => search_sound h⟩

/-- Sequential operational composition, including the switch to stage two. -/
def sequential (f : Machine S A) (g : Machine T B) (start : A → T) :
    Machine (Sum S T) B
  | .inl s => match f s with
    | .inl a => .inr (.inr (start a))
    | .inr t => .inr (.inl t)
  | .inr t => match g t with
    | .inl b => .inl b
    | .inr t' => .inr (.inr t')

theorem sequential_right {f : Machine S A} {g : Machine T B} {start : A → T}
    {s b k} (h : Evaluates g s b k) :
    Evaluates (sequential f g start) (.inr s) b k := by
  induction h with
  | done e => exact .done (by simp [sequential, e])
  | next e _ ih => exact .next (by simp [sequential, e]) ih

theorem sequential_evaluates {f : Machine S A} {g : Machine T B} {start : A → T}
    {s a b k l} (h : Evaluates f s a k) (j : Evaluates g (start a) b l) :
    Evaluates (sequential f g start) (.inl s) b (k + l) := by
  induction h with
  | done e =>
    simpa [Nat.add_comm] using
      Evaluates.next (by simp [sequential, e]) (sequential_right (f := f) j)
  | next e _ ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      Evaluates.next (by simp [sequential, e]) (ih j)

theorem sequential_total {f : Machine S A} {g : Machine T B} {start : A → T}
    {pre : S → Prop} {mid : S → A → Prop} {dom : T → Prop} {post : T → B → Prop}
    (hf : TotalOn f pre mid) (hg : TotalOn g dom post)
    (feeds : ∀ s a, pre s → mid s a → dom (start a)) :
    ∀ s, pre s → ∃ a b k, Evaluates (sequential f g start) (.inl s) b k ∧
      mid s a ∧ post (start a) b := by
  intro s hs
  obtain ⟨a, k, h, hm⟩ := hf s hs
  obtain ⟨b, l, j, hp⟩ := hg (start a) (feeds s a hs hm)
  exact ⟨a, b, k + l, sequential_evaluates h j, hm, hp⟩

end Progress
