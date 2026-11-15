import SquareKit.WeakMachine.Substitution

/-! Independent substitution-based left-to-right call-by-value execution. -/
namespace SquareKit.WeakMachine
open HigherOrderComparison (Ty Ctx Var Env extend empty)
open WeakHigherOrder

inductive Value : Term [] a → Prop where
  | lit : Value (.lit n)
  | lam : Value (.lam t)

def next {Γ : Ctx} {a : Ty} (t : Term Γ a) : Option (Term Γ a) := match t with
  | .var _ => none
  | .lit _ => none
  | .lam _ => none
  | .omega => some .omega
  | .app f x => match next f with
    | some f' => some (.app f' x)
    | none => match next x with
      | some x' => some (.app f x')
      | none => match f with
        | .lam body => some (beta body x)
        | _ => none
termination_by structural t

inductive Step : Term [] a → Term [] a → Prop where
  | loop : Step .omega .omega
  | left : Step f f' → Step (.app f x) (.app f' x)
  | right : Value f → Step x x' → Step (.app f x) (.app f x')
  | beta : Value x → Step (.app (.lam body) x) (beta body x)

theorem value_next (h : Value t) : next t = none := by cases h <;> rfl

theorem next_none (t : Term [] a) : next t = none ↔ Value t := by
  cases t with
  | var v => exact nomatch v
  | lit n => exact ⟨fun _ => .lit, fun _ => rfl⟩
  | lam t => exact ⟨fun _ => .lam, fun _ => rfl⟩
  | omega => constructor <;> intro h <;> cases h
  | app f x =>
    constructor
    · intro h
      cases hf : next f with
      | some f' => simp [next, hf] at h
      | none =>
        have hv := (next_none f).mp hf
        cases hv with
        | lam => cases hx : next x <;> simp [next, hx] at h
    · intro h; cases h
termination_by sizeOf t

theorem step_next (h : Step t u) : next t = some u := by
  induction h with
  | loop => rfl
  | left h ih => simp [next, ih]
  | right hv h ih => simp [next, value_next hv, ih]
  | beta hv => simp [next, value_next hv]

theorem next_step (t : Term [] a) : ∀ u, next t = some u → Step t u := by
  cases t with
  | var v => exact nomatch v
  | lit n => intro u h; cases h
  | lam t => intro u h; cases h
  | omega => intro u h; cases h; exact .loop
  | app f x =>
    intro u h
    cases hf : next f with
    | some f' => simp only [next, hf] at h; cases h; exact .left (next_step f _ hf)
    | none =>
      have hv := (next_none f).mp hf
      cases hx : next x with
      | some x' => simp only [next, hf, hx] at h; cases h; exact .right hv (next_step x _ hx)
      | none =>
        cases hv with
        | lam =>
          simp only [next, hx] at h
          cases h
          exact .beta ((next_none x).mp hx)
termination_by sizeOf t

theorem step_iff : Step t u ↔ next t = some u := ⟨step_next, next_step t u⟩
theorem deterministic (h : Step t u) (h' : Step t v) : u = v :=
  Option.some.inj ((step_next h).symm.trans (step_next h'))

def Stuck (t : Term [] a) := ¬ Value t ∧ next t = none
theorem no_stuck (t : Term [] a) : ¬ Stuck t := fun h => h.1 ((next_none t).mp h.2)
theorem progress (t : Term [] a) : Value t ∨ ∃ u, Step t u := by
  cases h : next t with
  | none => exact .inl ((next_none t).mp h)
  | some u => exact .inr ⟨u,next_step t u h⟩
theorem value_no_step (hv : Value t) : ¬ Step t u := by
  intro h
  have := step_next h
  rw [value_next hv] at this
  contradiction

inductive Steps : Term [] a → Term [] a → Prop where
  | refl : Steps t t
  | cons : Step t u → Steps u v → Steps t v

theorem Steps.trans (h : Steps t u) (h' : Steps u v) : Steps t v := by
  induction h with
  | refl => exact h'
  | cons hs h ih => exact .cons hs (ih h')

theorem Steps.left {f g : Term [] (.arr a b)} (h : Steps f g) (x : Term [] a) :
    Steps (.app f x) (.app g x) := by
  induction h with
  | refl => exact .refl
  | cons hs h ih => exact .cons (.left hs) ih

theorem Steps.right (hv : Value f) (h : Steps x y) : Steps (.app f x) (.app f y) := by
  induction h with
  | refl => exact .refl
  | cons hs h ih => exact .cons (.right hv hs) ih

/-- Actual infinite transition sequence. -/
def Infinite (t : Term [] a) :=
  ∃ p : Nat → Term [] a, p 0 = t ∧ ∀ n, Step (p n) (p (n+1))

theorem self_infinite (h : Step t t) : Infinite t := ⟨fun _ => t,rfl,fun _ => h⟩

theorem prefix_infinite (h : Steps t u) (hu : Infinite u) : Infinite t := by
  induction h with
  | refl => exact hu
  | cons hs h ih =>
    obtain ⟨p,hp,hpstep⟩ := ih hu
    refine ⟨fun n => match n with | 0 => _ | n+1 => p n,rfl,?_⟩
    intro n
    cases n with
    | zero => simpa [hp] using hs
    | succ n => exact hpstep n

theorem terminal_not_infinite (hv : Value v) (h : Steps t v) : ¬ Infinite t := by
  induction h with
  | refl => rintro ⟨p,hp,hs⟩; exact value_no_step hv (hp ▸ hs 0)
  | cons hs h ih =>
    rintro ⟨p,hp,hstep⟩
    apply ih hv
    refine ⟨fun n => p (n+1),?_,fun n => hstep (n+1)⟩
    exact (deterministic (hp ▸ hstep 0) hs)

theorem terminal_unique (h : Steps t v) (hv : Value v) (h' : Steps t w) (hw : Value w) : v = w := by
  induction h with
  | refl => cases h' with
    | refl => rfl
    | cons hs h => exact False.elim (value_no_step hv hs)
  | cons hs h ih => cases h' with
    | refl => exact False.elim (value_no_step hw hs)
    | cons hs' h' => have e := deterministic hs hs'; cases e; exact ih hv h'

inductive Result (a : Ty) where
  | terminal : (t : Term [] a) → Value t → Result a
  | timeout : Term [] a → Result a

/-- Inspect terminality at zero fuel; each successor consumes one source step. -/
def execute : Nat → (t : Term [] a) → Result a
  | 0, t => match h : next t with
    | none => .terminal t ((next_none t).mp h)
    | some _ => .timeout t
  | n+1, t => match h : next t with
    | none => .terminal t ((next_none t).mp h)
    | some u => execute n u

theorem execute_value (hv : Value t) (n : Nat) : execute n t = .terminal t hv := by
  cases n <;> unfold execute <;> split
  · rfl
  · rename_i u hu; have bad := (value_next hv).symm.trans hu; cases bad
  · rfl
  · rename_i u hu; have bad := (value_next hv).symm.trans hu; cases bad

theorem execute_step (hs : Step t u) (n : Nat) : execute (n+1) t = execute n u := by
  conv => lhs; unfold execute
  split
  · rename_i ht; have bad := ht.symm.trans (step_next hs); cases bad
  · rename_i v hv
    have e := Option.some.inj (hv.symm.trans (step_next hs))
    cases e
    rfl

theorem execute_sound (n : Nat) (t : Term [] a) :
    ∀ v hv, execute n t = .terminal v hv → Steps t v := by
  induction n generalizing t with
  | zero =>
    intro v hv h
    unfold execute at h
    split at h
    · cases h; exact .refl
    · cases h
  | succ n ih =>
    intro v hv h
    unfold execute at h
    split at h
    · cases h; exact .refl
    · rename_i u hu
      exact .cons (next_step t u hu) (ih u v hv h)

theorem execute_complete (h : Steps t v) (hv : Value v) :
    ∃ n, execute n t = .terminal v hv := by
  induction h with
  | refl =>
    refine ⟨0,?_⟩
    unfold execute
    split
    · rfl
    · rename_i u hu
      have bad := (value_next hv).symm.trans hu
      cases bad
  | cons hs h ih =>
    obtain ⟨n,hn⟩ := ih hv
    refine ⟨n+1,?_⟩
    unfold execute
    split
    · rename_i hu
      have bad := hu.symm.trans (step_next hs)
      cases bad
    · rename_i u hu
      have e := Option.some.inj (hu.symm.trans (step_next hs))
      cases e
      exact hn

theorem execute_sufficient (h : Steps t v) (hv : Value v) :
    ∃ bound, ∀ n, bound ≤ n → execute n t = .terminal v hv := by
  induction h with
  | refl => exact ⟨0,fun n _ => execute_value hv n⟩
  | cons hs h ih =>
    obtain ⟨bound,hbound⟩ := ih hv
    refine ⟨bound+1,fun n hn => ?_⟩
    cases n with
    | zero => omega
    | succ n => rw [execute_step hs]; exact hbound n (Nat.le_of_succ_le_succ hn)

end SquareKit.WeakMachine
