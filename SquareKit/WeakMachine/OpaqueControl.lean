import SquareKit.WeakMachine.Canonicity

/-! Opt-in counterexample language: semantic meaning does not supply execution.
This syntax deliberately does not extend or change the partial machine. -/
namespace SquareKit.WeakMachine.OpaqueControl
open HigherOrderComparison (Ty Ctx Var Env D extend empty)

inductive Term : Ctx → Ty → Type where
  | var : Var Γ a → Term Γ a
  | lit : Nat → Term Γ .ground
  | lam : Term (a :: Γ) b → Term Γ (.arr a b)
  | app : Term Γ (.arr a b) → Term Γ a → Term Γ b
  | kappa : Term Γ .ground

def denote : Term Γ a → Env D Γ → D a
  | .var v, ρ => ρ v
  | .lit n, _ => n
  | .lam t, ρ => fun x => denote t (extend ρ x)
  | .app f x, ρ => denote f ρ (denote x ρ)
  | .kappa, _ => (0 : Nat)

abbrev Ren (Γ Δ : Ctx) := {a : Ty} → Var Γ a → Var Δ a

def liftRen (r : Ren Γ Δ) : Ren (a :: Γ) (a :: Δ)
  | _, .here => .here
  | _, .there v => .there (r v)

def rename (r : Ren Γ Δ) : Term Γ a → Term Δ a
  | .var v => .var (r v)
  | .lit n => .lit n
  | .lam t => .lam (rename (liftRen r) t)
  | .app f x => .app (rename r f) (rename r x)
  | .kappa => .kappa

abbrev Sub (Γ Δ : Ctx) := {a : Ty} → Var Γ a → Term Δ a

def liftSub (s : Sub Γ Δ) : Sub (a :: Γ) (a :: Δ)
  | _, .here => .var .here
  | _, .there v => rename (fun w => .there w) (s v)

def subst (s : Sub Γ Δ) : Term Γ a → Term Δ a
  | .var v => s v
  | .lit n => .lit n
  | .lam t => .lam (subst (liftSub s) t)
  | .app f x => .app (subst s f) (subst s x)
  | .kappa => .kappa

def singleSub (x : Term Γ a) : Sub (a :: Γ) Γ
  | _, .here => x
  | _, .there v => .var v

def beta (t : Term (a :: Γ) b) (x : Term Γ a) : Term Γ b :=
  subst (singleSub x) t

theorem denote_rename (t : Term Γ a) (r : Ren Γ Δ)
    (h : ∀ {b} (v : Var Γ b), τ (r v) = δ v) :
    denote (rename r t) τ = denote t δ := by
  induction t generalizing Δ with
  | var v => exact h v
  | lit => rfl
  | kappa => rfl
  | lam t ih =>
    funext x
    apply ih
    intro b v
    cases v with
    | here => rfl
    | there v => exact h v
  | app f x ihf ihx => simp only [rename, denote, ihf r h, ihx r h]

theorem denote_subst (t : Term Γ a) (s : Sub Γ Δ)
    (h : ∀ {b} (v : Var Γ b), denote (s v) τ = δ v) :
    denote (subst s t) τ = denote t δ := by
  induction t generalizing Δ with
  | var v => exact h v
  | lit => rfl
  | kappa => rfl
  | lam t ih =>
    funext x
    apply ih
    intro b v
    cases v with
    | here => rfl
    | there v =>
      exact (denote_rename (s v) (fun w => .there w) (fun _ => rfl)).trans (h v)
  | app f x ihf ihx => simp only [subst, denote, ihf s h, ihx s h]

/-- The ordinary function interpretation validates beta even for opaque data.
That equation does not create an operational beta step on a non-value. -/
theorem denote_beta (body : Term (a :: Γ) b) (x : Term Γ a) (ρ : Env D Γ) :
    denote (beta body x) ρ = denote body (extend ρ (denote x ρ)) := by
  apply denote_subst
  intro c v
  cases v <;> rfl

inductive Value : Term Γ a → Prop where
  | lit : Value (.lit n)
  | lam : Value (.lam t)

def isValue : Term Γ a → Bool
  | .lit _ | .lam _ => true
  | _ => false

theorem isValue_iff (t : Term Γ a) : isValue t = true ↔ Value t := by
  cases t with
  | lit => exact ⟨fun _ => .lit, fun _ => rfl⟩
  | lam => exact ⟨fun _ => .lam, fun _ => rfl⟩
  | var => constructor <;> intro h <;> cases h
  | app => constructor <;> intro h <;> cases h
  | kappa => constructor <;> intro h <;> cases h

/-- A stuck function blocks evaluation; a stuck argument blocks beta reduction. -/
def next (t : Term Γ a) : Option (Term Γ a) := match t with
  | .var _ | .lit _ | .lam _ | .kappa => none
  | .app f x => match next f with
    | some f' => some (.app f' x)
    | none => if isValue f then match next x with
      | some x' => some (.app f x')
      | none => if isValue x then match f with
        | .lam body => some (beta body x)
        | _ => none
        else none
      else none
termination_by structural t

inductive Step : Term [] a → Term [] a → Prop where
  | left : Step f f' → Step (.app f x) (.app f' x)
  | right : Value f → Step x x' → Step (.app f x) (.app f x')
  | beta : Value x → Step (.app (.lam body) x) (beta body x)

theorem value_next (h : Value t) : next t = none := by cases h <;> rfl

theorem step_next (h : Step t u) : next t = some u := by
  induction h with
  | left h ih => simp [next, ih]
  | right hv h ih => simp [next, value_next hv, (isValue_iff _).mpr hv, ih]
  | beta hv => cases hv <;> rfl

inductive Steps : Term [] a → Term [] a → Prop where
  | refl : Steps t t
  | cons : Step t u → Steps u v → Steps t v

/-- Admission requires actual reduction to the assigned numeral, as well as
semantic agreement. A meaning equation alone cannot construct this evidence. -/
structure ExecutablePrimitive (t : Term [] .ground) (meaning : Nat) : Prop where
  semantic : denote t empty = meaning
  realizes : Steps t (.lit meaning)

theorem kappa_meaning : denote (.kappa : Term [] .ground) empty = (0 : Nat) := rfl

theorem kappa_no_step : next (.kappa : Term [] .ground) = none := rfl

theorem kappa_not_value : ¬ Value (.kappa : Term [] .ground) := by intro h; cases h

theorem kappa_not_admitted (n : Nat) : ¬ ExecutablePrimitive .kappa n := by
  intro h
  cases h.realizes with
  | cons hs rest => cases hs

theorem literal_admitted (n : Nat) : ExecutablePrimitive (.lit n) n := ⟨rfl, .refl⟩

def demanded : Term [] .ground := .app (.lam (.lit 0 : Term [.ground] .ground)) .kappa

def ignored : Term [] .ground :=
  .app (.lam (.lit 0 : Term [.arr .ground .ground] .ground))
    (.lam (.kappa : Term [.ground] .ground))

theorem demanded_stuck : next demanded = none ∧ ¬ Value demanded :=
  ⟨rfl, by intro h; cases h⟩

theorem demanded_not_admitted (n : Nat) : ¬ ExecutablePrimitive demanded n := by
  intro h
  cases h.realizes with
  | cons hs rest =>
    have bad := step_next hs
    rw [demanded_stuck.1] at bad
    cases bad

theorem ignored_returns : Steps ignored (.lit 0) := .cons (.beta .lam) .refl

theorem ignored_admitted : ExecutablePrimitive ignored 0 := ⟨rfl, ignored_returns⟩

/-- Unlike the original machine, absence of a step here can mean stuckness. -/
inductive Result (a : Ty) where
  | terminal : Term [] a → Result a
  | stuck : Term [] a → Result a
  | timeout : Term [] a → Result a

def execute : Nat → Term [] a → Result a
  | fuel, t => if isValue t then .terminal t else match next t with
    | none => .stuck t
    | some u => match fuel with
      | 0 => .timeout t
      | fuel+1 => execute fuel u

example : execute 0 (.kappa : Term [] .ground) = .stuck .kappa := rfl
example : execute 2 demanded = .stuck demanded := rfl
example : execute 0 ignored = .timeout ignored := rfl
example : execute 1 ignored = .terminal (.lit 0) := rfl

end SquareKit.WeakMachine.OpaqueControl
