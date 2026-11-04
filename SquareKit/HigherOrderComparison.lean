import Mathlib.Data.Nat.Basic

/-! A finite, total higher-order experiment. The two interpretations are
specified separately: mathematical functions, and call-by-value computations
counting beta contractions. No final-coalgebra hypothesis is assumed. -/
namespace SquareKit.HigherOrderComparison

inductive Ty where
  | ground
  | arr : Ty → Ty → Ty

def D : Ty → Type
  | .ground => Nat
  | .arr a b => D a → D b

/-- Behavioral values carry latent computations at function types. -/
def V : Ty → Type
  | .ground => Nat
  | .arr a b => V a → Nat × V b

abbrev B (a : Ty) := Nat × V a
abbrev Ctx := List Ty
inductive Var : Ctx → Ty → Type where
  | here : Var (a :: Γ) a
  | there : Var Γ a → Var (b :: Γ) a

/-- The tag distinguishes two presentations of the same ground constant.
It has no computational observation in the admitted language. -/
inductive Term : Ctx → Ty → Type where
  | var : Var Γ a → Term Γ a
  | lit (tag : Bool) (n : Nat) : Term Γ .ground
  | lam : Term (a :: Γ) b → Term Γ (.arr a b)
  | app : Term Γ (.arr a b) → Term Γ a → Term Γ b

abbrev Env (F : Ty → Type) (Γ : Ctx) := {a : Ty} → Var Γ a → F a

def extend (ρ : Env F Γ) (x : F a) : Env F (a :: Γ)
  | _, .here => x
  | _, .there v => ρ v

def denote : Term Γ a → Env D Γ → D a
  | .var v, ρ => ρ v
  | .lit _ n, _ => n
  | .lam t, ρ => fun x => denote t (extend ρ x)
  | .app f x, ρ => denote f ρ (denote x ρ)

/-- Evaluate function, then argument, then body. Each application pays one
beta contraction, in addition to the costs of all three computations. -/
def run : Term Γ a → Env V Γ → B a
  | .var v, ρ => (0, ρ v)
  | .lit _ n, _ => (0, n)
  | .lam t, ρ => (0, fun x => run t (extend ρ x))
  | .app f x, ρ =>
    let rf := run f ρ
    let rx := run x ρ
    let rb := rf.2 rx.2
    (rf.1 + rx.1 + 1 + rb.1, rb.2)

/-- Inputs must already be related; outputs are then related. This is the
contravariant input obligation, not equality of the two function carriers. -/
def Rel : (a : Ty) → V a → D a → Prop
  | .ground, v, d => v = d
  | .arr a b, v, d => ∀ x y, Rel a x y → Rel b (v x).2 (d y)

abbrev Related (r : B a) (d : D a) := Rel a r.2 d
abbrev EnvRel (ρ : Env V Γ) (δ : Env D Γ) := ∀ {a} (v : Var Γ a), Rel a (ρ v) (δ v)

theorem extend_related (h : EnvRel ρ δ) (hx : Rel a x y) :
    EnvRel (extend ρ x) (extend δ y) := by
  intro b v
  cases v with
  | here => exact hx
  | there v => exact h v

/-- Fundamental comparison, with the environment relation constructed at binders. -/
theorem comparison (t : Term Γ a) (h : EnvRel ρ δ) : Related (run t ρ) (denote t δ) := by
  induction t with
  | var v => exact h v
  | lit tag n => rfl
  | lam t ih => exact fun x y hxy => ih (extend_related h hxy)
  | app f x ihf ihx => exact ihf h _ _ (ihx h)

/-- Explicit compatibility of the mixed-carrier application interface. -/
theorem application {a b : Ty} {rf : B (.arr a b)} {df : D (.arr a b)}
    {rx : B a} {dx : D a} (hf : Related rf df) (hx : Related rx dx) :
    Rel b (rf.2 rx.2).2 (df dx) := hf _ _ hx

abbrev Ren (Γ Δ : Ctx) := {a : Ty} → Var Γ a → Var Δ a

def liftRen (r : Ren Γ Δ) : Ren (a :: Γ) (a :: Δ)
  | _, .here => .here
  | _, .there v => .there (r v)

def rename (r : Ren Γ Δ) : Term Γ a → Term Δ a
  | .var v => .var (r v)
  | .lit tag n => .lit tag n
  | .lam t => .lam (rename (liftRen r) t)
  | .app f x => .app (rename r f) (rename r x)

abbrev Sub (Γ Δ : Ctx) := {a : Ty} → Var Γ a → Term Δ a

def liftSub (s : Sub Γ Δ) : Sub (a :: Γ) (a :: Δ)
  | _, .here => .var .here
  | _, .there v => rename (fun w => .there w) (s v)

def subst (s : Sub Γ Δ) : Term Γ a → Term Δ a
  | .var v => s v
  | .lit tag n => .lit tag n
  | .lam t => .lam (subst (liftSub s) t)
  | .app f x => .app (subst s f) (subst s x)

theorem denote_rename (t : Term Γ a) (r : Ren Γ Δ)
    (h : ∀ {b} (v : Var Γ b), τ (r v) = δ v) :
    denote (rename r t) τ = denote t δ := by
  induction t generalizing Δ with
  | var v => exact h v
  | lit => rfl
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
  | lam t ih =>
    funext x
    apply ih
    intro b v
    cases v with
    | here => rfl
    | there v =>
      exact (denote_rename (s v) (fun w => .there w) (fun _ => rfl)).trans (h v)
  | app f x ihf ihx => simp only [subst, denote, ihf s h, ihx s h]

/-- Substitution preserves the independent meaning and its behavioral comparison.
The result does not assert cost preservation: substituted computations may run
more often than values held in an environment. -/
theorem substitution_comparison (t : Term Γ a) (s : Sub Γ Δ)
    (h : EnvRel ρ τ) (hs : ∀ {b} (v : Var Γ b), denote (s v) τ = δ v) :
    Related (run (subst s t) ρ) (denote t δ) := by
  rw [← denote_subst t s hs]
  exact comparison _ h

abbrev Equal (t u : Term Γ a) := ∀ δ, denote t δ = denote u δ

theorem app_congr (hf : Equal f g) (hx : Equal x y) :
    Equal (.app f x) (.app g y) := by
  intro δ
  simp only [denote, hf δ, hx δ]

theorem lam_congr (h : Equal t u) : Equal (.lam t) (.lam u) := by
  intro δ
  funext x
  exact h _

theorem subst_congr {t u : Term Γ a} (h : Equal t u) (s : Sub Γ Δ) : Equal (subst s t) (subst s u) := by
  intro τ
  rw [denote_subst t s (δ := fun v => denote (s v) τ) (fun _ => rfl),
    denote_subst u s (δ := fun v => denote (s v) τ) (fun _ => rfl)]
  exact h _

def empty : Env F [] := fun v => nomatch v

/-- Weak observations in this experiment expose only the terminating ground
result. Strong observations also expose the beta count. -/
def weak (t : Term [] .ground) : Nat := (run t empty).2
def strong (t : Term [] .ground) : Nat × Nat := run t empty

theorem weak_eq_denote (t : Term [] .ground) : weak t = denote t empty :=
  comparison t (fun v => nomatch v)

theorem weak_iff (t u : Term [] .ground) : weak t = weak u ↔ denote t empty = denote u empty := by
  simp only [weak_eq_denote]
  rfl

theorem strong_implies_denote (t u : Term [] .ground) (h : strong t = strong u) :
    denote t empty = denote u empty :=
  (weak_iff t u).mp (congrArg Prod.snd h)

def identity : Term Γ (.arr a a) := .lam (.var .here)
def zero : Term Γ .ground := .lit false 0
def redex : Term Γ .ground := .app identity zero

theorem redex_equal : Equal (redex : Term Γ .ground) zero := fun _ => rfl

theorem strong_distinguishes : strong redex ≠ strong zero := by decide

theorem weak_identifies : weak redex = weak zero :=
  (weak_iff _ _).mpr (redex_equal empty)

/-- A nontrivial higher-order context: pass the hole through a function input. -/
def applyTwice (t : Term Γ (.arr .ground .ground)) : Term Γ .ground :=
  .app t (.app t zero)

theorem twice_congr (h : Equal f g) : Equal (applyTwice f) (applyTwice g) :=
  app_congr h (app_congr h (fun _ => rfl))

/-- Open beta case under a binder, then capture-avoiding closing substitution. -/
def openIdentity : Term [.ground] (.arr .ground .ground) :=
  .lam (.var (.there .here))
def openRedex : Term [.ground] (.arr .ground .ground) :=
  .lam (.app identity (.var (.there .here)))

theorem binding_equal : Equal openRedex openIdentity :=
  lam_congr (fun _ => rfl)

def closeZero : Sub [.ground] []
  | _, .here => zero

theorem binding_substitution_equal : Equal (subst closeZero openRedex) (subst closeZero openIdentity) :=
  subst_congr binding_equal closeZero

theorem bound_context_weak :
    weak (applyTwice (subst closeZero openRedex)) =
      weak (applyTwice (subst closeZero openIdentity)) :=
  (weak_iff _ _).mpr (twice_congr binding_substitution_equal empty)

theorem bound_context_strong :
    strong (applyTwice (subst closeZero openRedex)) ≠
      strong (applyTwice (subst closeZero openIdentity)) := by decide

/-- An inadmissible observer: distinguish presentation tags of equal constants. -/
def inspect : Term Γ .ground → Bool
  | .lit tag _ => tag
  | _ => false

theorem no_uniform_inspector : ¬ ∃ obs : Nat → Bool,
    ∀ t : Term [] .ground, inspect t = obs (denote t empty) := by
  rintro ⟨obs, h⟩
  have hf := h (.lit false 0)
  have ht := h (.lit true 0)
  have bad : false = true := hf.trans ht.symm
  contradiction

/-- Ground behavior as a delay coalgebra: one transition per counted beta
contraction, then a terminal numeral. This is a projection of the evaluator,
not a construction of the papers' locally final higher-order domain. -/
def delayStep : B .ground → Sum Nat (B .ground)
  | (0, n) => .inl n
  | (k + 1, n) => .inr (k, n)

theorem delay_redex : delayStep (strong redex) = .inr (0, (0 : Nat)) := rfl
theorem delay_zero : delayStep (strong zero) = .inl 0 := rfl

/-- The same extensional numeral cannot determine whether this computation
has a step available. This prevents factoring the strong observer through D. -/
theorem no_strong_adapter : ¬ ∃ obs : Nat → Nat × Nat,
    ∀ t : Term [] .ground, strong t = obs (denote t empty) := by
  rintro ⟨obs, h⟩
  apply strong_distinguishes
  exact (h redex).trans (h zero).symm

def invoke : Term [] (.arr (.arr .ground .ground) .ground) :=
  .lam (.app (.var .here) zero)

theorem invoke_identity_comparison :
    Related (run (.app invoke identity) empty) (0 : Nat) :=
  application (comparison invoke (ρ := empty) (δ := empty) (fun v => nomatch v))
    (comparison (identity : Term [] (.arr .ground .ground)) (ρ := empty) (δ := empty) (fun v => nomatch v))

/-- The lifted substitution theorem is exercised beneath the binder with a
nonempty source environment; the free variable denotes seven. -/
def closeSeven : Sub [.ground] []
  | _, .here => .lit false 7

def sevenEnv : Env D [.ground]
  | _, .here => (7 : Nat)

theorem binding_comparison :
    Related (run (subst closeSeven openRedex) empty) (fun _ => (7 : Nat)) :=
  substitution_comparison openRedex closeSeven (ρ := empty) (τ := empty)
    (fun v => nomatch v) (δ := sevenEnv) (fun v => by
      cases v with
      | here => rfl
      | there v => exact nomatch v)

end SquareKit.HigherOrderComparison
