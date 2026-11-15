import SquareKit.HigherOrderComparison

/-! Experimental partial higher-order comparison (#303). The only recursion is
omega's silent self-loop. Finite computations retain beta counts; divergent
computations have an infinite silent execution, with finite prefixes hidden. -/
namespace SquareKit.WeakHigherOrder
open HigherOrderComparison (Ty Ctx Var Env extend empty)

inductive Comp (α : Type) where
  | done : Nat → α → Comp α
  | spin : Comp α

def Comp.bind (c : Comp α) (f : α → Comp β) : Comp β :=
  match c with
  | .spin => .spin
  | .done k x => match f x with
    | .spin => .spin
    | .done j y => .done (k + j) y

def Comp.tick (c : Comp α) : Comp α :=
  match c with
  | .spin => .spin
  | .done k x => .done (1 + k) x

def Comp.result : Comp α → Option α
  | .spin => none
  | .done _ x => some x

abbrev D : Ty → Type
  | .ground => Nat
  | .arr a b => D a → Option (D b)

abbrev V : Ty → Type
  | .ground => Nat
  | .arr a b => V a → Comp (V b)

inductive Term : Ctx → Ty → Type where
  | var : Var Γ a → Term Γ a
  | lit : Nat → Term Γ .ground
  | lam : Term (a :: Γ) b → Term Γ (.arr a b)
  | app : Term Γ (.arr a b) → Term Γ a → Term Γ b
  | omega : Term Γ a

/-- Lifted-set meaning: undefinedness is specified without execution or fuel. -/
def denote : Term Γ a → Env D Γ → Option (D a)
  | .var v, ρ => some (ρ v)
  | .lit n, _ => some n
  | .lam t, ρ => some (fun x => denote t (extend ρ x))
  | .app f x, ρ => (denote f ρ).bind fun g => (denote x ρ).bind g
  | .omega, _ => none

def run : Term Γ a → Env V Γ → Comp (V a)
  | .var v, ρ => .done 0 (ρ v)
  | .lit n, _ => .done 0 n
  | .lam t, ρ => .done 0 (fun x => run t (extend ρ x))
  | .app f x, ρ => (run f ρ).bind fun g =>
      (run x ρ).bind fun y => (g y).tick
  | .omega, _ => .spin

/-- Exact agreement about undefinedness and related returned values. -/
def Lift (R : α → β → Prop) : Comp α → Option β → Prop
  | .spin, none => True
  | .done _ x, some y => R x y
  | _, _ => False

def Rel : (a : Ty) → V a → D a → Prop
  | .ground, x, y => x = y
  | .arr a b, f, g => ∀ x y, Rel a x y → Lift (Rel b) (f x) (g y)

abbrev EnvRel (ρ : Env V Γ) (δ : Env D Γ) :=
  ∀ {a} (v : Var Γ a), Rel a (ρ v) (δ v)

theorem lift_bind (h : Lift R c d)
    (hf : ∀ x y, R x y → Lift S (f x) (g y)) :
    Lift S (c.bind f) (d.bind g) := by
  cases c with
  | spin => cases d <;> simp_all [Lift, Comp.bind]
  | done k x =>
    cases d with
    | none => exact False.elim h
    | some y =>
      have hh := hf x y h
      cases hf' : f x <;> cases hg' : g y <;> simp_all [Lift, Comp.bind]

theorem lift_tick (h : Lift R c d) : Lift R c.tick d := by
  cases c <;> cases d <;> exact h

theorem extend_related (h : EnvRel ρ δ) (hx : Rel a x y) :
    EnvRel (extend ρ x) (extend δ y) := by
  intro b v
  cases v with
  | here => exact hx
  | there v => exact h v

theorem application {a b : Ty} {cf : Comp (V (.arr a b))}
    {df : Option (D (.arr a b))} {cx : Comp (V a)} {dx : Option (D a)}
    (hf : Lift (Rel (.arr a b)) cf df) (hx : Lift (Rel a) cx dx) :
    Lift (Rel b) (cf.bind fun f => cx.bind fun x => (f x).tick)
      (df.bind fun f => dx.bind f) :=
  lift_bind hf (fun _ _ hfg => lift_bind hx (fun _ _ hxy => lift_tick (hfg _ _ hxy)))

theorem comparison (t : Term Γ a) (h : EnvRel ρ δ) :
    Lift (Rel a) (run t ρ) (denote t δ) := by
  induction t with
  | var v => exact h v
  | lit n => rfl
  | omega => trivial
  | lam t ih => exact fun x y hxy => ih (extend_related h hxy)
  | app f x ihf ihx => exact application (ihf h) (ihx h)

abbrev Equal (t u : Term Γ a) := ∀ δ, denote t δ = denote u δ

theorem app_congr (hf : Equal f g) (hx : Equal x y) :
    Equal (.app f x) (.app g y) := by
  intro δ
  simp only [denote, hf δ, hx δ]

theorem lam_congr (h : Equal t u) : Equal (.lam t) (.lam u) := by
  intro δ
  change some _ = some _
  congr 1
  funext x
  exact h _

/-- Finite typed contexts, including holes beneath binders. -/
inductive Context (Γ : Ctx) (a : Ty) : Ctx → Ty → Type where
  | hole : Context Γ a Γ a
  | appLeft : Context Γ a Δ (.arr b c) → Term Δ b → Context Γ a Δ c
  | appRight : Term Δ (.arr b c) → Context Γ a Δ b → Context Γ a Δ c
  | lam : Context Γ a (b :: Δ) c → Context Γ a Δ (.arr b c)

def Context.fill : Context Γ a Δ b → Term Γ a → Term Δ b
  | .hole, t => t
  | .appLeft c x, t => .app (c.fill t) x
  | .appRight f c, t => .app f (c.fill t)
  | .lam c, t => .lam (c.fill t)

theorem context_congr (c : Context Γ a Δ b) (h : Equal t u) :
    Equal (c.fill t) (c.fill u) := by
  induction c with
  | hole => exact h
  | appLeft c x ih => exact app_congr ih (fun _ => rfl)
  | appRight f c ih => exact app_congr (fun _ => rfl) ih
  | lam c ih => exact lam_congr ih

/-- A local semantic substitution law for a value held in the environment.
The right side evaluates the argument once, as call-by-value requires. -/
theorem beta_value (body : Term (a :: Γ) b) (arg : Term Γ a)
    (h : denote arg δ = some x) :
    denote (.app (.lam body) arg) δ = denote body (extend δ x) := by
  change (denote arg δ).bind _ = _
  rw [h]
  rfl

theorem binding_comparison (body : Term (a :: Γ) b)
    (h : EnvRel ρ δ) (hx : Rel a x y) :
    Lift (Rel b) (run body (extend ρ x)) (denote body (extend δ y)) :=
  comparison body (extend_related h hx)

abbrev Ren (Γ Δ : Ctx) := {a : Ty} → Var Γ a → Var Δ a

def liftRen (r : Ren Γ Δ) : Ren (a :: Γ) (a :: Δ)
  | _, .here => .here
  | _, .there v => .there (r v)

def rename (r : Ren Γ Δ) : Term Γ a → Term Δ a
  | .var v => .var (r v)
  | .lit n => .lit n
  | .lam t => .lam (rename (liftRen r) t)
  | .app f x => .app (rename r f) (rename r x)
  | .omega => .omega

abbrev Sub (Γ Δ : Ctx) := {a : Ty} → Var Γ a → Term Δ a

def liftSub (s : Sub Γ Δ) : Sub (a :: Γ) (a :: Δ)
  | _, .here => .var .here
  | _, .there v => rename (fun w => .there w) (s v)

def subst (s : Sub Γ Δ) : Term Γ a → Term Δ a
  | .var v => s v
  | .lit n => .lit n
  | .lam t => .lam (subst (liftSub s) t)
  | .app f x => .app (subst s f) (subst s x)
  | .omega => .omega

theorem denote_rename (t : Term Γ a) (r : Ren Γ Δ)
    (h : ∀ {b} (v : Var Γ b), τ (r v) = δ v) :
    denote (rename r t) τ = denote t δ := by
  induction t generalizing Δ with
  | var v => exact congrArg some (h v)
  | lit => rfl
  | omega => rfl
  | lam t ih =>
    change some _ = some _
    congr 1
    funext x
    apply ih
    intro b v
    cases v with
    | here => rfl
    | there v => exact h v
  | app f x ihf ihx => simp only [rename, denote, ihf r h, ihx r h]

/-- Substituends must denote values in this environment. Without this
hypothesis, replacing an unused variable by omega invalidates CBV beta. -/
theorem denote_subst (t : Term Γ a) (s : Sub Γ Δ)
    (h : ∀ {b} (v : Var Γ b), denote (s v) τ = some (δ v)) :
    denote (subst s t) τ = denote t δ := by
  induction t generalizing Δ with
  | var v => exact h v
  | lit => rfl
  | omega => rfl
  | lam t ih =>
    change some _ = some _
    congr 1
    funext x
    apply ih
    intro b v
    cases v with
    | here => rfl
    | there v =>
      exact (denote_rename (s v) (fun w => .there w) (fun _ => rfl)).trans (h v)
  | app f x ihf ihx => simp only [subst, denote, ihf s h, ihx s h]

theorem substitution_comparison (t : Term Γ a) (s : Sub Γ Δ)
    (h : EnvRel ρ τ) (hs : ∀ {b} (v : Var Γ b), denote (s v) τ = some (δ v)) :
    Lift (Rel a) (run (subst s t) ρ) (denote t δ) := by
  rw [← denote_subst t s hs]
  exact comparison _ h

/-- Silent transition system for the constructed operational computation.
Divergent prefixes are collapsed; finite beta lengths are retained exactly. -/
def step : Comp α → Sum α (Comp α)
  | .spin => .inr .spin
  | .done 0 x => .inl x
  | .done (k + 1) x => .inr (.done k x)

inductive Returns : Comp α → α → Prop where
  | now : Returns (.done 0 x) x
  | later : step c = .inr c' → Returns c' x → Returns c x

/-- An infinite silent execution, not the failure of any finite evaluator. -/
def Diverges (c : Comp α) : Prop :=
  ∃ path : Nat → Comp α, path 0 = c ∧ ∀ n, step (path n) = .inr (path (n + 1))

theorem spin_diverges : Diverges (Comp.spin : Comp α) :=
  ⟨fun _ => .spin, rfl, fun _ => rfl⟩

theorem returns_done (k : Nat) (x : α) : Returns (.done k x) x := by
  induction k with
  | zero => exact .now
  | succ k ih => exact .later rfl ih

theorem returns_result (h : Returns c x) : c.result = some x := by
  induction h with
  | now => rfl
  | @later c c' x hs h ih =>
    cases c with
    | spin => simp [step] at hs; subst c'; exact ih
    | done k y =>
      cases k with
      | zero => simp [step] at hs
      | succ k => simp [step] at hs; subst c'; exact ih

theorem returns_iff : Returns c x ↔ c.result = some x := by
  constructor
  · exact returns_result
  · cases c with
    | spin => simp [Comp.result]
    | done k y => intro h; cases Option.some.inj h; exact returns_done k x

theorem done_not_diverges (k : Nat) (x : α) : ¬ Diverges (.done k x) := by
  induction k with
  | zero =>
    rintro ⟨p, hp, hs⟩
    have := hs 0
    rw [hp] at this
    cases this
  | succ k ih =>
    rintro ⟨p, hp, hs⟩
    apply ih
    refine ⟨fun n => p (n + 1), ?_, fun n => hs (n + 1)⟩
    have h := hs 0
    rw [hp] at h
    exact (Sum.inr.inj h).symm

theorem divergence_iff : Diverges c ↔ c.result = none := by
  cases c with
  | spin => exact ⟨fun _ => rfl, fun _ => spin_diverges⟩
  | done k x => simp [done_not_diverges, Comp.result]

def weak (t : Term [] .ground) : Option Nat := (run t empty).result

theorem weak_eq_denote (t : Term [] .ground) : weak t = denote t empty := by
  have h := comparison t (ρ := empty) (δ := empty) (fun v => nomatch v)
  cases hr : run t empty <;> cases hd : denote t empty <;>
    simp_all [weak, Lift, Rel, Comp.result]

theorem observed_return (t : Term [] .ground) (n : Nat) :
    Returns (run t empty) n ↔ denote t empty = some n := by
  rw [returns_iff, ← weak_eq_denote]; rfl

theorem observed_divergence (t : Term [] .ground) :
    Diverges (run t empty) ↔ denote t empty = none := by
  rw [divergence_iff, ← weak_eq_denote]; rfl

/-- May-return preorder. Divergence is below every computation; equivalence
is its symmetric part, not a single direction. -/
def Pre (c d : Comp Nat) : Prop := ∀ n, Returns c n → Returns d n

theorem pre_iff (t u : Term [] .ground) :
    Pre (run t empty) (run u empty) ↔
      ∀ n, denote t empty = some n → denote u empty = some n := by
  constructor
  · intro h n hn
    exact (observed_return u n).mp (h n ((observed_return t n).mpr hn))
  · intro h n hn
    exact (observed_return u n).mpr (h n ((observed_return t n).mp hn))

theorem weak_iff (t u : Term [] .ground) :
    weak t = weak u ↔ denote t empty = denote u empty := by
  rw [weak_eq_denote, weak_eq_denote]

theorem context_weak (c : Context Γ a [] .ground) (h : Equal t u) :
    weak (c.fill t) = weak (c.fill u) :=
  (weak_iff _ _).mpr (context_congr c h empty)

theorem mutual_pre_iff (c d : Comp Nat) :
    (Pre c d ∧ Pre d c) ↔ c.result = d.result := by
  cases c with
  | spin =>
    cases d with
    | spin => simp [Pre, returns_iff, Comp.result]
    | done k x => simp [Pre, returns_iff, Comp.result]
  | done k x =>
    cases d with
    | spin => simp [Pre, returns_iff, Comp.result]
    | done j y => simp [Pre, returns_iff, Comp.result, eq_comm]

/-- Fuel is an approximation of transitions, never a divergence verdict. -/
def fuel : Nat → Comp α → Option α
  | 0, _ => none
  | k + 1, c => match step c with
    | .inl x => some x
    | .inr c' => fuel k c'

theorem fuel_spin (k : Nat) : fuel k (Comp.spin : Comp α) = none := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

def identity : Term Γ (.arr a a) := .lam (.var .here)
def zero : Term Γ .ground := .lit 0
def redex : Term Γ .ground := .app identity zero
def invoke : Term Γ (.arr (.arr .ground .ground) .ground) :=
  .lam (.app (.var .here) zero)
def client (f : Term Γ (.arr .ground .ground)) : Term Γ .ground := .app invoke f
def loopingFunction : Term Γ (.arr .ground .ground) := .lam .omega

def invokeContext : Context [] (.arr .ground .ground) [] .ground :=
  .appRight invoke .hole

theorem client_terminates : Returns (run (client identity) empty) 0 :=
  (observed_return _ _).mpr rfl

theorem client_diverges : Diverges (run (client loopingFunction) empty) :=
  (observed_divergence _).mpr rfl

theorem client_no_return (n : Nat) : ¬ Returns (run (client loopingFunction) empty) n := by
  rw [observed_return]; intro h; cases h

theorem client_context (h : Equal f g) : Equal (client f) (client g) :=
  app_congr (fun _ => rfl) h

theorem redex_equal : Equal (redex : Term Γ .ground) zero := fun _ => rfl

theorem weak_identifies : weak redex = weak zero :=
  (weak_iff _ _).mpr (redex_equal empty)

theorem strong_distinguishes : run redex empty ≠ run zero empty := by
  intro h
  have bad : (1 : Nat) = 0 := by cases h
  contradiction

theorem no_strong_adapter : ¬ ∃ obs : Option Nat → Comp Nat,
    ∀ t : Term [] .ground, run t empty = obs (denote t empty) := by
  rintro ⟨obs, h⟩
  exact strong_distinguishes ((h redex).trans (h zero).symm)

theorem preorder_not_equivalence :
    Pre (run (.omega : Term [] .ground) empty) (run zero empty) ∧
    ¬ Pre (run zero empty) (run (.omega : Term [] .ground) empty) := by
  constructor
  · intro n hn; have := returns_result hn; cases this
  · intro h; have := returns_result (h 0 .now); cases this

theorem exhaustion_not_divergence :
    fuel 1 (run redex empty) = fuel 1 (run (.omega : Term [] .ground) empty) ∧
    ¬ Diverges (run redex empty) ∧ Diverges (run (.omega : Term [] .ground) empty) :=
  ⟨rfl, done_not_diverges 1 0, spin_diverges⟩

/-- The chosen higher-order caller preserves the may-return preorder for
lambda arguments whose bodies satisfy the pointwise return obligation. -/
theorem client_pre {t u : Term [.ground] .ground}
    (h : ∀ x n, denote t (extend empty x) = some n →
      denote u (extend empty x) = some n) :
    Pre (run (client (.lam t)) empty) (run (client (.lam u)) empty) := by
  apply (pre_iff _ _).mpr
  exact h 0

theorem looping_client_pre :
    Pre (run (client loopingFunction) empty) (run (client identity) empty) :=
  client_pre (fun _ _ h => by cases h)

/-- Embed #285 without changing its public definitions or theorem statements. -/
def embed : HigherOrderComparison.Term Γ a → Term Γ a
  | .var v => .var v
  | .lit _ n => .lit n
  | .lam t => .lam (embed t)
  | .app f x => .app (embed f) (embed x)

/-- Recovery retains latent costs on related total inputs. It does not assert
that every partial function is a total function. -/
def TotalRel : (a : Ty) → HigherOrderComparison.V a → V a → Prop
  | .ground, x, y => x = y
  | .arr a b, f, g => ∀ x y, TotalRel a x y →
      ∃ z, g y = .done (f x).1 z ∧ TotalRel b (f x).2 z

abbrev TotalEnv (ρ : Env HigherOrderComparison.V Γ) (δ : Env V Γ) :=
  ∀ {a} (v : Var Γ a), TotalRel a (ρ v) (δ v)

theorem total_extend (h : TotalEnv ρ δ) (hx : TotalRel a x y) :
    TotalEnv (extend ρ x) (extend δ y) := by
  intro b v
  cases v with
  | here => exact hx
  | there v => exact h v

theorem recovery (t : HigherOrderComparison.Term Γ a) (h : TotalEnv ρ δ) :
    ∃ v, run (embed t) δ = .done (HigherOrderComparison.run t ρ).1 v ∧
      TotalRel a (HigherOrderComparison.run t ρ).2 v := by
  induction t with
  | var v => exact ⟨δ v, rfl, h v⟩
  | lit tag n => exact ⟨n, rfl, rfl⟩
  | lam t ih =>
    refine ⟨fun x => run (embed t) (extend δ x), rfl, ?_⟩
    exact fun x y hxy => ih (total_extend h hxy)
  | app f x ihf ihx =>
    obtain ⟨vf, hf, hrf⟩ := ihf h
    obtain ⟨vx, hx, hrx⟩ := ihx h
    obtain ⟨vb, hb, hrb⟩ := hrf _ _ hrx
    refine ⟨vb, ?_, hrb⟩
    simp only [embed, run, hf, hx, Comp.bind, hb, Comp.tick, HigherOrderComparison.run]
    congr 1
    omega

theorem recovery_ground (t : HigherOrderComparison.Term [] .ground) :
    run (embed t) empty = .done (HigherOrderComparison.strong t).1
      (HigherOrderComparison.strong t).2 := by
  obtain ⟨v, hv, hr⟩ := recovery t (ρ := empty) (δ := empty) (fun v => nomatch v)
  exact hv.trans (congrArg (Comp.done _) hr.symm)

theorem recovery_meaning (t : HigherOrderComparison.Term [] .ground) :
    denote (embed t) empty = some (HigherOrderComparison.denote t empty) := by
  rw [← weak_eq_denote]
  unfold weak
  rw [recovery_ground]
  exact congrArg some (HigherOrderComparison.weak_eq_denote t)

theorem recovered_bound_context :
    weak (embed (HigherOrderComparison.applyTwice
      (HigherOrderComparison.subst HigherOrderComparison.closeZero HigherOrderComparison.openRedex))) =
    weak (embed (HigherOrderComparison.applyTwice
      (HigherOrderComparison.subst HigherOrderComparison.closeZero HigherOrderComparison.openIdentity))) := by
  simp only [weak_eq_denote, recovery_meaning]
  exact congrArg some ((HigherOrderComparison.weak_iff _ _).mp
    HigherOrderComparison.bound_context_weak)

def openRedex : Term [.ground] (.arr .ground .ground) :=
  .lam (.app identity (.var (.there .here)))
def openIdentity : Term [.ground] (.arr .ground .ground) :=
  .lam (.var (.there .here))
def closeSeven : Sub [.ground] []
  | _, .here => .lit 7
def sevenEnv : Env D [.ground]
  | _, .here => 7

theorem bound_substitution_comparison :
    Lift (Rel (.arr .ground .ground)) (run (subst closeSeven openRedex) empty)
      (some (fun _ => some 7)) :=
  substitution_comparison openRedex closeSeven (ρ := empty) (τ := empty)
    (fun v => nomatch v) (δ := sevenEnv) (fun v => by
      cases v with
      | here => rfl
      | there v => exact nomatch v)

theorem bound_functions_equal : Equal (subst closeSeven openRedex)
    (subst closeSeven openIdentity) := by
  intro δ
  rfl

theorem bound_client_weak :
    weak (client (subst closeSeven openRedex)) =
      weak (client (subst closeSeven openIdentity)) :=
  context_weak invokeContext bound_functions_equal

theorem invoke_partial_comparison :
    Lift (Rel .ground) (run (client loopingFunction) empty) none :=
  application (comparison invoke (ρ := empty) (δ := empty) (fun v => nomatch v))
    (comparison loopingFunction (ρ := empty) (δ := empty) (fun v => nomatch v))

/-- Removing the value obligation from CBV beta is false. -/
theorem unrestricted_beta_fails :
    denote (.app (.lam (zero : Term [.ground] .ground)) .omega) empty ≠
      denote (zero : Term [] .ground) empty := by
  intro h
  cases h

end SquareKit.WeakHigherOrder
