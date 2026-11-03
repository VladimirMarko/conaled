import FirstOrder

/-! Capture-avoiding operations on the existing intrinsically typed compiler
first-order syntax, including lifting beneath its let binder. The higher-order
compiler has a separate syntax and its own substitution implementation. -/
namespace FirstOrderCompiler
namespace Term

private theorem binaryCongr (f : α → β → γ) {a a' : α} {b b' : β}
    (h : a = a') (k : b = b') : f a b = f a' b' := by cases h; cases k; rfl

abbrev Ren (Γ Δ : Ctx) := {a : Ty} → Var Γ a → Var Δ a

def liftRen (r : Ren Γ Δ) : Ren (a :: Γ) (a :: Δ)
  | _, .here => .here
  | _, .there v => .there (r v)

def rename (r : Ren Γ Δ) : Term P Γ a → Term P Δ a
  | .var v => .var (r v)
  | .unit => .unit
  | .pair t u => .pair (rename r t) (rename r u)
  | .fst t => .fst (rename r t)
  | .snd t => .snd (rename r t)
  | .letE t u => .letE (rename r t) (rename (liftRen r) u)
  | .prim p t => .prim p (rename r t)

abbrev Sub (P : Ty → Ty → Type) (Γ Δ : Ctx) := {a : Ty} → Var Γ a → Term P Δ a

def liftSub (s : Sub P Γ Δ) : Sub P (a :: Γ) (a :: Δ)
  | _, .here => .var .here
  | _, .there v => rename (fun w => .there w) (s v)

def subst (s : Sub P Γ Δ) : Term P Γ a → Term P Δ a
  | .var v => s v
  | .unit => .unit
  | .pair t u => .pair (subst s t) (subst s u)
  | .fst t => .fst (subst s t)
  | .snd t => .snd (subst s t)
  | .letE t u => .letE (subst s t) (subst (liftSub s) u)
  | .prim p t => .prim p (subst s t)

def single (u : Term P Γ a) : Sub P (a :: Γ) Γ
  | _, .here => u
  | _, .there v => .var v

private theorem liftRen_agrees {B : Type} (r : Ren Γ Δ)
    (ρ : Val B (context Γ)) (τ : Val B (context Δ))
    (h : ∀ {a} (v : Var Γ a), lookup (r v) τ = lookup v ρ) (x : Val B b) :
    ∀ {a} (v : Var (b :: Γ) a), lookup (liftRen r v) (τ, x) = lookup v (ρ, x)
  | _, .here => rfl
  | _, .there v => h v

/-- Renaming preserves meaning whenever the environments agree on renamed variables. -/
theorem eval_rename {B : Type} (m : {a b : Ty} → P a b → Val B a → Val B b)
    (t : Term P Γ a) (r : Ren Γ Δ) (ρ : Val B (context Γ))
    (τ : Val B (context Δ))
    (h : ∀ {a} (v : Var Γ a), lookup (r v) τ = lookup v ρ) :
    eval m (rename r t) τ = eval m t ρ := by
  induction t generalizing Δ with
  | var v => exact h v
  | unit => rfl
  | pair t u it iu => exact binaryCongr Prod.mk (it r ρ τ h) (iu r ρ τ h)
  | fst t it => exact congrArg Prod.fst (it r ρ τ h)
  | snd t it => exact congrArg Prod.snd (it r ρ τ h)
  | letE t u it iu =>
    simp only [rename, eval, it r ρ τ h]
    exact iu _ _ _ (liftRen_agrees r ρ τ h _)
  | prim p t it => exact congrArg (m p) (it r ρ τ h)

private theorem liftSub_agrees {B : Type} (m : {a b : Ty} → P a b → Val B a → Val B b)
    (s : Sub P Γ Δ) (ρ : Val B (context Γ)) (τ : Val B (context Δ))
    (h : ∀ {a} (v : Var Γ a), eval m (s v) τ = lookup v ρ) (x : Val B b) :
    ∀ {a} (v : Var (b :: Γ) a), eval m (liftSub s v) (τ, x) = lookup v (ρ, x)
  | _, .here => rfl
  | _, .there v => (eval_rename m (s v) (fun w => .there w) τ (τ, x) (fun _ => rfl)).trans (h v)

/-- Simultaneous substitution is capture-avoiding and preserves interpretation. -/
theorem eval_subst {B : Type} (m : {a b : Ty} → P a b → Val B a → Val B b)
    (t : Term P Γ a) (s : Sub P Γ Δ) (ρ : Val B (context Γ))
    (τ : Val B (context Δ))
    (h : ∀ {a} (v : Var Γ a), eval m (s v) τ = lookup v ρ) :
    eval m (subst s t) τ = eval m t ρ := by
  induction t generalizing Δ with
  | var v => exact h v
  | unit => rfl
  | pair t u it iu => exact binaryCongr Prod.mk (it s ρ τ h) (iu s ρ τ h)
  | fst t it => exact congrArg Prod.fst (it s ρ τ h)
  | snd t it => exact congrArg Prod.snd (it s ρ τ h)
  | letE t u it iu =>
    simp only [subst, eval, it s ρ τ h]
    exact iu _ _ _ (liftSub_agrees m s ρ τ h _)
  | prim p t it => exact congrArg (m p) (it s ρ τ h)

/-- The single-variable substitution contract, including open terms. -/
theorem eval_single {B : Type} (m : {a b : Ty} → P a b → Val B a → Val B b)
    (t : Term P (a :: Γ) b) (u : Term P Γ a) (ρ : Val B (context Γ)) :
    eval m (subst (single u) t) ρ = eval m t (ρ, eval m u ρ) :=
  eval_subst m t (single u) _ ρ (fun v => by cases v <;> rfl)

end Term
end FirstOrderCompiler
