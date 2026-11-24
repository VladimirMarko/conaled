import Mathlib.Data.Set.Basic

/-! A fixed two-sort signature with typed de Bruijn binding. Context extension
makes freshness structural: replacements are weakened under every binder. -/
namespace MatchingLogic
inductive SortCode where
  | nat | cfg
  deriving DecidableEq
abbrev Context := List SortCode
inductive Var : Context → SortCode → Type
  | here : Var (s :: Γ) s
  | there : Var Γ s → Var (t :: Γ) s

/-- All nonconstant symbols are unary; `zero` is the one nullary symbol. -/
inductive Symbol : SortCode → SortCode → Type
  | succ : Symbol .nat .nat
  | run : Symbol .nat .cfg
  | done : Symbol .nat .cfg
  | step : Symbol .cfg .cfg
  | defined : (s t : SortCode) → Symbol s t
inductive Pattern : Context → SortCode → Type
  | var : Var Γ s → Pattern Γ s
  | zero : Pattern Γ .nat
  | app : Symbol s t → Pattern Γ s → Pattern Γ t
  | neg : Pattern Γ s → Pattern Γ s
  | conj : Pattern Γ s → Pattern Γ s → Pattern Γ s
  | ex : (t : SortCode) → Pattern (t :: Γ) s → Pattern Γ s

abbrev Renaming (Γ Δ : Context) := ∀ {s}, Var Γ s → Var Δ s
abbrev Substitution (Γ Δ : Context) := ∀ {s}, Var Γ s → Pattern Δ s

def Renaming.lift (r : Renaming Γ Δ) : Renaming (t :: Γ) (t :: Δ)
  | _, .here => .here
  | _, .there v => .there (r v)

def Pattern.rename (r : Renaming Γ Δ) : Pattern Γ s → Pattern Δ s
  | .var v => .var (r v)
  | .zero => .zero
  | .app f p => .app f (p.rename r)
  | .neg p => .neg (p.rename r)
  | .conj p q => .conj (p.rename r) (q.rename r)
  | .ex t p => .ex t (p.rename r.lift)

def Substitution.lift (σ : Substitution Γ Δ) : Substitution (t :: Γ) (t :: Δ)
  | _, .here => .var .here
  | _, .there v => (σ v).rename Var.there

def Pattern.subst (σ : Substitution Γ Δ) : Pattern Γ s → Pattern Δ s
  | .var v => σ v
  | .zero => .zero
  | .app f p => .app f (p.subst σ)
  | .neg p => .neg (p.subst σ)
  | .conj p q => .conj (p.subst σ) (q.subst σ)
  | .ex t p => .ex t (p.subst σ.lift)

def replace (q : Pattern Γ t) : Substitution (t :: Γ) Γ
  | _, .here => q
  | _, .there v => .var v

def Pattern.substOne (p : Pattern (t :: Γ) s) (q : Pattern Γ t) := p.subst (replace q)
def Pattern.disj (p q : Pattern Γ s) : Pattern Γ s := .neg (.conj (.neg p) (.neg q))
def Pattern.imp (p q : Pattern Γ s) : Pattern Γ s := .neg (.conj p (.neg q))
def Pattern.iff (p q : Pattern Γ s) : Pattern Γ s := .conj (p.imp q) (q.imp p)
def Pattern.all (p : Pattern (t :: Γ) s) : Pattern Γ s := .neg (.ex t (.neg p))
def Pattern.top (p : Pattern Γ s) : Pattern Γ s := p.imp p
def Pattern.bot (p : Pattern Γ s) : Pattern Γ s := .neg p.top
def Pattern.ceil (t : SortCode) (p : Pattern Γ s) : Pattern Γ t := .app (.defined s t) p
def Pattern.floor (t : SortCode) (p : Pattern Γ s) : Pattern Γ t := .neg (p.neg.ceil t)
def Pattern.equal (t : SortCode) (p q : Pattern Γ s) : Pattern Γ t := (p.iff q).floor t
def Pattern.member (t : SortCode) (v : Var Γ s) (p : Pattern Γ s) : Pattern Γ t :=
  (Pattern.conj (.var v) p).ceil t
/-- The new witness is fresh for `q`, by weakening. -/
def Pattern.functional (t : SortCode) (q : Pattern Γ s) : Pattern Γ t :=
  .ex s ((q.rename Var.there).equal t (.var .here))

inductive Occurs : {Γ : Context} → {s : SortCode} → Var Γ s → {t : SortCode} → Pattern Γ t → Prop
  | var : Occurs v (.var v)
  | app : Occurs v p → Occurs v (.app f p)
  | neg : Occurs v p → Occurs v (.neg p)
  | left : Occurs v p → Occurs v (.conj p q)
  | right : Occurs v q → Occurs v (.conj p q)
  | ex : Occurs (Var.there (t := t) v) p → Occurs v (.ex t p)
end MatchingLogic
