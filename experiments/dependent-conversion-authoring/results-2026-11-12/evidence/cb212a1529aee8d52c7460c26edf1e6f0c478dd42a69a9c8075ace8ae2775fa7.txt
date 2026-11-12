/-! Experimental dependent structural source syntax. Base expressions are
algebraic trees; dependent expressions are variables or a named primitive.
Substitutions are finite assignments of these expressions, never semantic maps.
Type conversion is equality of the normalized source type expression. -/
namespace SquareKit.Internal.DependentStructural

inductive Base (n : Nat) where
  | var : Fin n → Base n
  | zero : Base n
  | neg : Base n → Base n
  deriving DecidableEq

def Base.sub {n m : Nat} (ρ : Fin n → Base m) : Base n → Base m
  | .var i => ρ i
  | .zero => .zero
  | .neg b => .neg (b.sub ρ)

def Base.wk {n : Nat} (b : Base n) : Base (n+1) := b.sub (fun i => .var i.succ)

@[simp] theorem Base.sub_id {n} (b : Base n) : b.sub Base.var = b := by
  induction b <;> simp_all [sub]

theorem Base.sub_comp {n m k} (b : Base n) (ρ : Fin n → Base m) (τ : Fin m → Base k) :
    (b.sub ρ).sub τ = b.sub (fun i => (ρ i).sub τ) := by
  induction b <;> simp_all [sub]

inductive Ctx : Nat → Type where
  | nil : Ctx 0
  | base {n} : Ctx n → Ctx (n+1)
  | family {n} : Ctx n → Base n → Ctx n

/-- Dependent variables are finite paths into a telescope. -/
inductive DVar : {n : Nat} → Ctx n → Type where
  | top {n} {Γ : Ctx n} {b : Base n} : DVar (.family Γ b)
  | family {n} {Γ : Ctx n} {b : Base n} : DVar Γ → DVar (.family Γ b)
  | base {n} {Γ : Ctx n} : DVar Γ → DVar (.base Γ)

def DVar.type {n} {Γ : Ctx n} : DVar Γ → Base n
  | .top (b := b) => b
  | .family v => v.type
  | .base v => v.type.wk

inductive Dep {n} (Γ : Ctx n) where
  | var : DVar Γ → Dep Γ
  | point : Dep Γ

def Dep.type {n} {Γ : Ctx n} : Dep Γ → Base n
  | .var v => v.type
  | .point => .zero

inductive Ty (n : Nat) where
  | base : Ty n
  | family : Base n → Ty n
  deriving DecidableEq

abbrev Tm {n} (Γ : Ctx n) : Ty n → Type
  | .base => Base n
  | .family b => {t : Dep Γ // t.type = b}

/-- A substitution assigns algebraic base expressions to the finitely many
base variables and dependent expressions to the finitely many dependent paths.
The certificate checks source types, with no reference to an interpretation. -/
structure Sub {m n} (Δ : Ctx m) (Γ : Ctx n) where
  base : Fin n → Base m
  dep : DVar Γ → Dep Δ
  typed : ∀ v, (dep v).type = v.type.sub base

namespace Sub
variable {l m n k : Nat} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx l} {Ω : Ctx k}

def depSub (σ : Sub Δ Γ) : Dep Γ → Dep Δ
  | .var v => σ.dep v
  | .point => .point

@[simp] theorem depSub_type (σ : Sub Δ Γ) (t : Dep Γ) :
    (σ.depSub t).type = t.type.sub σ.base := by
  cases t with
  | var v => exact σ.typed v
  | point => rfl

def tySub (σ : Sub Δ Γ) : Ty n → Ty m
  | .base => .base
  | .family b => .family (b.sub σ.base)

def tmSub (σ : Sub Δ Γ) {A : Ty n} : Tm Γ A → Tm Δ (σ.tySub A) := by
  cases A with
  | base => exact fun t => t.sub σ.base
  | family b => exact fun t => ⟨σ.depSub t.val, (σ.depSub_type t.val).trans (congrArg (Base.sub σ.base) t.property)⟩

def id (Γ : Ctx n) : Sub Γ Γ where
  base := Base.var
  dep := Dep.var
  typed v := (Base.sub_id v.type).symm

def comp (σ : Sub Δ Γ) (τ : Sub Ξ Δ) : Sub Ξ Γ where
  base i := (σ.base i).sub τ.base
  dep v := τ.depSub (σ.dep v)
  typed v := (τ.depSub_type (σ.dep v)).trans
    ((congrArg (Base.sub τ.base) (σ.typed v)).trans (Base.sub_comp v.type σ.base τ.base))

@[ext] theorem ext {σ τ : Sub Δ Γ} (hb : σ.base = τ.base) (hd : σ.dep = τ.dep) : σ = τ := by
  cases σ
  cases τ
  cases hb
  cases hd
  rfl

@[simp] theorem depSub_id (t : Dep Γ) : (id Γ).depSub t = t := by cases t <;> rfl
@[simp] theorem depSub_comp (σ : Sub Δ Γ) (τ : Sub Ξ Δ) (t : Dep Γ) :
    (comp σ τ).depSub t = τ.depSub (σ.depSub t) := by cases t <;> rfl

@[simp] theorem comp_id (σ : Sub Δ Γ) : comp σ (id Δ) = σ := by
  apply ext
  · funext i; exact Base.sub_id _
  · funext v; exact depSub_id _
@[simp] theorem id_comp (σ : Sub Δ Γ) : comp (id Γ) σ = σ := rfl

theorem comp_assoc (σ : Sub Δ Γ) (τ : Sub Ξ Δ) (υ : Sub Ω Ξ) :
    comp (comp σ τ) υ = comp σ (comp τ υ) := by
  apply ext
  · funext i; exact Base.sub_comp _ _ _
  · funext v; exact (depSub_comp τ υ (σ.dep v)).symm

/-- Projection from a dependent extension. -/
def p (Γ : Ctx n) (b : Base n) : Sub (.family Γ b) Γ where
  base := Base.var
  dep v := .var (.family v)
  typed v := (Base.sub_id v.type).symm

def q (Γ : Ctx n) (b : Base n) : Tm (.family Γ b) (.family b) := ⟨.var .top, rfl⟩

def pair (σ : Sub Δ Γ) (b : Base n) (t : Tm Δ (.family (b.sub σ.base))) : Sub Δ (.family Γ b) where
  base := σ.base
  dep
    | .top => t.val
    | .family v => σ.dep v
  typed
    | .top => t.property
    | .family v => σ.typed v

@[simp] theorem p_pair (σ : Sub Δ Γ) (b : Base n) (t : Tm Δ (.family (b.sub σ.base))) :
    comp (p Γ b) (pair σ b t) = σ := rfl
@[simp] theorem q_pair (σ : Sub Δ Γ) (b : Base n) (t : Tm Δ (.family (b.sub σ.base))) :
    (pair σ b t).depSub (.var .top) = t.val := rfl

theorem pair_eta (σ : Sub Δ (.family Γ b)) :
    pair (comp (p Γ b) σ) b ⟨σ.dep .top, σ.typed .top⟩ = σ := by
  apply ext
  · rfl
  · funext v
    cases v <;> rfl

/-- Lift is derived from projection, composition, the generic variable and pairing. -/
def lift (σ : Sub Δ Γ) (b : Base n) : Sub (.family Δ (b.sub σ.base)) (.family Γ b) :=
  pair (comp σ (p Δ (b.sub σ.base))) b
    ⟨.var .top, by change b.sub σ.base = b.sub (fun i => (σ.base i).sub Base.var); simp⟩

theorem pair_comp (σ : Sub Δ Γ) (τ : Sub Ξ Δ) (b : Base n)
    (t : Tm Δ (.family (b.sub σ.base))) :
    comp (pair σ b t) τ = pair (comp σ τ) b
      ⟨τ.depSub t.val, (τ.depSub_type t.val).trans
        ((congrArg (Base.sub τ.base) t.property).trans (Base.sub_comp b σ.base τ.base))⟩ := by
  apply ext
  · rfl
  · funext v; cases v <;> rfl

/-- Normalized weakening of a base expression under a paired assignment. -/
theorem wk_sub (b : Base n) (ρ : Fin n → Base m) (a : Base m) :
    b.wk.sub (Fin.cases a ρ) = b.sub ρ := by
  rw [Base.wk, Base.sub_comp]
  rfl

def pBase (Γ : Ctx n) : Sub (.base Γ) Γ where
  base i := .var i.succ
  dep v := .var (.base v)
  typed _ := rfl

def qBase (Γ : Ctx n) : Tm (.base Γ) .base := .var 0

def pairBase (σ : Sub Δ Γ) (b : Base m) : Sub Δ (.base Γ) where
  base := Fin.cases b σ.base
  dep | .base v => σ.dep v
  typed | .base v => (σ.typed v).trans (wk_sub v.type σ.base b).symm

@[simp] theorem pBase_pair (σ : Sub Δ Γ) (b : Base m) : comp (pBase Γ) (pairBase σ b) = σ := rfl
@[simp] theorem qBase_pair (σ : Sub Δ Γ) (b : Base m) :
    (qBase Γ).sub (pairBase σ b).base = b := rfl

theorem pairBase_eta (σ : Sub Δ (.base Γ)) : pairBase (comp (pBase Γ) σ) (σ.base 0) = σ := by
  apply ext
  · funext i; exact Fin.cases rfl (fun _ => rfl) i
  · funext v; cases v; rfl

end Sub

/-- Equality is generated on source expressions only. -/
inductive BaseEq {n} : Base n → Base n → Prop where
  | refl (b) : BaseEq b b
  | symm : BaseEq a b → BaseEq b a
  | trans : BaseEq a b → BaseEq b c → BaseEq a c
  | neg : BaseEq a b → BaseEq (.neg a) (.neg b)

inductive DepEq {n} {Γ : Ctx n} : Dep Γ → Dep Γ → Prop where
  | refl (a) : DepEq a a
  | symm : DepEq a b → DepEq b a
  | trans : DepEq a b → DepEq b c → DepEq a c

inductive SubEq {m n} {Δ : Ctx m} {Γ : Ctx n} : Sub Δ Γ → Sub Δ Γ → Prop where
  | refl (σ) : SubEq σ σ
  | symm : SubEq σ τ → SubEq τ σ
  | trans : SubEq σ τ → SubEq τ υ → SubEq σ υ
  | assignments {σ τ} : (∀ i, BaseEq (σ.base i) (τ.base i)) →
      (∀ v, DepEq (σ.dep v) (τ.dep v)) → SubEq σ τ

/-- Equality of algebraic expressions is sound in the source syntax itself;
there is no rule admitting an equality supplied by a semantic model. -/
theorem BaseEq.literal {n} {a b : Base n} (h : BaseEq a b) : a = b := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | neg _ ih => exact congrArg Base.neg ih

theorem DepEq.literal {n} {Γ : Ctx n} {a b : Dep Γ} (h : DepEq a b) : a = b := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik

theorem SubEq.literal {m n} {Δ : Ctx m} {Γ : Ctx n} {σ τ : Sub Δ Γ} (h : SubEq σ τ) : σ = τ := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih ik => exact ih.trans ik
  | assignments hb hd => exact Sub.ext (funext fun i => (hb i).literal) (funext fun v => (hd v).literal)

theorem SubEq.ofLiteral {m n} {Δ : Ctx m} {Γ : Ctx n} {σ τ : Sub Δ Γ} (h : σ = τ) : SubEq σ τ := by
  cases h
  exact .refl _

theorem SubEq.comp_congr {l m n} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx l}
    {σ σ' : Sub Δ Γ} {τ τ' : Sub Ξ Δ} (h : SubEq σ σ') (k : SubEq τ τ') :
    SubEq (Sub.comp σ τ) (Sub.comp σ' τ') := ofLiteral (by rw [h.literal, k.literal])

/-- Derived pairing naturality: only assignment congruence and reflexivity are
used after source substitution normalization; it is not a primitive rule. -/
theorem pairing_naturality {l m n} {Γ : Ctx n} {Δ : Ctx m} {Ξ : Ctx l}
    (σ : Sub Δ Γ) (τ : Sub Ξ Δ) (b : Base n) (t : Tm Δ (.family (b.sub σ.base))) :
    SubEq (Sub.comp (Sub.pair σ b t) τ) (Sub.pair (Sub.comp σ τ) b
      ⟨τ.depSub t.val, (τ.depSub_type t.val).trans
        ((congrArg (Base.sub τ.base) t.property).trans (Base.sub_comp b σ.base τ.base))⟩) := by
  apply SubEq.assignments
  · intro i; exact .refl _
  · intro v; cases v <;> exact .refl _

end SquareKit.Internal.DependentStructural
