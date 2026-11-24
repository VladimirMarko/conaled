import Applications.MatchingLogic.Syntax
import Mathlib.Tactic

namespace MatchingLogic
universe u
structure Model where
  Carrier : SortCode → Type u
  nonempty : ∀ s, Nonempty (Carrier s)
  zero : Set (Carrier .nat)
  symbol : Symbol s t → Carrier s → Set (Carrier t)
  defined : ∀ s t (a : Carrier s), symbol (.defined s t) a = Set.univ

abbrev Valuation (M : Model.{u}) (Γ : Context) := ∀ {s}, Var Γ s → M.Carrier s

def Valuation.extend {M : Model} (ρ : Valuation M Γ) (a : M.Carrier t) : Valuation M (t :: Γ)
  | _, .here => a
  | _, .there v => ρ v

def Valuation.pull {M : Model} (r : Renaming Γ Δ) (ρ : Valuation M Δ) : Valuation M Γ := fun v => ρ (r v)
@[simp] theorem Valuation.pull_lift {M : Model} (r : Renaming Γ Δ) (ρ : Valuation M Δ) (a : M.Carrier t) :
    @Valuation.pull (t :: Γ) (t :: Δ) M r.lift (Valuation.extend ρ a) =
      @Valuation.extend Γ t M (Valuation.pull r ρ) a := by
  funext s v
  cases v <;> rfl
@[simp] theorem Valuation.pull_there {M : Model} (ρ : Valuation M Γ) (a : M.Carrier t) :
    @Valuation.pull Γ (t :: Γ) M Var.there (Valuation.extend ρ a) = @ρ := rfl

def eval (M : Model) : Pattern Γ s → Valuation M Γ → Set (M.Carrier s)
  | .var v, ρ => {ρ v}
  | .zero, _ => M.zero
  | .app f p, ρ => {d | ∃ a ∈ eval M p ρ, d ∈ M.symbol f a}
  | .neg p, ρ => (eval M p ρ)ᶜ
  | .conj p q, ρ => eval M p ρ ∩ eval M q ρ
  | .ex _ p, ρ => {d | ∃ a, d ∈ eval M p (ρ.extend a)}

theorem eval_rename (M : Model) (p : Pattern Γ s) (r : Renaming Γ Δ) (ρ : Valuation M Δ) :
    eval M (p.rename r) ρ = eval M p (ρ.pull r) := by
  induction p generalizing Δ with
  | var v => rfl
  | zero => rfl
  | app f p ih => simp only [Pattern.rename, eval, ih]
  | neg p ih => simp only [Pattern.rename, eval, ih]
  | conj p q ihp ihq => simp only [Pattern.rename, eval, ihp, ihq]
  | ex t p ih => simp only [Pattern.rename, eval, ih, Valuation.pull_lift]

theorem eval_agree (M : Model) (p : Pattern Γ s) (ρ τ : Valuation M Γ)
    (h : ∀ {t} (v : Var Γ t), Occurs v p → ρ v = τ v) : eval M p ρ = eval M p τ := by
  induction p with
  | var v => simp only [eval, h v .var]
  | zero => rfl
  | app f p ih => rw [eval, eval, ih ρ τ (fun v hv => h v (.app hv))]
  | neg p ih => rw [eval, eval, ih ρ τ (fun v hv => h v (.neg hv))]
  | conj p q ihp ihq =>
    rw [eval, eval, ihp ρ τ (fun v hv => h v (.left hv)), ihq ρ τ (fun v hv => h v (.right hv))]
  | ex t p ih =>
    have he : ∀ a, eval M p (ρ.extend a) = eval M p (τ.extend a) := by
      intro a
      apply ih
      intro s v hv
      cases v with
      | here => rfl
      | there v => exact h v (.ex hv)
    simp only [eval, he]

/-- Exactly singleton substitutions agree with element-valued environments. -/
theorem eval_subst_singleton (M : Model) (p : Pattern Γ s) (σ : Substitution Γ Δ)
    (ρ : Valuation M Δ) (τ : Valuation M Γ)
    (h : ∀ {t} (v : Var Γ t), eval M (σ v) ρ = {τ v}) :
    eval M (p.subst σ) ρ = eval M p τ := by
  induction p generalizing Δ with
  | var v => exact h v
  | zero => rfl
  | app f p ih => simp only [Pattern.subst, eval, ih σ ρ τ h]
  | neg p ih => simp only [Pattern.subst, eval, ih σ ρ τ h]
  | conj p q ihp ihq => simp only [Pattern.subst, eval, ihp σ ρ τ h, ihq σ ρ τ h]
  | ex t p ih =>
    have he : ∀ a, eval M (p.subst σ.lift) (ρ.extend a) = eval M p (τ.extend a) := by
      intro a
      apply ih
      intro s v
      cases v with
      | here => rfl
      | there v => simpa only [Substitution.lift, eval_rename, Valuation.pull_there, Valuation.extend] using h v
    simp only [Pattern.subst, eval, he]

/-- Equal replacement sets give congruent substituted contexts, even when they
are not singletons. This conclusion is distinct from element substitution. -/
theorem eval_subst_congr (M : Model) (p : Pattern Γ s) (σ τ : Substitution Γ Δ)
    (ρ : Valuation M Δ) (h : ∀ {t} (v : Var Γ t), eval M (σ v) ρ = eval M (τ v) ρ) :
    eval M (p.subst σ) ρ = eval M (p.subst τ) ρ := by
  induction p generalizing Δ with
  | var v => exact h v
  | zero => rfl
  | app f p ih => simp only [Pattern.subst, eval, ih σ τ ρ h]
  | neg p ih => simp only [Pattern.subst, eval, ih σ τ ρ h]
  | conj p q ihp ihq => simp only [Pattern.subst, eval, ihp σ τ ρ h, ihq σ τ ρ h]
  | ex t p ih =>
    have he : ∀ a, eval M (p.subst σ.lift) (ρ.extend a) = eval M (p.subst τ.lift) (ρ.extend a) := by
      intro a
      apply ih
      intro s v
      cases v with
      | here => rfl
      | there v => simpa only [Substitution.lift, eval_rename, Valuation.pull_there] using h v
    simp only [Pattern.subst, eval, he]

theorem eval_substOne (M : Model) (p : Pattern (t :: Γ) s) (q : Pattern Γ t)
    (ρ : Valuation M Γ) (a : M.Carrier t) (h : eval M q ρ = {a}) :
    eval M (p.substOne q) ρ = eval M p (ρ.extend a) := by
  apply eval_subst_singleton
  intro t v
  cases v with
  | here => exact h
  | there v => rfl

theorem eval_substOne_congr (M : Model) (p : Pattern (t :: Γ) s) (q r : Pattern Γ t)
    (ρ : Valuation M Γ) (h : eval M q ρ = eval M r ρ) :
    eval M (p.substOne q) ρ = eval M (p.substOne r) ρ := by
  apply eval_subst_congr
  intro t v
  cases v with
  | here => exact h
  | there v => rfl

@[simp] theorem mem_eval_disj (M : Model) (p q : Pattern Γ s) (ρ : Valuation M Γ) (d : M.Carrier s) :
    d ∈ eval M (p.disj q) ρ ↔ d ∈ eval M p ρ ∨ d ∈ eval M q ρ := by
  classical
  simp only [Pattern.disj, eval, Set.mem_compl_iff, Set.mem_inter_iff]
  tauto
@[simp] theorem mem_eval_imp (M : Model) (p q : Pattern Γ s) (ρ : Valuation M Γ) (d : M.Carrier s) :
    d ∈ eval M (p.imp q) ρ ↔ (d ∈ eval M p ρ → d ∈ eval M q ρ) := by
  classical
  simp [Pattern.imp, eval]
@[simp] theorem mem_eval_iff (M : Model) (p q : Pattern Γ s) (ρ : Valuation M Γ) (d : M.Carrier s) :
    d ∈ eval M (p.iff q) ρ ↔ (d ∈ eval M p ρ ↔ d ∈ eval M q ρ) := by
  simp only [Pattern.iff, eval, Set.mem_inter_iff, mem_eval_imp]
  tauto
@[simp] theorem mem_eval_all (M : Model) (p : Pattern (t :: Γ) s) (ρ : Valuation M Γ) (d : M.Carrier s) :
    d ∈ eval M p.all ρ ↔ ∀ a, d ∈ eval M p (ρ.extend a) := by
  classical
  simp [Pattern.all, eval]
@[simp] theorem mem_eval_ceil (M : Model) (p : Pattern Γ s) (ρ : Valuation M Γ) (d : M.Carrier t) :
    d ∈ eval M (p.ceil t) ρ ↔ (eval M p ρ).Nonempty := by
  simp [Pattern.ceil, eval, M.defined, Set.Nonempty]
@[simp] theorem mem_eval_floor (M : Model) (p : Pattern Γ s) (ρ : Valuation M Γ) (d : M.Carrier t) :
    d ∈ eval M (p.floor t) ρ ↔ eval M p ρ = Set.univ := by
  classical
  simp only [Pattern.floor, eval, Set.mem_compl_iff, mem_eval_ceil, Set.nonempty_compl, not_not]
@[simp] theorem mem_eval_equal (M : Model) (p q : Pattern Γ s) (ρ : Valuation M Γ) (d : M.Carrier t) :
    d ∈ eval M (p.equal t q) ρ ↔ eval M p ρ = eval M q ρ := by
  rw [Pattern.equal, mem_eval_floor]
  simp only [Set.ext_iff, mem_eval_iff, Set.mem_univ, iff_true]
@[simp] theorem mem_eval_member (M : Model) (v : Var Γ s) (p : Pattern Γ s) (ρ : Valuation M Γ) (d : M.Carrier t) :
    d ∈ eval M (p.member t v) ρ ↔ ρ v ∈ eval M p ρ := by
  simp [Pattern.member, mem_eval_ceil, eval, Set.Nonempty]
@[simp] theorem mem_eval_functional (M : Model) (q : Pattern Γ s) (ρ : Valuation M Γ) (d : M.Carrier t) :
    d ∈ eval M (q.functional t) ρ ↔ ∃ a, eval M q ρ = {a} := by
  simp [Pattern.functional, eval, mem_eval_equal, eval_rename, Valuation.pull_there, Valuation.extend]

def Valid (M : Model) (p : Pattern Γ s) : Prop := ∀ ρ, eval M p ρ = Set.univ

theorem valid_iff (M : Model) (p : Pattern Γ s) : Valid M p ↔ ∀ ρ d, d ∈ eval M p ρ := by
  simp [Valid, Set.eq_univ_iff_forall]
end MatchingLogic
