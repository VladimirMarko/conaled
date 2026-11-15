import SquareKit.WeakMachine.Execution

/-! A related-input logical relation connects syntactic execution to Comp.
Divergence carries a finite path to a concrete self-loop, retaining the prefix
that the behavioral representation deliberately collapses. -/
namespace SquareKit.WeakMachine
open HigherOrderComparison (Ty Ctx Var Env extend empty)
open WeakHigherOrder

def Behavior (R : Term [] a → V a → Prop) (t : Term [] a) : Comp (V a) → Prop
  | .done _ v => ∃ u, Steps t u ∧ Value u ∧ R u v
  | .spin => ∃ u, Steps t u ∧ Step u u

def Related : (a : Ty) → Term [] a → V a → Prop
  | .ground, t, n => t = .lit n
  | .arr a b, t, f => ∃ body, t = .lam body ∧
      ∀ x v, Related a x v → Behavior (Related b) (beta body x) (f v)

theorem related_value (h : Related a t v) : Value t := by
  cases a with
  | ground => cases h; exact .lit
  | arr a b => obtain ⟨body,rfl,_⟩ := h; exact .lam

theorem behavior_now (h : Related a t v) : Behavior (Related a) t (.done 0 v) :=
  ⟨t,.refl,related_value h,h⟩

theorem behavior_prefix (h : Steps t u) (hu : Behavior R u c) : Behavior R t c := by
  cases c with
  | done k v => obtain ⟨w,hw,hv,hr⟩ := hu; exact ⟨w,h.trans hw,hv,hr⟩
  | spin => obtain ⟨w,hw,hs⟩ := hu; exact ⟨w,h.trans hw,hs⟩

theorem application (hf : Behavior (Related (.arr a b)) f cf)
    (hx : Behavior (Related a) x cx) :
    Behavior (Related b) (.app f x)
      (cf.bind fun g => cx.bind fun y => (g y).tick) := by
  cases cf with
  | spin =>
    obtain ⟨u,hu,hs⟩ := hf
    exact ⟨.app u x,hu.left x,.left hs⟩
  | done k g =>
    obtain ⟨vf,hfpath,hvf,body,hvfbody,hfg⟩ := hf
    subst vf
    cases cx with
    | spin =>
      obtain ⟨u,hu,hs⟩ := hx
      exact ⟨.app (.lam body) u,(hfpath.left x).trans (hu.right .lam),.right .lam hs⟩
    | done j y =>
      obtain ⟨vx,hxpath,hvx,hrx⟩ := hx
      have path : Steps (.app f x) (beta body vx) :=
        (hfpath.left x).trans ((hxpath.right .lam).trans (.cons (.beta hvx) .refl))
      have hb := behavior_prefix path (hfg vx y hrx)
      cases hg : g y <;> simpa only [Comp.bind, hg, Comp.tick, Behavior] using hb

abbrev ClosingRelated (s : Sub Γ []) (ρ : Env V Γ) :=
  ∀ {a} (v : Var Γ a), Related a (s v) (ρ v)

theorem extend_related (h : ClosingRelated s ρ) (hx : Related a x v) :
    ClosingRelated (extendSub s x) (extend ρ v) := by
  intro b w
  cases w with
  | here => exact hx
  | there w => exact h w

/-- Fundamental theorem over the original syntax and arbitrary related closing
values. No definability premise is imposed on unrelated semantic values. -/
theorem fundamental (t : Term Γ a) (s : Sub Γ []) (ρ : Env V Γ)
    (h : ClosingRelated s ρ) : Behavior (Related a) (subst s t) (run t ρ) := by
  induction t with
  | var v => exact behavior_now (h v)
  | lit n => exact behavior_now rfl
  | omega => exact ⟨.omega,.refl,.loop⟩
  | app f x ihf ihx => exact application (ihf s ρ h) (ihx s ρ h)
  | lam body ih =>
    apply behavior_now
    refine ⟨subst (liftSub s) body,rfl,?_⟩
    intro x v hx
    rw [beta_lift]
    exact ih (extendSub s x) (extend ρ v) (extend_related h hx)

theorem closed_fundamental (t : Term [] a) : Behavior (Related a) t (run t empty) := by
  have h := fundamental t (fun v => nomatch v) empty (fun v => nomatch v)
  rwa [closed_subst] at h

/-- Reusable higher-order application on related syntactic and semantic inputs. -/
theorem related_application (hf : Related (.arr a b) f g) (hx : Related a x y) :
    Behavior (Related b) (.app f x) ((g y).tick) := by
  have h := application (behavior_now hf) (behavior_now hx)
  cases hg : g y <;> simpa only [Comp.bind, hg, Comp.tick, Behavior] using h

def Returns (t : Term [] .ground) (n : Nat) : Prop := Steps t (.lit n)

theorem return_agreement (t : Term [] .ground) (n : Nat) :
    Returns t n ↔ WeakHigherOrder.Returns (run t empty) n := by
  have h := closed_fundamental t
  cases hr : run t empty with
  | spin =>
    rw [hr] at h
    obtain ⟨u,hu,hs⟩ := h
    have hi := prefix_infinite hu (self_infinite hs)
    constructor
    · intro ht; exact False.elim (terminal_not_infinite .lit ht hi)
    · intro ht; have bad := WeakHigherOrder.returns_result ht; cases bad
  | done k m =>
    rw [hr] at h
    obtain ⟨u,hu,hv,he⟩ := h
    change u = .lit m at he
    subst u
    constructor
    · intro hn
      have hm : m = n := by cases terminal_unique hu hv hn .lit; rfl
      subst m
      exact WeakHigherOrder.returns_done k n
    · intro hn
      have hm : m = n := Option.some.inj (WeakHigherOrder.returns_result hn)
      subst m
      exact hu

theorem divergence_agreement (t : Term [] a) :
    Infinite t ↔ WeakHigherOrder.Diverges (run t empty) := by
  have h := closed_fundamental t
  cases hr : run t empty with
  | spin =>
    rw [hr] at h
    obtain ⟨u,hu,hs⟩ := h
    exact ⟨fun _ => WeakHigherOrder.spin_diverges,
      fun _ => prefix_infinite hu (self_infinite hs)⟩
  | done k v =>
    rw [hr] at h
    obtain ⟨u,hu,hv,_⟩ := h
    exact ⟨fun hi => False.elim (terminal_not_infinite hv hu hi),
      fun hi => False.elim (WeakHigherOrder.done_not_diverges k v hi)⟩

theorem return_denotation (t : Term [] .ground) (n : Nat) :
    Returns t n ↔ denote t empty = some n :=
  (return_agreement t n).trans (observed_return t n)

theorem divergence_denotation (t : Term [] .ground) :
    Infinite t ↔ denote t empty = none :=
  (divergence_agreement t).trans (observed_divergence t)

theorem context_returns (c : Context Γ a [] .ground) (h : Equal t u) (n : Nat) :
    Returns (c.fill t) n ↔ Returns (c.fill u) n := by
  rw [return_denotation, return_denotation, context_congr c h empty]

theorem context_divergence (c : Context Γ a [] .ground) (h : Equal t u) :
    Infinite (c.fill t) ↔ Infinite (c.fill u) := by
  rw [divergence_denotation, divergence_denotation, context_congr c h empty]

end SquareKit.WeakMachine
