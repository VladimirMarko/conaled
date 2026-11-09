import SquareKit.WeakMachine.Adequacy

/-! Optional structural admission into the existing total fragment. -/
namespace SquareKit.WeakMachine
open HigherOrderComparison (Ty Ctx Var empty)
open WeakHigherOrder

/-- Sufficient, deliberately conservative admission: inspect even unforced bodies. -/
def NoOmega : Term Γ a → Prop
  | .var _ | .lit _ => True
  | .lam t => NoOmega t
  | .app f x => NoOmega f ∧ NoOmega x
  | .omega => False

theorem embed_admitted (t : HigherOrderComparison.Term Γ a) : NoOmega (embed t) := by
  induction t with
  | var => trivial
  | lit => trivial
  | lam t ih => exact ih
  | app f x ihf ihx => exact ⟨ihf, ihx⟩

/-- Choose the false presentation tag; no inverse claim about original tags. -/
def back : (t : Term Γ a) → NoOmega t → HigherOrderComparison.Term Γ a
  | .var v, _ => .var v
  | .lit n, _ => .lit false n
  | .lam t, h => .lam (back t h)
  | .app f x, h => .app (back f h.1) (back x h.2)
  | .omega, h => False.elim h

theorem embed_back (t : Term Γ a) (h : NoOmega t) : embed (back t h) = t := by
  induction t with
  | var => rfl
  | lit => rfl
  | lam t ih => exact congrArg Term.lam (ih h)
  | app f x ihf ihx => exact congrArg₂ Term.app (ihf h.1) (ihx h.2)
  | omega => exact False.elim h

theorem admitted_iff_image (t : Term Γ a) :
    NoOmega t ↔ ∃ s, embed s = t :=
  ⟨fun h => ⟨back t h, embed_back t h⟩, fun ⟨s, hs⟩ => hs ▸ embed_admitted s⟩

theorem NoOmega.rename {t : Term Γ a} (h : NoOmega t) (r : Ren Γ Δ) : NoOmega (rename r t) := by
  induction t generalizing Δ with
  | var => trivial
  | lit => trivial
  | omega => exact h
  | lam t ih => exact ih h _
  | app f x ihf ihx => exact ⟨ihf h.1 _, ihx h.2 _⟩

def AdmittedSub (s : Sub Γ Δ) : Prop := ∀ {a} (v : Var Γ a), NoOmega (s v)

theorem AdmittedSub.lift (h : AdmittedSub s) : AdmittedSub (liftSub (a := a) s) := by
  intro b v
  cases v with
  | here => trivial
  | there v => exact (h v).rename _

theorem NoOmega.subst {t : Term Γ a} {s : Sub Γ Δ} (h : NoOmega t) (hs : AdmittedSub s) : NoOmega (subst s t) := by
  induction t generalizing Δ with
  | var v => exact hs v
  | lit => trivial
  | omega => exact h
  | lam t ih => exact ih h hs.lift
  | app f x ihf ihx => exact ⟨ihf h.1 hs, ihx h.2 hs⟩

theorem NoOmega.beta (h : NoOmega body) (hx : NoOmega x) : NoOmega (beta body x) := by
  apply h.subst
  intro a v
  cases v with
  | here => exact hx
  | there => trivial

theorem NoOmega.step (h : NoOmega t) (hs : Step t u) : NoOmega u := by
  induction hs with
  | loop => exact h
  | left hs ih => exact ⟨ih h.1, h.2⟩
  | right hv hs ih => exact ⟨h.1, ih h.2⟩
  | beta hv => exact h.1.beta h.2

theorem NoOmega.steps (h : NoOmega t) (hs : Steps t u) : NoOmega u := by
  induction hs with
  | refl => exact h
  | cons hs rest ih => exact ih (h.step hs)

theorem embed_rename (t : HigherOrderComparison.Term Γ a) (r : Ren Γ Δ) :
    embed (HigherOrderComparison.rename r t) = rename r (embed t) := by
  induction t generalizing Δ with
  | var => rfl
  | lit => rfl
  | lam t ih => exact congrArg Term.lam (ih _)
  | app f x ihf ihx => exact congrArg₂ Term.app (ihf _) (ihx _)

theorem embed_subst (t : HigherOrderComparison.Term Γ a)
    (s : HigherOrderComparison.Sub Γ Δ) :
    embed (HigherOrderComparison.subst s t) = subst (fun v => embed (s v)) (embed t) := by
  induction t generalizing Δ with
  | var => rfl
  | lit => rfl
  | app f x ihf ihx => exact congrArg₂ Term.app (ihf _) (ihx _)
  | lam t ih =>
    simp only [HigherOrderComparison.subst, embed, subst, ih]
    congr 2
    funext a v
    cases v with
    | here => rfl
    | there v => exact embed_rename (s v) _

/-- Public home for the existing `Examples.WeakMachine.recovered` argument. -/
theorem embedded_returns (t : HigherOrderComparison.Term [] .ground) :
    Returns (embed t) (HigherOrderComparison.denote t empty) :=
  (return_denotation _ _).mpr (recovery_meaning t)

theorem admitted_returns (t : Term [] .ground) (h : NoOmega t) :
    Returns t (HigherOrderComparison.denote (back t h) empty) := by
  have hr := embedded_returns (back t h)
  rw [embed_back] at hr
  exact hr

/-- Existence of a bound is in Prop, not an extracted computable fuel algorithm.
The finite reductions and all larger-fuel executions select the same numeral. -/
theorem canonicity (t : Term [] .ground) (h : NoOmega t) :
    ∃ n, Returns t n ∧ (∀ m, Returns t m → m = n) ∧
      ∃ bound, ∀ fuel, bound ≤ fuel → execute fuel t = .terminal (.lit n) .lit := by
  obtain hr := admitted_returns t h
  refine ⟨_, hr, ?_, execute_sufficient hr .lit⟩
  intro m hm
  exact Term.lit.inj (terminal_unique hm .lit hr .lit)

end SquareKit.WeakMachine
