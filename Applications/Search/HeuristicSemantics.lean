import Applications.Search.HeuristicCore

/-! # Finite source evaluations and budget-independent observations -/
set_option autoImplicit false
set_option warningAsError true
namespace Search.Heuristic
universe u z
variable {V : Type u} [DecidableEq V]

inductive Eval (Q : Frontier.{u,z} V) (mode : Mode) (g : Graph V)
    (h : Heuristic V) (goal : V → Bool) : Store V → Q.Carrier → Option (Path V) → Prop where
  | empty {st : Store V} {q : Q.Carrier} : Q.remove q = none → Eval Q mode g h goal st q none
  | solved {st : Store V} {q r : Q.Carrier} {e : Path V × Nat} :
      Q.remove q = some (e,r) → goal e.1.vertex = true → Eval Q mode g h goal st q (some e.1)
  | skip {st : Store V} {q r : Q.Carrier} {e : Path V × Nat} {out : Option (Path V)} :
      Q.remove q = some (e,r) → goal e.1.vertex = false → skip mode st e.1 = true →
      Eval Q mode g h goal st r out → Eval Q mode g h goal st q out
  | expand {st : Store V} {q r : Q.Carrier} {e : Path V × Nat} {out : Option (Path V)} :
      Q.remove q = some (e,r) → goal e.1.vertex = false → skip mode st e.1 = false →
      Eval Q mode g h goal (record mode st e.1) (Q.add (children mode g h st e.1) r) out →
      Eval Q mode g h goal st q out

theorem run_eval (Q : Frontier.{u,z} V) (mode : Mode) (g : Graph V)
    (h : Heuristic V) (goal : V → Bool) (fuel : Nat) (st : Store V) (q : Q.Carrier)
    {out : Option (Path V)} (hr : run Q mode g h goal fuel st q = some out) :
    Eval Q mode g h goal st q out := by
  induction fuel generalizing st q with
  | zero => simp [run] at hr
  | succ fuel ih =>
    cases hd : Q.remove q with
    | none =>
      simp only [run,hd,Option.some.injEq] at hr
      subst out
      exact .empty hd
    | some z =>
      rcases z with ⟨e,r⟩
      simp only [run,hd] at hr
      split at hr
      next hg =>
        simp only [Option.some.injEq] at hr
        subst out
        exact .solved hd hg
      next hg =>
        have hg' := Bool.eq_false_iff.mpr hg
        split at hr
        next hs => exact .skip hd hg' hs (ih st r hr)
        next hs => exact .expand hd hg' (Bool.eq_false_iff.mpr hs) (ih _ _ hr)

theorem eval_run (Q : Frontier.{u,z} V) (mode : Mode) (g : Graph V)
    (h : Heuristic V) (goal : V → Bool) {st : Store V} {q : Q.Carrier}
    {out : Option (Path V)} (he : Eval Q mode g h goal st q out) :
    ∃ fuel, run Q mode g h goal fuel st q = some out := by
  induction he with
  | empty hd => exact ⟨1,by simp [run,hd]⟩
  | solved hd hg => exact ⟨1,by simp [run,hd,hg]⟩
  | skip hd hg hs he ih =>
    obtain ⟨fuel,hr⟩ := ih
    exact ⟨fuel+1,by simpa [run,hd,hg,hs] using hr⟩
  | expand hd hg hs he ih =>
    obtain ⟨fuel,hr⟩ := ih
    exact ⟨fuel+1,by simpa [run,hd,hg,hs] using hr⟩

theorem run_add_budget (Q : Frontier.{u,z} V) (mode : Mode) (g : Graph V)
    (h : Heuristic V) (goal : V → Bool) (fuel extra : Nat) (st : Store V) (q : Q.Carrier)
    {out : Option (Path V)} (hr : run Q mode g h goal fuel st q = some out) :
    run Q mode g h goal (fuel+extra) st q = some out := by
  induction fuel generalizing st q with
  | zero => simp [run] at hr
  | succ fuel ih =>
    rw [Nat.succ_add]
    cases hd : Q.remove q with
    | none => simpa [run,hd] using hr
    | some z =>
      rcases z with ⟨e,r⟩
      simp only [run,hd] at hr ⊢
      split at hr
      next hg => simp [hg] at *; exact hr
      next hg =>
        simp only [hg]
        split at hr
        next hs => simpa [hs] using ih st r hr
        next hs => simpa [hs] using ih _ _ hr

theorem run_unique (Q : Frontier.{u,z} V) (mode : Mode) (g : Graph V)
    (h : Heuristic V) (goal : V → Bool) (a b : Nat) (st : Store V) (q : Q.Carrier)
    {x y : Option (Path V)} (hx : run Q mode g h goal a st q = some x)
    (hy : run Q mode g h goal b st q = some y) : x = y := by
  have h₁ := run_add_budget Q mode g h goal a b st q hx
  have h₂ := run_add_budget Q mode g h goal b a st q hy
  rw [Nat.add_comm b a,h₁] at h₂
  exact Option.some.inj h₂

theorem eval_unique (Q : Frontier.{u,z} V) (mode : Mode) (g : Graph V)
    (h : Heuristic V) (goal : V → Bool) {st : Store V} {q : Q.Carrier}
    {x y : Option (Path V)} (hx : Eval Q mode g h goal st q x)
    (hy : Eval Q mode g h goal st q y) : x = y := by
  obtain ⟨a,ha⟩ := eval_run Q mode g h goal hx
  obtain ⟨b,hb⟩ := eval_run Q mode g h goal hy
  exact run_unique Q mode g h goal a b st q ha hb

end Search.Heuristic
