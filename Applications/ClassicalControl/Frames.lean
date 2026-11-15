import Applications.ClassicalControl.Machine
import Applications.ClassicalControl.TargetSyntax

/-! A separate machine with explicit data frames. Dispatch is a first-order
operation; the source callback cells store functions. -/
namespace ClassicalControl
namespace Target

def dispatch (k : Term 0) (L : List Nat) (j : Nat) (O : List Nat) : Value → Term 0
  | .odd h => .walk k L (j+1) (O++[h])
  | _ => .stuck

inductive State where
  | run : Term 0 → Stack → State
  | deliver : List Nat → Value → State

inductive Step : State → State → Prop where
  | app : Step (.run (.app t u) π) (.run t (.arg u π))
  | beta : Step (.run (.lam b) (.arg u π)) (.run (b.subst (single u)) π)
  | capture : Step (.run .cc (.arg t π)) (.run t (.arg (.saved π) π))
  | restore : Step (.run (.saved π) (.arg u ρ)) (.run u π)
  | next : Step (.run (.ret v) (.next k L j O π)) (.run (dispatch k L j O v) π)
  | output : Step (.run (.ret v) (.out L)) (.deliver L v)
  | walk (h : j < L.length) : Step (.run (.walk k L j O) π)
      (.run (.test k L j O) (.next k L j O π))
  | exhausted : Step (.run (.walk k L L.length O) π) (.run (.ret (.none O)) π)
  | odd (h : L[j]? = some (2*a+1)) : Step (.run (.test k L j O) π) (.run (.ret (.odd a)) π)
  | even (h : L[j]? = some (2*a)) : Step (.run (.test k L j O) π)
      (.run k (.arg (.ret (.found j (2*a) a O)) π))

abbrev Runs := Relation.ReflTransGen Step
end Target

namespace Representation
mutual
inductive TermRel : Source.Term n → Target.Term n → Prop where
  | var : TermRel (.var i) (.var i)
  | lam : TermRel b b' → TermRel (.lam b) (.lam b')
  | app : TermRel t t' → TermRel u u' → TermRel (.app t u) (.app t' u')
  | cc : TermRel .cc .cc
  | saved : StackRel π π' → TermRel (.saved π) (.saved π')
  | walk : TermRel k k' → TermRel (.walk k L j O) (.walk k' L j O)
  | test : TermRel k k' → TermRel (.test k L j O) (.test k' L j O)
  | ret : TermRel (.ret v) (.ret v)
  | stuck : TermRel .stuck .stuck
inductive StackRel : Source.Stack → Target.Stack → Prop where
  | halt : StackRel .halt .halt
  | out : StackRel (.out L) (.out L)
  | arg : TermRel t t' → StackRel π π' → StackRel (.arg t π) (.arg t' π')
  | callback : TermRel k k' → StackRel π π' →
      (∀ v, f v = Source.callback k L j O v) →
      StackRel (.cb f π) (.next k' L j O π')
end

/-- The relation admits precisely callbacks with the displayed family behavior. -/
theorem callback_pointwise {k k' L j O} {f : Value → Source.Term 0} (hk : TermRel k k')
    (hf : ∀ v, f v = Source.callback k L j O v) (v : Value) :
    TermRel (f v) (Target.dispatch k' L j O v) := by
  rw [hf]
  cases v with
  | found => exact .stuck
  | none => exact .stuck
  | odd => exact .walk hk

theorem rename {t : Source.Term n} {t' : Target.Term n} (h : TermRel t t')
    (f : Fin n → Fin m) : TermRel (t.rename f) (t'.rename f) := by
  induction t using Source.Term.induct generalizing m with
  | var => cases h; exact .var
  | lam b ih => cases h with | lam hb => exact .lam (ih hb _)
  | app t u it iu => cases h with | app ht hu => exact .app (it ht _) (iu hu _)
  | cc => cases h; exact .cc
  | saved π => cases h with | saved hp => exact .saved hp
  | walk k L j O ih => cases h with | walk hk => exact .walk (ih hk _)
  | test k L j O ih => cases h with | test hk => exact .test (ih hk _)
  | ret => cases h; exact .ret
  | stuck => cases h; exact .stuck
  | last => cases h

/-- Capture-avoiding substitution for all open mixed terms, including scanner k. -/
theorem subst {t : Source.Term n} {t' : Target.Term n} (h : TermRel t t')
    (σ : Fin n → Source.Term m) (τ : Fin n → Target.Term m)
    (hστ : ∀ i, TermRel (σ i) (τ i)) : TermRel (t.subst σ) (t'.subst τ) := by
  induction t using Source.Term.induct generalizing m with
  | var i => cases h; exact hστ i
  | lam b ih =>
    cases h with | lam hb =>
      apply TermRel.lam
      apply ih hb _ _
      intro i; refine Fin.cases ?_ (fun i => ?_) i
      · exact .var
      · exact rename (hστ i) Fin.succ
  | app t u it iu => cases h with | app ht hu => exact .app (it ht _ _ hστ) (iu hu _ _ hστ)
  | cc => cases h; exact .cc
  | saved π => cases h with | saved hp => exact .saved hp
  | walk k L j O ih => cases h with | walk hk => exact .walk (ih hk _ _ hστ)
  | test k L j O ih => cases h with | test hk => exact .test (ih hk _ _ hστ)
  | ret => cases h; exact .ret
  | stuck => cases h; exact .stuck
  | last => cases h

theorem beta_subst {b : Source.Term 1} {b' : Target.Term 1} {u u'}
    (hb : TermRel b b') (hu : TermRel u u') :
    TermRel (b.subst (Source.single u)) (b'.subst (Target.single u')) := by
  apply subst hb _ _
  intro i; refine Fin.cases ?_ (fun i => Fin.elim0 i) i
  exact hu

inductive StateRel : Source.State → Target.State → Prop where
  | run : TermRel t t' → StackRel π π' → StateRel (.run t π) (.run t' π')
  | deliver : StateRel (.deliver L v) (.deliver L v)


/-- Each source step has one target step, retaining all saved stacks and raw data. -/
theorem forward {s s' : Source.State} {t : Target.State}
    (h : Source.Step s s') (hr : StateRel s t) :
    ∃ t', Target.Step t t' ∧ StateRel s' t' := by
  cases h with
  | app =>
    cases hr with | run ht hp =>
      cases ht with | app ht hu => exact ⟨_, .app, .run ht (.arg hu hp)⟩
  | beta =>
    cases hr with | run ht hp =>
      cases ht with | lam hb =>
        cases hp with | arg hu hp => exact ⟨_, .beta, .run (beta_subst hb hu) hp⟩
  | capture =>
    cases hr with | run ht hp =>
      cases ht
      cases hp with | arg hu hp => exact ⟨_, .capture, .run hu (.arg (.saved hp) hp)⟩
  | restore =>
    cases hr with | run ht hp =>
      cases ht with | saved hs =>
        cases hp with | arg hu _ => exact ⟨_, .restore, .run hu hs⟩
  | callback =>
    cases hr with | run ht hp =>
      cases ht
      cases hp with | callback hk hp hf => exact ⟨_, .next, .run (callback_pointwise hk hf _) hp⟩
  | output =>
    cases hr with | run ht hp => cases ht; cases hp; exact ⟨_, .output, .deliver⟩
  | walk hj =>
    cases hr with | run ht hp =>
      cases ht with | walk hk => exact ⟨_, .walk hj, .run (.test hk) (.callback hk hp (fun _ => rfl))⟩
  | exhausted =>
    cases hr with | run ht hp => cases ht; exact ⟨_, .exhausted, .run .ret hp⟩
  | odd he =>
    cases hr with | run ht hp => cases ht; exact ⟨_, .odd he, .run .ret hp⟩
  | even he =>
    cases hr with | run ht hp =>
      cases ht with | test hk => exact ⟨_, .even he, .run hk (.arg .ret hp)⟩
  | lastOdd | lastEven | lastEnd => cases hr with | run ht _ => cases ht

/-- The reverse simulation is restricted by the same generated-family relation. -/
theorem backward {s : Source.State} {t t' : Target.State}
    (h : Target.Step t t') (hr : StateRel s t) :
    ∃ s', Source.Step s s' ∧ StateRel s' t' := by
  cases h with
  | app =>
    cases hr with | run ht hp =>
      cases ht with | app ht hu => exact ⟨_, .app, .run ht (.arg hu hp)⟩
  | beta =>
    cases hr with | run ht hp =>
      cases ht with | lam hb =>
        cases hp with | arg hu hp => exact ⟨_, .beta, .run (beta_subst hb hu) hp⟩
  | capture =>
    cases hr with | run ht hp =>
      cases ht
      cases hp with | arg hu hp => exact ⟨_, .capture, .run hu (.arg (.saved hp) hp)⟩
  | restore =>
    cases hr with | run ht hp =>
      cases ht with | saved hs =>
        cases hp with | arg hu _ => exact ⟨_, .restore, .run hu hs⟩
  | next =>
    cases hr with | run ht hp =>
      cases ht
      cases hp with | callback hk hp hf => exact ⟨_, .callback ⟨_, _, _, _, hf⟩, .run (callback_pointwise hk hf _) hp⟩
  | output =>
    cases hr with | run ht hp => cases ht; cases hp; exact ⟨_, .output, .deliver⟩
  | walk hj =>
    cases hr with | run ht hp =>
      cases ht with | walk hk => exact ⟨_, .walk hj, .run (.test hk) (.callback hk hp (fun _ => rfl))⟩
  | exhausted =>
    cases hr with | run ht hp => cases ht; exact ⟨_, .exhausted, .run .ret hp⟩
  | odd he =>
    cases hr with | run ht hp => cases ht; exact ⟨_, .odd he, .run .ret hp⟩
  | even he =>
    cases hr with | run ht hp =>
      cases ht with | test hk => exact ⟨_, .even he, .run hk (.arg .ret hp)⟩

theorem forward_runs {s s' : Source.State} {t : Target.State}
    (h : Source.Runs s s') (hr : StateRel s t) :
    ∃ t', Target.Runs t t' ∧ StateRel s' t' := by
  induction h generalizing t with
  | refl => exact ⟨_, .refl, hr⟩
  | tail path step ih =>
    obtain ⟨u, path', hu⟩ := ih hr
    obtain ⟨v, step', hv⟩ := forward step hu
    exact ⟨v, path'.tail step', hv⟩

theorem backward_runs {s : Source.State} {t t' : Target.State}
    (h : Target.Runs t t') (hr : StateRel s t) :
    ∃ s', Source.Runs s s' ∧ StateRel s' t' := by
  induction h generalizing s with
  | refl => exact ⟨_, .refl, hr⟩
  | tail path step ih =>
    obtain ⟨u, path', hu⟩ := ih hr
    obtain ⟨v, step', hv⟩ := backward step hu
    exact ⟨v, path'.tail step', hv⟩

/-- Deliveries retain every component of the certificate. -/
theorem observations {s : Source.State} {t : Target.State} (hr : StateRel s t)
    (L : List Nat) (v : Value) :
    Source.Runs s (.deliver L v) ↔ Target.Runs t (.deliver L v) := by
  constructor
  · intro h
    obtain ⟨u, hu, hr⟩ := forward_runs h hr
    cases hr; exact hu
  · intro h
    obtain ⟨u, hu, hr⟩ := backward_runs h hr
    cases hr; exact hu

/-- Accessibility transports through the reverse step simulation. -/
theorem target_normalizes {s : Source.State} {t : Target.State}
    (hs : Acc (fun s' s => Source.Step s s') s) (hr : StateRel s t) :
    Acc (fun t' t => Target.Step t t') t := by
  induction hs generalizing t with
  | intro s _ ih =>
    constructor
    intro t' h
    obtain ⟨s', hs', hr'⟩ := backward h hr
    exact ih s' hs' hr'

end Representation
end ClassicalControl
