import SquareKit.Temporal.Finite

/-! Relations on finite certificates retain every wait and the terminal index. -/
namespace Temporal.Until
universe u v w u' v'
variable {A B : Nat → Type u} {C D : Nat → Type v} {E F : Nat → Type w}

inductive Rel (RA : ∀ n, A n → C n → Prop) (RB : ∀ n, B n → D n → Prop) :
    {n : Nat} → Until A B n → Until C D n → Prop where
  | now {b d} : RB n b d → Rel RA RB (.now b) (.now d)
  | wait {a c t s} : RA n a c → Rel RA RB t s → Rel RA RB (.wait a t) (.wait c s)

namespace Rel
variable {RA : ∀ n, A n → C n → Prop} {RB : ∀ n, B n → D n → Prop}

theorem horizon_eq {t : Until A B n} {s : Until C D n} (h : Rel RA RB t s) :
    t.horizon = s.horizon := by
  induction h with
  | now => rfl
  | wait _ _ ih => exact congrArg (· + 1) ih

theorem window_horizon_eq {t : Until A B n} {s : Until C D n} (h : Rel RA RB t s) :
    t.window.1 = s.window.1 := by simpa using h.horizon_eq

theorem refl (t : Until A B n) : Rel (fun _ => Eq) (fun _ => Eq) t t := by
  induction t with
  | now b => exact .now rfl
  | wait a t ih => exact .wait rfl ih

/-- Each side can map into a different carrier, provided its pointwise relations agree. -/
theorem map {A' B' : Nat → Type u'} {C' D' : Nat → Type v'}
    {RA' : ∀ n, A' n → C' n → Prop} {RB' : ∀ n, B' n → D' n → Prop}
    (f : ∀ n, A n → A' n) (g : ∀ n, B n → B' n)
    (f' : ∀ n, C n → C' n) (g' : ∀ n, D n → D' n)
    (ha : ∀ n a c, RA n a c → RA' n (f n a) (f' n c))
    (hb : ∀ n b d, RB n b d → RB' n (g n b) (g' n d))
    {t : Until A B n} {s : Until C D n} (h : Rel RA RB t s) :
    Rel RA' RB' (t.map f g) (s.map f' g') := by
  induction h with
  | now h => exact .now (hb _ _ _ h)
  | wait h _ ih => exact .wait (ha _ _ _ h) ih

/-- Relational composition retains intermediate waiting and terminal witnesses. -/
theorem comp {SA : ∀ n, C n → E n → Prop} {SB : ∀ n, D n → F n → Prop}
    {t : Until A B n} {s : Until C D n} {r : Until E F n}
    (h : Rel RA RB t s) (k : Rel SA SB s r) :
    Rel (fun n a e => ∃ c, RA n a c ∧ SA n c e)
      (fun n b f => ∃ d, RB n b d ∧ SB n d f) t r := by
  induction h with
  | now h => cases k with | now k => exact .now ⟨_,h,k⟩
  | wait h _ ih => cases k with | wait k kt => exact .wait ⟨_,h,k⟩ (ih kt)

/-- Existing map identity and composition laws preserve this same certificate relation. -/
theorem map_id {t : Until A B n} {s : Until C D n} (h : Rel RA RB t s) :
    Rel RA RB (t.map (fun _ => id) (fun _ => id))
      (s.map (fun _ => id) (fun _ => id)) := by simpa using h

/-- The window presentation makes the pointwise waiting obligations explicit. -/
theorem ofWindow (n k : Nat)
    (as : (j : Fin k) → A (n+j.val)) (cs : (j : Fin k) → C (n+j.val))
    (b : B (n+k)) (d : D (n+k))
    (ha : ∀ j, RA (n+j.val) (as j) (cs j)) (hb : RB (n+k) b d) :
    Rel RA RB (Until.ofWindow n k as b) (Until.ofWindow n k cs d) := by
  induction k generalizing n with
  | zero => exact .now hb
  | succ k ih =>
    apply Rel.wait
    · exact ha ⟨0, by omega⟩
    · apply ih
      · intro j
        have e : n + j.succ.val = (n+1) + j.val := by simp [Nat.add_comm, Nat.add_left_comm]
        have transfer {i j} (e : i = j) (x : A i) (y : C i) (h : RA i x y) :
            RA j (e ▸ x) (e ▸ y) := by cases e; exact h
        simpa only [Eq.mpr, eqRec_eq_cast] using transfer e _ _ (ha j.succ)
      · have e : n + (k+1) = (n+1) + k := by omega
        have transfer {i j} (e : i = j) (x : B i) (y : D i) (h : RB i x y) :
            RB j (e ▸ x) (e ▸ y) := by cases e; exact h
        simpa only [Eq.mpr, eqRec_eq_cast] using transfer e b d hb

end Rel

/-- Constant-family terminal observation deliberately forgets the waiting horizon. -/
def terminal {X : Type u} : Until A (fun _ => X) n → X :=
  fold (fun _ => id) (fun _ _ x => x)

@[simp] theorem terminal_map {X : Type u} {Y : Type u'} {A' : Nat → Type u'}
    (f : ∀ n, A n → A' n) (g : X → Y) (t : Until A (fun _ => X) n) :
    terminal (t.map f (fun _ => g)) = g (terminal t) := by
  induction t with
  | now => rfl
  | wait _ _ ih => exact ih

end Temporal.Until
