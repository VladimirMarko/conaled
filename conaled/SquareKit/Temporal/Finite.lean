import Mathlib.Tactic

/-!
Finite, proof-relevant temporal certificates. Processing starts at `n`; a witness
with horizon `k` carries `A` on `[n,n+k)` and `B` at `n+k`. There is no guarded
or unrestricted recursion. Ordinary clients can use these types without syntax.
-/
namespace Temporal
universe u v w

inductive Until (A B : Nat → Type u) : Nat → Type u
  | now {n} : B n → Until A B n
  | wait {n} : A n → Until A B (n + 1) → Until A B n

abbrev Eventually (B : Nat → Type u) := Until (fun _ => PUnit) B

namespace Until
variable {A B : Nat → Type u} {A' B' : Nat → Type v} {n : Nat}

def horizon : {n : Nat} → Until A B n → Nat
  | _, .now _ => 0
  | _, .wait _ t => t.horizon + 1

def fold {C : Nat → Type v} (nowC : ∀ n, B n → C n)
    (waitC : ∀ n, A n → C (n + 1) → C n) : {n : Nat} → Until A B n → C n
  | _, .now b => nowC _ b
  | _, .wait a t => waitC _ a (fold nowC waitC t)

def map (f : ∀ n, A n → A' n) (g : ∀ n, B n → B' n) :
    Until A B n → Until A' B' n := fold (fun n => Until.now ∘ g n)
      (fun n a => Until.wait (f n a))

@[simp] theorem map_now (f : ∀ n, A n → A' n) (g : ∀ n, B n → B' n) (b : B n) :
    map f g (.now b) = .now (g n b) := rfl
@[simp] theorem map_wait (f : ∀ n, A n → A' n) (g : ∀ n, B n → B' n)
    (a : A n) (t : Until A B (n+1)) :
    map f g (.wait a t) = .wait (f n a) (map f g t) := rfl
@[simp] theorem horizon_map (f : ∀ n, A n → A' n) (g : ∀ n, B n → B' n)
    (t : Until A B n) : (map f g t).horizon = t.horizon := by
  induction t <;> simp_all [horizon]
@[simp] theorem map_id (t : Until A B n) : map (fun _ => id) (fun _ => id) t = t := by
  induction t <;> simp_all
theorem map_comp {A'' B'' : Nat → Type w}
    (f : ∀ n, A n → A' n) (g : ∀ n, B n → B' n)
    (f' : ∀ n, A' n → A'' n) (g' : ∀ n, B' n → B'' n) (t : Until A B n) :
    map f' g' (map f g t) = map (fun n => f' n ∘ f n) (fun n => g' n ∘ g n) t := by
  induction t <;> simp_all

/-- An independently usable finite interval representation. -/
abbrev Window (A B : Nat → Type u) (n : Nat) :=
  (k : Nat) × ((j : Fin k) → A (n + j.val)) × B (n + k)

def window : {n : Nat} → Until A B n → Window A B n
  | _, .now b => ⟨0, (fun j => Fin.elim0 j), b⟩
  | n, .wait a t => by
    obtain ⟨k, as, b⟩ := window t
    refine ⟨k+1, ?_, ?_⟩
    · intro j
      by_cases h : j.val = 0
      · simpa [h] using a
      · have e : n + j.val = (n+1) + (j.val-1) := by omega
        exact e ▸ as ⟨j.val-1, by omega⟩
    · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using b

def ofWindow (n : Nat) : (k : Nat) → ((j : Fin k) → A (n+j.val)) → B (n+k) → Until A B n
  | 0, _, b => .now b
  | k+1, as, b => .wait (as ⟨0, by omega⟩)
      (ofWindow (n+1) k (fun j => by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using as j.succ)
        (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using b))

@[simp] theorem horizon_ofWindow (n k : Nat) (as : (j : Fin k) → A (n+j.val)) (b : B (n+k)) :
    (ofWindow n k as b).horizon = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp [ofWindow, horizon, ih]

@[simp] theorem window_horizon (t : Until A B n) : t.window.1 = t.horizon := by
  induction t with
  | now => rfl
  | wait a t ih => simp [window, horizon, ih]

/-- Observationally exact reconstruction, retaining all waiting and terminal data. -/
theorem ofWindow_window (t : Until A B n) :
    ofWindow n t.window.1 t.window.2.1 t.window.2.2 = t := by
  induction t with
  | now => rfl
  | @wait n a t ih =>
    rw [window, ofWindow]
    simp only
    congr 1
    convert ih using 1
    congr 1
    · funext j
      simp
      simp only [eqRec_eq_cast, cast_cast, cast_eq]
    · simp only [Eq.mp, Eq.mpr, eqRec_eq_cast, cast_cast, cast_eq]

theorem window_ofWindow (n k : Nat) (as : (j : Fin k) → A (n+j.val)) (b : B (n+k)) :
    window (ofWindow n k as b) = ⟨k,as,b⟩ := by
  induction k generalizing n with
  | zero =>
    simp only [ofWindow, window, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq, and_true, true_and]
    funext j
    exact Fin.elim0 j
  | succ k ih =>
    rw [ofWindow, window, ih]
    dsimp only
    congr 1
    apply Prod.ext
    · funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · rfl
      · simp [Eq.mpr, eqRec_eq_cast]
    · simp only [Eq.mp, Eq.mpr, eqRec_eq_cast, cast_cast, cast_eq]

def windowEquiv (A B : Nat → Type u) (n : Nat) : Until A B n ≃ Window A B n where
  toFun := window
  invFun w := ofWindow n w.1 w.2.1 w.2.2
  left_inv := ofWindow_window
  right_inv w := by obtain ⟨k,as,b⟩ := w; exact window_ofWindow n k as b

/-- Finite eventuality requires terminal evidence somewhere, even for a total family. -/
theorem no_terminal (empty : ∀ j, B j → False) (w : Until A B n) : False := by
  induction w with
  | now b => exact empty _ b
  | wait _ _ ih => exact ih

end Until
end Temporal
