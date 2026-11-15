import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Group.Nat.Hom
import Mathlib.Data.Nat.Basic

/-! A coordinate-guarded fixed-point construction on independent stream
meanings. The solution is built by well-founded recursion, not postulated.
Causal operations may be substituted around guarded definitions. -/
namespace SquareKit.GuardedStreams
universe u v w
abbrev Stream (A : Type u) := Nat → A

/-- Output n depends only on input coordinates at most n. -/
def Causal (F : Stream A → Stream B) : Prop :=
  ∀ n s t, (∀ i, i ≤ n → s i = t i) → F s n = F t n

/-- Output n depends only on strictly earlier coordinates. -/
def Guarded (F : Stream A → Stream B) : Prop :=
  ∀ n s t, (∀ i, i < n → s i = t i) → F s n = F t n

def cons (a : A) (s : Stream A) : Stream A
  | 0 => a
  | n + 1 => s n

theorem causal_id : Causal (id : Stream A → Stream A) :=
  fun n _ _ h => h n (Nat.le_refl n)

theorem causal_comp {F : Stream B → Stream C} {G : Stream A → Stream B}
    (hF : Causal F) (hG : Causal G) : Causal (F ∘ G) := by
  intro n s t h
  apply hF
  intro i hi
  exact hG i s t (fun j hj => h j (Nat.le_trans hj hi))

theorem guarded_comp_causal {F : Stream B → Stream C} {G : Stream A → Stream B}
    (hF : Guarded F) (hG : Causal G) : Guarded (F ∘ G) := by
  intro n s t h
  apply hF
  intro i hi
  exact hG i s t (fun j hj => h j (Nat.lt_of_le_of_lt hj hi))

theorem causal_comp_guarded {F : Stream B → Stream C} {G : Stream A → Stream B}
    (hF : Causal F) (hG : Guarded G) : Guarded (F ∘ G) := by
  intro n s t h
  apply hF
  intro i hi
  exact hG i s t (fun j hj => h j (Nat.lt_of_lt_of_le hj hi))

theorem cons_guarded (a : A) : Guarded (cons a) := by
  intro n s t h
  cases n with
  | zero => rfl
  | succ n => exact h n (Nat.lt_succ_self n)

/-- Finite lower-coordinate recursion. The seed fills inaccessible coordinates;
guardedness will prove that those arbitrary values cannot affect the result. -/
def solve (F : Stream A → Stream A) (seed : A) (n : Nat) : A :=
  F (fun i => if _h : i < n then solve F seed i else seed) n
termination_by n

theorem solve_fixed {F : Stream A → Stream A} (hF : Guarded F) (seed : A) :
    solve F seed = F (solve F seed) := by
  funext n
  rw [solve]
  apply hF
  intro i hi
  simp only [dite_eq_left hi]

theorem unique {F : Stream A → Stream A} (hF : Guarded F) (seed : A)
    (s : Stream A) (hs : s = F s) : s = solve F seed := by
  funext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [congrFun hs n, congrFun (solve_fixed hF seed) n]
    exact hF n s (solve F seed) ih

theorem seed_independent {F : Stream A → Stream A} (hF : Guarded F) (a b : A) :
    solve F a = solve F b := unique hF b _ (solve_fixed hF a)

/-- A local interpretation square transports the constructed solution. The
coefficient map need be neither invertible nor injective. -/
theorem map_solution {F : Stream A → Stream A} {G : Stream B → Stream B}
    (hF : Guarded F) (hG : Guarded G) (f : A → B) (a : A) (b : B)
    (commutes : ∀ s, f ∘ F s = G (f ∘ s)) :
    f ∘ solve F a = solve G b := by
  apply unique hG b
  calc
    f ∘ solve F a = f ∘ F (solve F a) := congrArg (fun s => f ∘ s) (solve_fixed hF a)
    _ = G (f ∘ solve F a) := commutes _

/-- Replacing an admitted operation by an extensionally equal implementation
preserves the chosen solution, independent of initialization. -/
theorem solve_congr {F G : Stream A → Stream A} (hF : Guarded F)
    (h : ∀ s, F s = G s) (a b : A) : solve F a = solve G b := by
  have eq : F = G := funext h
  subst G
  exact seed_independent hF a b

/-- Parameterized first recursive definition; its result can be used as a
constant in later schemes. -/
def constantStream (a : A) : Stream A := solve (cons a) a

theorem constantStream_eq (a : A) : constantStream a = fun _ => a :=
  (unique (cons_guarded a) a (fun _ => a) (by funext n; cases n <;> rfl)).symm

theorem constantStream_fixed (a : A) : constantStream a = cons a (constantStream a) :=
  solve_fixed (cons_guarded a) a

/-- A fixed stream parameter is unrestricted; the recursive argument remains
causal, so using a previously solved definition introduces no new assumption. -/
def addLeft [Add A] (p s : Stream A) : Stream A := fun n => p n + s n

theorem addLeft_causal [Add A] (p : Stream A) : Causal (addLeft p) := by
  intro n s t h
  exact congrArg (fun x => p n + x) (h n (Nat.le_refl n))

def ones [One R] : Stream R := constantStream 1

/-- The later definition uses the earlier *constructed* ones, rather than its
closed formula, in the recursive scheme. -/
def sumsBody [Add R] [One R] : Stream R → Stream R := cons 1 ∘ addLeft (ones : Stream R)

theorem sums_guarded [Add R] [One R] : Guarded (sumsBody : Stream R → Stream R) :=
  guarded_comp_causal (cons_guarded 1) (addLeft_causal ones)

def sums [Add R] [One R] : Stream R := solve sumsBody 1

theorem ones_eq [One R] (n : Nat) : (ones : Stream R) n = 1 := congrFun (constantStream_eq 1) n

theorem sums_fixed [Add R] [One R] : (sums : Stream R) = cons 1 (addLeft ones sums) :=
  solve_fixed sums_guarded 1

theorem sums_unique [Add R] [One R] (s : Stream R)
    (hs : s = cons 1 (addLeft ones s)) : s = sums := unique sums_guarded 1 s hs

/-- Independently specified coordinate meaning. The recursive construction only
needs Add/One; this closed formula uses their natural-number compatibility. -/
theorem sums_eq [AddMonoidWithOne R] (n : Nat) : (sums : Stream R) n = (n + 1 : Nat) := by
  have h : (fun n => ((n + 1 : Nat) : R)) = cons 1 (addLeft ones (fun n => ((n + 1 : Nat) : R))) := by
    funext n
    cases n with
    | zero => simp [cons]
    | succ n =>
      change ((n + 1 + 1 : Nat) : R) = (ones : Stream R) n + ((n + 1 : Nat) : R)
      rw [ones_eq]
      rw [← Nat.cast_one_add]
      congr 1
      omega
  exact congrFun (sums_unique _ h).symm n

/-- This naturality square explicitly uses the already defined operation. -/
theorem ones_map [One R] [One S] (f : R → S) (h1 : f 1 = 1) :
    f ∘ (ones : Stream R) = (ones : Stream S) := by
  apply map_solution (cons_guarded (1 : R)) (cons_guarded (1 : S)) f 1 1
  intro s
  funext n
  cases n <;> simp [cons, h1]

theorem sums_map [AddMonoid R] [One R] [AddMonoid S] [One S]
    (f : R →+ S) (h1 : f 1 = 1) :
    f ∘ (sums : Stream R) = (sums : Stream S) := by
  apply map_solution sums_guarded sums_guarded f 1 1
  intro s
  funext n
  cases n with
  | zero => exact h1
  | succ n =>
    change f ((ones : Stream R) n + s n) = (ones : Stream S) n + f (s n)
    rw [map_add]
    exact congrArg (fun x => x + f (s n)) (congrFun (ones_map f h1) n)

/-- Unguarded identity has distinct solutions and fails exactly at coordinate
zero, where a guarded functional must not inspect its argument. -/
theorem identity_not_guarded : ¬ Guarded (id : Stream Nat → Stream Nat) := by
  intro h
  have bad := h 0 (fun _ => 0) (fun _ => 1) (by intro i hi; omega)
  change (0 : Nat) = 1 at bad
  contradiction

theorem identity_two_solutions :
    (fun _ : Nat => 0) = id (fun _ => 0) ∧
    (fun _ : Nat => 1) = id (fun _ => 1) ∧
    (fun _ : Nat => 0) ≠ (fun _ : Nat => 1) := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  have bad := congrFun h 0
  contradiction

end SquareKit.GuardedStreams
