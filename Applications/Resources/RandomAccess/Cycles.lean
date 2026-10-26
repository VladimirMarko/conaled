import Applications.Resources.RandomAccess.Drain
import Applications.Resources.RandomAccess.Families

/-! Finite end-operation accounting from checkpoint 233.
Provenance, source domains and statement review:
`docs/research/adwh-random-access-end-costs.md`. -/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.RandomAccessCosts
open RandomAccess
universe u
variable {α : Type u}

/-- A carry immediately undone by borrowing follows exactly the same digit depth. -/
theorem borrowCost_consT {r : Nat} {ds : RAList α} (h : Valid r ds) (t : Tree α) :
    borrowCost (consT t ds) = (consTRun t ds).2 := by
  induction h generalizing t with
  | nil r => rfl
  | zero hne h ih => rfl
  | one ht h ih => simp only [consT, borrowCost, consTRun, ih]

def pushPopRun (x : α) (ds : RAList α) : Option (α × RAList α) × Nat :=
  bind (consRARun x ds) unconsRARun

theorem pushPopRun_exact (x : α) {ds : RAList α} (h : Inv ds) :
    pushPopRun x ds = (some (x, ds), 2 * (consRARun x ds).2) := by
  simp only [pushPopRun, bind, consRARun_value, unconsRARun_exact, unconsRA_consRA x h]
  rw [consRA, borrowCost_consT h]
  change (some (x, ds), (consRARun x ds).2 + (consRARun x ds).2) = _
  congr 1
  omega

def mixedRun (x : α) : Nat → RAList α → RAList α × Nat
  | 0, ds => (ds, 0)
  | n + 1, ds =>
      let pair := pushPopRun x ds
      match pair.1 with
      | none => (ds, pair.2)
      | some (_, ys) =>
          let rest := mixedRun x n ys
          (rest.1, pair.2 + rest.2)

theorem mixedRun_exact (x : α) (n : Nat) {ds : RAList α} (h : Inv ds) :
    mixedRun x n ds = (ds, n * (2 * (consRARun x ds).2)) := by
  induction n with
  | zero => simp [mixedRun]
  | succ n ih =>
    rw [mixedRun, pushPopRun_exact x h]
    simp only [ih, Nat.add_mul, Nat.one_mul]
    congr 1
    omega

def fullDigits (x : α) (r : Nat) : Nat → RAList α
  | 0 => []
  | p + 1 => .one (perfectTree x r) :: fullDigits x (r + 1) p

theorem fullDigits_valid (x : α) (r p : Nat) : Valid r (fullDigits x r p) := by
  induction p generalizing r with
  | zero => exact Valid.nil r
  | succ p ih => exact Valid.one (perfectTree_valid x r) (ih (r + 1))

theorem fullDigits_length (x : α) (r p : Nat) : (fullDigits x r p).length = p := by
  induction p generalizing r with
  | zero => rfl
  | succ p ih => simp [fullDigits, ih]

theorem fullDigits_cons_cost (x : α) (r p : Nat) (t : Tree α) :
    (consTRun t (fullDigits x r p)).2 = p + 1 := by
  induction p generalizing r t with
  | zero => rfl
  | succ p ih => simp [fullDigits, consTRun, ih]

theorem mixed_fullDigits_exact (x : α) (n p : Nat) :
    mixedRun x n (fullDigits x 0 p) = (fullDigits x 0 p, n * (2 * p + 2)) := by
  rw [mixedRun_exact x n (fullDigits_valid x 0 p)]
  simp only [consRARun, fullDigits_cons_cost]
  congr 2

/-- No potential function can give both operations a uniform constant charge:
the costly pair leaves the state, hence every state potential, unchanged. -/
theorem no_uniform_mixed_charge (x : α) (potential : RAList α → Nat) (C : Nat) :
    ∃ ds, Inv ds ∧ (mixedRun x 1 ds).1 = ds ∧
      potential ds + 2 * C < (mixedRun x 1 ds).2 + potential (mixedRun x 1 ds).1 := by
  refine ⟨fullDigits x 0 (C + 1), fullDigits_valid x 0 (C + 1), ?_, ?_⟩
  · rw [mixed_fullDigits_exact]
  · rw [mixed_fullDigits_exact]
    simp only [Nat.one_mul]
    omega

end Resources.RandomAccessCosts
