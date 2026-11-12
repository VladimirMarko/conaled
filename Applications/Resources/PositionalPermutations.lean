import Applications.Sequences.Permutations
import Applications.Resources.ListFusion
import Applications.Linear.StructuredCosts
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Positional permutations with explicit scalar construction charges. These count
source operations, not host allocation or time. Source mapping and statement
review: `docs/research/positional-permutation-costs.md`. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.PositionalPermutations
universe u v
variable {α : Type u} {β : Type v}

/-- Local source-priced traversal: callback, produced outer cell and dispatch. -/
def mapRun (f : α → Measured β Nat) : List α → Measured (List β) Nat
  | [] => ([], 1)
  | x :: xs =>
    let a := f x
    let r := mapRun f xs
    (a.1 :: r.1, a.2 + r.2 + 2)

theorem mapRun_eq (f : α → Measured β Nat) (xs : List α) :
    mapRun f xs = (xs.map (fun x => (f x).1),
      (xs.map (fun x => (f x).2)).sum + 2 * xs.length + 1) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [mapRun, ih, Nat.mul_add]; omega

/-- The native traversal supplies callback observations; structure is additional. -/
theorem mapRun_native (f : α → Measured β Nat) (xs : List α) :
    mapRun f xs =
      let r := StructuredLinear.Costs.traverse
        (fun x => ((f x).1, StructuredLinear.Costs.tick .outputWrite (f x).2)) xs
      (r.1, r.2 .outputWrite + 2 * xs.length + 1) := by
  rw [mapRun_eq]
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [StructuredLinear.Costs.traverse, StructuredLinear.Costs.tick] at ih ⊢
    omega

theorem mapRun_attach (f : α → Measured β Nat) (xs : List α) :
    mapRun (fun x : {x // x ∈ xs} => f x.val) xs.attach = mapRun f xs := by
  simp [mapRun_eq]

def concatMapRun (f : α → Measured (List β) Nat) (xs : List α) :
    Measured (List β) Nat := bind (mapRun f xs) ListFusion.concat1

theorem concatMapRun_value (f : α → Measured (List β) Nat) (xs : List α) :
    (concatMapRun f xs).1 = xs.flatMap (fun x => (f x).1) := by
  simp [concatMapRun, bind, mapRun_eq, ListFusion.concat1_value, List.flatMap_def]

theorem concatMapRun_work (f : α → Measured (List β) Nat) (xs : List α) :
    (concatMapRun f xs).2 = (xs.map (fun x => (f x).2)).sum +
      2 * (xs.flatMap (fun x => (f x).1)).length + 4 * xs.length + 2 := by
  simp [concatMapRun, bind, mapRun_eq, ListFusion.concat1_work, List.flatMap_def]
  omega

theorem concatMapRun_attach (f : α → Measured (List β) Nat) (xs : List α) :
    concatMapRun (fun x : {x // x ∈ xs} => f x.val) xs.attach = concatMapRun f xs := by
  simp only [concatMapRun, mapRun_attach]

def triangle (n : Nat) : Nat := ∑ i ∈ Finset.range n, (i + 1)

theorem triangle_zero : triangle 0 = 0 := by simp [triangle]

theorem triangle_succ (n : Nat) : triangle (n+1) = triangle n + (n+1) :=
  Finset.sum_range_succ (fun i => i + 1) n

def picksRun : List α → Measured (List (α × List α)) Nat
  | [] => ([], 1)
  | x :: xs =>
    let r := picksRun xs
    let m := ListFusion.map 1 1 1 (fun p => (p.1, x :: p.2)) r.1
    ((x, xs) :: m.1, r.2 + m.2 + 2)

theorem picksRun_value (xs : List α) : (picksRun xs).1 = Sequences.Occurrences.picks xs := by
  induction xs <;> simp_all [picksRun, ListFusion.map_value, Sequences.Occurrences.picks]

theorem picksRun_length (xs : List α) : (picksRun xs).1.length = xs.length := by
  rw [picksRun_value]
  exact Sequences.Permutations.picks_length xs

theorem picksRun_work (xs : List α) : (picksRun xs).2 = 3 * triangle xs.length + 1 := by
  induction xs with
  | nil => simp [picksRun, triangle]
  | cons x xs ih =>
    simp only [picksRun, ListFusion.map_work, picksRun_length, List.length_cons,
      triangle_succ]
    omega

theorem picksRun_decrease (xs : List α) (p : α × List α)
    (hp : p ∈ (picksRun xs).1) : p.2.length < xs.length := by
  rw [picksRun_value] at hp
  have h := Sequences.Permutations.picks_remainder_length xs p hp
  omega

/-- Fuel-free public recursion executes its measured choices and every branch. -/
def generate (xs : List α) : Measured (List (List α)) Nat :=
  if xs = [] then ([[]], 1) else
    let p := picksRun xs
    let r := concatMapRun (fun q : {q // q ∈ p.1} =>
      let s := generate q.val.2
      let m := ListFusion.map 1 1 1 (q.val.1 :: ·) s.1
      (m.1, s.2 + m.2)) p.1.attach
    (r.1, p.2 + r.2 + 1)
termination_by xs.length
decreasing_by exact picksRun_decrease xs q.val q.property

theorem generate_eqn (xs : List α) : generate xs =
    if xs = [] then ([[]], 1) else
      let p := picksRun xs
      let r := concatMapRun (fun q =>
        let s := generate q.2
        let m := ListFusion.map 1 1 1 (q.1 :: ·) s.1
        (m.1, s.2 + m.2)) p.1
      (r.1, p.2 + r.2 + 1) := by
  rw [generate]
  split
  · rfl
  · exact congrArg (fun r : Measured (List (List α)) Nat =>
        (r.1, (picksRun xs).2 + r.2 + 1))
      (concatMapRun_attach (fun q : α × List α =>
        let s := generate q.2
        let m := ListFusion.map 1 1 1 (q.1 :: ·) s.1
        (m.1, s.2 + m.2)) (picksRun xs).1)

theorem generate_value (xs : List α) :
    (generate xs).1 = Sequences.Permutations.bySelection xs := by
  rw [generate_eqn, Sequences.Permutations.bySelection_eqn]
  split
  · rfl
  · simp only [concatMapRun_value, picksRun_value, Sequences.Permutations.picks]
    apply List.flatMap_congr
    intro p hp
    simp only [ListFusion.map_value, generate_value p.2]
termination_by xs.length
decreasing_by
  exact picksRun_decrease xs p (by simpa only [picksRun_value] using hp)

theorem generate_length (xs : List α) :
    (generate xs).1.length = Nat.factorial xs.length := by
  rw [generate_value, Sequences.Permutations.bySelection_length]

/-- The bounded source interpreter; insufficient fuel is deliberately observable. -/
def generateFuel : Nat → List α → Measured (List (List α)) Nat
  | 0, _ => ([[]], 1)
  | _+1, [] => ([[]], 1)
  | fuel+1, x :: xs =>
    let p := picksRun (x :: xs)
    let r := concatMapRun (fun q =>
      let s := generateFuel fuel q.2
      let m := ListFusion.map 1 1 1 (q.1 :: ·) s.1
      (m.1, s.2 + m.2)) p.1
    (r.1, p.2 + r.2 + 1)

theorem mapRun_congr (f g : α → Measured β Nat) (xs : List α)
    (h : ∀ x ∈ xs, f x = g x) : mapRun f xs = mapRun g xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [mapRun, h x List.mem_cons_self,
      ih (fun y hy => h y (List.mem_cons_of_mem x hy))]

theorem concatMapRun_congr (f g : α → Measured (List β) Nat) (xs : List α)
    (h : ∀ x ∈ xs, f x = g x) : concatMapRun f xs = concatMapRun g xs := by
  simp only [concatMapRun, mapRun_congr f g xs h]

theorem generateFuel_eq (fuel : Nat) (xs : List α) (h : xs.length ≤ fuel) :
    generateFuel fuel xs = generate xs := by
  induction fuel generalizing xs with
  | zero =>
    have hx : xs = [] := List.length_eq_zero_iff.mp (by omega)
    subst xs
    rw [generate_eqn]
    rfl
  | succ fuel ih =>
    cases xs with
    | nil => rw [generate_eqn]; rfl
    | cons x xs =>
      rw [generate_eqn]
      simp only [List.cons_ne_nil, ↓reduceIte, generateFuel]
      apply congrArg (fun r : Measured (List (List α)) Nat => (r.1, (picksRun (x :: xs)).2 + r.2 + 1))
      apply concatMapRun_congr
      intro p hp
      have hd := picksRun_decrease (x :: xs) p hp
      rw [ih p.2 (by simp only [List.length_cons] at h hd; omega)]

theorem flatMap_length_constant (f : α → List β) (xs : List α) (k : Nat)
    (h : ∀ x ∈ xs, (f x).length = k) : (xs.flatMap f).length = xs.length * k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons,
      h x List.mem_cons_self, ih (fun y hy => h y (List.mem_cons_of_mem x hy))]
    ring

theorem concatMapRun_constant (f : α → Measured (List β) Nat) (xs : List α) (c k : Nat)
    (hc : ∀ x ∈ xs, (f x).2 = c) (hk : ∀ x ∈ xs, (f x).1.length = k) :
    (concatMapRun f xs).2 = xs.length * (c + 2*k + 4) + 2 := by
  rw [concatMapRun_work, flatMap_length_constant _ xs k hk]
  have he : xs.map (fun x => (f x).2) = xs.map (fun _ => c) := List.map_congr_left hc
  rw [he]
  simp only [List.map_const', List.sum_replicate_nat]
  ring

/-- Source recurrence derived below from the executed operations. -/
def constructionWork : Nat → Nat
  | 0 => 1
  | n+1 => (n+1) * constructionWork n + 5 * Nat.factorial (n+1) +
      3 * triangle (n+1) + 5*(n+1) + 4

theorem generate_work (xs : List α) : (generate xs).2 = constructionWork xs.length := by
  rw [generate_eqn]
  cases xs with
  | nil => rfl
  | cons x xs =>
    simp only [List.cons_ne_nil, ↓reduceIte]
    let branch := fun q : α × List α =>
      let s := generate q.2
      let m := ListFusion.map 1 1 1 (q.1 :: ·) s.1
      (m.1, s.2 + m.2)
    have hl : ∀ q ∈ (picksRun (x :: xs)).1, q.2.length = xs.length := by
      intro q hq
      have h := Sequences.Permutations.picks_remainder_length (x :: xs) q
        (by simpa only [picksRun_value, Sequences.Permutations.picks] using hq)
      simp only [List.length_cons] at h
      omega
    have hc : ∀ q ∈ (picksRun (x :: xs)).1,
        (branch q).2 = constructionWork xs.length + 3 * Nat.factorial xs.length + 1 := by
      intro q hq
      simp only [branch, ListFusion.map_work, generate_work q.2, generate_length, hl q hq]
      omega
    have hk : ∀ q ∈ (picksRun (x :: xs)).1,
        (branch q).1.length = Nat.factorial xs.length := by
      intro q hq
      simp only [branch, ListFusion.map_value, List.length_map, generate_length, hl q hq]
    have hr := concatMapRun_constant branch (picksRun (x :: xs)).1
      (constructionWork xs.length + 3 * Nat.factorial xs.length + 1)
      (Nat.factorial xs.length) hc hk
    change (picksRun (x :: xs)).2 + (concatMapRun branch (picksRun (x :: xs)).1).2 + 1 = _
    rw [hr, picksRun_work, picksRun_length]
    simp only [List.length_cons, constructionWork, Nat.factorial_succ]
    ring
termination_by xs.length
decreasing_by exact picksRun_decrease (x :: xs) q hq

theorem generate_eq (xs : List α) :
    generate xs = (Sequences.Permutations.bySelection xs, constructionWork xs.length) :=
  Prod.ext (generate_value xs) (generate_work xs)

theorem generate_mem_length (xs ys : List α) (h : ys ∈ (generate xs).1) :
    ys.length = xs.length := by
  rw [generate_value] at h
  exact ((Sequences.Permutations.bySelection_mem_iff xs ys).mp h).length_eq

theorem generate_mass (xs : List α) :
    (generate xs).1.flatten.length = xs.length * Nat.factorial xs.length := by
  have h := flatMap_length_constant id (generate xs).1 xs.length
    (fun ys hy => generate_mem_length xs ys hy)
  simpa [generate_length, Nat.mul_comm] using h

/-- Observe each actual inner spine through a native fold, retaining its labels. -/
def observeSpines (xss : List (List α)) : Measured (List (List α)) Nat :=
  mapRun (fun xs =>
    let inner := ListExecution.foldl 0 (fun n (_ : α) => n+1) 0 xs
    (xs, inner.2)) xss

theorem observeSpines_eq (xss : List (List α)) :
    observeSpines xss = (xss, xss.flatten.length + 3 * xss.length + 1) := by
  induction xss with
  | nil => rfl
  | cons xs xss ih =>
    simp only [observeSpines, mapRun, ListExecution.foldl_work] at ih ⊢
    simp only [Nat.add_zero, Nat.one_mul, List.flatten_cons, List.length_append,
      List.length_cons]
    simp only [Nat.add_zero, Nat.one_mul] at ih
    rw [ih]
    congr 1
    omega

def observed (xs : List α) : Measured (List (List α)) Nat := bind (generate xs) observeSpines

theorem observed_eq (xs : List α) : observed xs =
    (Sequences.Permutations.bySelection xs,
      constructionWork xs.length + xs.length * Nat.factorial xs.length +
        3 * Nat.factorial xs.length + 1) := by
  simp only [observed, bind, observeSpines_eq]
  rw [generate_mass, generate_length, generate_value, generate_work]
  congr 1
  omega

end Resources.PositionalPermutations
