import Applications.Resources.PositionalPermutations

/-! First-equal removal and permutation execution. One equality decision is one
oracle event; representation-dependent equality time is outside this source tariff. -/
set_option autoImplicit false
set_option warningAsError true
namespace Resources.ErasurePermutations
open PositionalPermutations
universe u
variable {α : Type u} [DecidableEq α]

/-- Dispatch, equality oracle, and a copied prefix cell on a failed comparison. -/
def removeRun (x : α) : List α → Measured (List α) Nat
  | [] => ([],1)
  | y :: ys => if x = y then (ys,2) else
      let r := removeRun x ys
      (y :: r.1,r.2+3)

theorem removeRun_value (x : α) (xs : List α) : (removeRun x xs).1 = xs.erase x := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    by_cases h : x = y
    · subst y; simp [removeRun]
    · simp [removeRun, h, Ne.symm h, ih]

theorem removeRun_absent (x : α) (xs : List α) (h : x ∉ xs) :
    removeRun x xs = (xs,3*xs.length+1) := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    have hn : x ≠ y := fun e => h (by simp [e])
    have ht : x ∉ ys := fun hm => h (List.mem_cons_of_mem y hm)
    simp [removeRun, hn, ih ht, Nat.mul_add]

theorem removeRun_first (x : α) (pre post : List α) (h : x ∉ pre) :
    removeRun x (pre ++ x :: post) = (pre ++ post,3*pre.length+2) := by
  induction pre with
  | nil => simp [removeRun]
  | cons y pre ih =>
    have hn : x ≠ y := fun e => h (by simp [e])
    have ht : x ∉ pre := fun hm => h (List.mem_cons_of_mem y hm)
    simp [removeRun, hn, ih ht, Nat.mul_add]

theorem removeRun_upper (x : α) (xs : List α) : (removeRun x xs).2 ≤ 3*xs.length+1 := by
  induction xs with
  | nil => simp [removeRun]
  | cons y ys ih => by_cases h : x = y <;> simp [removeRun, h] <;> omega

theorem removeRun_length (x : α) (xs : List α) (h : x ∈ xs) :
    (removeRun x xs).1.length+1 = xs.length := by
  rw [removeRun_value]
  exact List.length_erase_add_one h

theorem removeRun_decrease (x : α) (xs : List α) (h : x ∈ xs) :
    (removeRun x xs).1.length < xs.length := by
  have hh := removeRun_length x xs h
  omega

/-- Each occurrence selects the first equal remainder, retaining duplicate branches. -/
def generate (xs : List α) : Measured (List (List α)) Nat :=
  if xs = [] then ([[]],1) else
    let r := concatMapRun (fun x : {x // x ∈ xs} =>
      let d := removeRun x.val xs
      let s := generate d.1
      let m := ListFusion.map 1 1 1 (x.val :: ·) s.1
      (m.1,d.2+s.2+m.2)) xs.attach
    (r.1,r.2+1)
termination_by xs.length
decreasing_by exact removeRun_decrease x.val xs x.property

theorem generate_eqn (xs : List α) : generate xs =
    if xs = [] then ([[]],1) else
      let r := concatMapRun (fun x =>
        let d := removeRun x xs
        let s := generate d.1
        let m := ListFusion.map 1 1 1 (x :: ·) s.1
        (m.1,d.2+s.2+m.2)) xs
      (r.1,r.2+1) := by
  rw [generate]
  split
  · rfl
  · exact congrArg (fun r : Measured (List (List α)) Nat => (r.1,r.2+1))
      (concatMapRun_attach (fun x : α =>
        let d := removeRun x xs
        let s := generate d.1
        let m := ListFusion.map 1 1 1 (x :: ·) s.1
        (m.1,d.2+s.2+m.2)) xs)

theorem generate_value (xs : List α) : (generate xs).1 = Sequences.Permutations.byErasure xs := by
  rw [generate_eqn, Sequences.Permutations.byErasure_eqn]
  split
  · rfl
  · simp only [concatMapRun_value]
    apply List.flatMap_congr
    intro x hx
    rw [ListFusion.map_value, generate_value (removeRun x xs).1, removeRun_value]
termination_by xs.length
decreasing_by exact removeRun_decrease x xs hx

theorem generate_length (xs : List α) : (generate xs).1.length = Nat.factorial xs.length := by
  rw [generate_value, Sequences.Permutations.byErasure_length]

/-- A source interpreter for full-pair comparison, not the public recursion interface. -/
def generateFuel : Nat → List α → Measured (List (List α)) Nat
  | 0, _ => ([[]],1)
  | _+1, [] => ([[]],1)
  | fuel+1, x :: xs =>
    let r := concatMapRun (fun y =>
      let d := removeRun y (x :: xs)
      let s := generateFuel fuel d.1
      let m := ListFusion.map 1 1 1 (y :: ·) s.1
      (m.1,d.2+s.2+m.2)) (x :: xs)
    (r.1,r.2+1)

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
      apply congrArg (fun r : Measured (List (List α)) Nat => (r.1,r.2+1))
      apply concatMapRun_congr
      intro y hy
      have hd := removeRun_decrease y (x :: xs) hy
      rw [ih _ (by simp only [List.length_cons] at h hd; omega)]

/-- Actual removal and recursive bills, once for each ordered input occurrence. -/
def subproblemWork (xs : List α) : Nat :=
  (xs.map (fun x => (removeRun x xs).2 + (generate (removeRun x xs).1).2)).sum

theorem generate_work_cons (x : α) (xs : List α) :
    (generate (x :: xs)).2 = subproblemWork (x :: xs) +
      5*Nat.factorial (xs.length+1)+5*(xs.length+1)+3 := by
  let f := fun y : α =>
    let d := removeRun y (x :: xs)
    let s := generate d.1
    let m := ListFusion.map 1 1 1 (y :: ·) s.1
    (m.1,d.2+s.2+m.2)
  have hl : ∀ y ∈ x :: xs, (removeRun y (x :: xs)).1.length = xs.length := by
    intro y hy
    have hh := removeRun_length y (x :: xs) hy
    simp only [List.length_cons] at hh
    omega
  have hb : ∀ y ∈ x :: xs, (f y).1.length = Nat.factorial xs.length := by
    intro y hy
    simp only [f, ListFusion.map_value, List.length_map, generate_length, hl y hy]
  have hs : ∀ ys : List α, (∀ y ∈ ys, y ∈ x :: xs) →
      (ys.map (fun y => (f y).2)).sum =
        (ys.map (fun y => (removeRun y (x :: xs)).2 +
          (generate (removeRun y (x :: xs)).1).2)).sum +
        ys.length * (3*Nat.factorial xs.length+1) := by
    intro ys
    induction ys with
    | nil => simp
    | cons y ys ih =>
      intro h
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        ih (fun z hz => h z (List.mem_cons_of_mem y hz))]
      simp only [f, ListFusion.map_work, generate_length, hl y (h y List.mem_cons_self)]
      ring
  rw [generate_eqn]
  simp only [List.cons_ne_nil, ↓reduceIte]
  change (concatMapRun f (x :: xs)).2+1 = _
  rw [concatMapRun_work, flatMap_length_constant _ _ _ hb, hs _ (fun _ h => h)]
  simp only [subproblemWork, List.length_cons, Nat.factorial_succ]
  ring

theorem generate_mass (xs : List α) :
    (generate xs).1.flatten.length = xs.length * Nat.factorial xs.length := by
  have h := flatMap_length_constant id (generate xs).1 xs.length (by
    intro ys hy
    rw [generate_value] at hy
    exact ((Sequences.Permutations.byErasure_mem_iff xs ys).mp hy).length_eq)
  simpa [generate_length, Nat.mul_comm] using h

def observed (xs : List α) : Measured (List (List α)) Nat := bind (generate xs) observeSpines

theorem observed_eq (xs : List α) : observed xs =
    (Sequences.Permutations.byErasure xs,
      (generate xs).2+xs.length*Nat.factorial xs.length+3*Nat.factorial xs.length+1) := by
  simp only [observed, bind, observeSpines_eq]
  rw [generate_mass, generate_length, generate_value]
  congr 1
  omega

end Resources.ErasurePermutations
