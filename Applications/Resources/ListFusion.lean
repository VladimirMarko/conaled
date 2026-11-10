import Applications.Resources.ListExecution

/-!
# Executed finite-list fusion and demand costs

Weighted map prices source dispatches, produced cells and opaque function calls.
Pipelines use the existing measured bind; append uses the shared executed primitive.
Independent closed formulas describe the observed work after execution. `takeWhile`
retains a first-false test and never visits the later suffix. These are finite
source-model observations, with no compiler, native-time or peak-memory claim.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Resources.ListFusion

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

def map (dispatch cells calls : Nat) (f : α → β) : List α → Measured (List β) Nat
  | [] => ([], dispatch)
  | x :: xs =>
    let r := map dispatch cells calls f xs
    (f x :: r.1, r.2 + dispatch + cells + calls)

theorem map_value (d k c : Nat) (f : α → β) (xs : List α) :
    (map d k c f xs).1 = List.map f xs := by
  induction xs <;> simp_all [map]

theorem map_work (d k c : Nat) (f : α → β) (xs : List α) :
    (map d k c f xs).2 = (d + k + c) * xs.length + d := by
  induction xs <;> simp_all [map, Nat.mul_add]; omega

def mapTwice (d k cf cg : Nat) (f : β → γ) (g : α → β) (xs : List α) : Measured (List γ) Nat :=
  bind (map d k cg g xs) (map d k cf f)

def mapFused (d k cf cg : Nat) (f : β → γ) (g : α → β) (xs : List α) : Measured (List γ) Nat :=
  map d k (cf + cg) (fun x => f (g x)) xs

theorem mapTwice_value (d k cf cg : Nat) (f : β → γ) (g : α → β) (xs : List α) :
    (mapTwice d k cf cg f g xs).1 = List.map f (List.map g xs) := by
  simp [mapTwice, bind, map_value]

theorem mapFused_value (d k cf cg : Nat) (f : β → γ) (g : α → β) (xs : List α) :
    (mapFused d k cf cg f g xs).1 = List.map (fun x => f (g x)) xs := by
  exact map_value _ _ _ _ _

theorem map_fusion_value (d k cf cg : Nat) (f : β → γ) (g : α → β) (xs : List α) :
    (mapTwice d k cf cg f g xs).1 = (mapFused d k cf cg f g xs).1 := by
  rw [mapTwice_value, mapFused_value, List.map_map]
  rfl

theorem map_fusion_saving (d k cf cg : Nat) (f : β → γ) (g : α → β) (xs : List α) :
    (mapTwice d k cf cg f g xs).2 =
      (mapFused d k cf cg f g xs).2 + (d + k) * xs.length + d := by
  simp only [mapTwice, bind, mapFused, map_work, map_value, List.length_map, Nat.add_mul]
  omega

theorem map_fusion_dispatch_saving (f : β → γ) (g : α → β) (xs : List α) :
    (mapTwice 1 0 0 0 f g xs).2 = (mapFused 1 0 0 0 f g xs).2 + xs.length + 1 := by
  simpa using map_fusion_saving 1 0 0 0 f g xs

theorem map_fusion_cell_saving (f : β → γ) (g : α → β) (xs : List α) :
    (mapTwice 0 1 0 0 f g xs).2 = (mapFused 0 1 0 0 f g xs).2 + xs.length := by
  simpa using map_fusion_saving 0 1 0 0 f g xs

def foldMap (d k cf cg : Nat) (f : β → γ → γ) (g : α → β) (e : γ)
    (xs : List α) : Measured γ Nat :=
  bind (map d k cg g xs) (ListExecution.foldr cf f e)

def foldMapFused (cf cg : Nat) (f : β → γ → γ) (g : α → β) (e : γ)
    (xs : List α) : Measured γ Nat :=
  ListExecution.foldr (cf + cg) (fun x y => f (g x) y) e xs

theorem foldMap_value (d k cf cg : Nat) (f : β → γ → γ) (g : α → β) (e : γ)
    (xs : List α) : (foldMap d k cf cg f g e xs).1 = List.foldr f e (List.map g xs) := by
  simp [foldMap, bind, map_value, ListExecution.foldr_value]

theorem foldMapFused_value (cf cg : Nat) (f : β → γ → γ) (g : α → β) (e : γ)
    (xs : List α) :
    (foldMapFused cf cg f g e xs).1 = List.foldr (fun x y => f (g x) y) e xs := by
  exact ListExecution.foldr_value _ _ _ _

theorem fold_map_fusion_value (d k cf cg : Nat) (f : β → γ → γ) (g : α → β) (e : γ)
    (xs : List α) : (foldMap d k cf cg f g e xs).1 = (foldMapFused cf cg f g e xs).1 := by
  rw [foldMap_value, foldMapFused_value, List.foldr_map]

theorem fold_map_fusion_saving (d k cf cg : Nat) (f : β → γ → γ) (g : α → β) (e : γ)
    (xs : List α) : (foldMap d k cf cg f g e xs).2 =
      (foldMapFused cf cg f g e xs).2 + (d + k) * xs.length + d := by
  simp only [foldMap, bind, foldMapFused, map_work, map_value, List.length_map,
    ListExecution.foldr_work, Nat.add_mul]
  omega

def concat1 : List (List α) → Measured (List α) Nat
  | [] => ([], 1)
  | xs :: xss =>
    let r := concat1 xss
    let a := ListAppend.weighted 1 1 xs r.1
    (a.1, 1 + r.2 + a.2)

theorem concat1_value (xss : List (List α)) : (concat1 xss).1 = xss.flatten := by
  induction xss <;> simp_all [concat1, ListAppend.weighted_value]

theorem concat1_work (xss : List (List α)) :
    (concat1 xss).2 = 2 * xss.flatten.length + 2 * xss.length + 1 := by
  induction xss <;>
    simp_all [concat1, ListAppend.weighted_work, Nat.mul_add]; omega

def concat2Acc (acc : List α) : List (List α) → Measured (List α) Nat
  | [] => (acc, 1)
  | xs :: xss =>
    let a := ListAppend.weighted 1 1 acc xs
    let r := concat2Acc a.1 xss
    (r.1, 1 + a.2 + r.2)

def concat2 (xss : List (List α)) : Measured (List α) Nat := concat2Acc [] xss

/-- Sum of actual accumulator lengths before each left-associated append. -/
def prefixMass (k : Nat) : List (List α) → Nat
  | [] => 0
  | xs :: xss => k + prefixMass (k + xs.length) xss

theorem concat2Acc_value (acc : List α) (xss : List (List α)) :
    (concat2Acc acc xss).1 = List.foldl (· ++ ·) acc xss := by
  induction xss generalizing acc <;>
    simp_all [concat2Acc, ListAppend.weighted_value, List.foldl]

theorem concat2_value (xss : List (List α)) : (concat2 xss).1 = xss.flatten := by
  rw [concat2, concat2Acc_value]
  simpa using (List.foldl_append_eq_append (l := xss) (f := id) (l' := []))

theorem concat2Acc_work (acc : List α) (xss : List (List α)) :
    (concat2Acc acc xss).2 = 2 * prefixMass acc.length xss + 2 * xss.length + 1 := by
  induction xss generalizing acc <;>
    simp_all [concat2Acc, ListAppend.weighted_work, ListAppend.weighted_value,
      prefixMass, Nat.mul_add]; omega

theorem concat2_work (xss : List (List α)) :
    (concat2 xss).2 = 2 * prefixMass 0 xss + 2 * xss.length + 1 := by
  exact concat2Acc_work [] xss

theorem prefixMass_upper (k : Nat) (xss : List (List α)) :
    prefixMass k xss ≤ xss.length * (k + xss.flatten.length) := by
  induction xss generalizing k with
  | nil => simp [prefixMass]
  | cons xs xss ih =>
    have h := ih (k + xs.length)
    simp only [prefixMass, List.length_cons, List.flatten_cons, List.length_append,
      Nat.add_mul, Nat.one_mul]
    simp only [Nat.add_assoc] at h ⊢
    omega

theorem concat2_upper (xss : List (List α)) :
    (concat2 xss).2 ≤ 2 * xss.length * xss.flatten.length + 2 * xss.length + 1 := by
  have h := prefixMass_upper 0 xss
  simp only [Nat.zero_add] at h
  rw [concat2_work]
  simp only [Nat.mul_assoc]
  omega

theorem concat_values_equal (xss : List (List α)) : (concat1 xss).1 = (concat2 xss).1 := by
  rw [concat1_value, concat2_value]

theorem flatten_singletons_length (xs : List α) :
    (xs.map (fun x => [x])).flatten.length = xs.length := by
  induction xs <;> simp_all

theorem concat1_singletons_work (xs : List α) :
    (concat1 (xs.map (fun x => [x]))).2 = 4 * xs.length + 1 := by
  rw [concat1_work, flatten_singletons_length, List.length_map]
  omega

theorem concat2Acc_singletons_work (acc xs : List α) :
    (concat2Acc acc (xs.map (fun x => [x]))).2 =
      2 * xs.length * acc.length + xs.length * xs.length + xs.length + 1 := by
  induction xs generalizing acc with
  | nil => simp [concat2Acc]
  | cons x xs ih =>
    simp only [List.map_cons, concat2Acc, ih, ListAppend.weighted_work,
      ListAppend.weighted_value, List.length_append, List.length_cons,
      List.length_nil, Nat.zero_add, Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega

theorem concat2_singletons_work (xs : List α) :
    (concat2 (xs.map (fun x => [x]))).2 = xs.length * xs.length + xs.length + 1 := by
  simpa [concat2] using concat2Acc_singletons_work [] xs

def concatMap (d k cf : Nat) (f : α → List β) (xs : List α) : Measured (List β) Nat :=
  bind (map d k cf f xs) concat1

def concatMapMap (d k cf cg : Nat) (f : β → List γ) (g : α → β)
    (xs : List α) : Measured (List γ) Nat :=
  bind (map d k cg g xs) (concatMap d k cf f)

def concatMapFused (d k cf cg : Nat) (f : β → List γ) (g : α → β)
    (xs : List α) : Measured (List γ) Nat :=
  concatMap d k (cf + cg) (fun x => f (g x)) xs

theorem concatMap_value (d k cf : Nat) (f : α → List β) (xs : List α) :
    (concatMap d k cf f xs).1 = xs.flatMap f := by
  simp [concatMap, bind, map_value, concat1_value, List.flatMap_def]

theorem concatMapMap_value (d k cf cg : Nat) (f : β → List γ) (g : α → β)
    (xs : List α) :
    (concatMapMap d k cf cg f g xs).1 = (xs.map g).flatMap f := by
  simp [concatMapMap, bind, concatMap_value, map_value]

theorem concatMapFused_value (d k cf cg : Nat) (f : β → List γ) (g : α → β)
    (xs : List α) :
    (concatMapFused d k cf cg f g xs).1 = xs.flatMap (fun x => f (g x)) := by
  exact concatMap_value _ _ _ _ _

theorem concatMap_map_fusion_value (d k cf cg : Nat) (f : β → List γ) (g : α → β)
    (xs : List α) :
    (concatMapMap d k cf cg f g xs).1 = (concatMapFused d k cf cg f g xs).1 := by
  rw [concatMapMap_value, concatMapFused_value, List.flatMap_map]

theorem concatMap_map_fusion_saving (d k cf cg : Nat) (f : β → List γ) (g : α → β)
    (xs : List α) : (concatMapMap d k cf cg f g xs).2 =
      (concatMapFused d k cf cg f g xs).2 + (d + k) * xs.length + d := by
  simp only [concatMapMap, bind, concatMapFused, concatMap, map_work, map_value,
    List.length_map, List.map_map, Function.comp_def, Nat.add_mul]
  omega

/-- The literal fold-after-concat pipeline. -/
def foldConcat (c : Nat) (f : α → β → β) (e : β) (xss : List (List α)) : Measured β Nat :=
  bind (concat1 xss) (ListExecution.foldr c f e)

/-- The nested fold obtained by the source foldr/concat fusion law. -/
def foldConcatFused (c : Nat) (f : α → β → β) (e : β) : List (List α) → Measured β Nat
  | [] => (e, 1)
  | xs :: xss =>
    let r := foldConcatFused c f e xss
    let s := ListExecution.foldr c f r.1 xs
    (s.1, 1 + r.2 + s.2)

theorem foldConcat_value (c : Nat) (f : α → β → β) (e : β) (xss : List (List α)) :
    (foldConcat c f e xss).1 = List.foldr f e (xss.flatten) := by
  simp [foldConcat, bind, ListExecution.foldr_value, concat1_value]

theorem foldConcatFused_value (c : Nat) (f : α → β → β) (e : β)
    (xss : List (List α)) :
    (foldConcatFused c f e xss).1 = List.foldr (fun xs y => List.foldr f y xs) e xss := by
  induction xss <;> simp_all [foldConcatFused, ListExecution.foldr_value, List.foldr]

theorem fold_concat_fusion_value (c : Nat) (f : α → β → β) (e : β)
    (xss : List (List α)) :
    (foldConcat c f e xss).1 = (foldConcatFused c f e xss).1 := by
  rw [foldConcat_value, foldConcatFused_value, List.foldr_flatten]

theorem foldConcatFused_work (c : Nat) (f : α → β → β) (e : β)
    (xss : List (List α)) :
    (foldConcatFused c f e xss).2 = (1 + c) * xss.flatten.length + 2 * xss.length + 1 := by
  induction xss <;>
    simp_all [foldConcatFused, ListExecution.foldr_work, Nat.mul_add]; omega

theorem fold_concat_fusion_saving (c : Nat) (f : α → β → β) (e : β)
    (xss : List (List α)) :
    (foldConcat c f e xss).2 = (foldConcatFused c f e xss).2 + 2 * xss.flatten.length + 1 := by
  simp only [foldConcat, bind, concat1_work, ListExecution.foldr_work, concat1_value,
    foldConcatFused_work]
  omega

/-- Demand-driven unfolding of Answer 1.7's fold: the false step ignores the tail. -/
def takeWhile (dispatch cells tests : Nat) (p : α → Bool) : List α → Measured (List α) Nat
  | [] => ([], dispatch)
  | x :: xs =>
    if p x then
      let r := takeWhile dispatch cells tests p xs
      (x :: r.1, r.2 + dispatch + cells + tests)
    else ([], dispatch + tests)

theorem takeWhile_value (d k c : Nat) (p : α → Bool) (xs : List α) :
    (takeWhile d k c p xs).1 = xs.takeWhile p := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases hp : p x <;> simp_all [takeWhile]

/-- The final predicate is absent at nil and present on a failed next cell. -/
theorem takeWhile_work (d k c : Nat) (p : α → Bool) (xs : List α) :
    (takeWhile d k c p xs).2 = (d + k + c) * (xs.takeWhile p).length + d +
      c * (if xs.dropWhile p = [] then 0 else 1) := by
  induction xs with
  | nil => simp [takeWhile]
  | cons x xs ih =>
    cases hp : p x <;>
      simp_all [takeWhile, Nat.mul_add]; omega

theorem takeWhile_dispatches (p : α → Bool) (xs : List α) :
    (takeWhile 1 0 0 p xs).2 = (xs.takeWhile p).length + 1 := by
  simpa using takeWhile_work 1 0 0 p xs

theorem takeWhile_cells (p : α → Bool) (xs : List α) :
    (takeWhile 0 1 0 p xs).2 = (xs.takeWhile p).length := by
  simpa using takeWhile_work 0 1 0 p xs

theorem takeWhile_tests (p : α → Bool) (xs : List α) :
    (takeWhile 0 0 1 p xs).2 = (xs.takeWhile p).length +
      (if xs.dropWhile p = [] then 0 else 1) := by
  simpa using takeWhile_work 0 0 1 p xs

theorem takeWhile_linear_bounds (p : α → Bool) (xs : List α) :
    3 * (xs.takeWhile p).length + 1 ≤ (takeWhile 1 1 1 p xs).2 ∧
      (takeWhile 1 1 1 p xs).2 ≤ 3 * (xs.takeWhile p).length + 2 := by
  rw [takeWhile_work]
  split <;> omega

theorem takeWhile_failure (d k c : Nat) (p : α → Bool) (pre : List α) (bad : α)
    (rest : List α) (all : ∀ x ∈ pre, p x = true) (failed : p bad = false) :
    takeWhile d k c p (pre ++ bad :: rest) =
      (pre, (d + k + c) * pre.length + d + c) := by
  induction pre with
  | nil => simp [takeWhile, failed]
  | cons x pre ih =>
    have hx := all x (by simp)
    have ht : ∀ y ∈ pre, p y = true := fun y hy => all y (by simp [hy])
    simp [takeWhile, hx, ih ht, Nat.mul_add]
    omega

theorem takeWhile_suffix_independent (d k c : Nat) (p : α → Bool) (pre : List α)
    (bad : α) (left right : List α) (all : ∀ x ∈ pre, p x = true)
    (failed : p bad = false) :
    takeWhile d k c p (pre ++ bad :: left) = takeWhile d k c p (pre ++ bad :: right) := by
  rw [takeWhile_failure d k c p pre bad left all failed,
    takeWhile_failure d k c p pre bad right all failed]

end Resources.ListFusion
