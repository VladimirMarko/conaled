import Applications.Optimization.Transport
import Mathlib.Data.List.Basic

/-!
# Candidate refinement and adjacent thinning

Reconstructed from ADWH checkpoint 233, Chapter 10. See
`docs/research/adwh-thinning-reconstruction.md` for declaration provenance.
Coverage, origin, and order are separate contracts. No antichain or idempotence
claim is made for the adjacent implementation.
-/
namespace Optimization.Thinning
universe u v w
variable {α : Type u} {β : Type v} {δ : Type w}

def Covers (R : α → α → Prop) (representatives candidates : List α) : Prop :=
  ∀ y ∈ candidates, ∃ x ∈ representatives, R x y

/-- The book's nondeterministic `ThinBy` relation, including order preservation. -/
def IsThinning (R : α → α → Prop) (input output : List α) : Prop :=
  output.Sublist input ∧ Covers R output input

theorem thinning_refl (R : α → α → Prop) (hr : ∀ x, R x x) (xs : List α) :
    IsThinning R xs xs := ⟨.refl _, fun x hx => ⟨x, hx, hr x⟩⟩

theorem thinning_trans (R : α → α → Prop)
    (ht : ∀ x y z, R x y → R y z → R x z)
    (xs ys zs : List α) (hxy : IsThinning R xs ys) (hyz : IsThinning R ys zs) :
    IsThinning R xs zs := by
  refine ⟨hyz.1.trans hxy.1, ?_⟩
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hxy.2 x hx
  obtain ⟨z, hz, hzy⟩ := hyz.2 y hy
  exact ⟨z, hz, ht z y x hzy hyx⟩

/-- Relational idempotence does not claim idempotence of every deterministic
implementation of the specification. -/
theorem thinning_composition (R : α → α → Prop) (hr : ∀ x, R x x)
    (ht : ∀ x y z, R x y → R y z → R x z) (xs zs : List α) :
    IsThinning R xs zs ↔ ∃ ys, IsThinning R xs ys ∧ IsThinning R ys zs := by
  constructor
  · intro h
    exact ⟨xs, thinning_refl R hr xs, h⟩
  · rintro ⟨ys, hxy, hyz⟩
    exact thinning_trans R ht xs ys zs hxy hyz

theorem thinning_nil_iff (R : α → α → Prop) (ys : List α) :
    IsThinning R [] ys ↔ ys = [] := by
  constructor
  · intro h
    exact List.sublist_nil.mp h.1
  · rintro rfl
    exact ⟨.refl _, by intro x hx; simp at hx⟩

theorem thinning_empty_iff (R : α → α → Prop) (xs ys : List α)
    (h : IsThinning R xs ys) : ys = [] ↔ xs = [] := by
  constructor
  · intro hy
    cases xs with
    | nil => rfl
    | cons x xs =>
        obtain ⟨z, hz, _⟩ := h.2 x (by simp)
        simp [hy] at hz
  · intro hx
    subst xs
    exact (thinning_nil_iff R ys).mp h

theorem thinning_length_le (R : α → α → Prop) (xs ys : List α)
    (h : IsThinning R xs ys) : ys.length ≤ xs.length := h.1.length_le

/-! ## The actual adjacent-comparison implementation -/

/-- This is the source's `bump`, with its stated left-to-right guard priority. -/
def bump (R : α → α → Prop) [DecidableRel R] (x : α) : List α → List α
  | [] => [x]
  | y :: ys => if R x y then x :: ys else if R y x then y :: ys else x :: y :: ys

def thinBy (R : α → α → Prop) [DecidableRel R] (xs : List α) : List α :=
  xs.foldr (bump R) []

theorem bump_sublist (R : α → α → Prop) [DecidableRel R] (x : α) (ys : List α) :
    (bump R x ys).Sublist (x :: ys) := by
  cases ys with
  | nil => exact .refl _
  | cons y ys =>
      by_cases hxy : R x y
      · simp only [bump, ite_eq_left hxy]
        exact (List.sublist_cons_self y ys).cons_cons x
      · by_cases hyx : R y x
        · simp only [bump, ite_eq_right hxy, ite_eq_left hyx]
          exact List.sublist_cons_self x (y :: ys)
        · simp only [bump, ite_eq_right hxy, ite_eq_right hyx]
          exact .refl _

theorem bump_thinning (R : α → α → Prop) [DecidableRel R]
    (hr : ∀ x, R x x) (x : α) (ys : List α) :
    IsThinning R (x :: ys) (bump R x ys) := by
  refine ⟨bump_sublist R x ys, ?_⟩
  cases ys with
  | nil => exact fun y hy => ⟨y, hy, hr y⟩
  | cons y ys =>
      by_cases hxy : R x y
      · simp only [bump, ite_eq_left hxy]
        intro z hz
        rcases List.mem_cons.mp hz with hzx | hz
        · subst z; exact ⟨x, by simp, hr x⟩
        · rcases List.mem_cons.mp hz with hzy | hz
          · subst z; exact ⟨x, by simp, hxy⟩
          · exact ⟨z, by simp [hz], hr z⟩
      · by_cases hyx : R y x
        · simp only [bump, ite_eq_right hxy, ite_eq_left hyx]
          intro z hz
          rcases List.mem_cons.mp hz with hzx | hz
          · subst z; exact ⟨y, by simp, hyx⟩
          · exact ⟨z, hz, hr z⟩
        · simp only [bump, ite_eq_right hxy, ite_eq_right hyx]
          exact fun z hz => ⟨z, hz, hr z⟩

theorem thinning_cons (R : α → α → Prop) (hr : ∀ x, R x x)
    (x : α) (xs ys : List α) (h : IsThinning R xs ys) :
    IsThinning R (x :: xs) (x :: ys) := by
  refine ⟨h.1.cons_cons x, ?_⟩
  intro z hz
  rcases List.mem_cons.mp hz with hzx | hz
  · subst z; exact ⟨x, by simp, hr x⟩
  · obtain ⟨y, hy, hyz⟩ := h.2 z hz
    exact ⟨y, by simp [hy], hyz⟩

theorem thinBy_correct (R : α → α → Prop) [DecidableRel R]
    (hr : ∀ x, R x x) (ht : ∀ x y z, R x y → R y z → R x z) (xs : List α) :
    IsThinning R xs (thinBy R xs) := by
  induction xs with
  | nil => exact thinning_refl R hr []
  | cons x xs ih =>
      change IsThinning R (x :: xs) (bump R x (thinBy R xs))
      exact thinning_trans R ht _ _ _ (thinning_cons R hr x xs _ ih)
        (bump_thinning R hr x _)

theorem thinning_map (R : α → α → Prop) (S : β → β → Prop) (f : α → β)
    (hm : ∀ x y, R x y → S (f x) (f y))
    (xs ys : List α) (h : IsThinning R xs ys) :
    IsThinning S (xs.map f) (ys.map f) := by
  refine ⟨h.1.map f, ?_⟩
  intro z hz
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hz
  obtain ⟨y, hy, hyx⟩ := h.2 x hx
  exact ⟨f y, List.mem_map.mpr ⟨y, hy, rfl⟩, hm y x hyx⟩

theorem thinning_filter (R : α → α → Prop) (good : α → Bool)
    (hc : ∀ x y, R x y → good y = true → good x = true)
    (xs ys : List α) (h : IsThinning R xs ys) :
    IsThinning R (xs.filter good) (ys.filter good) := by
  refine ⟨h.1.filter good, ?_⟩
  intro x hx
  obtain ⟨hx, hg⟩ := List.mem_filter.mp hx
  obtain ⟨y, hy, hyx⟩ := h.2 x hx
  exact ⟨y, List.mem_filter.mpr ⟨hy, hc y x hyx hg⟩, hyx⟩


/-- Representatives originate in the input and cover it. Reordering is allowed. -/
def Represents (R : α → α → Prop) (input output : List α) : Prop :=
  output ⊆ input ∧ Covers R output input

theorem IsThinning.represents {R : α → α → Prop} {xs ys : List α}
    (h : IsThinning R xs ys) : Represents R xs ys := ⟨h.1.subset, h.2⟩

theorem represents_refl (R : α → α → Prop) (hr : ∀ x, R x x) (xs : List α) :
    Represents R xs xs := ⟨fun _ h => h, fun x hx => ⟨x, hx, hr x⟩⟩

theorem represents_trans {R : α → α → Prop}
    (ht : ∀ x y z, R x y → R y z → R x z) {xs ys zs : List α}
    (hxy : Represents R xs ys) (hyz : Represents R ys zs) : Represents R xs zs := by
  refine ⟨fun _ h => hxy.1 (hyz.1 h), ?_⟩
  intro x hx
  obtain ⟨y, hy, hyx⟩ := hxy.2 x hx
  obtain ⟨z, hz, hzy⟩ := hyz.2 y hy
  exact ⟨z, hz, ht z y x hzy hyx⟩

theorem represents_empty_iff {R : α → α → Prop} {xs ys : List α}
    (h : Represents R xs ys) : ys = [] ↔ xs = [] := by
  constructor
  · intro hy
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro x hx
    obtain ⟨y, hmem, _⟩ := h.2 x hx
    simp [hy] at hmem
  · intro hx
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro y hy
    have := h.1 hy
    simp [hx] at this

theorem represents_map {R : α → α → Prop} {S : β → β → Prop}
    (f : α → β) (hm : ∀ x y, R x y → S (f x) (f y))
    {xs ys : List α} (h : Represents R xs ys) :
    Represents S (xs.map f) (ys.map f) := by
  constructor
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    exact List.mem_map.mpr ⟨a, h.1 ha, rfl⟩
  · intro b hb
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
    obtain ⟨c, hc, hca⟩ := h.2 a ha
    exact ⟨f c, List.mem_map.mpr ⟨c, hc, rfl⟩, hm c a hca⟩

theorem represents_flatMap {R : α → α → Prop} {S : β → β → Prop}
    (extend : α → List β)
    (he : ∀ x y, R x y → Covers S (extend x) (extend y))
    {xs ys : List α} (h : Represents R xs ys) :
    Represents S (xs.flatMap extend) (ys.flatMap extend) := by
  constructor
  · intro b hb
    obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp hb
    exact List.mem_flatMap.mpr ⟨a, h.1 ha, hb⟩
  · intro b hb
    obtain ⟨a, ha, hb⟩ := List.mem_flatMap.mp hb
    obtain ⟨c, hc, hca⟩ := h.2 a ha
    obtain ⟨d, hd, hdb⟩ := he c a hca b hb
    exact ⟨d, List.mem_flatMap.mpr ⟨c, hc, hd⟩, hdb⟩

/-- Insert pruning after every generator step. The generator remains independently
specified and can enumerate edge-first or candidate-first. -/
def pruneFold (step : δ → List α → List α) (prune : List α → List α)
    (seed : List α) (ds : List δ) : List α :=
  ds.foldr (fun d xs => prune (step d xs)) seed

theorem pruneFold_refinement (R : α → α → Prop)
    (hr : ∀ x, R x x) (ht : ∀ x y z, R x y → R y z → R x z)
    (step : δ → List α → List α) (prune : List α → List α)
    (step_preserves : ∀ d xs ys, Represents R xs ys → Represents R (step d xs) (step d ys))
    (prune_correct : ∀ xs, Represents R xs (prune xs)) (seed : List α) (ds : List δ) :
    Represents R (ds.foldr step seed) (pruneFold step prune seed ds) := by
  induction ds with
  | nil => exact represents_refl R hr seed
  | cons d ds ih =>
    exact represents_trans ht (step_preserves d _ _ ih) (prune_correct _)

theorem pruneFold_thinning (R : α → α → Prop)
    (hr : ∀ x, R x x) (ht : ∀ x y z, R x y → R y z → R x z)
    (step : δ → List α → List α) (prune : List α → List α)
    (step_preserves : ∀ d xs ys, IsThinning R xs ys → IsThinning R (step d xs) (step d ys))
    (prune_correct : ∀ xs, IsThinning R xs (prune xs)) (seed : List α) (ds : List δ) :
    IsThinning R (ds.foldr step seed) (pruneFold step prune seed ds) := by
  induction ds with
  | nil => exact thinning_refl R hr seed
  | cons d ds ih =>
    exact thinning_trans R ht _ _ _ (step_preserves d _ _ ih) (prune_correct _)

/-- The retained minimum is admissible because it originates in the input.
Dominance supplies the lifts required by the existing optimization transport. -/
theorem minimizer_of_represents {K : Type*} [Preorder K]
    {R : α → α → Prop} {xs ys : List α} (h : Represents R xs ys)
    (cost : α → K) (hc : ∀ x ∈ xs, ∀ y ∈ xs, R x y → cost x ≤ cost y)
    {z : α} (hz : z ∈ minimizers {x | x ∈ ys} cost) :
    z ∈ minimizers {x | x ∈ xs} cost := by
  apply minimizer_transport (A := {x | x ∈ ys}) (B := {x | x ∈ xs})
    (c := cost) (J := cost) id id (fun _ _ h => h)
    (fun _ hx => h.1 hx) (fun _ _ => rfl) ?_ hz
  intro t ht
  obtain ⟨q, hq, hqt⟩ := h.2 t ht
  exact ⟨q, hq, hc q (h.1 hq) t ht hqt⟩

/-- A total selector. Equal costs retain the first occurrence. -/
def argmin {K : Type*} [LinearOrder K] (cost : α → K) : List α → Option α
  | [] => none
  | x :: xs =>
    match argmin cost xs with
    | none => some x
    | some y => some (if cost x ≤ cost y then x else y)

theorem argmin_eq_none_iff {K : Type*} [LinearOrder K] (cost : α → K) (xs : List α) :
    argmin cost xs = none ↔ xs = [] := by
  cases xs with
  | nil => simp [argmin]
  | cons x xs => cases he : argmin cost xs <;> simp [argmin, he]

theorem argmin_correct {K : Type*} [LinearOrder K] (cost : α → K) (xs : List α) (z : α)
    (hz : argmin cost xs = some z) : z ∈ minimizers {x | x ∈ xs} cost := by
  induction xs generalizing z with
  | nil => simp [argmin] at hz
  | cons x xs ih =>
    cases he : argmin cost xs with
    | none =>
      have hx := (argmin_eq_none_iff cost xs).mp he
      subst xs
      have hzx : z = x := by simpa [argmin] using hz.symm
      subst z
      refine ⟨by simp, ?_⟩
      intro y hy
      have : y = x := List.mem_singleton.mp hy
      subst y
      exact le_rfl
    | some y =>
      have hy := ih y he
      by_cases hc : cost x ≤ cost y
      · have hzx : z = x := by simpa [argmin, he, hc] using hz.symm
        subst z
        refine ⟨by simp, ?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact le_rfl
        · exact le_trans hc (hy.2 ha)
      · have hzy : z = y := by simpa [argmin, he, hc] using hz.symm
        subst z
        refine ⟨List.mem_cons_of_mem x hy.1, ?_⟩
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact le_of_not_ge hc
        · exact hy.2 ha

/-- If the first candidate has least cost, the selector retains it even on ties. -/
theorem argmin_first {K : Type*} [LinearOrder K] (cost : α → K) (x : α) (xs : List α)
    (h : ∀ y ∈ xs, cost x ≤ cost y) : argmin cost (x :: xs) = some x := by
  cases he : argmin cost xs with
  | none => simp [argmin, he]
  | some y =>
    have hy := (argmin_correct cost xs y he).1
    simp [argmin, he, h y hy]

end Optimization.Thinning
