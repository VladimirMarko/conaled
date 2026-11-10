import Applications.Progress.SpineObservations

/-!
# Partial observations consumed after actual producer deliveries

An output followed by silence has a known head and an unknown continuation.
The map/head composition below uses strict finite fusion and the existing mapped
producer. Guarded and paused observations agree while their step counts differ.
-/

set_option autoImplicit false
set_option warningAsError true

namespace PartialSpineProgress

open SquareKit PartialSpine Progress Progress.SpineObservations

universe u
variable {A B S : Type u}

def head (q : PartialSpine A) : Option A :=
  foldr none (fun a _ => some a) none q

theorem head_cons (a : A) (q : PartialSpine A) : head (.cons a q) = some a := rfl

/-- The strict observer law supplies the head/map transport, including unknown ends. -/
theorem mapped_head (f : A → B) (q : PartialSpine A) :
    (head q).map f = head (PartialSpine.map f q) := by
  simpa only [head, foldr_map, Option.map_none] using
    foldr_fusion (none : Option A) (none : Option B)
      (fun a _ => some a) (fun a _ => some (f a)) (Option.map f) none
      rfl (fun _ _ => rfl) q

/-- A mapped producer's delivered prefix is consumed through the shared fusion law. -/
theorem mapped_producer_prefix (f : A → B) (c : Coalgebra S A) (s : S) (n : Nat) :
    let q := PartialSpine.map f (openPrefix (unfold c s (n + 1)))
    q ∈ observations (guarded (mapCoalgebra f c)) s ∧ head q = some (f (c s).1) := by
  constructor
  · rw [map_observed_unfold]
    exact (openPrefix_mem_iff _ _ _).mpr
      ⟨_, _, guarded_delivery (mapCoalgebra f c) s (n + 1)⟩
  · rw [← mapped_head]
    change (head (.cons (c s).1 (openPrefix (unfold c (c s).2 n)))).map f = _
    rw [head_cons]
    rfl

/-- Emit once, then continue silently forever. There is no end-of-stream transition. -/
def once : Producer (Option A) A
  | some a => .inl (a, none)
  | none => .inr none

private theorem once_none_no_eval {r : A × Option A} {k : Nat} :
    ¬ Evaluates once none r k := by
  intro h
  induction k generalizing r with
  | zero => cases h
  | succ k ih =>
    cases h with
    | done he => cases he
    | next he rest => cases he; exact ih rest

/-- The whole finite-observation ideal is determined, not just its first member. -/
theorem once_observations (a : A) :
    observations once (some a) = Order.Ideal.principal (.cons a .bottom) := by
  apply Order.Ideal.ext
  apply Set.ext
  intro q
  constructor
  · rintro ⟨xs, t, k, delivery, hq⟩
    cases delivery with
    | nil => exact le_trans hq bot_le
    | cons first rest =>
      have same := (first.unique
        (show Evaluates once (some a) (a, none) 1 from .done rfl)).1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      cases rest with
      | nil => exact hq
      | cons first _ => exact False.elim (once_none_no_eval first)
  · intro hq
    refine ⟨[a], none, 1, ?_, hq⟩
    simpa using Delivers.cons
      (show Evaluates once (some a) (a, none) 1 from .done rfl) (Delivers.nil none)

theorem once_no_second (a b c : A) :
    openPrefix [b, c] ∉ observations once (some a) := by
  rw [once_observations]
  intro h
  have lengths := knownLength_mono h
  change 2 ≤ 1 at lengths
  omega

theorem once_not_productive (a : A) : ¬ Productive once (some a) := by
  intro productive
  obtain ⟨xs, length, observed⟩ := (productive_iff_observations once (some a)).mp productive 2
  rw [once_observations] at observed
  have lengths := knownLength_mono observed
  rw [knownLength_openPrefix, length] at lengths
  change 2 ≤ 1 at lengths
  omega

theorem once_head_observed (a : A) :
    (.cons a .bottom : PartialSpine A) ∈ observations once (some a) ∧
      head (.cons a .bottom) = some a := by
  rw [once_observations]
  exact ⟨Order.Ideal.mem_principal_self, head_cons a .bottom⟩

/-- One delivered observation supports a head consumer but not a strict tail sum. -/
theorem once_consumers (a : Nat) :
    ∃ q ∈ observations once (some a), head q = some a ∧
      foldr none (fun x (ys : Option Nat) => ys.map (x + ·)) (some 0) q = none := by
  refine ⟨.cons a .bottom, (once_head_observed a).1, (once_head_observed a).2, ?_⟩
  rw [foldr_eq_view]
  rfl

example (a : A) : (.nil : PartialSpine A) ∉ observations once (some a) :=
  ofList_not_mem once (some a) []

def count : Coalgebra Nat Nat := fun n => (n, n + 1)

theorem count_deliveries (s n : Nat) :
    Delivers (guarded count) s (unfold count s n) (advance count s n) n ∧
      Delivers (paused count) (false, s) (unfold count s n)
        (false, advance count s n) (2 * n) :=
  guarded_paused_progress count s n

example : Delivers (guarded count) 4 [4, 5, 6] 7 3 ∧
    Delivers (paused count) (false, 4) [4, 5, 6] (false, 7) 6 := by
  simpa [unfold, advance, count] using count_deliveries 4 3

example (s : Nat) : observations (guarded count) s = observations (paused count) (false, s) :=
  guarded_paused_observations count s

example (s : Nat) (q : PartialSpine Nat) :
    observations (guarded count) s ≠ Order.Ideal.principal q := by
  rw [observations_guarded]
  exact stream_ne_principal _ q

example : PartialSpine.map (fun n : Nat => n + 1) (openPrefix (unfold count 4 3)) ∈
    observations (guarded (mapCoalgebra (fun n => n + 1) count)) 4 ∧
    head (PartialSpine.map (fun n : Nat => n + 1) (openPrefix (unfold count 4 3))) = some 5 :=
  mapped_producer_prefix (fun n => n + 1) count 4 2

example (s : Nat) : observations (fun n => .inr (n + 1) : Producer Nat Nat) s = ⊥ :=
  observations_silent _ s

example (s : Nat) : observations (filterProducer (fun _ : Nat => false) count) s = ⊥ :=
  observations_filter_never _ count (fun _ => rfl) s

private def constantStep (_ : Unit) (_ : Option Bool) : Option Bool := some true
private def constantObserver (_ : Option Bool) : Option Bool := some true

/-- Commuting alone does not justify fusion at the unknown end. -/
theorem nonstrict_counterexample :
    (∀ a b, constantObserver (constantStep a b) =
      constantStep a (constantObserver b)) ∧
    constantObserver none ≠ none ∧
    constantObserver (foldr none constantStep none (.bottom : PartialSpine Unit)) ≠
      foldr none constantStep (constantObserver none) (.bottom : PartialSpine Unit) := by
  exact ⟨fun _ _ => rfl, by decide, by decide⟩

theorem nonstrict_total_fusion (xs : List Unit) :
    constantObserver (foldr none constantStep none (ofList xs)) =
      foldr none constantStep (constantObserver none) (ofList xs) :=
  foldr_fusion_ofList none none constantStep constantStep constantObserver none
    nonstrict_counterexample.1 xs

example : head (.bottom : PartialSpine Nat) = none ∧ head (.nil : PartialSpine Nat) = none ∧
    head (.cons 7 .bottom) = some 7 :=
  ⟨rfl, rfl, head_cons 7 .bottom⟩

-- All six anonymous PartialLists source cases, connected to public interpretations.
example : foldr none (fun x (_ : Option Nat) => some x) none
    (.cons 7 .bottom) = some 7 := by
  rw [foldr_eq_view]
  rfl

example : foldr none (fun x (ys : Option Nat) => ys.map (x + ·)) (some 0)
    (.cons 7 .bottom) = none := by
  rw [foldr_eq_view]
  rfl

example : (.cons none .nil : PartialSpine (Option Nat)) ≠ .bottom := by decide

example : foldr none (fun (_ : Option Nat) (_ : Option Bool) => some true) none
    (.cons none .nil) = some true := by
  rw [foldr_eq_view]
  rfl

example : PartialSpine.map (· + 1) (.cons 7 (.cons 9 .bottom)) =
    (.cons 8 (.cons 10 .bottom) : PartialSpine Nat) := by
  apply view_injective
  rw [view_map]
  rfl

example : foldr 100 (· + ·) 0 (ofList [2, 3, 5]) = 10 := by
  rw [foldr_ofList]
  rfl

example : (view (.bottom : PartialSpine Nat), view (.nil : PartialSpine Nat),
    view (.cons 7 .bottom : PartialSpine Nat)) = (([], false), ([], true), ([7], false)) := rfl

example : openPrefix [2, 2] ≤ ofList [2, 2, 5] := by
  rw [openPrefix_le_iff, view_ofList]
  exact ⟨[5], rfl⟩

example : ¬ ofList [2, 2] ≤ ofList [2, 2, 5] := by
  rw [ofList_le_iff]
  intro same
  have lists := ofList_injective same
  cases lists

end PartialSpineProgress
