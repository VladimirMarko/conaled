import Applications.Progress.Streams
import SquareKit.PartialSpine.Observations

/-!
# Partial-spine observations of existing deterministic producers

Finite delivery is the operational judgment already used by this domain.
Coherence and prefix closure turn its finite witnesses into an observation
ideal. Guarded and paused realizations refine an independent total-stream ideal;
the observation forgets time, while their original exact delivery counts remain.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Progress

open SquareKit PartialSpine

universe u
variable {S A B : Type u}

/-- Every output prefix of a finite delivery has its own finite delivery witness. -/
theorem Delivers.prefix {step : Producer S A} {s xs t k ys}
    (h : Delivers step s xs t k) (pre : ys <+: xs) :
    ∃ z l, Delivers step s ys z l := by
  induction h generalizing ys with
  | nil s =>
    have hy : ys = [] := List.prefix_nil.mp pre
    subst ys
    exact ⟨s, 0, .nil s⟩
  | cons first rest ih =>
    cases ys with
    | nil => exact ⟨_, 0, .nil _⟩
    | cons b ys =>
      obtain ⟨rfl, hp⟩ := List.cons_prefix_cons.mp pre
      obtain ⟨z, l, hl⟩ := ih hp
      exact ⟨z, _, .cons first hl⟩

/-- Determinism orders finite output observations by their lengths. -/
theorem Delivers.prefix_of_length_le {step : Producer S A} {s xs ys t z k l}
    (h : Delivers step s xs t k) (j : Delivers step s ys z l)
    (lengths : xs.length ≤ ys.length) : xs <+: ys := by
  apply List.prefix_iff_eq_take.mpr
  simpa only [List.take_of_length_le lengths] using h.coherent j

namespace SpineObservations

/-- All finite observations justified by a finite delivery, without a fuel budget. -/
def observations (step : Producer S A) (s : S) : Observations A where
  carrier := {q | ∃ xs t k, Delivers step s xs t k ∧ q ≤ openPrefix xs}
  lower' := by
    rintro p q hpq ⟨xs, t, k, delivery, hq⟩
    exact ⟨xs, t, k, delivery, le_trans hpq hq⟩
  nonempty' := ⟨.bottom, [], s, 0, .nil s, le_rfl⟩
  directed' := by
    rintro p ⟨xs, t, k, hx, hp⟩ q ⟨ys, z, l, hy, hq⟩
    have widen {as bs : List A} (pre : as <+: bs) : openPrefix as ≤ openPrefix bs := by
      rw [openPrefix_le_iff, view_openPrefix]
      exact pre
    rcases Nat.le_total xs.length ys.length with hlen | hlen
    · exact ⟨openPrefix ys, ⟨ys, z, l, hy, le_rfl⟩,
        le_trans hp (widen (hx.prefix_of_length_le hy hlen)), hq⟩
    · exact ⟨openPrefix xs, ⟨xs, t, k, hx, le_rfl⟩, hp,
        le_trans hq (widen (hy.prefix_of_length_le hx hlen))⟩

theorem mem_observations (step : Producer S A) (s : S) (q : PartialSpine A) :
    q ∈ observations step s ↔ ∃ xs t k, Delivers step s xs t k ∧ q ≤ openPrefix xs :=
  Iff.rfl

/-- Exact open prefixes correspond to exact finite deliveries, in both directions. -/
theorem openPrefix_mem_iff (step : Producer S A) (s : S) (xs : List A) :
    openPrefix xs ∈ observations step s ↔ ∃ t k, Delivers step s xs t k := by
  constructor
  · rintro ⟨ys, t, k, delivery, pre⟩
    have hp : xs <+: ys := by simpa only [openPrefix_le_iff, view_openPrefix] using pre
    exact delivery.prefix hp
  · rintro ⟨t, k, delivery⟩
    exact ⟨xs, t, k, delivery, le_rfl⟩

/-- The producer interface has no completed-end transition. -/
theorem ofList_not_mem (step : Producer S A) (s : S) (xs : List A) :
    ofList xs ∉ observations step s := by
  rintro ⟨ys, _, _, _, h⟩
  have he := (ofList_le_iff xs (openPrefix ys)).mp h
  have flags := congrArg (fun q => (view q).2) he
  simp only [view_ofList, view_openPrefix] at flags
  cases flags

theorem not_total_of_mem (step : Producer S A) (s : S) (q : PartialSpine A)
    (observed : q ∈ observations step s) : ¬ IsTotal q := by
  rintro total
  obtain ⟨xs, rfl⟩ := (isTotal_iff_exists q).mp total
  exact ofList_not_mem step s xs observed

/-- Productivity is precisely availability of output observations of every length. -/
theorem productive_iff_observations (step : Producer S A) (s : S) :
    Productive step s ↔
      ∀ n, ∃ xs : List A, xs.length = n ∧ openPrefix xs ∈ observations step s := by
  constructor
  · intro productive n
    obtain ⟨xs, t, k, length, delivery⟩ := productive n
    exact ⟨xs, length, (openPrefix_mem_iff step s xs).mpr ⟨t, k, delivery⟩⟩
  · intro observable n
    obtain ⟨xs, length, observed⟩ := observable n
    obtain ⟨t, k, delivery⟩ := (openPrefix_mem_iff step s xs).mp observed
    exact ⟨xs, t, k, length, delivery⟩

/-- The existing finite coalgebra unfolding is the ordinary stream prefix. -/
theorem unfold_eq_take_corec (c : Coalgebra S A) (s : S) (n : Nat) :
    unfold c s n = (Stream'.corec' c s).take n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    rw [Stream'.corec'_eq, Stream'.take_succ_cons]
    exact congrArg (List.cons (c s).1) (ih (c s).2)

/-- Sufficient finite operational evidence determines the independently given stream. -/
theorem observations_eq_stream (step : Producer S A) (s : S) (σ : Stream' A)
    (delivered : ∀ n, ∃ t k, Delivers step s (σ.take n) t k) :
    observations step s = stream σ := by
  apply Order.Ideal.ext
  apply Set.ext
  intro q
  constructor
  · rintro ⟨xs, t, k, hx, hq⟩
    obtain ⟨z, l, hz⟩ := delivered xs.length
    have lengths : xs.length = (σ.take xs.length).length := (Stream'.length_take _ _).symm
    have same : xs = σ.take xs.length :=
      (hx.prefix_of_length_le hz (Nat.le_of_eq lengths)).eq_of_length lengths
    exact ⟨xs.length, same ▸ hq⟩
  · rintro ⟨n, hq⟩
    obtain ⟨t, k, delivery⟩ := delivered n
    exact ⟨σ.take n, t, k, delivery, hq⟩

theorem observations_guarded (c : Coalgebra S A) (s : S) :
    observations (guarded c) s = stream (Stream'.corec' c s) := by
  apply observations_eq_stream
  intro n
  refine ⟨advance c s n, n, ?_⟩
  rw [← unfold_eq_take_corec]
  exact guarded_delivery c s n

theorem observations_paused (c : Coalgebra S A) (s : S) :
    observations (paused c) (false, s) = stream (Stream'.corec' c s) := by
  apply observations_eq_stream
  intro n
  refine ⟨(false, advance c s n), 2 * n, ?_⟩
  rw [← unfold_eq_take_corec]
  exact paused_delivery c s n

theorem guarded_paused_observations (c : Coalgebra S A) (s : S) :
    observations (guarded c) s = observations (paused c) (false, s) := by
  rw [observations_guarded, observations_paused]

/-- A map of finite partial observations is realized by the existing mapped producer. -/
theorem map_observed_unfold (f : A → B) (c : Coalgebra S A) (s : S) (n : Nat) :
    PartialSpine.map f (openPrefix (unfold c s n)) =
      openPrefix (unfold (mapCoalgebra f c) s n) := by
  rw [map_openPrefix, unfold_map]

/-- This conclusion uses absence of finite evaluations, not exhausted search fuel. -/
theorem observations_silent (next : S → S) (s : S) :
    observations (fun x => .inr (next x) : Producer S A) s = ⊥ := by
  apply Order.Ideal.ext
  apply Set.ext
  intro q
  constructor
  · rintro ⟨xs, t, k, delivery, hq⟩
    cases delivery with
    | nil => exact hq
    | cons first _ => exact False.elim (silent_no_evaluation next first)
  · intro hq
    exact ⟨[], s, 0, .nil s, hq⟩

theorem observations_filter_never (p : A → Bool) (c : Coalgebra S A)
    (never : ∀ s, p (c s).1 = false) (s : S) :
    observations (filterProducer p c) s = ⊥ := by
  have same : filterProducer p c = fun x => .inr (c x).2 := by
    funext x
    simp [filterProducer, never]
  rw [same]
  exact observations_silent _ s

end SpineObservations
end Progress
