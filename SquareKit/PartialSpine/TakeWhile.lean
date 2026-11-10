import SquareKit.PartialSpine.Append

/-!
# Stopping a partial spine with a partial predicate

A false result seals a completed output, while an undefined result leaves an
unknown end. Both differ from lack of an input constructor. The interpretation
uses the shared semantic fold and ordinary `Option Bool` predicate data.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace SquareKit.PartialSpine.Observations

open Order

universe u
variable {α : Type u}

/-- Undefined, false and true tests retain their different end observations. -/
def takeWhileStep (p : α → Option Bool) (a : α) (tail : Observations α) : Observations α :=
  match p a with
  | none => ⊥
  | some false => Ideal.principal .nil
  | some true => cons a tail

theorem takeWhileStep_continuous (p : α → Option Bool) (a : α) :
    ScottContinuous (takeWhileStep p a) := by
  unfold takeWhileStep
  cases p a with
  | none => exact ScottContinuous.const ⊥
  | some b => cases b with
    | false => exact ScottContinuous.const (Ideal.principal (.nil : PartialSpine α))
    | true => exact cons_continuous a

/-- Demand successive tests until the first false or undefined result. -/
def takeWhile (p : α → Option Bool) (I : Observations α) : Observations α :=
  foldr (takeWhileStep p) (Ideal.principal .nil) I

theorem takeWhile_continuous (p : α → Option Bool) : ScottContinuous (takeWhile p) :=
  foldr_continuous (takeWhileStep p) (Ideal.principal .nil)
    (fun a => (takeWhileStep_continuous p a).monotone)

@[simp] theorem takeWhile_bottom (p : α → Option Bool) : takeWhile p ⊥ = ⊥ :=
  foldr_bottom (takeWhileStep p) (Ideal.principal .nil)
    (fun a => (takeWhileStep_continuous p a).monotone)

@[simp] theorem takeWhile_nil (p : α → Option Bool) :
    takeWhile p (Ideal.principal .nil) = Ideal.principal .nil :=
  foldr_nil (takeWhileStep p) (Ideal.principal .nil)
    (fun a => (takeWhileStep_continuous p a).monotone)

theorem takeWhile_cons (p : α → Option Bool) (a : α) (I : Observations α) :
    takeWhile p (cons a I) = takeWhileStep p a (takeWhile p I) :=
  foldr_cons (takeWhileStep p) (Ideal.principal .nil)
    (fun b => (takeWhileStep_continuous p b).monotone) a (takeWhileStep_continuous p a) I

theorem takeWhile_cons_true (p : α → Option Bool) (a : α) (I : Observations α)
    (accepted : p a = some true) : takeWhile p (cons a I) = cons a (takeWhile p I) := by
  rw [takeWhile_cons]
  simp only [takeWhileStep, accepted]

theorem takeWhile_cons_false (p : α → Option Bool) (a : α) (I : Observations α)
    (failed : p a = some false) : takeWhile p (cons a I) = Ideal.principal .nil := by
  rw [takeWhile_cons]
  simp only [takeWhileStep, failed]

theorem takeWhile_cons_undefined (p : α → Option Bool) (a : α) (I : Observations α)
    (undefined : p a = none) : takeWhile p (cons a I) = ⊥ := by
  rw [takeWhile_cons]
  simp only [takeWhileStep, undefined]

/-- Total finite tests refine the independently owned standard list operation. -/
theorem takeWhile_ofList (p : α → Bool) (xs : List α) :
    takeWhile (fun a => some (p a)) (Ideal.principal (ofList xs)) =
      Ideal.principal (ofList (xs.takeWhile p)) := by
  induction xs with
  | nil => exact takeWhile_nil _
  | cons a xs ih =>
    simp only [ofList_cons, ← cons_principal]
    rw [takeWhile_cons]
    cases result : p a <;>
      simp [takeWhileStep, result, ih, cons_principal]

/-- A known accepted prefix passes an arbitrary suffix to the same consumer. -/
theorem takeWhile_prepend (p : α → Option Bool) (pre : List α)
    (accepted : ∀ a ∈ pre, p a = some true) (suffix : Observations α) :
    takeWhile p (append (Ideal.principal (ofList pre)) suffix) =
      append (Ideal.principal (ofList pre)) (takeWhile p suffix) := by
  induction pre with
  | nil => simp only [ofList_nil, append_nil]
  | cons a pre ih =>
    simp only [ofList_cons, ← cons_principal, append_cons]
    rw [takeWhile_cons_true p a _ (accepted a (by simp)),
      ih (fun b hb => accepted b (by simp [hb]))]

/-- The first false test completes the accepted prefix without observing the suffix. -/
theorem takeWhile_stops (p : α → Option Bool) (pre : List α) (a : α)
    (accepted : ∀ b ∈ pre, p b = some true) (failed : p a = some false)
    (suffix : Observations α) :
    takeWhile p (append (Ideal.principal (ofList pre)) (cons a suffix)) =
      Ideal.principal (ofList pre) := by
  rw [takeWhile_prepend p pre accepted, takeWhile_cons_false p a suffix failed,
    append_right_nil]

theorem takeWhile_suffix_independent (p : α → Option Bool) (pre : List α) (a : α)
    (accepted : ∀ b ∈ pre, p b = some true) (failed : p a = some false)
    (xs ys : Observations α) :
    takeWhile p (append (Ideal.principal (ofList pre)) (cons a xs)) =
      takeWhile p (append (Ideal.principal (ofList pre)) (cons a ys)) := by
  rw [takeWhile_stops p pre a accepted failed, takeWhile_stops p pre a accepted failed]

/-- An undefined next test leaves the accepted prefix open, independently of the suffix. -/
theorem takeWhile_undefined_after_prefix (p : α → Option Bool) (pre : List α) (a : α)
    (accepted : ∀ b ∈ pre, p b = some true) (undefined : p a = none)
    (suffix : Observations α) :
    takeWhile p (append (Ideal.principal (ofList pre)) (cons a suffix)) =
      append (Ideal.principal (ofList pre)) ⊥ := by
  rw [takeWhile_prepend p pre accepted, takeWhile_cons_undefined p a suffix undefined]

/-- An accepted open prefix stays open until a subsequent constructor is observed. -/
theorem takeWhile_openPrefix (p : α → Option Bool) (pre : List α)
    (accepted : ∀ a ∈ pre, p a = some true) :
    takeWhile p (Ideal.principal (openPrefix pre)) = Ideal.principal (openPrefix pre) := by
  induction pre with
  | nil => exact takeWhile_bottom p
  | cons a pre ih =>
    simp only [openPrefix_cons, ← cons_principal]
    rw [takeWhile_cons_true p a _ (accepted a (by simp)),
      ih (fun b hb => accepted b (by simp [hb]))]

/-- Every accepted infinite stream is the directed limit of fixed open prefixes. -/
theorem takeWhile_stream (p : α → Option Bool) (σ : Stream' α)
    (accepted : ∀ n, p (σ n) = some true) : takeWhile p (stream σ) = stream σ := by
  have prefix_fixed (n : Nat) : takeWhile p (Ideal.principal (openPrefix (σ.take n))) =
      Ideal.principal (openPrefix (σ.take n)) := by
    apply takeWhile_openPrefix
    intro a ha
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ha
    simpa only [Stream'.take_get, Stream'.get] using accepted k
  have fixed : takeWhile p '' (Set.range fun n => Ideal.principal (openPrefix (σ.take n))) =
      Set.range (fun n => Ideal.principal (openPrefix (σ.take n))) := by
    rw [← Set.range_comp']
    exact congrArg Set.range (funext prefix_fixed)
  have lub := takeWhile_continuous p (Set.range_nonempty _)
    (stream_prefixes_directed σ) (stream_prefixes_isLUB σ)
  rw [fixed] at lub
  exact lub.unique (stream_prefixes_isLUB σ)

end SquareKit.PartialSpine.Observations
