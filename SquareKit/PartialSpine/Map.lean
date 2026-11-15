import SquareKit.PartialSpine.Limits

/-!
# Mapping observations and consuming their first label

Map and head specialize the existing semantic fold. Mapping changes known
labels without changing the distinction between unknown and completed ends.
Head uses a standard CPO supplied on its result labels; the spine information
order still fixes those labels and imposes no order on a mapping function.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace SquareKit.PartialSpine.Observations

open Order

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- Map known labels through the shared fold, retaining the observed end. -/
def map (f : α → β) (I : Observations α) : Observations β :=
  foldr (fun a => cons (f a)) (Ideal.principal .nil) I

theorem map_continuous (f : α → β) : ScottContinuous (map f) :=
  foldr_continuous (fun a => cons (f a)) (Ideal.principal .nil)
    (fun a => cons_monotone (f a))

@[simp] theorem map_bottom (f : α → β) : map f ⊥ = ⊥ :=
  foldr_bottom (fun a => cons (f a)) (Ideal.principal .nil)
    (fun a => cons_monotone (f a))

@[simp] theorem map_nil (f : α → β) :
    map f (Ideal.principal .nil) = Ideal.principal .nil :=
  foldr_nil (fun a => cons (f a)) (Ideal.principal .nil)
    (fun a => cons_monotone (f a))

theorem map_cons (f : α → β) (a : α) (I : Observations α) :
    map f (cons a I) = cons (f a) (map f I) :=
  foldr_cons (fun a => cons (f a)) (Ideal.principal .nil)
    (fun a => cons_monotone (f a)) a (cons_continuous (f a)) I

/-- Every finite observation reuses the existing finite map, including its end flag. -/
theorem map_principal (f : α → β) (s : PartialSpine α) :
    map f (Ideal.principal s) = Ideal.principal (PartialSpine.map f s) := by
  rw [map, foldr_principal _ _ (fun a => cons_monotone (f a))]
  exact (PartialSpine.foldr_unique (⊥ : Observations β) (fun a => cons (f a))
    (Ideal.principal .nil) (fun s => Ideal.principal (PartialSpine.map f s))
    rfl rfl (fun a s => (cons_principal (f a) (PartialSpine.map f s)).symm) s).symm

theorem map_ofList (f : α → β) (xs : List α) :
    map f (Ideal.principal (ofList xs)) = Ideal.principal (ofList (xs.map f)) := by
  rw [map_principal, PartialSpine.map_ofList]

theorem map_id (I : Observations α) : map id I = I := foldr_cons_identity I

/-- Strict continuous fold fusion retains the original seed and composed algebra. -/
theorem foldr_map [CompletePartialOrder γ] (f : β → γ → γ) (g : α → β) (e : γ)
    (continuous : ∀ b, ScottContinuous (f b)) (I : Observations α) :
    foldr f e (map g I) = foldr (fun a => f (g a)) e I := by
  have fused := foldr_fusion (fun a => cons (g a)) (fun a => f (g a))
    (Ideal.principal .nil) (fun a => cons_monotone (g a))
    (fun a => (continuous (g a)).monotone) (foldr f e)
    (foldr_continuous f e (fun b => (continuous b).monotone))
    (foldr_bottom f e (fun b => (continuous b).monotone))
    (fun a J => foldr_cons f e (fun b => (continuous b).monotone)
      (g a) (continuous (g a)) J) I
  change foldr f e (map g I) =
    foldr (fun a => f (g a)) (foldr f e (Ideal.principal .nil)) I at fused
  rw [foldr_nil f e (fun b => (continuous b).monotone)] at fused
  exact fused

theorem map_fusion (f : β → γ) (g : α → β) (I : Observations α) :
    map f (map g I) = map (fun a => f (g a)) I :=
  foldr_map (fun b => cons (f b)) g (Ideal.principal .nil)
    (fun b => cons_continuous (f b)) I

/-- Mapping the directed family of finite prefixes gives ordinary stream map. -/
theorem map_stream (f : α → β) (σ : Stream' α) :
    map f (stream σ) = stream (Stream'.map f σ) := by
  have mapped : map f '' (Set.range fun n => Ideal.principal (openPrefix (σ.take n))) =
      Set.range (fun n => Ideal.principal (openPrefix ((Stream'.map f σ).take n))) := by
    rw [← Set.range_comp']
    simp only [map_principal, PartialSpine.map_openPrefix, Stream'.map_take]
  have lub := map_continuous f (Set.range_nonempty _)
    (stream_prefixes_directed σ) (stream_prefixes_isLUB σ)
  rw [mapped] at lub
  exact lub.unique (stream_prefixes_isLUB (Stream'.map f σ))

section Head

variable [CompletePartialOrder α]

/-- Observe the first known label in the caller's CPO, defaulting to its bottom. -/
def head (I : Observations α) : α := foldr (fun a _ => a) ⊥ I

theorem head_continuous : ScottContinuous (head (α := α)) :=
  foldr_continuous (fun a _ => a) ⊥ (fun a => (ScottContinuous.const a).monotone)

@[simp] theorem head_bottom : head (⊥ : Observations α) = ⊥ :=
  foldr_bottom (fun a _ => a) ⊥ (fun a => (ScottContinuous.const a).monotone)

@[simp] theorem head_nil : head (Ideal.principal (.nil : PartialSpine α)) = ⊥ :=
  foldr_nil (fun a _ => a) ⊥ (fun a => (ScottContinuous.const a).monotone)

/-- No observation of an arbitrary tail is needed once its first cons is known. -/
theorem head_cons (a : α) (I : Observations α) : head (cons a I) = a :=
  foldr_cons (fun a _ => a) ⊥ (fun a => (ScottContinuous.const a).monotone)
    a (ScottContinuous.const a) I

theorem head_tail_independent (a : α) (I J : Observations α) :
    head (cons a I) = head (cons a J) := by
  rw [head_cons, head_cons]

theorem head_stream (σ : Stream' α) : head (stream σ) = σ 0 := by
  rw [stream_cons, head_cons]

theorem head_ofList (xs : List α) :
    head (Ideal.principal (ofList xs)) = xs.headD ⊥ := by
  cases xs with
  | nil => exact head_nil
  | cons a xs =>
    rw [ofList_cons, ← cons_principal, head_cons]
    rfl

end Head
end SquareKit.PartialSpine.Observations
