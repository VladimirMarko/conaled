import SquareKit.PartialSpine.Map

/-!
# Zipping a total stream with partial observations

The first input supplies a label at every natural index. The second may have
an unknown end, a completed end, or infinitely many observations. One finite
interpreter extends through the existing ideal completion; labels need no order.
Online labeling specializes the total first stream to natural indices.
-/

set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.PartialSpine

universe u v
variable {α : Type u} {β : Type v}

/-- Zip known labels, preserving the second input's observed end. -/
def zipStream (σ : Stream' β) : PartialSpine α → PartialSpine (β × α)
  | .bottom => .bottom
  | .nil => .nil
  | .cons a s => .cons (σ 0, a) (zipStream σ.tail s)

/-- The independent finite specification is native list zip with the same end flag. -/
theorem view_zipStream (σ : Stream' β) (s : PartialSpine α) :
    view (zipStream σ s) =
      ((σ.take (view s).1.length).zip (view s).1, (view s).2) := by
  induction s generalizing σ with
  | bottom => rfl
  | nil => rfl
  | cons a s ih =>
    simp only [zipStream, view, ih, List.length_cons, Stream'.take_succ,
      Stream'.head, Stream'.get, List.zip_cons_cons]

theorem zipStream_monotone (σ : Stream' β) : Monotone (zipStream (α := α) σ) := by
  intro s t h
  induction h generalizing σ with
  | bottom => exact bot_le
  | nil => exact le_rfl
  | cons a _ ih => exact Below.cons (σ 0, a) (ih σ.tail)

theorem zipStream_ofList (σ : Stream' β) (xs : List α) :
    zipStream σ (ofList xs) = ofList ((σ.take xs.length).zip xs) := by
  apply view_injective
  simp only [view_zipStream, view_ofList]

theorem zipStream_openPrefix (σ : Stream' β) (xs : List α) :
    zipStream σ (openPrefix xs) = openPrefix ((σ.take xs.length).zip xs) := by
  apply view_injective
  simp only [view_zipStream, view_openPrefix]

/-- Enough first-stream labels are available for every known second-input label. -/
theorem map_snd_zipStream (σ : Stream' β) (s : PartialSpine α) :
    map Prod.snd (zipStream σ s) = s := by
  apply view_injective
  rw [view_map, view_zipStream]
  change (((σ.take (view s).1.length).zip (view s).1).map Prod.snd, (view s).2) = view s
  rw [List.map_snd_zip (by simp)]

theorem zipStream_streamPrefix (σ : Stream' β) (τ : Stream' α) (n : Nat) :
    zipStream σ (openPrefix (τ.take n)) =
      openPrefix ((Stream'.zip Prod.mk σ τ).take n) := by
  induction n generalizing σ τ with
  | zero => rfl
  | succ n ih =>
    change cons (σ 0, τ 0) (zipStream σ.tail (openPrefix (τ.tail.take n))) =
      cons (σ 0, τ 0) (openPrefix ((Stream'.zip Prod.mk σ.tail τ.tail).take n))
    exact congrArg (cons (σ 0, τ 0)) (ih σ.tail τ.tail)

private theorem indexStream_tail (n : Nat) :
    Stream'.tail (fun k => n + k) = fun k => (n + 1) + k := by
  funext k
  change n + (k + 1) = (n + 1) + k
  rw [Nat.add_assoc, Nat.add_comm 1 k]

private theorem take_indexStream (n m : Nat) :
    Stream'.take m (fun k => n + k) = List.range' n m := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih =>
    change n :: (Stream'.tail (fun k => n + k)).take m = n :: List.range' (n + 1) m
    rw [indexStream_tail, ih]

theorem zipStream_index_ofList (n : Nat) (xs : List α) :
    zipStream (fun k => n + k) (ofList xs) =
      ofList ((List.range' n xs.length).zip xs) := by
  erw [zipStream_ofList, take_indexStream]

theorem zipStream_index_openPrefix (n : Nat) (xs : List α) :
    zipStream (fun k => n + k) (openPrefix xs) =
      openPrefix ((List.range' n xs.length).zip xs) := by
  erw [zipStream_openPrefix, take_indexStream]

namespace Observations

open Order
noncomputable section

private theorem principalZip_monotone (σ : Stream' β) :
    Monotone (fun s : PartialSpine α => Ideal.principal (PartialSpine.zipStream σ s)) :=
  IdealCompletion.principal_monotone.comp (PartialSpine.zipStream_monotone σ)

/-- Extend the single finite interpreter in the existing observation CPO. -/
def zipStream (σ : Stream' β) (I : Observations α) : Observations (β × α) :=
  IdealCompletion.extend (fun s => Ideal.principal (PartialSpine.zipStream σ s)) I

theorem zipStream_continuous (σ : Stream' β) :
    ScottContinuous (zipStream (α := α) σ) :=
  IdealCompletion.extend_scottContinuous (principalZip_monotone σ)

theorem mem_zipStream (σ : Stream' β) (I : Observations α) (q : PartialSpine (β × α)) :
    q ∈ zipStream σ I ↔ ∃ s ∈ I, q ≤ PartialSpine.zipStream σ s :=
  mem_extend_principal (PartialSpine.zipStream σ) (PartialSpine.zipStream_monotone σ) I q

theorem zipStream_principal (σ : Stream' β) (s : PartialSpine α) :
    zipStream σ (Ideal.principal s) = Ideal.principal (PartialSpine.zipStream σ s) :=
  IdealCompletion.extend_principal (principalZip_monotone σ) s

@[simp] theorem zipStream_bottom (σ : Stream' β) : zipStream (α := α) σ ⊥ = ⊥ :=
  zipStream_principal σ .bottom

@[simp] theorem zipStream_nil (σ : Stream' β) :
    zipStream σ (Ideal.principal (.nil : PartialSpine α)) = Ideal.principal .nil :=
  zipStream_principal σ .nil

/-- The total first stream advances once when the second input reveals a cons. -/
theorem zipStream_cons (σ : Stream' β) (a : α) (I : Observations α) :
    zipStream σ (cons a I) = cons (σ 0, a) (zipStream σ.tail I) := by
  apply IdealCompletion.continuous_ext
    ((cons_continuous a).comp (zipStream_continuous σ))
    ((zipStream_continuous σ.tail).comp (cons_continuous (σ 0, a))) (I := I)
  intro s
  change zipStream σ (cons a (Ideal.principal s)) =
    cons (σ 0, a) (zipStream σ.tail (Ideal.principal s))
  rw [cons_principal, zipStream_principal, zipStream_principal, cons_principal]
  rfl

theorem zipStream_ofList (σ : Stream' β) (xs : List α) :
    zipStream σ (Ideal.principal (ofList xs)) =
      Ideal.principal (ofList ((σ.take xs.length).zip xs)) := by
  rw [zipStream_principal, PartialSpine.zipStream_ofList]

theorem zipStream_openPrefix (σ : Stream' β) (xs : List α) :
    zipStream σ (Ideal.principal (openPrefix xs)) =
      Ideal.principal (openPrefix ((σ.take xs.length).zip xs)) := by
  rw [zipStream_principal, PartialSpine.zipStream_openPrefix]

/-- Full directed continuity carries the native family of zipped finite prefixes. -/
theorem zipStream_stream (σ : Stream' β) (τ : Stream' α) :
    zipStream σ (stream τ) = stream (Stream'.zip Prod.mk σ τ) := by
  have mapped : zipStream σ '' (Set.range fun n => Ideal.principal (openPrefix (τ.take n))) =
      Set.range (fun n => Ideal.principal
        (openPrefix ((Stream'.zip Prod.mk σ τ).take n))) := by
    rw [← Set.range_comp']
    simp only [zipStream_principal, PartialSpine.zipStream_streamPrefix]
  have lub := zipStream_continuous σ (Set.range_nonempty _)
    (stream_prefixes_directed τ) (stream_prefixes_isLUB τ)
  rw [mapped] at lub
  exact lub.unique (stream_prefixes_isLUB (Stream'.zip Prod.mk σ τ))

/-- Second projection loses none of the second input's observations or end information. -/
theorem map_snd_zipStream (σ : Stream' β) (I : Observations α) :
    map Prod.snd (zipStream σ I) = I := by
  apply IdealCompletion.continuous_ext
    ((zipStream_continuous σ).comp (map_continuous Prod.snd)) ScottContinuous.id (I := I)
  intro s
  change map Prod.snd (zipStream σ (Ideal.principal s)) = Ideal.principal s
  rw [zipStream_principal, map_principal, PartialSpine.map_snd_zipStream]

/-- Natural indices are supplied online; the input length is never inspected. -/
def labelFrom (n : Nat) (I : Observations α) : Observations (Nat × α) :=
  zipStream (fun k => n + k) I

def label (I : Observations α) : Observations (Nat × α) := labelFrom 0 I

theorem labelFrom_continuous (n : Nat) : ScottContinuous (labelFrom (α := α) n) :=
  zipStream_continuous (fun k => n + k)

theorem labelFrom_cons (n : Nat) (a : α) (I : Observations α) :
    labelFrom n (cons a I) = cons (n, a) (labelFrom (n + 1) I) := by
  unfold labelFrom
  erw [zipStream_cons, indexStream_tail, Nat.add_zero]

theorem labelFrom_ofList (n : Nat) (xs : List α) :
    labelFrom n (Ideal.principal (ofList xs)) =
      Ideal.principal (ofList ((List.range' n xs.length).zip xs)) := by
  erw [labelFrom, zipStream_principal, PartialSpine.zipStream_index_ofList]

theorem labelFrom_openPrefix (n : Nat) (xs : List α) :
    labelFrom n (Ideal.principal (openPrefix xs)) =
      Ideal.principal (openPrefix ((List.range' n xs.length).zip xs)) := by
  erw [labelFrom, zipStream_principal, PartialSpine.zipStream_index_openPrefix]

theorem label_ofList (xs : List α) :
    label (Ideal.principal (ofList xs)) =
      Ideal.principal (ofList ((List.range' 0 xs.length).zip xs)) :=
  labelFrom_ofList 0 xs

theorem labelFrom_stream (n : Nat) (σ : Stream' α) :
    labelFrom n (stream σ) = stream (fun k => (n + k, σ k)) :=
  zipStream_stream (fun k => n + k) σ

theorem label_stream (σ : Stream' α) : label (stream σ) = stream (Stream'.enum σ) := by
  change zipStream (fun k => 0 + k) (stream σ) = stream (Stream'.enum σ)
  calc
    _ = stream (Stream'.zip Prod.mk (fun k => 0 + k) σ) := zipStream_stream _ _
    _ = stream (Stream'.enum σ) := by
      apply congrArg stream
      funext k
      change (0 + k, σ k) = (Stream'.enum σ).get k
      rw [Stream'.get_enum, Nat.zero_add]
      rfl

theorem map_snd_labelFrom (n : Nat) (I : Observations α) :
    map Prod.snd (labelFrom n I) = I :=
  map_snd_zipStream (fun k => n + k) I

end
end Observations
end SquareKit.PartialSpine
