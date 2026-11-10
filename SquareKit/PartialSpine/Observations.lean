import SquareKit.PartialSpine
import Mathlib.Order.Ideal
import Mathlib.Data.Stream.Init

/-!
# Ideals of finite spine observations

The carrier and its principal embeddings belong to `Order.Ideal`. A total
stream is specified independently by its ordinary finite `Stream'.take`
prefixes, all with unknown ends. No directed-limit interpreter is defined here.
-/

set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.PartialSpine

universe u
variable {α : Type u}

abbrev Observations (α : Type u) := Order.Ideal (PartialSpine α)

/-- Principal observation sets retain the entire finite spine, including its end. -/
theorem principal_injective :
    Function.Injective (Order.Ideal.principal : PartialSpine α → Observations α) := by
  intro s t h
  apply le_antisymm
  · have hs : s ∈ Order.Ideal.principal t := by
      rw [← h]
      exact Order.Ideal.mem_principal_self
    exact hs
  · have ht : t ∈ Order.Ideal.principal s := by
      rw [h]
      exact Order.Ideal.mem_principal_self
    exact ht

theorem streamPrefix_mono (σ : Stream' α) {m n : Nat} (h : m ≤ n) :
    openPrefix (σ.take m) ≤ openPrefix (σ.take n) := by
  rw [openPrefix_le_iff, view_openPrefix]
  exact Stream'.take_prefix_take_left m n σ h

@[simp] theorem knownLength_streamPrefix (σ : Stream' α) (n : Nat) :
    knownLength (openPrefix (σ.take n)) = n := by
  rw [knownLength_openPrefix, Stream'.length_take]

/-- All and only finite observations consistent with the given total stream. -/
def stream (σ : Stream' α) : Observations α where
  carrier := {s | ∃ n, s ≤ openPrefix (σ.take n)}
  lower' := by
    rintro s t hst ⟨n, ht⟩
    exact ⟨n, le_trans hst ht⟩
  nonempty' := ⟨.bottom, 0, le_rfl⟩
  directed' := by
    rintro s ⟨m, hm⟩ t ⟨n, hn⟩
    exact ⟨openPrefix (σ.take (max m n)), ⟨max m n, le_rfl⟩,
      le_trans hm (streamPrefix_mono σ (Nat.le_max_left m n)),
      le_trans hn (streamPrefix_mono σ (Nat.le_max_right m n))⟩

@[simp] theorem mem_stream (σ : Stream' α) (s : PartialSpine α) :
    s ∈ stream σ ↔ ∃ n, s ≤ openPrefix (σ.take n) := Iff.rfl

theorem stream_observes_prefix (σ : Stream' α) (n : Nat) :
    openPrefix (σ.take n) ∈ stream σ := ⟨n, le_rfl⟩

/-- Unbounded observation depth separates a stream from every finite spine. -/
theorem stream_ne_principal (σ : Stream' α) (s : PartialSpine α) :
    stream σ ≠ Order.Ideal.principal s := by
  intro h
  have hp := stream_observes_prefix σ (knownLength s + 1)
  rw [h] at hp
  have hn := knownLength_mono hp
  rw [knownLength_streamPrefix] at hn
  exact Nat.not_succ_le_self _ hn

end SquareKit.PartialSpine
