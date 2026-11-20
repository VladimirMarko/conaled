import Applications.Search.IntervalKey
import Mathlib.Data.Set.Insert

/-! An independent existential overlap observation. It assumes no tree,
finiteness, enumeration order, or injectivity of a complete-key projection.
Update and search implementations have separate validity contracts.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Search.IntervalSet
universe u v
variable {α : Type u} {κ : Type v} [LE α]

def hasOverlap (contents : Set (IntervalKey α)) (query : IntervalKey α) : Prop :=
  ∃ key ∈ contents, IntervalKey.overlap key query

@[simp] theorem not_hasOverlap_empty (query : IntervalKey α) :
    ¬ hasOverlap ∅ query := by
  rintro ⟨_, h, _⟩
  exact h

theorem hasOverlap_insert_iff (key query : IntervalKey α)
    (contents : Set (IntervalKey α)) :
    hasOverlap (insert key contents) query ↔
      IntervalKey.overlap key query ∨ hasOverlap contents query := by
  constructor
  · rintro ⟨other, h, overlaps⟩
    rcases h with rfl | h
    · exact Or.inl overlaps
    · exact Or.inr ⟨other, h, overlaps⟩
  · rintro (h | ⟨other, hmem, h⟩)
    · exact ⟨key, Or.inl rfl, h⟩
    · exact ⟨other, Or.inr hmem, h⟩

@[simp] theorem hasOverlap_singleton_iff (key query : IntervalKey α) :
    hasOverlap {key} query ↔ IntervalKey.overlap key query := by
  simpa only [← Set.singleton_def, not_hasOverlap_empty, or_false] using
    hasOverlap_insert_iff key query ∅

theorem hasOverlap_mono {left right : Set (IntervalKey α)} (subset : left ⊆ right)
    {query : IntervalKey α} (h : hasOverlap left query) : hasOverlap right query := by
  rcases h with ⟨key, member, overlaps⟩
  exact ⟨key, subset member, overlaps⟩

/-- Image membership supplies an original complete key; injectivity is not needed. -/
theorem hasOverlap_image_iff (iv : κ → IntervalKey α) (contents : Set κ)
    (query : IntervalKey α) :
    hasOverlap (iv '' contents) query ↔
      ∃ key ∈ contents, IntervalKey.overlap (iv key) query := by
  constructor
  · rintro ⟨_, ⟨key, member, rfl⟩, overlaps⟩
    exact ⟨key, member, overlaps⟩
  · rintro ⟨key, member, overlaps⟩
    exact ⟨iv key, ⟨key, member, rfl⟩, overlaps⟩

end Search.IntervalSet
