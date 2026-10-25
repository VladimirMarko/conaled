import SquareKit.Internal.PartitionSection
import Mathlib.CategoryTheory.Adhesive.Basic

/-! The coproduct presentation of complementary predicates is equivalent to
coverage and exclusion. Coverage is joint epimorphy; exclusion says their
intersection is initial. In a topos these are exactly the interpretations of
`⊤ ⊢ p ∨ q` and `p ∧ q ⊢ ⊥`. The bound is the third sequent `p ⊢ u`. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
namespace SquareKit.Internal.PartitionSection
open CategoryTheory CategoryTheory.Limits
universe v u
variable {C : Type u} [Category.{v} C] [HasTerminal C] [FinitaryExtensive C]
variable {U P Q : C} {u : U ⟶ ⊤_ C} [Mono u]

/-- A colimiting complementary partition covers the terminal object. -/
instance Model.cover (M : Model u) : Epi (coprod.desc M.p M.q) := by
  let e := (coprodIsCoprod M.P M.Q).coconePointUniqueUpToIso M.partition
  have he : e.hom = coprod.desc M.p M.q := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc]
      exact (coprodIsCoprod M.P M.Q).comp_coconePointUniqueUpToIso_hom M.partition ⟨WalkingPair.left⟩
    · rw [coprod.inr_desc]
      exact (coprodIsCoprod M.P M.Q).comp_coconePointUniqueUpToIso_hom M.partition ⟨WalkingPair.right⟩
  rw [← he]
  infer_instance

/-- The two predicates have empty intersection in the categorical sense. -/
theorem Model.exclusion (M : Model u) :
    IsPullback (initial.to M.P) (initial.to M.Q) M.p M.q :=
  FinitaryExtensive.isPullback_initial_to_binaryCofan M.partition

variable [Adhesive C]

/-- Coverage and disjointness construct, rather than assume, the coproduct partition. -/
def partitionOfSequents (p : P ⟶ ⊤_ C) (q : Q ⟶ ⊤_ C) [Mono p] [Mono q]
    [Epi (coprod.desc p q)] (disjoint : IsPullback (initial.to P) (initial.to Q) p q) :
    IsColimit (BinaryCofan.mk p q) := by
  let h := IsPushout.of_hasBinaryCoproduct' P Q
  have hm : Mono (h.desc p q disjoint.w) := h.desc_mono_of_isPullback disjoint
  have he : h.desc p q disjoint.w = coprod.desc p q := by
    apply coprod.hom_ext <;> simp [h]
  rw [he] at hm
  haveI : Mono (coprod.desc p q) := hm
  haveI : IsIso (coprod.desc p q) := isIso_of_mono_of_epi _
  have heq : (coprodIsCoprod P Q).desc (BinaryCofan.mk p q) = coprod.desc p q := by
    apply coprod.hom_ext
    · rw [coprod.inl_desc]
      exact (coprodIsCoprod P Q).fac _ ⟨WalkingPair.left⟩
    · rw [coprod.inr_desc]
      exact (coprodIsCoprod P Q).fac _ ⟨WalkingPair.right⟩
  haveI : IsIso ((coprodIsCoprod P Q).desc (BinaryCofan.mk p q)) := heq ▸ inferInstance
  exact (coprodIsCoprod P Q).ofPointIso

/-- This constructor uses precisely the two complementary predicates and their bound. -/
def Model.ofSequents (p : P ⟶ ⊤_ C) (q : Q ⟶ ⊤_ C) [Mono p] [Mono q]
    [Epi (coprod.desc p q)] (disjoint : IsPullback (initial.to P) (initial.to Q) p q)
    (bound : P ⟶ U) (bound_over : bound ≫ u = p) : Model u :=
  ⟨P, Q, p, q, bound, bound_over, partitionOfSequents p q disjoint⟩

/-- No extra complement-choice axiom is hidden in the partition presentation. -/
theorem partition_iff_sequents (p : P ⟶ ⊤_ C) (q : Q ⟶ ⊤_ C) [Mono p] [Mono q] :
    Nonempty (IsColimit (BinaryCofan.mk p q)) ↔
      Epi (coprod.desc p q) ∧ IsPullback (initial.to P) (initial.to Q) p q := by
  constructor
  · rintro ⟨hc⟩
    let e := (coprodIsCoprod P Q).coconePointUniqueUpToIso hc
    have he : e.hom = coprod.desc p q := by
      apply coprod.hom_ext
      · rw [coprod.inl_desc]
        exact (coprodIsCoprod P Q).comp_coconePointUniqueUpToIso_hom hc ⟨WalkingPair.left⟩
      · rw [coprod.inr_desc]
        exact (coprodIsCoprod P Q).comp_coconePointUniqueUpToIso_hom hc ⟨WalkingPair.right⟩
    refine ⟨?_, FinitaryExtensive.isPullback_initial_to_binaryCofan hc⟩
    rw [← he]
    infer_instance
  · rintro ⟨hc, hd⟩
    letI := hc
    exact ⟨partitionOfSequents p q hd⟩
end SquareKit.Internal.PartitionSection
