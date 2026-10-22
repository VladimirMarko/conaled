import Applications.Optimization.Basic

/-! # Transport of least-cost choices

A semantic equation alone does not constrain costs. The hypotheses below
expose admissibility, cost agreement, order preservation, and coverage separately.
-/

namespace Optimization

variable {P Q K L : Type*} [Preorder K] [Preorder L]

/-- Without coverage, optimality is only over the image of source candidates. -/
theorem minimizer_image {A : Set P} {c : P → K} {J : Q → L}
    (C : P → Q) (h : K → L) (hm : Monotone h)
    (cost : ∀ p ∈ A, J (C p) = h (c p)) {p : P}
    (hp : p ∈ minimizers A c) : C p ∈ minimizers (C '' A) J := by
  refine ⟨⟨p, hp.1, rfl⟩, ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  change J (C p) ≤ J (C q)
  rw [cost p hp.1, cost q hq]
  exact hm (hp.2 hq)

/-- Every target alternative has a source lift whose realized cost is no worse.
The lift need not realize the target itself. -/
theorem minimizer_transport {A : Set P} {B : Set Q} {c : P → K} {J : Q → L}
    (C : P → Q) (h : K → L) (hm : Monotone h)
    (admissible : ∀ p ∈ A, C p ∈ B)
    (cost : ∀ p ∈ A, J (C p) = h (c p))
    (lifts : ∀ t ∈ B, ∃ q ∈ A, J (C q) ≤ J t) {p : P}
    (hp : p ∈ minimizers A c) : C p ∈ minimizers B J := by
  refine ⟨admissible p hp.1, fun t ht => ?_⟩
  obtain ⟨q, hq, hqt⟩ := lifts t ht
  exact le_trans ((minimizer_image C h hm cost hp).2 ⟨q, hq, rfl⟩) hqt

/-- Exact coverage is one sufficient source of dominating lifts. -/
theorem minimizer_transport_of_surjOn {A : Set P} {B : Set Q}
    {c : P → K} {J : Q → L} (C : P → Q) (h : K → L) (hm : Monotone h)
    (admissible : Set.MapsTo C A B)
    (cost : ∀ p ∈ A, J (C p) = h (c p)) (cover : Set.SurjOn C A B)
    {p : P} (hp : p ∈ minimizers A c) : C p ∈ minimizers B J :=
  minimizer_transport C h hm admissible cost (fun t ht => by
    obtain ⟨q, hq, rfl⟩ := cover ht
    exact ⟨q, hq, le_rfl⟩) hp

/-- Reflection requires order reflection as well as source feasibility.
No target coverage is needed to compare source alternatives. -/
theorem minimizer_reflect {A : Set P} {B : Set Q} {c : P → K} {J : Q → L}
    (C : P → Q) (h : K ↪o L) (admissible : Set.MapsTo C A B)
    (cost : ∀ p ∈ A, J (C p) = h (c p)) {p : P} (hp : p ∈ A)
    (opt : C p ∈ minimizers B J) : p ∈ minimizers A c := by
  refine ⟨hp, fun q hq => ?_⟩
  apply h.le_iff_le.mp
  rw [← cost p hp, ← cost q hq]
  exact opt.2 (admissible hq)

/-- Infimum preservation uses an infimum-preserving map, not mere monotonicity,
and exact coverage of the target candidate set. Empty sets are included.
Preserving all infima is sufficient; preservation of this cost-image infimum
alone would also suffice. -/
theorem value_transport {K L : Type*} [CompleteLattice K] [CompleteLattice L]
    {A : Set P} {B : Set Q} {c : P → K} {J : Q → L}
    (C : P → Q) (h : sInfHom K L) (admissible : Set.MapsTo C A B)
    (cost : ∀ p ∈ A, J (C p) = h (c p)) (cover : Set.SurjOn C A B) :
    value B J = h (value A c) := by
  unfold value
  rw [map_sInf]
  congr 1
  ext y
  constructor
  · rintro ⟨t, ht, rfl⟩
    obtain ⟨p, hp, rfl⟩ := cover ht
    exact ⟨c p, ⟨p, hp, rfl⟩, (cost p hp).symm⟩
  · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    exact ⟨C p, admissible hp, cost p hp⟩

end Optimization
