import SquareKit.DirectedLimits
import Mathlib.Order.Ideal

/-!
# Directed completion and one generic ideal extension

All carriers, order laws and continuity predicates retain their standard owners.
The pointed ideal CPO is a named construction, not a broad overlapping instance.
The interpreter extension itself needs no bottom in the source preorder.
-/

set_option autoImplicit false
set_option warningAsError true

noncomputable section

namespace SquareKit.IdealCompletion

open Order

universe u v w z
variable {P : Type u} [Preorder P]

/-- A nonempty directed union, using the standard ideal-union theorem. -/
def directedUnion (S : Set (Ideal P)) (nonempty : S.Nonempty)
    (directed : DirectedOn (· ≤ ·) S) : Ideal P :=
  (Order.isIdeal_sUnion_of_directedOn
    (C := (fun I : Ideal P => (I : Set P)) '' S)
    (by rintro _ ⟨I, _, rfl⟩; exact I.isIdeal)
    (directed.mono_comp (fun _ _ h => h)) (nonempty.image _)).toIdeal

theorem mem_directedUnion (S : Set (Ideal P)) (nonempty : S.Nonempty)
    (directed : DirectedOn (· ≤ ·) S) (p : P) :
    p ∈ directedUnion S nonempty directed ↔ ∃ I ∈ S, p ∈ I := by
  constructor
  · rintro ⟨_, ⟨I, hI, rfl⟩, hp⟩
    exact ⟨I, hI, hp⟩
  · rintro ⟨I, hI, hp⟩
    exact ⟨(I : Set P), ⟨I, hI, rfl⟩, hp⟩

theorem directedUnion_isLUB (S : Set (Ideal P)) (nonempty : S.Nonempty)
    (directed : DirectedOn (· ≤ ·) S) : IsLUB S (directedUnion S nonempty directed) := by
  constructor
  · intro I hI p hp
    exact (mem_directedUnion S nonempty directed p).mpr ⟨I, hI, hp⟩
  · intro J upper p hp
    obtain ⟨I, hI, hp⟩ := (mem_directedUnion S nonempty directed p).mp hp
    exact upper hI hp

/-- Directed nonempty families use union; all other inputs use the existing bottom. -/
def pointedSup [OrderBot P] (S : Set (Ideal P)) : Ideal P := by
  classical
  exact if h : S.Nonempty ∧ DirectedOn (· ≤ ·) S then directedUnion S h.1 h.2 else ⊥

@[simp] theorem pointedSup_empty [OrderBot P] : pointedSup (∅ : Set (Ideal P)) = ⊥ := by
  simp [pointedSup]

theorem mem_pointedSup [OrderBot P] (S : Set (Ideal P)) (nonempty : S.Nonempty)
    (directed : DirectedOn (· ≤ ·) S) (p : P) :
    p ∈ pointedSup S ↔ ∃ I ∈ S, p ∈ I := by
  rw [pointedSup, dite_eq_left ⟨nonempty, directed⟩]
  exact mem_directedUnion S nonempty directed p

theorem pointedSup_isLUB [OrderBot P] (S : Set (Ideal P))
    (directed : DirectedOn (· ≤ ·) S) : IsLUB S (pointedSup S) := by
  by_cases nonempty : S.Nonempty
  · rw [pointedSup, dite_eq_left ⟨nonempty, directed⟩]
    exact directedUnion_isLUB S nonempty directed
  · have empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp nonempty
    subst S
    rw [pointedSup_empty]
    exact ⟨fun _ h => False.elim h, fun _ _ => bot_le⟩

/-- A reusable pointed-ideal CPO construction with the existing order and bottom. -/
@[instance_reducible] def pointedIdealCPO [OrderBot P] : CompletePartialOrder (Ideal P) where
  __ := (inferInstance : PartialOrder (Ideal P))
  __ := (inferInstance : OrderBot (Ideal P))
  sSup := pointedSup
  lubOfDirected := pointedSup_isLUB

/-- The standard principal embedding is monotone on every preorder. -/
theorem principal_monotone : Monotone (Ideal.principal : P → Ideal P) := by
  intro p q hpq
  exact Ideal.principal_le_iff.mpr hpq

/-- Every ideal is the directed least upper bound of its observed principal ideals. -/
theorem principal_isLUB (I : Ideal P) : IsLUB (Ideal.principal '' (I : Set P)) I := by
  constructor
  · rintro _ ⟨p, hp, rfl⟩
    exact Ideal.principal_le_iff.mpr hp
  · intro J upper p hp
    exact upper ⟨p, hp, rfl⟩ Ideal.mem_principal_self

/-- Continuous maps out of ideals are determined by their principal values. -/
theorem continuous_ext {B : Type v} [PartialOrder B] {F G : Ideal P → B}
    (fContinuous : ScottContinuous F) (gContinuous : ScottContinuous G)
    (principals : ∀ p, F (Ideal.principal p) = G (Ideal.principal p)) (I : Ideal P) :
    F I = G I := by
  have nonempty := I.nonempty.image Ideal.principal
  have directed := I.directed.mono_comp principal_monotone
  have imageEq : F '' (Ideal.principal '' (I : Set P)) =
      G '' (Ideal.principal '' (I : Set P)) := by
    ext b
    constructor
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨Ideal.principal p, ⟨p, hp, rfl⟩, (principals p).symm⟩
    · rintro ⟨_, ⟨p, hp, rfl⟩, rfl⟩
      exact ⟨Ideal.principal p, ⟨p, hp, rfl⟩, principals p⟩
  have hf := fContinuous nonempty directed (principal_isLUB I)
  rw [imageEq] at hf
  exact hf.unique (gContinuous nonempty directed (principal_isLUB I))

/-- Directed extension of a finite-observation interpreter; law hypotheses are separate. -/
def extend {B : Type v} [SupSet B] (h : P → B) (I : Ideal P) : B :=
  sSup (h '' (I : Set P))

section Extension

variable {B : Type v} {C : Type w} [CompletePartialOrder B] [CompletePartialOrder C]

theorem extend_isLUB {h : P → B} (monotone : Monotone h) (I : Ideal P) :
    IsLUB (h '' (I : Set P)) (extend h I) :=
  (I.directed.mono_comp monotone).isLUB_sSup

theorem le_extend {h : P → B} (monotone : Monotone h) (I : Ideal P) {p : P} (hp : p ∈ I) :
    h p ≤ extend h I :=
  (extend_isLUB monotone I).1 ⟨p, hp, rfl⟩

theorem extend_le {h : P → B} (monotone : Monotone h) (I : Ideal P) {b : B}
    (upper : ∀ p ∈ I, h p ≤ b) : extend h I ≤ b := by
  apply (extend_isLUB monotone I).2
  rintro _ ⟨p, hp, rfl⟩
  exact upper p hp

theorem extend_principal {h : P → B} (monotone : Monotone h) (p : P) :
    extend h (Ideal.principal p) = h p := by
  apply le_antisymm
  · exact extend_le monotone _ (fun _ hp => monotone hp)
  · exact le_extend monotone _ Ideal.mem_principal_self

theorem extend_monotone {h : P → B} (monotone : Monotone h) : Monotone (extend h) := by
  intro I J below
  exact extend_le monotone I (fun _ hp => le_extend monotone J (below hp))

theorem extend_scottContinuous {h : P → B} (monotone : Monotone h) :
    ScottContinuous (extend h) := by
  intro S nonempty directed I lub
  have unionEq : I = directedUnion S nonempty directed :=
    lub.unique (directedUnion_isLUB S nonempty directed)
  constructor
  · rintro _ ⟨J, hJ, rfl⟩
    exact extend_monotone monotone (lub.1 hJ)
  · intro b upper
    apply extend_le monotone I
    intro p hp
    rw [unionEq] at hp
    obtain ⟨J, hJ, hp⟩ := (mem_directedUnion S nonempty directed p).mp hp
    exact le_trans (le_extend monotone J hp) (upper ⟨J, hJ, rfl⟩)

/-- Continuous observers commute with the one shared extension, without a strictness premise. -/
theorem map_extend {h : P → B} (monotone : Monotone h) {g : B → C}
    (continuous : ScottContinuous g) (I : Ideal P) :
    g (extend h I) = extend (g ∘ h) I := by
  unfold extend
  rw [DirectedLimits.map_sSup continuous (I.nonempty.image h) (I.directed.mono_comp monotone)]
  rw [Set.image_image]
  rfl

theorem extend_fusion {h : P → B} {k : P → C} {g : B → C}
    (hMonotone : Monotone h) (kMonotone : Monotone k) (continuous : ScottContinuous g)
    (commute : ∀ p, g (h p) = k p) (I : Ideal P) : g (extend h I) = extend k I := by
  have imageEq : g '' (h '' (I : Set P)) = k '' (I : Set P) := by
    rw [Set.image_image]
    congr 1
    exact funext commute
  have mapped := continuous (I.nonempty.image h) (I.directed.mono_comp hMonotone)
    (extend_isLUB hMonotone I)
  rw [imageEq] at mapped
  exact mapped.unique (extend_isLUB kMonotone I)

theorem extend_mono_interpreter {h k : P → B} (hMonotone : Monotone h)
    (kMonotone : Monotone k) (below : ∀ p, h p ≤ k p) (I : Ideal P) :
    extend h I ≤ extend k I :=
  extend_le hMonotone I (fun p hp => le_trans (below p) (le_extend kMonotone I hp))

/-- Pointwise parameter continuity commutes with the ideal extension. -/
theorem extend_param_scottContinuous {D : Type z} [Preorder D] (h : D → P → B)
    (monotone : ∀ d, Monotone (h d)) (continuous : ∀ p, ScottContinuous (fun d => h d p))
    (I : Ideal P) : ScottContinuous (fun d => extend (h d) I) := by
  have parameterMonotone : Monotone (fun d => extend (h d) I) := by
    intro d e hde
    exact extend_mono_interpreter (monotone d) (monotone e)
      (fun p => (continuous p).monotone hde) I
  intro S nonempty directed d lub
  constructor
  · rintro _ ⟨e, he, rfl⟩
    exact parameterMonotone (lub.1 he)
  · intro b upper
    apply extend_le (monotone d) I
    intro p hp
    apply (continuous p nonempty directed lub).2
    rintro _ ⟨e, he, rfl⟩
    exact le_trans (le_extend (monotone e) I hp) (upper ⟨e, he, rfl⟩)

end Extension

open scoped DirectedLimits

/-- One function-valued extension has the separately extended value at every index. -/
theorem extend_apply {ι : Type v} {X : ι → Type w} [∀ i, CompletePartialOrder (X i)]
    (h : P → ∀ i, X i) (I : Ideal P) (i : ι) :
    extend h I i = extend (fun p => h p i) I := by
  unfold extend
  rw [sSup_apply_eq_sSup_image, Set.image_image]

end SquareKit.IdealCompletion
