import Mathlib.Data.Set.Basic

/-! Observation extension at fixed indices. Each observer has its own result
 type; agreement uses equality in that fibre. This interface does not compare
 results at different indices or prescribe an observation family for clients. -/
namespace SquareKit.ObservationExtension

universe u v w z
variable {X : Type u} {I : Type v} {R : I → Type w}

/-- Agreement on a selected family, retaining the full result at each index. -/
def agreement (observe : (i : I) → X → R i) (family : Set I) : Setoid X where
  r x y := ∀ i ∈ family, observe i x = observe i y
  iseqv := ⟨fun _ _ _ => rfl, fun h i hi => (h i hi).symm,
    fun h k i hi => (h i hi).trans (k i hi)⟩

/-- More observations imply the old agreement, with no converse assumed. -/
theorem restrict (observe : (i : I) → X → R i) {small large : Set I}
    (included : small ⊆ large) {x y : X}
    (h : (agreement observe large).r x y) :
    (agreement observe small).r x y :=
  fun i hi => h i (included hi)

/-- The obligation for an exact-valued observer to respect an old contract. -/
def Compatible (old : Setoid X) {Y : Type z} (observe : X → Y) : Prop :=
  ∀ ⦃x y⦄, old.r x y → observe x = observe y

/-- One additional observation refines, rather than replaces, the old contract. -/
def extend (old : Setoid X) {Y : Type z} (observe : X → Y) : Setoid X where
  r x y := old.r x y ∧ observe x = observe y
  iseqv := ⟨fun _ => ⟨old.refl _, rfl⟩,
    fun h => ⟨old.symm h.1, h.2.symm⟩,
    fun h k => ⟨old.trans h.1 k.1, h.2.trans k.2⟩⟩

theorem extend_restrict (old : Setoid X) {Y : Type z} (observe : X → Y)
    {x y : X} (h : (extend old observe).r x y) : old.r x y := h.1

/-- Compatibility is precisely the premise needed for the converse restriction. -/
theorem extend_iff (old : Setoid X) {Y : Type z} (observe : X → Y)
    (h : Compatible old observe) (x y : X) :
    (extend old observe).r x y ↔ old.r x y :=
  ⟨fun hxy => hxy.1, fun hxy => ⟨hxy, h hxy⟩⟩

/-- Factoring through an existing interpretation suffices for compatibility. -/
theorem compatible_of_factor {S : Type v} {Y : Type z} (old : Setoid X)
    (meaning : X → S) (hmeaning : Compatible old meaning)
    (observe : X → Y) (semantic : S → Y)
    (square : ∀ x, observe x = semantic (meaning x)) : Compatible old observe := by
  intro x y h
  exact (square x).trans ((congrArg semantic (hmeaning h)).trans (square y).symm)

/-- Quotient descent needs exactly equality preservation for this old setoid. -/
def descend (old : Setoid X) {Y : Type z} (observe : X → Y)
    (h : Compatible old observe) : Quotient old → Y :=
  Quotient.lift observe (fun _ _ hxy => h hxy)

theorem descend_mk (old : Setoid X) {Y : Type z} (observe : X → Y)
    (h : Compatible old observe) (x : X) :
    descend old observe h (Quotient.mk old x) = observe x := rfl

/-- A distinguishing pair obstructs any factor, including noncomputable ones. -/
theorem no_factor (old : Setoid X) {Y : Type z} (observe : X → Y)
    {x y : X} (related : old.r x y) (different : observe x ≠ observe y) :
    ¬ ∃ f : Quotient old → Y, ∀ a, f (Quotient.mk old a) = observe a := by
  rintro ⟨f, hf⟩
  exact different ((hf x).symm.trans
    ((congrArg f (Quotient.sound related)).trans (hf y)))

end SquareKit.ObservationExtension
