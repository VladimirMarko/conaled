import SquareKit.Internal.DependentJudgments.Sigma.Maps
import SquareKit.Internal.DependentJudgments.Sigma.PairStability
import SquareKit.Internal.DependentJudgments.CoherentTypePresentations
import SquareKit.Internal.DependentJudgments.NativeTypeModel

/-! Native dependent pairs realize the full Sigma capability over the existing
Type-family interpretation. This adds no claim about higher identity models. -/
namespace SquareKit.Internal.DependentJudgments.Sigma.Native
open PathTransport.Typed StructuralModel
universe u
set_option backward.isDefEq.respectTransparency false
variable (Base : Type u) (Fiber : Base → Type u)
local notation "M" => NativeType.structuralModel Base Fiber

def capability : Capability M where
  sigma A B γ := (a : A γ) × B ⟨γ, a⟩
  pack _ _ := ⟨fun p => ⟨p.1.1, p.1.2, p.2⟩⟩
  unpack _ _ := ⟨fun p => ⟨⟨p.1, p.2.1⟩, p.2.2⟩⟩
  pack_over _ _ := rfl
  unpack_pack _ _ := rfl
  pack_unpack _ _ := rfl

def stable : Stable M where
  toCapability := capability Base Fiber
  sigma_sub _ _ _ := rfl
  pack_sub _ _ _ := rfl

/-- The generic eliminator computes the usual dependent pair elimination. -/
theorem split_apply {Γ : Type u} (A : Γ → Type u) (B : ((γ : Γ) × A γ) → Type u)
    (C : ((γ : Γ) × ((a : A γ) × B ⟨γ, a⟩)) → Type u)
    (d : (p : (q : (γ : Γ) × A γ) × B q) → C ⟨p.1.1, p.1.2, p.2⟩)
    (p : (γ : Γ) × ((a : A γ) × B ⟨γ, a⟩)) :
    ((capability Base Fiber).split A B C ⟨d⟩).down p = d ⟨⟨p.1, p.2.1⟩, p.2.2⟩ := rfl

/-- A nonconstant second family and motive: the result is a bounded index whose
bound depends on the first component of the dependent pair. -/
def boundedBranch :
    (p : (q : (_γ : Unit) × Nat) × Fin (q.2 + 1)) → Fin (p.1.2 + 1) := fun p => p.2

theorem bounded_split (n : Nat) (i : Fin (n + 1)) :
    ((capability Unit (fun _ => Unit)).split (fun _ : Unit => Nat)
      (fun p => Fin (p.2 + 1)) (fun p => Fin (p.2.1 + 1)) ⟨boundedBranch⟩).down
        ⟨(), n, i⟩ = i :=
  split_apply Unit (fun _ => Unit) (fun _ : Unit => Nat)
    (fun p => Fin (p.2 + 1)) (fun p => Fin (p.2.1 + 1)) boundedBranch ⟨(), n, i⟩

/-- The generic beta theorem specializes to the same nonconstant motive. -/
theorem bounded_beta :
    HEq ((NativeType.structuralModel Unit (fun _ => Unit)).subTm
      ((capability Unit (fun _ => Unit)).split (fun _ : Unit => Nat)
        (fun p => Fin (p.2 + 1)) (fun p => Fin (p.2.1 + 1)) ⟨boundedBranch⟩)
      ((capability Unit (fun _ => Unit)).pack (fun _ : Unit => Nat)
        (fun p => Fin (p.2 + 1)))) (ULift.up boundedBranch) :=
  (capability Unit (fun _ => Unit)).split_beta _ _ _ _

/-- Reassociate the two comprehension binders into the chosen sum. -/
def packEquiv {Γ : Type u} (A : Γ → Type u) (B : _root_.Sigma A → Type u) :
    _root_.Sigma B ≃ _root_.Sigma ((capability Base Fiber).sigma A B) where
  toFun := ((capability Base Fiber).pack A B).down
  invFun := ((capability Base Fiber).unpack A B).down
  left_inv _ := rfl
  right_inv _ := rfl

section Comparisons
open CoherentTypePresentations
variable {Γ Δ : Type u} {e : Γ ≃ Δ} {A : Γ → Type u} {A' : Δ → Type u}
variable (f : FamilyComparison e A A')
variable {B : _root_.Sigma A → Type u} {B' : _root_.Sigma A' → Type u}
variable (g : FamilyComparison f.total B B')

/-- Both fields may change to unequal, equivalent presentations. -/
def sigmaComparison : FamilyComparison e ((capability Base Fiber).sigma A B)
    ((capability Base Fiber).sigma A' B') := fun γ =>
  Equiv.sigmaCongr (f γ) (fun a => g ⟨γ, a⟩)

theorem pack_compare (p : _root_.Sigma B) :
    (sigmaComparison Base Fiber f g).total (packEquiv Base Fiber A B p) =
      packEquiv Base Fiber A' B' (g.total p) := rfl

variable {C : _root_.Sigma ((capability Base Fiber).sigma A B) → Type u}
  {D : _root_.Sigma ((capability Base Fiber).sigma A' B') → Type u}
variable (m : FamilyComparison (sigmaComparison Base Fiber f g).total C D)

def comparedBranch (d : (M).Section (_root_.Sigma B)
    ((M).subTy C ((capability Base Fiber).pack A B))) :
    (M).Section (_root_.Sigma B') ((M).subTy D ((capability Base Fiber).pack A' B')) :=
  ⟨branchTerm (packEquiv Base Fiber A B) (packEquiv Base Fiber A' B')
    (sigmaComparison Base Fiber f g).total m d.down⟩

/-- Motive and branch comparisons determine dependent elimination on the new
presentation. The shared extension theorem derives the section equation. -/
theorem split_compare (d : (M).Section (_root_.Sigma B)
    ((M).subTy C ((capability Base Fiber).pack A B))) :
    m.term ((capability Base Fiber).split A B C d).down =
      ((capability Base Fiber).split A' B' D (comparedBranch Base Fiber f g m d)).down :=
  extension_map (packEquiv Base Fiber A B) (packEquiv Base Fiber A' B')
    (sigmaComparison Base Fiber f g).total m d.down

end Comparisons

namespace FiniteOption
open CoherentTypePresentations
local notation "M₀" => NativeType.structuralModel Nat (fun n => Fin (n + 1))
local notation "S₀" => capability Nat (fun n => Fin (n + 1))

abbrev firstSource := CoherentTypePresentations.FiniteOption.direct
abbrev firstTarget := CoherentTypePresentations.FiniteOption.coded
abbrev firstComparison := CoherentTypePresentations.FiniteOption.comparison

def secondSource (p : _root_.Sigma firstSource) : Type := Fin (p.2.val + 1)
def secondTarget (p : _root_.Sigma firstTarget) : Type :=
  Option (Fin ((finSuccEquiv p.1.1).symm p.2).val)

def secondComparison : FamilyComparison firstComparison.total secondSource secondTarget := by
  intro p
  change Fin (p.2.val + 1) ≃ Option (Fin ((finSuccEquiv p.1.1).symm (finSuccEquiv p.1.1 p.2)).val)
  simpa only [Equiv.symm_apply_apply] using finSuccEquiv p.2.val

def sums := sigmaComparison Nat (fun n => Fin (n + 1)) firstComparison secondComparison

def sourceMotive (p : _root_.Sigma ((S₀).sigma firstSource secondSource)) : Type :=
  Fin (p.2.1.val + 1)
def targetMotive (p : _root_.Sigma ((S₀).sigma firstTarget secondTarget)) : Type :=
  Option (Fin ((finSuccEquiv p.1.1).symm p.2.1).val)

def motives : FamilyComparison sums.total sourceMotive targetMotive := by
  intro p
  change Fin (p.2.1.val + 1) ≃ Option (Fin ((finSuccEquiv p.1.1).symm
    (finSuccEquiv p.1.1 p.2.1)).val)
  simpa only [Equiv.symm_apply_apply] using finSuccEquiv p.2.1.val

def sourceBranch : (M₀).Section (_root_.Sigma secondSource)
    ((M₀).subTy sourceMotive ((S₀).pack firstSource secondSource)) := ⟨fun p => p.2⟩

def sourceResult := (S₀).split firstSource secondSource sourceMotive sourceBranch
def targetResult := (S₀).split firstTarget secondTarget targetMotive
  (comparedBranch Nat (fun n => Fin (n + 1)) firstComparison secondComparison motives sourceBranch)

/-- Both Sigma components and the motive change presentation. Exact selected
values are transported by the supplied equivalences. -/
theorem preserves_selected : motives.term sourceResult.down = targetResult.down :=
  split_compare Nat (fun n => Fin (n + 1)) firstComparison secondComparison motives sourceBranch

def sample : _root_.Sigma ((S₀).sigma firstSource secondSource) :=
  ⟨(3, false), (⟨2, by decide⟩ : Fin 4), (⟨1, by decide⟩ : Fin 3)⟩

theorem source_selected_one : sourceResult.down sample = (⟨1, by decide⟩ : Fin 3) := rfl

theorem target_selected_some_zero :
    targetResult.down (sums.total sample) = some (⟨0, by decide⟩ : Fin 2) := by
  rw [← preserves_selected, FamilyComparison.term_apply]
  rfl

/-- The selected section is recoverable through the inverse comparison. -/
theorem recovers_selected : motives.term.symm targetResult.down = sourceResult.down := by
  rw [← preserves_selected]
  exact Equiv.symm_apply_apply _ _

/-- A nonidentity base substitution changes the first family's bound. -/
def shift : (M₀).Substitution CoherentTypePresentations.FiniteOption.Base
    CoherentTypePresentations.FiniteOption.Base := ⟨fun p => (p.1 + 1, !p.2)⟩

theorem split_shift :
    (M₀).subTm sourceResult ((stable Nat (fun n => Fin (n + 1))).sumMap
      firstSource secondSource shift) =
    (S₀).split ((M₀).subTy firstSource shift)
      ((M₀).subTy secondSource ((M₀).lift firstSource shift))
      ((M₀).subTy sourceMotive ((stable Nat (fun n => Fin (n + 1))).sumMap
        firstSource secondSource shift))
      ((stable Nat (fun n => Fin (n + 1))).branch firstSource secondSource shift
        sourceMotive sourceBranch) :=
  (stable Nat (fun n => Fin (n + 1))).split_sub _ _ _ _ _

def lastFirst : (M₀).Section CoherentTypePresentations.FiniteOption.Base firstSource :=
  ⟨fun p => Fin.last p.1⟩

def lastSecond : (M₀).Section CoherentTypePresentations.FiniteOption.Base
    ((M₀).subTy secondSource ((M₀).sectionSub firstSource lastFirst)) :=
  ⟨fun p => Fin.last p.1⟩

theorem pair_shift :
    HEq ((M₀).subTm ((S₀).pair firstSource secondSource lastFirst lastSecond) shift)
      ((S₀).pair ((M₀).subTy firstSource shift)
        ((M₀).subTy secondSource ((M₀).lift firstSource shift))
        ((M₀).subTm lastFirst shift)
        (Stable.pairSecond firstSource secondSource lastFirst lastSecond shift)) :=
  (stable Nat (fun n => Fin (n + 1))).pair_sub _ _ _ _ _

theorem pair_sample : ((S₀).pair firstSource secondSource lastFirst lastSecond).down (3, false) =
    ⟨Fin.last 3, Fin.last 3⟩ := rfl

end FiniteOption

end SquareKit.Internal.DependentJudgments.Sigma.Native
