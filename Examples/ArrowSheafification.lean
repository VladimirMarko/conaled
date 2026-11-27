import SquareKit.ArrowSheafification
import Mathlib.GroupTheory.Perm.Basic

/-! On two discrete points, arrow correction both identifies empty-open labels
and adds the permutation label which varies between the two points. The
normalized input has genuine compatible local arrows with no global amalgamation.
All corrected labels survive the subsequent represented-groupoid completion. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
namespace Examples.ArrowSheafification
open CategoryTheory Opposite TopologicalSpace SquareKit
open SquareKit.LocallyConstantSheaf SquareKit.ArrowSheafification
local instance : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := ⟨rfl⟩
abbrev X : TopCat := TopCat.of Bool
abbrev G := Equiv.Perm Bool

def flip : G := Equiv.swap false true

theorem flip_ne_one : flip ≠ 1 := by
  intro h
  have e := congrArg (fun p : G => p false) h
  simp [flip] at e

def varying : LocallyConstant (⊤ : Opens X) G :=
  ⟨fun p => if p.val then flip else 1, IsLocallyConstant.of_discrete _⟩

theorem varying_not_constant (g : G) : LocallyConstant.const (⊤ : Opens X) g ≠ varying := by
  intro h
  have hf := congrArg (fun s : LocallyConstant (⊤ : Opens X) G => s ⟨false, trivial⟩) h
  have ht := congrArg (fun s : LocallyConstant (⊤ : Opens X) G => s ⟨true, trivial⟩) h
  change g = 1 at hf
  change g = flip at ht
  exact flip_ne_one (ht.symm.trans hf)

/-- The actual raw unit gains a nonconstant automorphism. -/
theorem raw_not_surjective : ¬ Function.Surjective ((unit X G).app (op ⊤)) := by
  intro h
  obtain ⟨g, hg⟩ := h varying
  exact varying_not_constant g hg

/-- Labels already differ in the input even though they agree locally at the empty open. -/
theorem raw_not_injective_empty : ¬ Function.Injective ((unit X G).app (op ⊥)) := by
  intro h
  apply flip_ne_one
  apply h
  apply LocallyConstant.ext
  intro p
  exact False.elim p.property

def singleton (b : Bool) : Opens X := ⟨{b}, isOpen_discrete _⟩

theorem singleton_cover : singleton false ⊔ singleton true = ⊤ := by
  ext b
  cases b <;> simp [singleton]

theorem singleton_overlap : singleton false ⊓ singleton true = ⊥ := by
  ext b
  cases b <;> simp [singleton]

def localLabel (b : Bool) : constants X G (singleton b) :=
  ⟨LocallyConstant.const _ (if b then flip else 1), fun _ _ => rfl⟩

/-- Unlike the raw constant presheaf, the normalized sections agree on the overlap. -/
theorem local_compatible :
    (normalized X G).map (homOfLE inf_le_left : singleton false ⊓ singleton true ⟶ _).op
        (localLabel false) =
      (normalized X G).map (homOfLE inf_le_right : singleton false ⊓ singleton true ⟶ _).op
        (localLabel true) := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro p
  have h : (p.val : Bool) ∈ (⊥ : Opens X) := by rw [← singleton_overlap]; exact p.property
  exact False.elim h

/-- The matching family is not globally constant and hence has no normalized amalgamation. -/
theorem no_normalized_amalgamation : ¬ ∃ s : constants X G ⊤, ∀ b : Bool,
    (normalized X G).map (homOfLE le_top : singleton b ⟶ ⊤).op s = localLabel b := by
  rintro ⟨s, hs⟩
  have hf := congrArg (fun t : constants X G (singleton false) => t.val ⟨false, rfl⟩) (hs false)
  have ht := congrArg (fun t : constants X G (singleton true) => t.val ⟨true, rfl⟩) (hs true)
  have hc := s.property ⟨false, trivial⟩ ⟨true, trivial⟩
  change s.val ⟨false, trivial⟩ = 1 at hf
  change s.val ⟨true, trivial⟩ = flip at ht
  exact flip_ne_one (ht.symm.trans (hc.symm.trans hf))

/-- The corrected hom sheaf supplies the required amalgamation. -/
theorem varying_restricts (b : Bool) :
    (data X G).map (homOfLE le_top : singleton b ⟶ ⊤).op varying = (localLabel b).val := by
  apply LocallyConstant.ext
  intro p
  have hp : p.val = b := p.property
  change (if p.val then flip else 1) = (if b then flip else 1)
  rw [hp]

/-- The completion unit retains the nontrivial original isotropy on the inhabited open. -/
theorem completed_distinct :
    (Completion.completedUnit X G (op ⊤)).map (X := SingleObj.star G) (Y := SingleObj.star G) flip ≠
      (Completion.completedUnit X G (op ⊤)).map (X := SingleObj.star G) (Y := SingleObj.star G) (1 : G) := by
  intro h
  have e := Completion.completed_loop_injective X G (op ⊤) h
  have hf := congrArg (fun s : LocallyConstant (⊤ : Opens X) G => s ⟨false, trivial⟩) e
  exact flip_ne_one hf

/-- Newly glued arrows remain new after effective object descent. -/
theorem completed_new_arrow : ¬ ∃ g : G,
    (Completion.completedUnit X G (op ⊤)).map (X := SingleObj.star G) (Y := SingleObj.star G) g =
      (SheafGroupoid.Bundle.regularFunctor (Completion.operations X G)).map
        (Completion.loop X G (op ⊤) varying) := by
  rintro ⟨g, h⟩
  exact varying_not_constant g (Completion.completed_loop_injective X G (op ⊤) h)

/-- The raw hom presheaf fails the actual sheaf predicate. -/
theorem raw_not_sheaf : ¬ Presheaf.IsSheaf (site X) ((Functor.const (TopologicalSpace.Opens X)ᵒᵖ).obj G) := by
  intro h
  let f : (⟨_, h⟩ : Sheaf (site X) (Type 0)) ⟶ obj X G := ⟨unit X G⟩
  have : IsIso f := (Sheaf.isLocallyBijective_iff_isIso f).mp ⟨unit_isLocallyInjective X G,
    unit_isLocallySurjective X G⟩
  have : IsIso f.hom := (sheafToPresheaf _ _).map_isIso f
  exact raw_not_surjective (ConcreteCategory.bijective_of_isIso (f.hom.app (op ⊤))).surjective
/-- Normalizing the empty open does not repair the gluing failure. -/
theorem normalized_not_sheaf : ¬ Presheaf.IsSheaf (site X) (normalized X G ⋙ forget GrpCat) := by
  intro h
  let f : (⟨_, h⟩ : Sheaf (site X) (Type 0)) ⟶ obj X G := ⟨inclusion X G⟩
  have : IsIso f := (Sheaf.isLocallyBijective_iff_isIso f).mp ⟨inclusion_isLocallyInjective X G,
    inclusion_isLocallySurjective X G⟩
  have : IsIso f.hom := (sheafToPresheaf _ _).map_isIso f
  obtain ⟨s, hs⟩ := (ConcreteCategory.bijective_of_isIso (f.hom.app (op ⊤))).surjective varying
  have hc := s.property ⟨false, trivial⟩ ⟨true, trivial⟩
  change s.val = varying at hs
  rw [hs] at hc
  exact flip_ne_one hc.symm

/-- The sheaf-parameter completion topology does not supply original-site empty descent. -/
theorem empty_sieve_not_covering (P : Sheaf (site X) (Type 0)) :
    (⊥ : Sieve P) ∉ SheafCover.topology (J := site X) P := by
  rintro ⟨Y, f, hf, h⟩
  exact h

end Examples.ArrowSheafification
