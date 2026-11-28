import SquareKit.Internal.DecoderSheafification
import SquareKit.Internal.HomRepresentableClassification

/-! Local finite-state choices use newly glued codes and expose empty-open state loss. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace Examples.DecoderSheafification
open CategoryTheory Opposite TopologicalSpace SquareKit
open LocallyConstantSheaf DecoderSheafification
local instance : TopologicalSpace Bool := ⊥
local instance : DiscreteTopology Bool := ⟨rfl⟩
abbrev X : TopCat := TopCat.of Bool
def State (b : Bool) : Type := Fin (if b then 2 else 1)

def mixedCode : LocallyConstant (⊤ : Opens X) Bool :=
  ⟨Subtype.val, IsLocallyConstant.of_discrete _⟩

def mixedState : LocalState X State ⊤ mixedCode :=
  ⟨⟨fun p => if p.val then ⟨true, (1 : Fin 2)⟩ else ⟨false, (0 : Fin 1)⟩,
    IsLocallyConstant.of_discrete _⟩,
    by apply LocallyConstant.ext; intro p; cases h : p.val <;> simp [mixedCode, h]⟩

def atom (b : Bool) : Opens X := ⟨{b}, isOpen_discrete _⟩

def atomInclusion (b : Bool) : atom b ⟶ (⊤ : Opens X) := homOfLE le_top

theorem mixedCode_restrict (b : Bool) :
    (data X Bool).map (atomInclusion b).op mixedCode = LocallyConstant.const (atom b) b := by
  apply LocallyConstant.ext
  intro p
  exact p.property

theorem mixedState_false :
    (restrictState X State (atomInclusion false) mixedState).val =
      (fiberUnit X State (atom false) false (0 : Fin 1)).val := by
  apply LocallyConstant.ext
  intro p
  have hp : p.val = false := p.property
  change (if p.val then (⟨true, (1 : Fin 2)⟩ : Sigma State) else ⟨false, (0 : Fin 1)⟩) = ⟨false, (0 : Fin 1)⟩
  simp only [hp, Bool.false_eq_true, ↓reduceIte]

theorem mixedState_true :
    (restrictState X State (atomInclusion true) mixedState).val =
      (fiberUnit X State (atom true) true (1 : Fin 2)).val := by
  apply LocallyConstant.ext
  intro p
  have hp : p.val = true := p.property
  change (if p.val then (⟨true, (1 : Fin 2)⟩ : Sigma State) else ⟨false, (0 : Fin 1)⟩) = ⟨true, (1 : Fin 2)⟩
  simp only [hp, ↓reduceIte]

theorem mixedCode_not_constant (b : Bool) :
    LocallyConstant.const (⊤ : Opens X) b ≠ mixedCode := by
  intro h
  have hf := congrArg (fun s : LocallyConstant (⊤ : Opens X) Bool => s ⟨false, trivial⟩) h
  have ht := congrArg (fun s : LocallyConstant (⊤ : Opens X) Bool => s ⟨true, trivial⟩) h
  exact Bool.false_ne_true (hf.symm.trans ht)

theorem raw_unit_not_surjective : ¬ Function.Surjective ((unit X Bool).app (op ⊤)) := by
  intro h
  obtain ⟨b, hb⟩ := h mixedCode
  exact mixedCode_not_constant b hb

theorem raw_codes_not_sheaf : ¬ Presheaf.IsSheaf (site X) (rawCodes X (C := Bool)) := by
  intro h
  let f : (⟨_, h⟩ : Sheaf (site X) (Type 0)) ⟶ obj X Bool := ⟨unit X Bool⟩
  have : IsIso f := (Sheaf.isLocallyBijective_iff_isIso f).mp
    ⟨unit_isLocallyInjective X Bool, unit_isLocallySurjective X Bool⟩
  have : IsIso f.hom := (sheafToPresheaf _ _).map_isIso f
  exact raw_unit_not_surjective (ConcreteCategory.bijective_of_isIso (f.hom.app (op ⊤))).surjective

/-- The canonical pullback comparison cannot give exact original-state recovery. -/
theorem two_states_not_recovered : ¬ Function.Injective (fiberUnit X State ⊥ true) :=
  exact_recovery_obstruction X State true (d := (0 : Fin 2)) (e := (1 : Fin 2)) (by change (0 : Fin 2) ≠ 1; decide)

/-- Pointwise reversal is an operation on both the one-state and two-state fibers. -/
def reverseStates (b : Bool) : State b → State b := Fin.rev

theorem reversal_preserved (U : Opens X) (b : Bool) (d : State b) :
    mapState X State reverseStates (fiberUnit X State U b d) =
      fiberUnit X State U b (reverseStates b d) := mapState_unit X State reverseStates U b d

theorem reversal_true_zero : reverseStates true (0 : Fin 2) = (1 : Fin 2) := by
  change Fin.rev (0 : Fin 2) = 1
  decide

theorem reversal_involutive {U : Opens X} {c : LocallyConstant U Bool}
    (s : LocalState X State U c) :
    mapState X State reverseStates (mapState X State reverseStates s) = s := by
  rw [mapState_comp]
  have hf : (fun b d => reverseStates b (reverseStates b d)) = (fun b (d : State b) => d) := by
    funext b d
    exact Fin.rev_rev d
  rw [hf, mapState_id]

/-- The existing representable classification has the same non-sheaf code obstruction. -/
theorem homSystem_codes_not_sheaf : ¬ Presheaf.IsSheaf (site X)
    (RepresentableClassification.HomSystem.system (rawCodes X (C := Bool))).codes := by
  intro h
  exact raw_codes_not_sheaf
    ((RepresentableClassification.HomSystem.codes_isSheaf_iff _ _).mp h)

end Examples.DecoderSheafification
