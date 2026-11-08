import SquareKit.AssemblyLiftClassifier
import SquareKit.AssemblyDiagonalLift
import Mathlib.Computability.Halting

/-! Domain, selected-value and noncomputability controls for #385. -/

namespace AssemblyPartialMaps
open Realizability Realizability.Assembly Encodable Denumerable
open Nat.Partrec (Code)

/-- All inputs are admitted, and the selected value is the input itself. -/
def totalIdentity (A : Assembly) : PartialMap A A :=
  ⟨fun _ => True, admissible_univ A, inclusion A (fun _ => True)⟩

theorem totalIdentity_classify (A : Assembly) :
    (totalIdentity A).classify = programLiftUnit A := by
  apply Hom.ext
  intro x
  exact (totalIdentity A).value_some x trivial

/-- Empty-domain identity, compared to the total one using the same codomain. -/
def emptyIdentity (A : Assembly) : PartialMap A A :=
  ⟨fun _ => False, admissible_empty A, inclusion A (fun _ => False)⟩

theorem emptyIdentity_classify (A : Assembly) (x : A.Carrier) :
    (emptyIdentity A).classify.toFun x = none :=
  (emptyIdentity A).value_none x id

/-- The halting input index, not merely a truth bit, is the selected result. -/
def haltingIdentity : PartialMap (encoded Nat) (encoded Nat) where
  domain n := (run n).Dom
  admissible := ⟨run, run_partrec, fun x n hn => by cases hn; rfl⟩
  map := inclusion _ _

theorem haltingIdentity_graph (n m : Nat) :
    haltingIdentity.classify.toFun n = some m ↔ (run n).Dom ∧ n = m := by
  constructor
  · intro h
    obtain ⟨hd, he⟩ := (haltingIdentity.classify_graph n m).mp h
    exact ⟨hd, he⟩
  · rintro ⟨hd, he⟩
    exact (haltingIdentity.classify_graph n m).mpr ⟨hd, he⟩

theorem haltingIdentity_defined :
    haltingIdentity.classify.toFun (encode (Code.const 7)) = some (encode (Code.const 7)) := by
  apply (haltingIdentity_graph _ _).mpr
  exact ⟨by simp [Code.eval_const], rfl⟩

theorem haltingIdentity_undefined : ∃ n, haltingIdentity.classify.toFun n = none := by
  obtain ⟨c, hc⟩ := Code.exists_code.mp Nat.Partrec.none
  refine ⟨encode c, haltingIdentity.value_none _ ?_⟩
  simp [haltingIdentity, hc]

/-- Semidecidability in the classifier is strictly weaker than a total
computable decision of its domain. -/
theorem halting_domain_not_computable : ¬ ComputablePred (fun n => (run n).Dom) := by
  intro h
  apply ComputablePred.halting_problem 0
  obtain ⟨dec, hc⟩ := h
  let := dec
  have h' : ComputablePred (fun c : Code => (run (encode c)).Dom) :=
    ⟨inferInstance, hc.comp Computable.encode⟩
  exact h'.of_eq fun c => by rw [run_encode]

/-- Pullback preserves the actual selected value and works for every
computable change of parameter, even though the domain is undecidable. -/
theorem halting_reindex (f : Nat → Nat) (hf : Computable f) (n m : Nat) :
    (haltingIdentity.reindex (ofComputable f hf)).classify.toFun n = some m ↔
      (run (f n)).Dom ∧ f n = m := by
  rw [PartialMap.classify_reindex]
  exact haltingIdentity_graph (f n) m

/-- Sharing every realizer makes a proper Boolean subset non-admissible. -/
def indiscreteBool : Assembly where
  Carrier := Bool
  realizes _ _ := True
  inhabited _ := ⟨0, trivial⟩

theorem not_every_subset_admissible :
    ¬ Admissible indiscreteBool (fun b => b = true) := by
  rintro ⟨φ, _, hs⟩
  have h : (φ 0).Dom := (hs true 0 trivial).mpr rfl
  have he := (hs false 0 trivial).mp h
  cases he

/-- The subset still defines a legitimate inherited-realizer subobject.
Its inclusion cannot be classified by a map with precisely this domain. -/
def properInclusion := inclusion indiscreteBool (fun b => b = true)

theorem no_classifier_for_properInclusion
    (g : Hom indiscreteBool (programLift (encoded Nat))) :
    ¬ (∀ b, definedDomain g b ↔ b = true) := by
  intro h
  apply not_every_subset_admissible
  obtain ⟨φ, hp, hs⟩ := definedDomain_admissible g
  exact ⟨φ, hp, fun x n hn => (hs x n hn).trans (h x)⟩

/-- An arbitrary external map on an admitted total domain still need not be
tracked: the same input realizer cannot return two distinct coded numbers. -/
theorem external_map_not_tracked :
    ¬ ∃ f : Hom indiscreteBool (encoded Nat), f.toFun false = (0 : Nat) ∧ f.toFun true = (1 : Nat) := by
  rintro ⟨f, h0, h1⟩
  obtain ⟨φ, _, ht⟩ := f.tracked
  obtain ⟨m, hm, hm'⟩ := ht false 0 trivial
  obtain ⟨n, hn, hn'⟩ := ht true 0 trivial
  change m = f.toFun false at hm'
  change n = f.toFun true at hn'
  have he := Part.mem_unique hm hn
  rw [hm', hn', h0, h1] at he
  cases he

/-- The presentation conversion preserves both undefinedness and exact data. -/
theorem diagonal_selected (n : Nat) :
    (zeroToDiagonal (encoded Nat)).toFun (some n) = some n := rfl

theorem diagonal_bottom :
    (zeroToDiagonal (encoded Nat)).toFun none = none := rfl

example : (zeroToDiagonal (encoded Nat)).comp (diagonalToZero (encoded Nat)) =
    Hom.id (programLift (encoded Nat)) := zero_diagonal_inverse _

example : (partialMapEquiv (encoded Nat) (encoded Nat)).symm
    (haltingIdentity.classify) = haltingIdentity := unclassify_classify _

end AssemblyPartialMaps
