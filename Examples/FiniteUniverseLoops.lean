import Examples.CompositionalUnivalence
import Examples.CubicalNativeUnivalence
import SquareKit.Internal.Cubical.DiscreteEquivalences
import SquareKit.Internal.Cubical.UniverseLoopObservations

/-! Closed finite-type loops retain permutation information through native
univalence. Native two-paths, closed observations and host equalities remain
separate in the statements below. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.FiniteUniverseLoops
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open SmallUniverse SmallUniverse.NativeUnivalence
open Examples.CubicalGlue Examples.CubicalUnivalenceTransport
open Examples.CompositionalUnivalence

abbrev loops (S : Type) := paths (code S) (code S)

noncomputable def lowerTransport {S : Type} (p : Term (loops S)) :
    Presheaf.decode (code S) ⟶ Presheaf.decode (code S) :=
  Raising.lowerMap (A := Presheaf.decode (code S)) (B := Presheaf.decode (code S)) (pathToMap p)

noncomputable def observedMap {S : Type} (p : Term (loops S)) :
    constantFamily terminal S ⟶ constantFamily terminal S :=
  (constantLocal terminal S).decodeCodeIso.inv ≫ lowerTransport p ≫
    (constantLocal terminal S).decodeCodeIso.hom

noncomputable def observedEquivalence {S : Type} (p : Term (loops S)) :
    HomotopyEquivalence (observedMap p) :=
  (Raising.lowerEquivalence (f := lowerTransport p)
    (pathToEquivalence p)).conjugateIso
      (constantLocal terminal S).decodeCodeIso.symm (constantLocal terminal S).decodeCodeIso

/-- The permutation classifies closed transport observations; its definition
uses the actual native fiber contractions of the transported map. -/
noncomputable def loopPermutation {S : Type} (p : Term (loops S)) : S ≃ S :=
  DiscreteEquivalences.closedEquiv (observedMap p) (observedEquivalence p)

theorem loopPermutation_apply {S : Type} (p : Term (loops S)) (s : S) :
    loopPermutation p s =
      (observe (Term.map (pathToMap p) (nativeInput s))).val DiscreteEquivalences.point := rfl

theorem permutation_map {S : Type} (p : Term (loops S)) :
    nativeMap (loopPermutation p) = pathToMap p := by
  let i := (constantLocal terminal S).decodeCodeIso
  have hc : (constantIso (loopPermutation p)).hom = observedMap p := by
    apply NatTrans.ext
    funext x
    apply ConcreteCategory.hom_ext
    intro s
    exact (DiscreteEquivalences.closedEquiv_app (observedMap p) (observedEquivalence p) x s).symm
  have hl : (codeIso (loopPermutation p)).hom = lowerTransport p := by
    change i.hom ≫ (constantIso (loopPermutation p)).hom ≫ i.inv = _
    rw [hc]
    change i.hom ≫ (i.inv ≫ lowerTransport p ≫ i.hom) ≫ i.inv = _
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  exact congrArg Raising.map hl

/-- Every closed loop is natively connected to the ua loop of its observed
permutation. This does not identify the loop terms by host equality. -/
noncomputable def classifyLoop {S : Type} (p : Term (loops S)) :
    Term (homogeneousPath (loops S) (equivalencePath (loopPermutation p)) p) :=
  uaOfTransportHomotopy (code S) (code S) (nativeMap (loopPermutation p))
    (nativeEquivalence (loopPermutation p)) p
    (by rw [permutation_map]; exact homogeneousRefl _)

theorem loopPermutation_eq_of_homogeneousPath {S : Type} {p q : Term (loops S)}
    (h : Term (homogeneousPath (loops S) p q)) : loopPermutation p = loopPermutation q := by
  apply Equiv.ext
  intro s
  exact congrArg (fun t => t.val DiscreteEquivalences.point)
    (observe_path (transportTwoPath (code S) (code S) h (nativeInput s)))

noncomputable def samePermutationPath {S : Type} (p q : Term (loops S))
    (h : loopPermutation p = loopPermutation q) : Term (homogeneousPath (loops S) p q) := by
  have hq : Term (homogeneousPath (loops S) (equivalencePath (loopPermutation p)) q) :=
    h.symm ▸ classifyLoop q
  exact homogeneousConcat (pathsFilling (code S) (code S)) (pathsFilling_lawful _ _)
    (homogeneousReverse (classifyLoop p)) hq

/-- Classification of closed loop components by actual permutations, stated
without introducing a quotient or claiming a native-family isomorphism. -/
theorem nonempty_homogeneousPath_iff_loopPermutation_eq {S : Type} (p q : Term (loops S)) :
    Nonempty (Term (homogeneousPath (loops S) p q)) ↔ loopPermutation p = loopPermutation q :=
  ⟨fun ⟨h⟩ => loopPermutation_eq_of_homogeneousPath h, fun h => ⟨samePermutationPath p q h⟩⟩

/-- Native family classification still retains the entire equivalence witness. -/
noncomputable def booleanLoopFamilyEquivalence := univalence (code Bool) (code Bool)


theorem loopPermutation_ua {S : Type} (e : S ≃ S) : loopPermutation (equivalencePath e) = e := by
  apply Equiv.ext
  intro s
  rw [loopPermutation_apply]
  exact congrArg (fun t => t.val DiscreteEquivalences.point)
    (Examples.CubicalNativeUnivalenceTransport.observedNative_eq e s)

theorem loopPermutation_refl (S : Type) :
    loopPermutation (homogeneousRefl (term (code S))) = Equiv.refl S := by
  apply Equiv.ext
  intro s
  exact congrArg (fun t => t.val DiscreteEquivalences.point)
    ((observe_path (reflexiveTransportComparison (code S) (nativeInput s))).trans (observe_input s))

/-- Concatenation acts in the order used by `Equiv.trans`: e, then d. -/
theorem loopPermutation_concat {S : Type} (e d : S ≃ S) :
    loopPermutation (homogeneousConcat (filling _) (filling_lawful _)
      (equivalencePath e) (equivalencePath d)) = e.trans d := by
  apply Equiv.ext
  intro s
  rw [loopPermutation_apply]
  exact congrArg (fun t => t.val DiscreteEquivalences.point) (observedConcat_eq e d s)

theorem boolean_equiv_cases (e : Bool ≃ Bool) :
    e = Equiv.refl Bool ∨ e = booleanTransposition := by
  have hne : e false ≠ e true := fun h => Bool.false_ne_true (e.injective h)
  cases hf : e false <;> cases ht : e true
  · exact (hne (hf.trans ht.symm)).elim
  · left
    apply Equiv.ext
    intro b
    cases b <;> assumption
  · right
    apply Equiv.ext
    intro b
    cases b <;> assumption
  · exact (hne (hf.trans ht.symm)).elim

noncomputable def booleanIdentityLoop : Term (loops Bool) := homogeneousRefl (term (code Bool))
noncomputable def booleanNegationLoop : Term (loops Bool) := equivalencePath booleanTransposition

/-- Exactly the two Boolean permutation components occur among closed loops. -/
theorem boolean_loop_cases (p : Term (loops Bool)) :
    Nonempty (Term (homogeneousPath (loops Bool) p booleanIdentityLoop)) ∨
    Nonempty (Term (homogeneousPath (loops Bool) p booleanNegationLoop)) := by
  rcases boolean_equiv_cases (loopPermutation p) with h | h
  · exact Or.inl ⟨samePermutationPath p booleanIdentityLoop (h.trans (loopPermutation_refl Bool).symm)⟩
  · exact Or.inr ⟨samePermutationPath p booleanNegationLoop (h.trans (loopPermutation_ua booleanTransposition).symm)⟩

/-- A native two-path would identify the transported values of true. -/
theorem booleanLoops_no_two_path :
    ¬ Nonempty (Term (homogeneousPath (loops Bool) booleanIdentityLoop booleanNegationLoop)) := by
  rintro ⟨h⟩
  have he := loopPermutation_eq_of_homogeneousPath h
  change loopPermutation (homogeneousRefl (term (code Bool))) =
    loopPermutation (equivalencePath booleanTransposition) at he
  rw [loopPermutation_refl, loopPermutation_ua] at he
  exact (by decide : true ≠ false) (congrArg (fun e : Bool ≃ Bool => e true) he)

/-- Scoped rejection: this universe's closed Boolean loop family does not
connect every pair of points by a native path. -/
theorem boolean_loops_not_path_unique :
    ¬ ∀ p q : Term (loops Bool), Nonempty (Term (homogeneousPath (loops Bool) p q)) :=
  fun h => booleanLoops_no_two_path (h booleanIdentityLoop booleanNegationLoop)

def swap01 : Fin 3 ≃ Fin 3 := Equiv.swap 0 1
def swap12 : Fin 3 ≃ Fin 3 := Equiv.swap 1 2

noncomputable def forwardLoop : Term (loops (Fin 3)) :=
  homogeneousConcat (filling _) (filling_lawful _) (equivalencePath swap01) (equivalencePath swap12)
noncomputable def backwardLoop : Term (loops (Fin 3)) :=
  homogeneousConcat (filling _) (filling_lawful _) (equivalencePath swap12) (equivalencePath swap01)

/-- The first permutation acts first: 0 → 1 → 2. -/
theorem forward_zero : observedConcat swap01 swap12 0 = constantSection (2 : Fin 3) := by
  exact observedConcat_eq swap01 swap12 0

/-- Reversing the order gives 0 → 0 → 1. -/
theorem backward_zero : observedConcat swap12 swap01 0 = constantSection (1 : Fin 3) := by
  exact observedConcat_eq swap12 swap01 0

theorem swaps_do_not_commute : swap01.trans swap12 ≠ swap12.trans swap01 := by
  intro h
  have bad : (2 : Fin 3) = 1 := congrArg (fun e : Fin 3 ≃ Fin 3 => e 0) h
  exact (by decide : (2 : Fin 3) ≠ 1) bad

/-- Different actual transport observations prohibit a native two-path. -/
theorem compositeLoops_no_two_path :
    ¬ Nonempty (Term (homogeneousPath (loops (Fin 3)) forwardLoop backwardLoop)) := by
  rintro ⟨h⟩
  have ho := observe_path (transportTwoPath (code (Fin 3)) (code (Fin 3)) h (nativeInput 0))
  have bad := congrArg (fun t => t.val DiscreteEquivalences.point)
    (forward_zero.symm.trans (ho.trans backward_zero))
  exact (by decide : (2 : Fin 3) ≠ 1) bad

/-- The supplied maps are composed, and the comparison points from their ua
to concatenation in the same first-then-second orientation. -/
noncomputable def swapComposition := NaturalUnivalenceLaws.composition
  (code (Fin 3)) (code (Fin 3)) (code (Fin 3))
  (nativeMap swap01) (nativeEquivalence swap01) (nativeMap swap12) (nativeEquivalence swap12)

noncomputable def swapCompositionAt {Δ : Context.{1}} (σ : Δ ⟶ raisedContext terminal) :=
  NaturalUnivalenceLaws.composition (σ ≫ code (Fin 3)) (σ ≫ code (Fin 3)) (σ ≫ code (Fin 3))
    (Functor.whiskerLeft σ.mapElements (nativeMap swap01)) ((nativeEquivalence swap01).reindex σ)
    (Functor.whiskerLeft σ.mapElements (nativeMap swap12)) ((nativeEquivalence swap12).reindex σ)

theorem swapComposition_reindex {Δ : Context.{1}} (σ : Δ ⟶ raisedContext terminal) :
    comparisonSquare (swapCompositionAt σ) = (comparisonSquare swapComposition).reindex
      (liftSub (interval (total (interval (raisedContext terminal))))
        (liftSub (interval (raisedContext terminal)) σ)) :=
  NaturalUnivalenceLaws.composition_body_reindex (code (Fin 3)) (code (Fin 3)) (code (Fin 3))
    (nativeMap swap01) (nativeEquivalence swap01) (nativeMap swap12) (nativeEquivalence swap12) σ

/-- Arbitrary closed loops recover through the full chosen native equivalence. -/
noncomputable def originalLoopRecovery {S : Type} (p : Term (loops S)) := recoverLoopPath (code S) p

noncomputable def intervalLoopRecovery {S : Type} (p : Term (loops S)) :=
  recoverLoopPathReindex (code S) p (projection (interval (raisedContext terminal)))

theorem recoverLoop_reindex_interval {S : Type} (p : Term (loops S)) :
    reindexPath (recoverLoop (code S) p) (projection (interval (raisedContext terminal))) =
      recoverLoop (projection (interval (raisedContext terminal)) ≫ code S)
        (reindexPath p (projection (interval (raisedContext terminal)))) :=
  recoverLoop_reindex (code S) p (projection (interval (raisedContext terminal)))

/-- Retain the preexisting recovered-loop and full-witness clients. -/
noncomputable def acceptedBooleanRecovery := Examples.CubicalNativeUnivalence.recoveredBooleanLoopPath
noncomputable def acceptedBooleanWitness := Examples.CubicalNativeUnivalence.booleanEquivalenceRoundtrip

end Examples.FiniteUniverseLoops
