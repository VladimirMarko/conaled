import SquareKit.SheafTorsorStack
import Examples.ClassifierDescent

/-! A proper torsor cover, effective recovery, retained automorphisms, and a noncover control. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace Examples.TorsorStack
open CategoryTheory SquareKit SquareKit.SheafTorsor
open SmoothTorsors Orbifolds.QuarterTurn

example : (Stack.pseudofunctor group).IsStack
    (Stack.topology (J := SmoothOpenSite.topology)) := inferInstance

abbrev cover := nontrivialTorsor.family
instance cover_locallySurjective :
    Presheaf.IsLocallySurjective SmoothOpenSite.topology (SplitSheaf.p cover).hom :=
  nontrivialTorsor.isLocallySurjective

abbrev coverSieve := Sieve.ofArrows _ (Stack.singleton cover)

theorem cover_mem : coverSieve ∈ Stack.topology SmoothClutching.base :=
  ⟨_, SplitSheaf.p cover, inferInstance, Sieve.ofArrows_mk _ _ ()⟩

/-- This cover cannot be replaced by the identity cover: that would choose a
section of the quarter-turn clutching torsor. -/
theorem cover_proper : coverSieve ≠ ⊤ := by
  intro h
  have hi : coverSieve (𝟙 SmoothClutching.base) := by rw [h]; trivial
  obtain ⟨i, f, hf⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hi
  exact nontrivialTorsor_no_section ⟨SplitSheaf.readTerm cover f hf.symm⟩

abbrev localDatum := ((Stack.pseudofunctor group).toDescentData (Stack.singleton cover)).obj
  nontrivialTorsor

/-- The glued object selected by the bridge recovers the original torsor. -/
def recovery : SheafTorsor.Arrow (Stack.glue localDatum) nontrivialTorsor :=
  Descent.canonicalRecovery cover nontrivialTorsor

theorem glued_not_trivializable :
    ¬ Nonempty (SheafTorsor.Arrow (trivial group SmoothClutching.base) (Stack.glue localDatum)) := by
  rintro ⟨h⟩
  exact nontrivialTorsor_not_trivializable ⟨h.comp recovery⟩

example : ((Stack.pseudofunctor group).toDescentData (Stack.singleton cover)).obj
    (Stack.glue localDatum) ≅ localDatum := Stack.localComparison localDatum

/-- The proof applies directly to Mathlib's sieve-indexed category. -/
example : ((Stack.pseudofunctor group).toDescentData
    (fun f : coverSieve.arrows.category => f.obj.hom)).IsEquivalence :=
  (Stack.pseudofunctor group).isEquivalence_toDescentData _ (by
    simpa only [Sieve.ofArrows_category] using cover_mem)

abbrev regular := ClassifierDescent.regular
abbrev regularData := ((Stack.pseudofunctor group).toDescentData (Stack.singleton regular.family)).obj
  regular

/-- Restriction and classifier recovery both retain the two distinct loops. -/
theorem loops_distinct :
    Stack.classifiedMapEquiv regularData regularData
      (Stack.homEquiv regular regular (loop quarterTurn)) ≠
    Stack.classifiedMapEquiv regularData regularData
      (Stack.homEquiv regular regular (loop 1)) := by
  intro h
  exact nonidentity_loop ((Stack.homEquiv regular regular).injective
    ((Stack.classifiedMapEquiv regularData regularData).injective h))

/-- Omitting coverage really loses information: an empty local family cannot
see the two loops, so its descent functor is not faithful. -/
def emptyFamily : ∀ _ : Empty, point ⟶ point := fun i => nomatch i

theorem empty_descent_not_faithful :
    ¬ ((Stack.pseudofunctor group).toDescentData emptyFamily).Faithful := by
  intro h
  have he : ((Stack.pseudofunctor group).toDescentData emptyFamily).map (loop quarterTurn) =
      ((Stack.pseudofunctor group).toDescentData emptyFamily).map (loop 1) := by
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    exact i.elim
  exact nonidentity_loop (((Stack.pseudofunctor group).toDescentData emptyFamily).map_injective he)

end Examples.TorsorStack
