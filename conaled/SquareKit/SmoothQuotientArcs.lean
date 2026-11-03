import SquareKit.QuotientPointedArcs
import SquareKit.DiscreteSheaf
import SquareKit.SmoothTorsorParameters

/-! The all-parameter homotopy-pullback comparison for smooth finite-action
quotients, constructed from torsor rigidity and actual sheaf exponentials. -/
noncomputable section
namespace SquareKit.SmoothQuotientArcs
open CategoryTheory Opposite SheafActionQuotient SmoothOpenSite SheafRelation SheafFunction
variable {H : Type} [Group H] {M : Sheaf topology Type}
local notation "G" => locallyConstantGroup H
local notation "D" => PresentationGeometry.infinitesimal topology
variable (a : SheafActionQuotient.Action (locallyConstantGroup H) M)

instance zeroRestriction_full (X : Sheaf topology Type) :
    (SheafTorsor.restriction («G» := G) (parameterZero X)).Full :=
  inferInstanceAs (parameterTorsorEquivalence (H := H) X).inverse.Full

instance zeroRestriction_faithful (X : Sheaf topology Type) :
    (SheafTorsor.restriction («G» := G) (parameterZero X)).Faithful :=
  inferInstanceAs (parameterTorsorEquivalence (H := H) X).inverse.Faithful

/-- Mapping parameters preserve covering maps, so effective quotient descent
also applies to maps out of D over arbitrary parameter covers. -/
instance parameterMap_locallySurjective {X Y : Sheaf topology Type} (f : Y ⟶ X)
    [Presheaf.IsLocallySurjective topology f.hom] :
    Presheaf.IsLocallySurjective topology (parameterMap D f).hom where
  imageSieve_mem {U} x := by
    apply topology.superset_covering _ (Presheaf.imageSieve_mem topology f.hom x.2)
    intro V k hk
    obtain ⟨y,hy⟩ := hk
    exact ⟨((D).obj.map k.op x.1, y), Prod.ext rfl hy⟩

/-- Map(iD,Q)(X) is Q(D×X), so the right side is an actual isocomma groupoid. -/
abbrev Pointed (X : Sheaf topology Type) := QuotientPointedArcs.Pullback a (parameterZero X)

/-- i(M^D) ≃ iM ×ʰ_Q Map(iD,Q), for every sheaf-valued parameter.
The comma boundary is retained as an isomorphism, with its coherence square. -/
def comparison (X : Sheaf topology Type) :
    DiscreteSheaf.sections (exponential D M) X ≌ Pointed a X :=
  (DiscreteSheaf.mappingEquiv D M X).trans
    (QuotientPointedArcs.equivalence a (parameterZero X))

/-- Chart inclusion commutes with arbitrary change of parameters. -/
theorem chartFunctor_restriction {X Y : Sheaf topology Type} (f : Y ⟶ X) :
    DiscreteSheaf.restriction M f ⋙ chartFunctor a Y =
      chartFunctor a X ⋙ restriction f := by
  apply CategoryTheory.Functor.ext
  · intro m n h
    cases m
    cases n
    cases Discrete.eq_of_hom h
    rfl
  · intro m
    rfl

theorem chartMap_reindex {X Y : Sheaf topology Type} (f : Y ⟶ X)
    {m n : Discrete (X ⟶ M)} (h : m ⟶ n) :
    ((chartFunctor a X).map h).reindex f =
      (chartFunctor a Y).map ((DiscreteSheaf.restriction M f).map h) := by
  cases m
  cases n
  cases Discrete.eq_of_hom h
  rfl

/-- Restriction of the full pointed datum, including its boundary isomorphism. -/
def baseChange {X Y : Sheaf topology Type} (f : Y ⟶ X) : Pointed a X ⥤ Pointed a Y where
  obj P := {
    left := ⟨f ≫ P.left.as⟩
    right := reindex P.right (parameterMap D f)
    hom := P.hom.reindex f }
  map {P Q} h := {
    left := (DiscreteSheaf.restriction M f).map h.left
    right := h.right.reindex (parameterMap D f)
    w := by
      have hw := congrArg (fun k => k.reindex f) h.w
      have hc := chartMap_reindex a f h.left
      apply SheafActionQuotient.Arrow.ext
      apply SheafTorsor.Arrow.ext
      ext x g
      have hc' := congrArg (fun k => k.torsorArrow.iso.hom.app x g) hc
      have hw' := congrArg (fun k => k.torsorArrow.iso.hom.app x g) hw
      exact (congrArg (fun v => (Q.hom.reindex f).torsorArrow.iso.hom.app x v) hc').symm.trans hw' }
  map_id P := by
    apply CommaMorphism.ext
    · apply Subsingleton.elim
    · rfl
  map_comp h k := by
    apply CommaMorphism.ext
    · apply Subsingleton.elim
    · rfl

/-- Restriction retains the complete pointed datum under identities. -/
theorem baseChange_id (X : Sheaf topology Type) : baseChange a (𝟙 X) = 𝟭 (Pointed a X) := by
  apply CategoryTheory.Functor.ext
  · intro P Q h
    apply CommaMorphism.ext
    · apply Subsingleton.elim
    · rfl
  · intro P
    apply Comma.ext
    · rfl
    · rfl
    · apply heq_of_eq
      apply SheafActionQuotient.Arrow.ext
      apply SheafTorsor.Arrow.ext
      rfl

/-- Successive changes of parameters retain the boundary and its square. -/
theorem baseChange_comp {X Y Z : Sheaf topology Type} (f : Y ⟶ X) (g : Z ⟶ Y) :
    baseChange a (g ≫ f) = baseChange a f ⋙ baseChange a g := by
  apply CategoryTheory.Functor.ext
  · intro P Q h
    apply CommaMorphism.ext
    · apply Subsingleton.elim
    · rfl
  · intro P
    apply Comma.ext
    · rfl
    · rfl
    · apply heq_of_eq
      apply SheafActionQuotient.Arrow.ext
      apply SheafTorsor.Arrow.ext
      rfl

/-- The uncurried comparison retains its boundary under base change. -/
theorem arcComparison_natural {X Y : Sheaf topology Type} (f : Y ⟶ X) :
    DiscreteSheaf.restriction M (parameterMap D f) ⋙
        QuotientPointedArcs.comparison a (parameterZero Y) =
      QuotientPointedArcs.comparison a (parameterZero X) ⋙ baseChange a f := by
  apply CategoryTheory.Functor.ext
  · intro m n h
    cases m
    cases n
    cases Discrete.eq_of_hom h
    simp
  · intro m
    apply Comma.ext
    · rfl
    · rfl
    · apply heq_of_eq
      apply SheafActionQuotient.Arrow.ext
      apply SheafTorsor.Arrow.ext
      ext x g
      rfl

/-- The quotient comparison commutes with every map of sheaf parameters. -/
theorem comparison_natural {X Y : Sheaf topology Type} (f : Y ⟶ X) :
    DiscreteSheaf.restriction (exponential D M) f ⋙ (comparison a Y).functor =
      (comparison a X).functor ⋙ baseChange a f := by
  change DiscreteSheaf.restriction (exponential D M) f ⋙
      ((DiscreteSheaf.mappingEquiv D M Y).functor ⋙
        QuotientPointedArcs.comparison a (parameterZero Y)) =
    ((DiscreteSheaf.mappingEquiv D M X).functor ⋙
      QuotientPointedArcs.comparison a (parameterZero X)) ⋙ baseChange a f
  rw [← CategoryTheory.Functor.assoc, DiscreteSheaf.mappingEquiv_natural,
    CategoryTheory.Functor.assoc, arcComparison_natural, CategoryTheory.Functor.assoc]

/-- The comparison's boundary really is identity on the restricted chart. -/
theorem comparison_boundary (X : Sheaf topology Type) (h : X ⟶ exponential D M) :
    ((comparison a X).functor.obj ⟨h⟩).hom =
      (𝟙 (chart a (parameterZero X ≫ uncurry h))) := rfl

end SquareKit.SmoothQuotientArcs
