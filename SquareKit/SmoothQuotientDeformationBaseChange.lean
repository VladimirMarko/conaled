import SquareKit.SheafActionQuotientDescentBaseChange
import SquareKit.SmoothQuotientDeformationDescentMaps

/-! Deformation cocycles and their gluing commute with parameter change through
the actual quotient descent comparison. -/
noncomputable section
namespace SquareKit.SmoothQuotientDeformations.CocycleDatum
open CategoryTheory SheafActionQuotient SmoothOpenSite
set_option backward.isDefEq.respectTransparency false
variable {H : Type} [Group H] {M X Y Z : Sheaf topology Type}
variable {a : Action (locallyConstantGroup H) M} {A : SplitSheaf.Ty X}

/-- Pull back the supplied local deformation and its cocycle equation. -/
def baseChange (d : CocycleDatum (a := a) A) (f : Y ⟶ X) :
    CocycleDatum (a := a) (SplitSheaf.tySub A f) where
  quotient := d.quotient.baseChange f
  localDeformation := restrict (SplitSheaf.lift A f) d.localDeformation
  compatible x := d.compatible (f.hom.mapElements.obj x)

variable [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom]

/-- The chosen quotient comparison identifies the restricted glued deformation
with the gluing of the restricted local data. -/
theorem baseChange_descend (d : CocycleDatum (a := a) A) (f : Y ⟶ X) :
    transport (d.quotient.baseChangeComparison f) (restrict f d.descend) =
      (d.baseChange f).descend := by
  apply (d.baseChange f).unique
  rw [transport_restrict, ← transport_comp]
  change transport
    (((d.quotient.baseChangeComparison f).reindex (SplitSheaf.p (SplitSheaf.tySub A f))).comp
      (d.quotient.baseChange f).comparison)
    (restrict (SplitSheaf.p (SplitSheaf.tySub A f)) (restrict f d.descend)) = _
  rw [d.quotient.baseChangeComparison_recover f]
  have h := congrArg (restrict (SplitSheaf.lift A f)) d.recover
  rw [transport_restrict] at h
  exact h

/-- Restriction on compatible local fibers uses their local deformation data. -/
def baseChangeFiber (d : Descent.Datum (a := a) A) (f : Y ⟶ X)
    (s : Fiber d) : Fiber (d.baseChange f) :=
  ⟨(baseChange (ofFiber d s) f).localDeformation, (baseChange (ofFiber d s) f).compatible⟩

/-- The fiber restriction respects every selected local cocycle arrow. -/
def fiberBaseChange (f : Y ⟶ X) :
    fiberFamily (a := a) (A := A) ⟶
      Descent.baseChange f ⋙ fiberFamily (a := a) (A := SplitSheaf.tySub A f) where
  app d := ↾fun s => baseChangeFiber d f s
  naturality {d e} h := by
    apply ConcreteCategory.hom_ext
    intro s
    apply Subtype.ext
    change restrict (SplitSheaf.lift A f) ((fiberFamily.map h) s).val =
      ((fiberFamily.map (h.baseChange f)) (baseChangeFiber d f s)).val
    rw [fiberFamily_map_val, fiberFamily_map_val, transport_restrict,
      Descent.Map.baseChange_localArrow]
    rfl

/-- The local fiber comparison and parameter restriction form a commuting
square through the chosen quotient comparison. -/
theorem fiberBaseChange_comparison (d : Descent.Datum (a := a) A) (f : Y ⟶ X)
    (h : Deformation d.object) :
    fiberEquivalence (d.baseChange f)
        (transport (d.baseChangeComparison f) (restrict f h)) =
      (fiberBaseChange f).app d (fiberEquivalence d h) := by
  apply Subtype.ext
  change transport (d.baseChange f).comparison
    (restrict (SplitSheaf.p (SplitSheaf.tySub A f))
      (transport (d.baseChangeComparison f) (restrict f h))) =
    restrict (SplitSheaf.lift A f)
      (transport d.comparison (restrict (SplitSheaf.p A) h))
  rw [transport_restrict, ← transport_comp]
  change transport
    (((d.baseChangeComparison f).reindex (SplitSheaf.p (SplitSheaf.tySub A f))).comp
      (d.baseChange f).comparison) _ = _
  rw [d.baseChangeComparison_recover f, transport_restrict]
  rfl

omit [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom] in
/-- Identity parameter change preserves the selected compatible local fiber. -/
theorem baseChangeFiber_id (d : Descent.Datum (a := a) A) (s : Fiber d) :
    baseChangeFiber d (𝟙 X) s = s := by
  apply Subtype.ext
  apply Deformation.ext
  rfl

omit [Presheaf.IsLocallySurjective topology (SplitSheaf.p A).hom] in
/-- Successive parameter changes agree with their composite on local data. -/
theorem baseChangeFiber_comp (d : Descent.Datum (a := a) A) (f : Y ⟶ X) (g : Z ⟶ Y)
    (s : Fiber d) :
    baseChangeFiber (d.baseChange f) g (baseChangeFiber d f s) =
      baseChangeFiber d (g ≫ f) s := by
  apply Subtype.ext
  apply Deformation.ext
  rfl

/-- The chosen comparison acts coherently on every deformation under successive
parameter changes, not just on a particular descended deformation. -/
theorem comparison_transport_comp (d : Descent.Datum (a := a) A)
    (f : Y ⟶ X) (g : Z ⟶ Y) (h : Deformation d.object) :
    transport ((d.baseChange f).baseChangeComparison g)
        (restrict g (transport (d.baseChangeComparison f) (restrict f h))) =
      transport (d.baseChangeComparison (g ≫ f)) (restrict (g ≫ f) h) := by
  rw [transport_restrict, ← transport_comp]
  change transport (((d.baseChangeComparison f).reindex g).comp
    ((d.baseChange f).baseChangeComparison g)) _ = _
  rw [d.baseChangeComparison_comp f g, restrict_comp]

/-- The identity comparison acts as the identity on every deformation. -/
theorem comparison_transport_id (d : Descent.Datum (a := a) A)
    (h : Deformation d.object) :
    transport (d.baseChangeComparison (𝟙 X)) (restrict (𝟙 X) h) = h := by
  rw [d.baseChangeComparison_id, restrict_id]
  exact transport_id h

end SquareKit.SmoothQuotientDeformations.CocycleDatum
