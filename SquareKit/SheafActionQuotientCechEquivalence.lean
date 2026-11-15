import SquareKit.SheafActionQuotientCechTransport

/-! Both directions between independent quotient Čech data and pointwise
cocycles, retaining their local objects and selected arrows. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SheafActionQuotient.Cech
open CategoryTheory SplitSheaf.Cech
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M X : Sheaf J (Type (max u v))}
variable {a : Action G M} {A : SplitSheaf.Ty X}

/-- The forward presentation retains the actual selected overlap arrow. -/
def ofDescent (d : Descent.Datum (a := a) A) : Datum (a := a) A where
  localObject := d.localObject
  overlap := d.overlapArrow.toIso
  diagonal := by
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    ext x p
    exact d.torsorDatum.identity (X.obj.elementsMk x.obj x.val.1) x.val.2 p
  cocycle := by
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    ext x p
    exact d.torsorDatum.cocycle (X.obj.elementsMk x.obj x.val.1.1.1)
      x.val.1.1.2 x.val.1.2 x.val.2 p

def mapOfDescent {d e : Descent.Datum (a := a) A} (h : Descent.Map d e) :
    Map (ofDescent d) (ofDescent e) where
  localArrow := h.localArrow
  commutes := by
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    ext x p
    exact (h.torsorMap.transport (X.obj.elementsMk x.obj x.val.1.1)
      x.val.1.2 x.val.2 p).symm

def fromDescent : Descent.Datum (a := a) A ⥤ Datum (a := a) A where
  obj := ofDescent
  map := mapOfDescent
  map_id _ := by
    apply Map.ext
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    rfl
  map_comp _ _ := by
    apply Map.ext
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    rfl

/-- The reverse construction recovers the complete original pointwise datum. -/
theorem toDescent_ofDescent (d : Descent.Datum (a := a) A) :
    (ofDescent d).toDescent = d := by
  cases d with
  | mk P t h =>
    cases t
    rfl

/-- Both routes have exactly the original selected local arrow. -/
theorem mapOfDescent_toDescent_localArrow {d e : Datum (a := a) A} (h : Map d e) :
    (mapOfDescent h.toDescent).localArrow = h.localArrow := by
  apply SheafActionQuotient.Arrow.ext
  apply SheafTorsor.Arrow.ext
  rfl

/-- The round trip preserves the local object and overlap arrow, not merely
its isomorphism class. The inverse overlap is then uniquely determined. -/
theorem ofDescent_toDescent (d : Datum (a := a) A) :
    ofDescent d.toDescent = d := by
  cases d with
  | mk P overlap hd hc =>
    unfold ofDescent
    congr 1
    apply Iso.ext
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    rfl

/-- Identification of independent Čech matching data with pointwise cocycles. -/
def equivalence : Datum (a := a) A ≌ Descent.Datum (a := a) A where
  functor := toDescent
  inverse := fromDescent
  unitIso := NatIso.ofComponents (fun d =>
    { hom := { localArrow := Arrow.ident d.localObject
               commutes := by
                 apply SheafActionQuotient.Arrow.ext
                 apply SheafTorsor.Arrow.ext
                 rfl }
      inv := { localArrow := Arrow.ident d.localObject
               commutes := by
                 apply SheafActionQuotient.Arrow.ext
                 apply SheafTorsor.Arrow.ext
                 rfl }
      hom_inv_id := Map.ext _ _ rfl
      inv_hom_id := Map.ext _ _ rfl }) (by
        intro d e h
        apply Map.ext
        apply SheafActionQuotient.Arrow.ext
        apply SheafTorsor.Arrow.ext
        rfl)
  counitIso := NatIso.ofComponents (fun d =>
    eqToIso (toDescent_ofDescent d)) (by
      intro d e h
      apply Descent.Map.ext_hom
      cases d with
      | mk P t hd =>
        cases t
        cases e with
        | mk Q s he =>
          cases s
          rfl)
  functor_unitIso_comp d := by
    apply Descent.Map.ext_hom
    cases d with
    | mk P overlap hd hc => rfl

end SquareKit.SheafActionQuotient.Cech
