import SquareKit.SheafActionQuotientDescent

/-! The category of quotient cocycles and its effective descent equivalence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SquareKit.SheafActionQuotient.Descent
open CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M X : Sheaf J (Type (max u v))}
variable {a : Action G M} {A : SplitSheaf.Ty X}

@[ext] theorem Map.ext_hom {d e : Datum (a := a) A} (h k : Map d e)
    (he : h.torsorMap.hom = k.torsorMap.hom) : h = k := by
  cases h with | mk h hp =>
    cases k with | mk k kp =>
      cases h with | mk h ht =>
        cases k with | mk k kt =>
          cases h with | mk h heq =>
            cases k with | mk k keq =>
              cases he
              rfl

instance : Category (Datum (a := a) A) where
  Hom := Map
  id := Map.ident
  comp := Map.comp
  id_comp _ :=  Map.ext_hom _ _ (Category.id_comp _)
  comp_id _ :=  Map.ext_hom _ _ (Category.comp_id _)
  assoc _ _ _ :=  Map.ext_hom _ _ (Category.assoc _ _ _)

/-- The local map includes its actual equivariant torsor arrow. -/
def Map.localArrow {d e : Datum (a := a) A} (h : Map d e) :
    Arrow d.localObject e.localObject where
  torsorArrow := SheafTorsor.equivariantArrowEquiv h.torsorMap.toEquivariantMap
  preserves := h.preserves

/-- Forget the cocycle while retaining the local quotient and its arrows. -/
def localFunctor : Datum (a := a) A ⥤ Object a (SplitSheaf.Ext A) where
  obj d := d.localObject
  map h := h.localArrow
  map_id d := by
    apply Arrow.ext
    apply SheafTorsor.Arrow.ext
    rfl
  map_comp h k := by
    apply Arrow.ext
    apply SheafTorsor.Arrow.ext
    rfl

variable (a A) [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]

/-- The selected recovery comparison is natural in compatible local arrows. -/
theorem Map.comparison_naturality {d e : Datum (a := a) A} (h : Map d e) :
    (h.arrow.reindex (SplitSheaf.p A)).comp e.comparison = d.comparison.comp h.localArrow := by
  apply Arrow.ext
  apply SheafTorsor.Arrow.ext
  ext x t
  exact h.torsorMap.evaluation (X.obj.elementsMk x.obj x.val.1) x.val.2 t


/-- Compatible local maps descend along with their objects. -/
def descentFunctor : Datum (a := a) A ⥤ Object a X where
  obj d := d.object
  map h := h.arrow
  map_id d := Map.arrow_ident d
  map_comp h k := Map.arrow_comp h k

/-- Recovery is natural on the complete local cocycle category. -/
def comparisonIso : descentFunctor a A ⋙ restriction (SplitSheaf.p A) ≅
    localFunctor (a := a) (A := A) :=
  NatIso.ofComponents (fun d => d.comparison.toIso) (fun h => h.comparison_naturality)

instance : (descentFunctor a A).Faithful where
  map_injective {d e} := (arrowEquiv d e).injective

instance : (descentFunctor a A).Full where
  map_surjective {d e} := (arrowEquiv d e).surjective

instance : (descentFunctor a A).EssSurj where
  mem_essImage P := ⟨canonicalDatum A P, ⟨(canonicalRecovery A P).toIso⟩⟩

instance : (descentFunctor a A).IsEquivalence where

instance : IsGroupoid (Datum (a := a) A) :=
  isGroupoid_of_reflects_iso (descentFunctor a A)

/-- Every quotient object and every actual quotient arrow descends. The inverse
and its coherence are obtained from the proved fully faithful, essentially
surjective functor, not assumed as part of the local datum. -/
def quotientDescentEquivalence : Datum (a := a) A ≌ Object a X :=
  (descentFunctor a A).asEquivalence

end SquareKit.SheafActionQuotient.Descent
