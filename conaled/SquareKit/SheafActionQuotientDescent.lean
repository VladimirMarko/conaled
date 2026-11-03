import SquareKit.SheafActionQuotient
import SquareKit.SheafTorsorDescent
import Mathlib.CategoryTheory.Sites.RegularEpi

/-! Effective descent of the extra equivariant map in the action quotient. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafActionQuotient.Descent
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M X : Sheaf J (Type (max u v))}
variable {a : Action G M}

instance effectiveEpi_of_local {B E : Sheaf J (Type (max u v))} (f : B ⟶ E)
    [Presheaf.IsLocallySurjective J f.hom] : EffectiveEpi f :=
  (isRegularEpi_iff_effectiveEpi f).mp (IsRegularEpiCategory.regularEpiOfEpi f)

/-- A map constant on the fibers of a locally surjective sheaf map descends
by the proved regular-epimorphism theorem for the actual sheaf category. -/
def descendMap {B E N : Sheaf J (Type (max u v))} (f : B ⟶ E)
    [Presheaf.IsLocallySurjective J f.hom] (m : B ⟶ N)
    (h : ∀ U (p q : B.obj.obj U), f.hom.app U p = f.hom.app U q → m.hom.app U p = m.hom.app U q) : E ⟶ N :=
  EffectiveEpi.desc f m (by
    intro Z g₁ g₂ he
    ext U z
    exact h U (g₁.hom.app U z) (g₂.hom.app U z)
      (congrArg (fun k : Z ⟶ E => k.hom.app U z) he))

theorem descendMap_fac {B E N : Sheaf J (Type (max u v))} (f : B ⟶ E)
    [Presheaf.IsLocallySurjective J f.hom] (m : B ⟶ N)
    (h : ∀ U (p q : B.obj.obj U), f.hom.app U p = f.hom.app U q → m.hom.app U p = m.hom.app U q) :
    f ≫ descendMap f m h = m := by
  unfold descendMap
  apply EffectiveEpi.fac
  intro Z g₁ g₂ he
  ext U z
  exact h U (g₁.hom.app U z) (g₂.hom.app U z)
    (congrArg (fun k : Z ⟶ E => k.hom.app U z) he)

/-- Descent data contains the accepted torsor cocycle and compatibility of
its equivariant map. Effectiveness is a conclusion, not an input field. -/
structure Datum (A : SplitSheaf.Ty X) where
  localObject : Object a (SplitSheaf.Ext A)
  torsorDatum : SheafTorsor.Descent.Datum A localObject.torsor
  value_compatible (x : X.obj.Elements) (p q : A.family.obj x)
    (t : localObject.torsor.family.family.obj (SheafTorsor.Descent.point A x p)) :
    localObject.value (SheafTorsor.Descent.point A x q) (torsorDatum.transport x p q t) =
      localObject.value (SheafTorsor.Descent.point A x p) t

namespace Datum
variable {A : SplitSheaf.Ty X} (d : Datum (a := a) A)
variable [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]

abbrev descendedTorsor := SheafTorsor.Descent.torsor d.torsorDatum
abbrev cover : SplitSheaf.Ext (SplitSheaf.tySub d.descendedTorsor.family (SplitSheaf.p A)) ⟶
    SplitSheaf.Ext d.descendedTorsor.family := SplitSheaf.lift _ (SplitSheaf.p A)

instance cover_locallySurjective : Presheaf.IsLocallySurjective J d.cover.hom where
  imageSieve_mem {U} t := by
    have h := Presheaf.imageSieve_mem J (SplitSheaf.p A).hom t.1
    apply J.superset_covering _ h
    intro V k hk
    obtain ⟨⟨x,b⟩, hb⟩ := hk
    change x = X.obj.map k.op t.1 at hb
    subst x
    exact ⟨⟨⟨X.obj.map k.op t.1,b⟩,
      d.descendedTorsor.family.family.map (ElementFamilies.along X.obj k.op t.1) t.2⟩, rfl⟩

def localObjectOver : Object a (SplitSheaf.Ext A) :=
  d.localObject.transfer (SheafTorsor.Descent.comparison d.torsorDatum)

theorem localMap_fiber_constant (U : Cᵒᵖ)
    (p q : (SplitSheaf.Ext (SplitSheaf.tySub d.descendedTorsor.family (SplitSheaf.p A))).obj.obj U)
    (h : d.cover.hom.app U p = d.cover.hom.app U q) :
    d.localObjectOver.totalMap.hom.app U p = d.localObjectOver.totalMap.hom.app U q := by
  rcases p with ⟨⟨x,b⟩,t⟩
  rcases q with ⟨⟨y,c⟩,s⟩
  have hx : x = y := congrArg Sigma.fst h
  subst y
  have ht : t = s := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  subst s
  let z := X.obj.elementsMk U x
  change d.localObject.value (SheafTorsor.Descent.point A z b)
    (SheafTorsor.Descent.evaluationEquiv d.torsorDatum z b t) =
      d.localObject.value (SheafTorsor.Descent.point A z c)
        (SheafTorsor.Descent.evaluationEquiv d.torsorDatum z c t)
  rw [← SheafTorsor.Descent.evaluation_transport d.torsorDatum z b c t]
  exact (d.value_compatible z b c _).symm

def totalMap : SplitSheaf.Ext d.descendedTorsor.family ⟶ M :=
  descendMap d.cover d.localObjectOver.totalMap d.localMap_fiber_constant

theorem totalMap_fac : d.cover ≫ d.totalMap = d.localObjectOver.totalMap :=
  descendMap_fac d.cover d.localObjectOver.totalMap d.localMap_fiber_constant

def value (x : X.obj.Elements) (t : d.descendedTorsor.family.family.obj x) : M.obj.obj x.obj :=
  d.totalMap.hom.app x.obj ⟨x.val,t⟩

theorem value_natural {x y : X.obj.Elements} (f : x ⟶ y)
    (t : d.descendedTorsor.family.family.obj x) :
    M.obj.map f.hom (d.value x t) = d.value y (d.descendedTorsor.family.family.map f t) := by
  have h := NatTrans.naturality_apply d.totalMap.hom f.hom ⟨x.val,t⟩
  have he : (SplitSheaf.Ext d.descendedTorsor.family).obj.map f.hom ⟨x.val,t⟩ =
      ⟨y.val,d.descendedTorsor.family.family.map f t⟩ := by
    apply ElementFamilies.total_ext X.obj f.map_val
    change d.descendedTorsor.family.family.map _
      (d.descendedTorsor.family.family.map _ t) = _
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    congr 2
    apply congrArg d.descendedTorsor.family.family.map
    apply Functor.Elements.hom_ext
    simp [ElementFamilies.vertical]
  exact h.symm.trans (congrArg (d.totalMap.hom.app _) he)

theorem value_at_lift (x : X.obj.Elements) (b : A.family.obj x)
    (t : d.descendedTorsor.family.family.obj x) :
    d.value x t = d.localObject.value (SheafTorsor.Descent.point A x b)
      (SheafTorsor.Descent.evaluationEquiv d.torsorDatum x b t) :=
  congrArg (fun k => k.hom.app x.obj ⟨⟨x.val,b⟩,t⟩) d.totalMap_fac

theorem value_equivariant (x : X.obj.Elements) (g : G.obj.obj x.obj)
    (t : d.descendedTorsor.family.family.obj x) :
    d.value x (d.descendedTorsor.act x g t) = a.act x.obj g (d.value x t) := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp M.property)
    (Presheaf.imageSieve (SplitSheaf.p A).hom x.val)
    (Presheaf.imageSieve_mem J (SplitSheaf.p A).hom x.val)).isSeparatedFor.ext
  intro V k hk
  obtain ⟨⟨y,b⟩, hb⟩ := hk
  change y = X.obj.map k.op x.val at hb
  subst y
  let f := ElementFamilies.along X.obj k.op x.val
  rw [d.value_natural f, a.natural, d.value_natural f, d.descendedTorsor.natural f]
  rw [d.value_at_lift _ b, d.value_at_lift _ b]
  have he := SheafTorsor.Descent.evaluation_equivariant d.torsorDatum
    (SheafTorsor.Descent.point A _ b) (G.obj.map k.op g)
    (d.descendedTorsor.family.family.map f t)
  exact (congrArg (d.localObject.value _) he).trans (d.localObject.equivariant _ _ _)

/-- The quotient object is constructed from effective torsor descent and the
proved descent of its extra equivariant map. -/
def object : Object a X where
  torsor := d.descendedTorsor
  value := d.value
  natural := d.value_natural
  equivariant := d.value_equivariant

/-- Restriction recovers the local quotient object, including its map to M. -/
def comparison : Arrow (reindex d.object (SplitSheaf.p A)) d.localObject where
  torsorArrow := SheafTorsor.Descent.comparison d.torsorDatum
  preserves x t := (d.value_at_lift (X.obj.elementsMk x.obj x.val.1) x.val.2 t).symm

end Datum

variable {A : SplitSheaf.Ty X} (d e : Datum (a := a) A)

/-- A morphism of quotient descent data preserves both the torsor cocycle
and the full equivariant map to the acted-on sheaf. -/
structure Map where
  torsorMap : SheafTorsor.Descent.Map d.torsorDatum e.torsorDatum
  preserves (x : (SplitSheaf.Ext A).obj.Elements)
    (p : d.localObject.torsor.family.family.obj x) :
    e.localObject.value x (torsorMap.hom.app x p) = d.localObject.value x p

namespace Map
variable {d e}
variable [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]

theorem value_preserves (h : Map d e) (x : X.obj.Elements)
    (t : d.descendedTorsor.family.family.obj x) :
    e.value x (h.torsorMap.descend.app x t) = d.value x t := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp M.property)
    (Presheaf.imageSieve (SplitSheaf.p A).hom x.val)
    (Presheaf.imageSieve_mem J (SplitSheaf.p A).hom x.val)).isSeparatedFor.ext
  intro V k hk
  obtain ⟨⟨y,b⟩, hb⟩ := hk
  change y = X.obj.map k.op x.val at hb
  subst y
  let f := ElementFamilies.along X.obj k.op x.val
  erw [e.value_natural f, d.value_natural f,
    ← NatTrans.naturality_apply h.torsorMap.descend f t]
  erw [e.value_at_lift _ b, d.value_at_lift _ b, h.torsorMap.evaluation]
  exact h.preserves _ _

def arrow (h : Map d e) : Arrow d.object e.object where
  torsorArrow := h.torsorMap.arrow
  preserves := h.value_preserves

def ofArrow (f : Arrow d.object e.object) : Map d e where
  torsorMap := SheafTorsor.Descent.Map.ofEquivariantMap
    (SheafTorsor.equivariantArrowEquiv.symm f.torsorArrow)
  preserves x p := by
    let y := X.obj.elementsMk x.obj x.val.1
    let b := x.val.2
    change e.localObject.value (SheafTorsor.Descent.point A y b)
      (SheafTorsor.Descent.evaluationEquiv e.torsorDatum y b
        (f.torsorArrow.iso.hom.app y
          ((SheafTorsor.Descent.evaluationEquiv d.torsorDatum y b).symm p))) = _
    rw [← e.value_at_lift]
    change e.object.value y (f.torsorArrow.iso.hom.app y _) = _
    rw [f.preserves]
    change d.value y _ = _
    rw [d.value_at_lift y b, Equiv.apply_symm_apply]
    rfl

omit [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] in
@[ext] theorem ext (h k : Map d e) (hh : h.torsorMap = k.torsorMap) : h = k := by
  cases h
  cases k
  cases hh
  rfl

theorem ofArrow_arrow (h : Map d e) : ofArrow h.arrow = h := by
  apply ext
  exact SheafTorsor.Descent.Map.ofEquivariantMap_equivariantMap h.torsorMap

theorem arrow_ofArrow (f : Arrow d.object e.object) : (ofArrow f).arrow = f := by
  apply Arrow.ext
  apply SheafTorsor.Arrow.ext
  exact congrArg SheafTorsor.EquivariantMap.hom
    (SheafTorsor.Descent.Map.equivariantMap_ofEquivariantMap
      (SheafTorsor.equivariantArrowEquiv.symm f.torsorArrow))

end Map

/-- Effective descent of all quotient arrows, with their value-preservation
condition, is a genuine equivalence of hom types. -/
def arrowEquiv [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    Map d e ≃ Arrow d.object e.object where
  toFun h := h.arrow
  invFun f := Map.ofArrow f
  left_inv h := Map.ofArrow_arrow h
  right_inv f := Map.arrow_ofArrow f

/-- The canonical datum of any quotient object retains its actual torsor,
including objects which have no global chart lift. -/
def canonicalDatum (A : SplitSheaf.Ty X) (P : Object a X) : Datum (a := a) A where
  localObject := reindex P (SplitSheaf.p A)
  torsorDatum := SheafTorsor.Descent.canonicalDatum A P.torsor
  value_compatible _ _ _ _ := rfl

theorem canonical_value (A : SplitSheaf.Ty X) (P : Object a X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]
    (x : X.obj.Elements) (p : P.torsor.family.family.obj x) :
    (canonicalDatum A P).value x ((SheafTorsor.Descent.canonicalFamilyMap A P.torsor).app x p) =
      P.value x p := by
  let d := canonicalDatum A P
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp M.property)
    (Presheaf.imageSieve (SplitSheaf.p A).hom x.val)
    (Presheaf.imageSieve_mem J (SplitSheaf.p A).hom x.val)).isSeparatedFor.ext
  intro V k hk
  obtain ⟨⟨y,b⟩, hb⟩ := hk
  change y = X.obj.map k.op x.val at hb
  subst y
  let f := ElementFamilies.along X.obj k.op x.val
  erw [d.value_natural f, P.natural f,
    ← NatTrans.naturality_apply (SheafTorsor.Descent.canonicalFamilyMap A P.torsor) f p]
  rw [d.value_at_lift _ b]
  let z := X.obj.elementsMk (op V) (X.obj.map k.op x.val)
  have he := SheafTorsor.Descent.canonicalValue_evaluate A P.torsor (𝟙 z)
    (P.torsor.family.family.map f p) b
  rw [SplitFunctionDiagram.restrict_id, P.torsor.family.family.map_id] at he
  exact congrArg (P.value z) he

def canonicalEmbedding (A : SplitSheaf.Ty X) (P : Object a X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    Arrow P (canonicalDatum A P).object where
  torsorArrow := (SheafTorsor.Descent.canonicalEmbedding A P.torsor).toArrow
  preserves := canonical_value A P

/-- Effectiveness recovers arbitrary original quotient objects globally, not
just their restrictions to the cover. -/
def canonicalRecovery (A : SplitSheaf.Ty X) (P : Object a X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    Arrow (canonicalDatum A P).object P := (canonicalEmbedding A P).inverse

/-- Compatible arrows recover all arrows between arbitrary original objects. -/
def canonicalArrowEquiv (A : SplitSheaf.Ty X) (P Q : Object a X)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    Map (canonicalDatum A P) (canonicalDatum A Q) ≃ Arrow P Q :=
  (arrowEquiv (canonicalDatum A P) (canonicalDatum A Q)).trans (CategoryTheory.Iso.homCongr
    (canonicalRecovery A P).toIso (canonicalRecovery A Q).toIso)

def Map.ident (d : Datum (a := a) A) : Map d d where
  torsorMap := SheafTorsor.Descent.Map.ident d.torsorDatum
  preserves _ _ := rfl

def Map.comp {d e r : Datum (a := a) A} (h : Map d e) (k : Map e r) : Map d r where
  torsorMap := h.torsorMap.comp k.torsorMap
  preserves x p := (k.preserves x _).trans (h.preserves x p)

theorem Map.arrow_ident (d : Datum (a := a) A)
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom] :
    (Map.ident d).arrow = Arrow.ident d.object := by
  apply Arrow.ext
  exact SheafTorsor.Descent.Map.arrow_ident d.torsorDatum

theorem Map.arrow_comp {d e r : Datum (a := a) A}
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]
    (h : Map d e) (k : Map e r) :
    (h.comp k).arrow = h.arrow.comp k.arrow := by
  apply Arrow.ext
  exact SheafTorsor.Descent.Map.arrow_comp h.torsorMap k.torsorMap

end SquareKit.SheafActionQuotient.Descent
