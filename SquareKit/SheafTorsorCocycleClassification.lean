import SquareKit.SheafTorsorCocycle
import SquareKit.SheafTorsorLocalIso
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.IsomorphismClasses

/-! Classification on one fixed cover retains every equivariant torsor arrow. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafTorsor.Cocycle
open CategoryTheory Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {X : Sheaf J (Type (max u v))}
variable {A : SplitSheaf.Ty X}

private theorem descentMap_ext {P Q : Torsor G (SplitSheaf.extension A)}
    {c : Descent.Datum A P} {d : Descent.Datum A Q} (h k : Descent.Map c d)
    (eq : h.hom = k.hom) : h = k := by
  rcases h with ⟨⟨h, he⟩, ht⟩
  rcases k with ⟨⟨k, ke⟩, kt⟩
  dsimp at eq
  cases eq
  rfl

/-- All equivariant regular maps commuting with transport are exactly gauges. -/
def Gauge.toDescentMap {c d : Datum G A} (g : Gauge c d) :
    Descent.Map c.toDescent d.toDescent where
  hom := (regularArrow g.label).iso.hom
  equivariant := (regularArrow g.label).equivariant
  transport x a b p := by
    change G.obj.obj x.obj at p
    change (p * c.label x a b) * (show G.obj.obj x.obj from g.label.hom.app x.obj ⟨x.val, b⟩) =
      (p * (show G.obj.obj x.obj from g.label.hom.app x.obj ⟨x.val, a⟩)) * d.label x a b
    rw [mul_assoc, g.compatible, ← mul_assoc]

def gaugeOfDescentMap {c d : Datum G A} (h : Descent.Map c.toDescent d.toDescent) :
    Gauge c d where
  label := regularArrowLabel h.toEquivariantMap.toArrow
  compatible x a b := by
    have ht := h.transport x a b (1 : G.obj.obj x.obj)
    have he := h.equivariant (Descent.point A x b) (c.label x a b) (1 : G.obj.obj x.obj)
    let t (a : A.family.obj x) (p : G.obj.obj x.obj) : G.obj.obj x.obj :=
      h.hom.app (Descent.point A x a) p
    change t b (1 * c.label x a b) = t a 1 * d.label x a b at ht
    change t b (c.label x a b * 1) = c.label x a b * t b 1 at he
    rw [one_mul] at ht
    rw [mul_one] at he
    exact he.symm.trans ht

theorem gaugeOfDescentMap_toDescentMap {c d : Datum G A} (g : Gauge c d) :
    gaugeOfDescentMap g.toDescentMap = g := by
  apply Gauge.ext
  ext U x
  exact one_mul (show G.obj.obj U from g.label.hom.app U x)

theorem Gauge.toDescentMap_gaugeOfDescentMap {c d : Datum G A}
    (h : Descent.Map c.toDescent d.toDescent) :
    (gaugeOfDescentMap h).toDescentMap = h := by
  have he := congrArg (fun a : Arrow (SheafTorsor.trivial G (SplitSheaf.extension A))
      (SheafTorsor.trivial G (SplitSheaf.extension A)) => a.iso.hom)
    (regularArrowLabel_recovers h.toEquivariantMap.toArrow)
  exact descentMap_ext _ _ he

def gaugeDescentEquiv (c d : Datum G A) : Gauge c d ≃ Descent.Map c.toDescent d.toDescent where
  toFun := Gauge.toDescentMap
  invFun := gaugeOfDescentMap
  left_inv := gaugeOfDescentMap_toDescentMap
  right_inv := Gauge.toDescentMap_gaugeOfDescentMap

theorem Gauge.toDescentMap_ident (c : Datum G A) :
    (Gauge.ident c).toDescentMap = Descent.Map.ident c.toDescent := by
  apply descentMap_ext
  exact congrArg (fun h : Arrow (SheafTorsor.trivial G (SplitSheaf.extension A))
    (SheafTorsor.trivial G (SplitSheaf.extension A)) => h.iso.hom) regularArrow_ident

theorem Gauge.toDescentMap_comp {c d e : Datum G A} (g : Gauge c d) (h : Gauge d e) :
    (g.comp h).toDescentMap = g.toDescentMap.comp h.toDescentMap := by
  apply descentMap_ext
  exact congrArg (fun k : Arrow (SheafTorsor.trivial G (SplitSheaf.extension A))
    (SheafTorsor.trivial G (SplitSheaf.extension A)) => k.iso.hom)
    (regularArrow_comp g.label h.label).symm

private theorem descentDatum_ext {P : Torsor G (SplitSheaf.extension A)}
    (c d : Descent.Datum A P)
    (h : ∀ x a b p, c.transport x a b p = d.transport x a b p) : c = d := by
  have ht : c.transport = d.transport := funext fun x => funext fun a => funext fun b => funext (h x a b)
  cases c
  cases d
  dsimp at ht
  cases ht
  rfl

theorem toDescent_ofDescent (d : Descent.Datum A (SheafTorsor.trivial G (SplitSheaf.extension A))) :
    (ofDescent d).toDescent = d := by
  apply descentDatum_ext
  intro x a b p
  change G.obj.obj x.obj at p
  have h := d.equivariant x a b p (1 : G.obj.obj x.obj)
  change d.transport x a b (p * 1) = p * (show G.obj.obj x.obj from d.transport x a b (1 : G.obj.obj x.obj)) at h
  rw [mul_one] at h
  exact h.symm

theorem ofDescent_toDescent (c : Datum G A) : ofDescent c.toDescent = c := by
  apply Datum.ext
  intro x a b
  exact one_mul (c.label x a b)

/-- Chosen local trivializations are data used to extract labels, separately from admission. -/
def chosenCocycle (P : Torsor G X)
    (e : Arrow (SheafTorsor.trivial G (SplitSheaf.extension A)) (reindex P (SplitSheaf.p A))) : Datum G A :=
  ofDescent (Descent.ofLocalIso P _ e)

/-- Admission is a property; no chosen trivialization is retained in the target object. -/
def Admits (A : SplitSheaf.Ty X) : ObjectProperty (Torsor G X) :=
  fun P => Nonempty (Arrow (SheafTorsor.trivial G (SplitSheaf.extension A))
    (reindex P (SplitSheaf.p A)))

abbrev Admitted (A : SplitSheaf.Ty X) := (Admits (G := G) A).FullSubcategory

/-- The property admits a chosen trivialization exactly when there is a section on the cover. -/
theorem admits_iff_section (P : Torsor G X) :
    Admits A P ↔ Nonempty (SplitSheaf.Tm (reindex P (SplitSheaf.p A)).family) :=
  trivializable_iff_section _

variable [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]

def Datum.glue (c : Datum G A) : Admitted (G := G) A :=
  ⟨Descent.torsor c.toDescent, ⟨(Descent.comparison c.toDescent).inverse⟩⟩

def Gauge.glue {c d : Datum G A} (g : Gauge c d) : c.glue ⟶ d.glue :=
  ObjectProperty.homMk g.toDescentMap.arrow

/-- Full faithfulness is inherited from effective arrow descent and regular-arrow labels. -/
def glueHomEquiv (c d : Datum G A) : Gauge c d ≃ (c.glue ⟶ d.glue) :=
  ((gaugeDescentEquiv c d).trans ((Descent.mapEquiv c.toDescent d.toDescent).trans
    equivariantArrowEquiv)).trans {
      toFun := fun h => ⟨h⟩
      invFun := fun h => h.hom
      left_inv := fun _ => rfl
      right_inv := fun h => by cases h; rfl }

def glueFunctor : Datum G A ⥤ Admitted (G := G) A where
  obj := Datum.glue
  map := Gauge.glue
  map_id c := by
    apply ObjectProperty.hom_ext
    change (Gauge.ident c).toDescentMap.arrow = _
    rw [Gauge.toDescentMap_ident, Descent.Map.arrow_ident]
    rfl
  map_comp g h := by
    apply ObjectProperty.hom_ext
    change (Gauge.comp g h).toDescentMap.arrow = _
    rw [Gauge.toDescentMap_comp, Descent.Map.arrow_comp]
    rfl

def glueFullyFaithful : (glueFunctor (G := G) (A := A)).FullyFaithful where
  preimage h := (glueHomEquiv _ _).symm h
  map_preimage h := (glueHomEquiv _ _).apply_symm_apply h
  preimage_map g := (glueHomEquiv _ _).symm_apply_apply g

instance : (glueFunctor (G := G) (A := A)).Full := glueFullyFaithful.full
instance : (glueFunctor (G := G) (A := A)).Faithful := glueFullyFaithful.faithful

def chosenRecovery (P : Torsor G X)
    (e : Arrow (SheafTorsor.trivial G (SplitSheaf.extension A)) (reindex P (SplitSheaf.p A))) :
    Arrow (chosenCocycle P e).glue.obj P :=
  (show Arrow (chosenCocycle P e).glue.obj (Descent.torsor (Descent.ofLocalIso P _ e)) from
    eqToHom (congrArg (fun d => Descent.torsor d) (toDescent_ofDescent (Descent.ofLocalIso P _ e)))).comp
      (Descent.ofLocalIsoRecovery P _ e)

theorem descentComparison_eqToHom
    {d e : Descent.Datum A (SheafTorsor.trivial G (SplitSheaf.extension A))} (h : d = e) :
    ((show Arrow (Descent.torsor d) (Descent.torsor e) from
      eqToHom (congrArg (fun d => Descent.torsor d) h)).reindex (SplitSheaf.p A)).comp
        (Descent.comparison e) = Descent.comparison d := by
  cases h
  rfl

/-- The chosen recovery restricts to exactly the specified local trivialization. -/
theorem chosenRecovery_reindex (P : Torsor G X)
    (e : Arrow (SheafTorsor.trivial G (SplitSheaf.extension A)) (reindex P (SplitSheaf.p A))) :
    (chosenRecovery P e).reindex (SplitSheaf.p A) =
      (Descent.comparison (chosenCocycle P e).toDescent).comp e := by
  change ((show Arrow (chosenCocycle P e).glue.obj
      (Descent.torsor (Descent.ofLocalIso P _ e)) from
        eqToHom (congrArg (fun d => Descent.torsor d) (toDescent_ofDescent (Descent.ofLocalIso P _ e)))).reindex _).comp
    ((Descent.ofLocalIsoRecovery P _ e).reindex _) = _
  rw [Descent.ofLocalIsoRecovery_reindex]
  exact congrArg (fun k => k.comp e)
    (descentComparison_eqToHom (toDescent_ofDescent (Descent.ofLocalIso P _ e)))

def extract (P : Admitted (G := G) A) : Datum G A := chosenCocycle P.obj P.property.some

def recovery (P : Admitted (G := G) A) : (extract P).glue ≅ P :=
  (Admits (G := G) A).isoMk (chosenRecovery P.obj P.property.some).toIso

instance : (glueFunctor (G := G) (A := A)).EssSurj where
  mem_essImage P := ⟨extract P, ⟨recovery P⟩⟩

instance : (glueFunctor (G := G) (A := A)).IsEquivalence := {}

/-- Fixed-cover cocycles classify exactly the full category admitted by that cover. -/
def equivalence : Datum G A ≌ Admitted (G := G) A := glueFunctor.asEquivalence

/-- Identity transitions recover the actual globally trivial torsor. -/
def trivialRecovery : Arrow (trivial (G := G) (A := A)).glue.obj (SheafTorsor.trivial G X) :=
  chosenRecovery (SheafTorsor.trivial G X) (Arrow.ident _)

/-- An explicit coboundary gauge yields an explicit trivialization of its glued torsor. -/
def coboundaryRecovery (g : SplitSheaf.extension A ⟶ groupSheaf G) :
    Arrow (coboundary g).glue.obj (SheafTorsor.trivial G X) :=
  ((coboundaryGauge g).inverse.glue.hom).comp trivialRecovery

/-- Gauge equivalence on this fixed cover; no commutativity or group law is imposed. -/
def gaugeSetoid : Setoid (Datum G A) where
  r c d := Nonempty (Gauge c d)
  iseqv := ⟨fun c => ⟨Gauge.ident c⟩, fun ⟨g⟩ => ⟨g.inverse⟩,
    fun ⟨g⟩ ⟨h⟩ => ⟨g.comp h⟩⟩

/-- The categorical comparison induces the corresponding fixed-cover set of classes. -/
def classEquivalence : Quotient (gaugeSetoid (G := G) (A := A)) ≃
    Quotient (isIsomorphicSetoid (Admitted (G := G) A)) where
  toFun := Quotient.map (equivalence (G := G) (A := A)).functor.obj
    (fun _ _ ⟨g⟩ => ⟨(equivalence (G := G) (A := A)).functor.mapIso g.toIso⟩)
  invFun := Quotient.map (equivalence (G := G) (A := A)).inverse.obj
    (fun _ _ ⟨e⟩ => ⟨((equivalence (G := G) (A := A)).inverse.mapIso e).hom⟩)
  left_inv q := Quotient.inductionOn q fun c => Quotient.sound
    ⟨((equivalence (G := G) (A := A)).unitIso.app c).inv⟩
  right_inv q := Quotient.inductionOn q fun P => Quotient.sound
    ⟨(equivalence (G := G) (A := A)).counitIso.app P⟩

/-- In particular, no stabilizers are discarded by the categorical comparison. -/
def stabilizerEquiv (c : Datum G A) : Gauge c c ≃ (c.glue ⟶ c.glue) := glueHomEquiv c c

end SquareKit.SheafTorsor.Cocycle
