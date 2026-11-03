import SquareKit.QuotientPointedArcs
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic

/-! The fixed-lift homotopy fiber and its actual boundary transport. -/
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace SquareKit.QuotientFixedArcs
open CategoryTheory Opposite SheafActionQuotient
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{w}} {M : Sheaf J (Type w)}
variable (a : Action G M) {X Y : Sheaf J (Type w)} (f : X ⟶ Y) (m : X ⟶ M)

abbrev Fiber := StructuredArrow (chart a m) (restriction (a := a) f)
instance : Groupoid (Fiber a f m) := Groupoid.ofIsIso (fun e => by
  let i := StructuredArrow.isoMk (asIso e.right) (StructuredArrow.w e)
  have hi : i.hom = e := by apply StructuredArrow.hom_ext; rfl
  rw [← hi]
  exact i.isIso_hom)

abbrev Arcs := {h : Y ⟶ M // f ≫ h = m}

def boundary (h : Arcs f m) : chart a m ⟶ (restriction f).obj (chart a h.val) where
  torsorArrow := SheafTorsor.Arrow.ident _
  preserves x p := congrArg (a.act x.obj p)
    (congrArg (fun k : X ⟶ M => k.hom.app x.obj x.val) h.property)

def comparison : Discrete (Arcs f m) ⥤ Fiber a f m :=
  Discrete.functor fun h => StructuredArrow.mk (boundary a f m h)

instance comparison_faithful : (comparison a f m).Faithful where
  map_injective _ := Subsingleton.elim _ _

def toPullback (P : Fiber a f m) : QuotientPointedArcs.Pullback a f :=
  ⟨⟨m⟩, P.right, P.hom⟩

theorem comparison_arrow_underlying
    [CategoryTheory.Functor.Faithful (SheafTorsor.restriction (G := G) f)]
    {h k : Discrete (Arcs f m)} (e : (comparison a f m).obj h ⟶ (comparison a f m).obj k) :
    e.right.torsorArrow = SheafTorsor.Arrow.ident (SheafTorsor.trivial G Y) := by
  apply (SheafTorsor.restriction f).map_injective
  have hw := congrArg Arrow.torsorArrow (StructuredArrow.w e)
  exact hw

theorem comparison_arrow_eq
    [CategoryTheory.Functor.Faithful (SheafTorsor.restriction (G := G) f)]
    {h k : Discrete (Arcs f m)} (e : (comparison a f m).obj h ⟶ (comparison a f m).obj k) : h = k := by
  apply Discrete.ext
  apply Subtype.ext
  ext U y
  have hp := e.right.preserves (Y.obj.elementsMk U y) (1 : G.obj.obj U)
  rw [comparison_arrow_underlying a f m e] at hp
  exact ((a.one_act U (k.as.val.hom.app U y)).symm.trans hp).trans
    (a.one_act U (h.as.val.hom.app U y)) |>.symm

instance comparison_full [CategoryTheory.Functor.Faithful (SheafTorsor.restriction (G := G) f)] :
    (comparison a f m).Full where
  map_surjective {h k} e := by
    have he := comparison_arrow_eq a f m e
    subst k
    refine ⟨𝟙 h, ?_⟩
    rw [CategoryTheory.Functor.map_id]
    apply StructuredArrow.hom_ext
    apply SheafActionQuotient.Arrow.ext
    exact (comparison_arrow_underlying a f m e).symm

section Lifting
variable [CategoryTheory.Functor.Full (SheafTorsor.restriction (G := G) f)]

def lift (P : Fiber a f m) : Arcs f m :=
  ⟨QuotientPointedArcs.liftArc a f (toPullback a f m P),
    QuotientPointedArcs.liftArc_boundary a f (toPullback a f m P)⟩

def comparisonIso (P : Fiber a f m) : (comparison a f m).obj ⟨lift a f m P⟩ ≅ P :=
  StructuredArrow.isoMk
    (Arrow.toIso (P.right.chartOfTrivialization
      (QuotientPointedArcs.liftTrivialization a f (toPullback a f m P)))) (by
    apply SheafActionQuotient.Arrow.ext
    change (QuotientPointedArcs.liftTrivialization a f (toPullback a f m P)).reindex f = _
    exact QuotientPointedArcs.liftTrivialization_boundary a f (toPullback a f m P))

instance comparison_essSurj : (comparison a f m).EssSurj where
  mem_essImage P := ⟨⟨lift a f m P⟩, ⟨comparisonIso a f m P⟩⟩
end Lifting

def equivalence [CategoryTheory.Functor.Full (SheafTorsor.restriction (G := G) f)]
    [CategoryTheory.Functor.Faithful (SheafTorsor.restriction (G := G) f)] :
    Discrete (Arcs f m) ≌ Fiber a f m := by
  letI : (comparison a f m).IsEquivalence := {}
  exact (comparison a f m).asEquivalence

variable {a f m}

/-- Forward transport keeps the quotient arc and precomposes its boundary by
an inverse arrow. The coherent boundary is retained as data. -/
def transport {n : X ⟶ M} (c : chart a m ⟶ chart a n) : Fiber a f m ⥤ Fiber a f n :=
  StructuredArrow.map (SheafActionQuotient.Arrow.inverse c)

@[simp] theorem transport_boundary {n : X ⟶ M} (c : chart a m ⟶ chart a n) (P : Fiber a f m) :
    ((transport c).obj P).hom = SheafActionQuotient.Arrow.inverse c ≫ P.hom := rfl

theorem transport_identity (P : Fiber a f m) : (transport (𝟙 (chart a m))).obj P = P := by
  exact StructuredArrow.map_id

theorem transport_composition {n k : X ⟶ M}
    (c : chart a m ⟶ chart a n) (d : chart a n ⟶ chart a k) (P : Fiber a f m) :
    (transport (c ≫ d)).obj P = (transport d).obj ((transport c).obj P) := by
  change (StructuredArrow.map (SheafActionQuotient.Arrow.inverse d ≫ SheafActionQuotient.Arrow.inverse c)).obj P = _
  exact StructuredArrow.map_comp

/-- A retraction extends a boundary group label over the arc parameter. -/
def forwardArcs (p : Y ⟶ X) (hp : f ≫ p = 𝟙 X) {n : X ⟶ M}
    (c : chart a m ⟶ chart a n) (h : Arcs f m) : Arcs f n :=
  ⟨a.onMap (p ≫ arrowLabel (SheafActionQuotient.Arrow.inverse c)) h.val, by
    have hc := arrowLabel_relation (SheafActionQuotient.Arrow.inverse c)
    ext U x
    have hf := congrArg (fun k : X ⟶ X => k.hom.app U x) hp
    have hh := congrArg (fun k : X ⟶ M => k.hom.app U x) h.property
    have he := congrArg (fun k : X ⟶ M => k.hom.app U x) hc
    change a.act U ((arrowLabel (SheafActionQuotient.Arrow.inverse c)).hom.app U
      (p.hom.app U (f.hom.app U x))) (h.val.hom.app U (f.hom.app U x)) = _
    change p.hom.app U (f.hom.app U x) = x at hf
    change h.val.hom.app U (f.hom.app U x) = m.hom.app U x at hh
    rw [hf, hh]
    exact he⟩

/-- The concrete transported arc is isomorphic to boundary transport, with its
actual quotient arrow supplying the coherent triangle. -/
def forwardComparisonIso (p : Y ⟶ X) (hp : f ≫ p = 𝟙 X) {n : X ⟶ M}
    (c : chart a m ⟶ chart a n) (h : Arcs f m) :
    (comparison a f n).obj ⟨forwardArcs p hp c h⟩ ≅
      (transport c).obj ((comparison a f m).obj ⟨h⟩) :=
  StructuredArrow.isoMk
    (SheafActionQuotient.Arrow.toIso
      (chartArrowOfRelation (p ≫ arrowLabel (SheafActionQuotient.Arrow.inverse c))
        (forwardArcs p hp c h).val h.val rfl)) (by
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    ext x q
    change G.obj.obj x.obj at q
    have hf := congrArg (fun k : X ⟶ X => k.hom.app x.obj x.val) hp
    change p.hom.app x.obj (f.hom.app x.obj x.val) = x.val at hf
    change q * (show G.obj.obj x.obj from (SheafActionQuotient.Arrow.inverse c).torsorArrow.iso.hom.app
      (X.obj.elementsMk x.obj (p.hom.app x.obj (f.hom.app x.obj x.val))) (1 : G.obj.obj x.obj)) =
      (SheafActionQuotient.Arrow.inverse c).torsorArrow.iso.hom.app x q
    rw [hf]
    have he := (SheafActionQuotient.Arrow.inverse c).torsorArrow.equivariant x q (1 : G.obj.obj x.obj)
    change (SheafActionQuotient.Arrow.inverse c).torsorArrow.iso.hom.app x (q * 1) =
      q * (show G.obj.obj x.obj from (SheafActionQuotient.Arrow.inverse c).torsorArrow.iso.hom.app x (1 : G.obj.obj x.obj)) at he
    simpa only [mul_one] using he.symm)

def forwardComparisonNatIso (p : Y ⟶ X) (hp : f ≫ p = 𝟙 X) {n : X ⟶ M}
    (c : chart a m ⟶ chart a n) :
    Discrete.functor (fun h => (comparison a f n).obj ⟨forwardArcs p hp c h⟩) ≅
      comparison a f m ⋙ transport c :=
  Discrete.natIso (fun h => forwardComparisonIso p hp c h.as)

theorem forwardArcs_identity (p : Y ⟶ X) (hp : f ≫ p = 𝟙 X) (h : Arcs f m) :
    forwardArcs p hp (𝟙 (chart a m)) h = h := by
  apply Subtype.ext
  ext U y
  exact a.one_act U (h.val.hom.app U y)

theorem forwardArcs_composition (p : Y ⟶ X) (hp : f ≫ p = 𝟙 X) {n k : X ⟶ M}
    (c : chart a m ⟶ chart a n) (d : chart a n ⟶ chart a k) (h : Arcs f m) :
    forwardArcs p hp (c ≫ d) h = forwardArcs p hp d (forwardArcs p hp c h) := by
  apply Subtype.ext
  ext U y
  let x := X.obj.elementsMk U (p.hom.app U y)
  let gc : G.obj.obj U := (SheafActionQuotient.Arrow.inverse c).torsorArrow.iso.hom.app x (1 : G.obj.obj U)
  let gd : G.obj.obj U := (SheafActionQuotient.Arrow.inverse d).torsorArrow.iso.hom.app x (1 : G.obj.obj U)
  have he := (SheafActionQuotient.Arrow.inverse c).torsorArrow.equivariant x gd (1 : G.obj.obj U)
  change (SheafActionQuotient.Arrow.inverse c).torsorArrow.iso.hom.app x (gd * 1) = gd * gc at he
  rw [mul_one] at he
  change a.act U ((SheafActionQuotient.Arrow.inverse c).torsorArrow.iso.hom.app x gd)
    (h.val.hom.app U y) = a.act U gd (a.act U gc (h.val.hom.app U y))
  rw [he, a.mul_act]

/-- Restriction of fixed arcs along a commuting square. -/
def restrictArcs {X' Y' : Sheaf J (Type w)} (f' : X' ⟶ Y')
    (s : X' ⟶ X) (t : Y' ⟶ Y) (hs : f' ≫ t = s ≫ f) (h : Arcs f m) :
    Arcs f' (s ≫ m) :=
  ⟨t ≫ h.val, by rw [← Category.assoc, hs, Category.assoc, h.property]⟩

theorem forwardArcs_natural {X' Y' : Sheaf J (Type w)} (f' : X' ⟶ Y')
    (s : X' ⟶ X) (t : Y' ⟶ Y) (hs : f' ≫ t = s ≫ f)
    (p : Y ⟶ X) (hp : f ≫ p = 𝟙 X) (p' : Y' ⟶ X') (hp' : f' ≫ p' = 𝟙 X')
    (ht : t ≫ p = p' ≫ s) {n : X ⟶ M} (c : chart a m ⟶ chart a n) (h : Arcs f m) :
    restrictArcs f' s t hs (forwardArcs p hp c h) =
      forwardArcs p' hp' (show chart a (s ≫ m) ⟶ chart a (s ≫ n) from c.reindex s) (restrictArcs f' s t hs h) := by
  apply Subtype.ext
  ext U y
  have he := congrArg (fun k : Y' ⟶ X => k.hom.app U y) ht
  change p.hom.app U (t.hom.app U y) = s.hom.app U (p'.hom.app U y) at he
  change a.act U ((arrowLabel (SheafActionQuotient.Arrow.inverse c)).hom.app U
    (p.hom.app U (t.hom.app U y))) (h.val.hom.app U (t.hom.app U y)) = _
  rw [he]
  rfl

end SquareKit.QuotientFixedArcs
