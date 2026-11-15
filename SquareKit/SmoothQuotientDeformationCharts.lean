import SquareKit.SmoothQuotientDeformations
import SquareKit.SmoothQuotientTransport

/-! On chart lifts, equivariant torsor deformations recover the existing
fixed arcs, preserving the inverse-label orientation of forward transport. -/
noncomputable section
namespace SquareKit.SmoothQuotientDeformations
open CategoryTheory SheafActionQuotient SmoothOpenSite SheafRelation Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {H : Type} [Group H] {M : Sheaf topology Type}
variable {a : Action (locallyConstantGroup H) M} {X : Sheaf topology Type}
local notation "D" => SmoothOpenSite.infinitesimal

/-- Evaluate the equivariant deformation at the identity of the regular torsor. -/
def toArc {m : X ⟶ M} (h : Deformation (chart a m)) : QuotientFixedArcs.Arcs (parameterZero X) m :=
  ⟨⟨{ app U := ↾fun y => h.map.hom.app U (y.1, ⟨y.2,(1 : (locallyConstantGroup H).obj.obj U)⟩)
      naturality {U V} f := by
        apply ConcreteCategory.hom_ext
        intro y
        have hn := NatTrans.naturality_apply h.map.hom f (show (product D (SplitSheaf.Ext (chart a m).torsor.family)).obj.obj U from (y.1, ⟨y.2,(1 : (locallyConstantGroup H).obj.obj U)⟩))
        change h.map.hom.app V ((D).obj.map f y.1,
          ⟨X.obj.map f y.2, (locallyConstantGroup H).obj.map f 1⟩) = _ at hn
        change h.map.hom.app V ((D).obj.map f y.1,⟨X.obj.map f y.2,(1 : (locallyConstantGroup H).obj.obj V)⟩) =
          M.obj.map f (h.map.hom.app U (y.1,⟨y.2,(1 : (locallyConstantGroup H).obj.obj U)⟩))
        simpa only [map_one] using hn }⟩, by
    ext U x
    have hz := congrArg (fun k => k.hom.app U ⟨x,(1 : (locallyConstantGroup H).obj.obj U)⟩) h.zero
    exact hz.trans (a.one_act U (m.hom.app U x))⟩

/-- Extend an arc equivariantly over the regular torsor. -/
def ofArc {m : X ⟶ M} (h : QuotientFixedArcs.Arcs (parameterZero X) m) : Deformation (chart a m) where
  map := ⟨{ app U := ↾fun y => a.act U y.2.2 (h.val.hom.app U (y.1,y.2.1))
            naturality {U V} f := by
              apply ConcreteCategory.hom_ext
              intro y
              change a.act V ((locallyConstantGroup H).obj.map f y.2.2)
                (h.val.hom.app V ((D).obj.map f y.1,X.obj.map f y.2.1)) =
                  M.obj.map f (a.act U y.2.2 (h.val.hom.app U (y.1,y.2.1)))
              rw [a.natural]
              apply congrArg (a.act V _)
              have hn := NatTrans.naturality_apply h.val.hom f (show (product D X).obj.obj U from (y.1,y.2.1))
              exact hn }⟩
  zero := by
    ext U y
    exact congrArg (a.act U y.2) (congrArg (fun k => k.hom.app U y.1) h.property)
  equivariant U d x g p := a.mul_act U g p _

def chartEquiv (m : X ⟶ M) : Deformation (chart a m) ≃ QuotientFixedArcs.Arcs (parameterZero X) m where
  toFun := toArc
  invFun := ofArc
  left_inv h := by
    apply Deformation.ext
    ext U y
    have he := h.equivariant U y.1 y.2.1 y.2.2 (1 : (locallyConstantGroup H).obj.obj U)
    change h.map.hom.app U (y.1,⟨y.2.1,(show (locallyConstantGroup H).obj.obj U from y.2.2) * 1⟩) = _ at he
    simpa [toArc, ofArc, mul_one] using he.symm
  right_inv h := by
    apply Subtype.ext
    ext U y
    exact a.one_act U _

/-- This equality identifies actual forward transport, including its orientation. -/
theorem toArc_transport {m n : X ⟶ M} (c : chart a m ⟶ chart a n)
    (h : Deformation (chart a m)) :
    toArc (transport c h) = SmoothQuotientTransport.forwardArcTransport c (toArc h) := by
  apply Subtype.ext
  ext U y
  have he := h.equivariant U y.1 y.2
    ((Arrow.inverse c).torsorArrow.iso.hom.app (X.obj.elementsMk U y.2) (1 : (locallyConstantGroup H).obj.obj U)) (1 : (locallyConstantGroup H).obj.obj U)
  change h.map.hom.app U (y.1,⟨y.2,
      (show (locallyConstantGroup H).obj.obj U from (Arrow.inverse c).torsorArrow.iso.hom.app (X.obj.elementsMk U y.2) (1 : (locallyConstantGroup H).obj.obj U)) * 1⟩) = _ at he
  change h.map.hom.app U (y.1,⟨y.2,
    (Arrow.inverse c).torsorArrow.iso.hom.app (X.obj.elementsMk U y.2) (1 : (locallyConstantGroup H).obj.obj U)⟩) =
      a.act U ((Arrow.inverse c).torsorArrow.iso.hom.app (X.obj.elementsMk U y.2) (1 : (locallyConstantGroup H).obj.obj U))
        (h.map.hom.app U (y.1,⟨y.2,(1 : (locallyConstantGroup H).obj.obj U)⟩))
  simpa only [mul_one] using he

/-- The all-torsor interpretation agrees with the coherent fixed-lift fiber
through the existing boundary isomorphism, not by object equality. -/
def chartBoundaryComparison {m n : X ⟶ M} (c : chart a m ⟶ chart a n)
    (h : Deformation (chart a m)) :
    (QuotientFixedArcs.comparison a (parameterZero X) n).obj ⟨toArc (transport c h)⟩ ≅
      (QuotientFixedArcs.transport c).obj
        ((QuotientFixedArcs.comparison a (parameterZero X) m).obj ⟨toArc h⟩) := by
  rw [toArc_transport]
  exact SmoothQuotientTransport.forwardArcTransportIso c (toArc h)

/-- Classical arc composition extracted from the original source proof in
the all-torsor deformation model. -/
theorem source_arc_composition {m n k : X ⟶ M}
    (c : chart a m ⟶ chart a n) (e : chart a n ⟶ chart a k)
    (h : QuotientFixedArcs.Arcs (parameterZero X) m) :
    SmoothQuotientTransport.forwardArcTransport (c ≫ e) h =
      SmoothQuotientTransport.forwardArcTransport e (SmoothQuotientTransport.forwardArcTransport c h) := by
  have hs := congrArg toArc (source_composition c e (ofArc h))
  have eh : toArc (ofArc (a := a) h) = h := (chartEquiv (a := a) m).apply_symm_apply h
  simpa only [toArc_transport, eh] using hs

end SquareKit.SmoothQuotientDeformations
