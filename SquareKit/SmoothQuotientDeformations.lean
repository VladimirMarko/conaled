import SquareKit.SmoothQuotientArcs
import SquareKit.GroupoidTransport

/-! Infinitesimal deformations on the total sheaf of an arbitrary quotient
 torsor. No global section or trivialization of the torsor is assumed. -/
noncomputable section
namespace SquareKit.SmoothQuotientDeformations
open CategoryTheory SheafActionQuotient SmoothOpenSite SheafRelation
set_option backward.isDefEq.respectTransparency false
variable {H : Type} [Group H] {M : Sheaf topology Type}
variable {a : Action (locallyConstantGroup H) M} {X Y : Sheaf topology Type}
local notation "D" => SmoothOpenSite.infinitesimal

/-- An equivariant arc over the entire torsor, with its prescribed zero value.
The underlying map is a sheaf morphism, so naturality in stages is retained. -/
structure Deformation (P : Object a X) where
  map : product D (SplitSheaf.Ext P.torsor.family) ⟶ M
  zero : parameterZero (SplitSheaf.Ext P.torsor.family) ≫ map = P.totalMap
  equivariant (U : SmoothPresentationSite.Siteᵒᵖ) (d : (D).obj.obj U) (x : X.obj.obj U)
    (g : (locallyConstantGroup H).obj.obj U)
    (p : P.torsor.family.family.obj (X.obj.elementsMk U x)) :
    map.hom.app U (d, ⟨x, P.torsor.act (X.obj.elementsMk U x) g p⟩) =
      a.act U g (map.hom.app U (d, ⟨x,p⟩))

@[ext] theorem Deformation.ext {P : Object a X} (h k : Deformation P) (e : h.map = k.map) : h = k := by
  cases h
  cases k
  cases e
  rfl

/-- Every quotient object has its constant deformation, without a section of
its torsor. This also witnesses nonemptiness in nontrivial-torsor examples. -/
def constant (P : Object a X) : Deformation P where
  map := snd D (SplitSheaf.Ext P.torsor.family) ≫ P.totalMap
  zero := rfl
  equivariant U _ x g p := P.equivariant (X.obj.elementsMk U x) g p

/-- The total-space map of a quotient arrow preserves its actual torsor data. -/
def totalArrow {P Q : Object a X} (c : P ⟶ Q) :
    SplitSheaf.Ext P.torsor.family ⟶ SplitSheaf.Ext Q.torsor.family :=
  ⟨ElementFamilies.totalNat X.obj c.torsorArrow.iso.hom⟩

def transport {P Q : Object a X} (c : P ⟶ Q) (h : Deformation P) : Deformation Q where
  map := SheafFunction.parameterMap D (totalArrow (Arrow.inverse c)) ≫ h.map
  zero := by
    ext U q
    have hz := congrArg (fun k => k.hom.app U
      (⟨q.1, (Arrow.inverse c).torsorArrow.iso.hom.app (X.obj.elementsMk U q.1) q.2⟩ :
        (SplitSheaf.Ext P.torsor.family).obj.obj U)) h.zero
    exact hz.trans ((Arrow.inverse c).preserves (X.obj.elementsMk U q.1) q.2)
  equivariant U d x g q := by
    change h.map.hom.app U (d, ⟨x, (Arrow.inverse c).torsorArrow.iso.hom.app
      (X.obj.elementsMk U x) (Q.torsor.act (X.obj.elementsMk U x) g q)⟩) = _
    rw [(Arrow.inverse c).torsorArrow.equivariant]
    exact h.equivariant U d x g _

theorem transport_id {P : Object a X} (h : Deformation P) : transport (𝟙 P) h = h := by
  apply Deformation.ext
  rfl

theorem transport_comp {P Q R : Object a X} (c : P ⟶ Q) (e : Q ⟶ R) (h : Deformation P) :
    transport (c ≫ e) h = transport e (transport c h) := by
  apply Deformation.ext
  rfl

def family (a : Action (locallyConstantGroup H) M) (X : Sheaf topology Type) : Object a X ⥤ Type where
  obj P := Deformation P
  map c := ↾(transport c)
  map_id P := by apply ConcreteCategory.hom_ext; intro h; exact transport_id h
  map_comp c e := by apply ConcreteCategory.hom_ext; intro h; exact transport_comp c e h

/-- The original first-path source derivation interpreted on all quotient
objects. Restriction and descent remain separate model obligations. -/
theorem source_composition {P Q R : Object a X} (c : P ⟶ Q) (e : Q ⟶ R) (h : Deformation P) :
    transport (c ≫ e) h = transport e (transport c h) :=
  GroupoidTransport.transport_concat (Object a X) (family a X) c e h

/-- Pull back a deformation along an arbitrary sheaf-parameter map. -/
def restrict (f : Y ⟶ X) {P : Object a X} (h : Deformation P) : Deformation (reindex P f) where
  map := SheafFunction.parameterMap D (SplitSheaf.lift P.torsor.family f) ≫ h.map
  zero := by
    ext U y
    exact congrArg (fun k => k.hom.app U
      (⟨f.hom.app U y.1,y.2⟩ : (SplitSheaf.Ext P.torsor.family).obj.obj U)) h.zero
  equivariant U d y g p := h.equivariant U d (f.hom.app U y) g p

theorem restrict_id {P : Object a X} (h : Deformation P) : restrict (𝟙 X) h = h := by
  apply Deformation.ext
  rfl

theorem restrict_comp {Z : Sheaf topology Type} (f : Y ⟶ X) (g : Z ⟶ Y)
    {P : Object a X} (h : Deformation P) : restrict g (restrict f h) = restrict (g ≫ f) h := by
  apply Deformation.ext
  rfl

theorem transport_restrict (f : Y ⟶ X) {P Q : Object a X} (c : P ⟶ Q) (h : Deformation P) :
    restrict f (transport c h) = transport (c.reindex f) (restrict f h) := by
  apply Deformation.ext
  rfl

end SquareKit.SmoothQuotientDeformations
