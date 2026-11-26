import SquareKit.ElementSiteLocalEquivalence
import SquareKit.SheafTorsor
import SquareKit.PrincipalSheaf
import SquareKit.SheafActionQuotient
import Mathlib.CategoryTheory.Sites.Limits

/-! Principal sheaves on a parameter element site express torsors over that sheaf context. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.PrincipalSheafContext
open CategoryTheory Opposite
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable (X : Sheaf J (Type u)) (G : Sheaf J GrpCat.{u})

abbrev group : Sheaf (ElementSite.topology X.obj J) GrpCat.{u} :=
  ((ElementSite.projection X.obj).sheafPushforwardContinuous GrpCat.{u}
    (ElementSite.topology X.obj J) J).obj G

/-- The original action and local lifting certificate give a principal element sheaf. -/
def structureOf (P : SheafTorsor.Torsor G X) :
    PrincipalSheaf.Structure (group X G) (SplitSheaf.elementSheaf P.family) where
  act x := P.act x.unop.unop
  one_act _ := P.one_act _
  mul_act x g h p := P.mul_act x.unop.unop g h p
  natural f := P.natural f.unop.unop
  principal _ := P.principal _
  locally_inhabited x := by
    apply J.superset_covering ?_
      (Presheaf.imageSieve_mem J (SplitSheaf.p P.family).hom x.unop.val)
    rintro V f ⟨⟨y,p⟩, hp⟩
    exact ⟨y, hp.symm, ⟨p⟩⟩

/-- A sheaf on the parameter element site determines a split family over that parameter. -/
def family (Q : Sheaf (ElementSite.topology X.obj J) (Type u)) : SplitSheaf.Ty X where
  family := ElementSheaf.family X.obj Q.obj
  isSheaf := (SheafSlice.totalSheaf X Q).property

/-- Local inhabitation translates back to local lifting of the display. -/
def torsor (Q : Sheaf (ElementSite.topology X.obj J) (Type u))
    (A : PrincipalSheaf.Structure (group X G) Q) : SheafTorsor.Torsor G X where
  family := family X Q
  act x := A.act (op (op x))
  one_act _ := A.one_act _
  mul_act x g h p := A.mul_act (op (op x)) g h p
  natural f := A.natural f.op.op
  principal _ := A.principal _
  isLocallySurjective := ⟨by
    intro V x
    apply J.superset_covering ?_ (A.locally_inhabited (ElementSite.point X.obj V x))
    rintro W f ⟨y, hy, ⟨p⟩⟩
    exact ⟨⟨y,p⟩, hy.symm⟩⟩

/-- Reconstructing a torsor retains its original split family and action exactly. -/
theorem torsor_structureOf (P : SheafTorsor.Torsor G X) :
    torsor X G (SplitSheaf.elementSheaf P.family) (structureOf X G P) = P := rfl

end SquareKit.PrincipalSheafContext

namespace SquareKit.PrincipalSheafContext
open CategoryTheory Opposite
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}

/-- A terminal sheaf with one explicitly named section at every stage. -/
def terminal (J : GrothendieckTopology C) : Sheaf J (Type u) :=
  ⟨(Functor.const Cᵒᵖ).obj PUnit, Presheaf.isSheaf_of_isTerminal J Limits.Types.isTerminalPUnit⟩

/-- A principal sheaf is a torsor over the terminal parameter sheaf. -/
def overTerminal {G : Sheaf J GrpCat.{u}} {Q : Sheaf J (Type u)}
    (A : PrincipalSheaf.Structure G Q) : SheafTorsor.Torsor G (terminal J) where
  family := SplitSheaf.constant Q (terminal J)
  act x := A.act x.obj
  one_act x := A.one_act x.obj
  mul_act x := A.mul_act x.obj
  natural f := A.natural f.hom
  principal x := A.principal x.obj
  isLocallySurjective := ⟨by
    intro U x
    apply J.superset_covering ?_ (A.locally_inhabited U)
    rintro V f ⟨p⟩
    refine ⟨⟨PUnit.unit,p⟩, ?_⟩
    change PUnit.unit = _
    exact Subsingleton.elim _ _⟩

variable (X : Sheaf J (Type u)) (G : Sheaf J GrpCat.{u})
abbrev elementTerminal := terminal (ElementSite.topology X.obj J)

/-- Realize an original-context torsor on its element site over the terminal parameter. -/
def onElements (P : SheafTorsor.Torsor G X) :
    SheafTorsor.Torsor (group X G) (elementTerminal X) := overTerminal (structureOf X G P)

abbrev terminalPoint (x : X.obj.Elements) : (elementTerminal X).obj.Elements :=
  (elementTerminal X).obj.elementsMk (op (op x)) PUnit.unit

abbrev terminalArrow {x y : X.obj.Elements} (f : x ⟶ y) :
    terminalPoint X x ⟶ terminalPoint X y := Functor.Elements.homMk f.op.op rfl

def onElementsFunctor : SheafTorsor.Torsor G X ⥤
    SheafTorsor.Torsor (group X G) (elementTerminal X) where
  obj := onElements X G
  map h :=
    { iso := Functor.isoWhiskerLeft
        (Functor.Elements.π (elementTerminal X).obj ⋙ (opOpEquivalence X.obj.Elements).functor) h.iso
      equivariant x := h.equivariant x.obj.unop.unop }

/-- All equivariant arrows between original objects are recovered by evaluation at the unique terminal section. -/
def fromElementsArrow {P Q : SheafTorsor.Torsor G X}
    (h : onElements X G P ⟶ onElements X G Q) : P ⟶ Q where
  iso := NatIso.ofComponents (fun x => h.iso.app (terminalPoint X x)) (by
    intro x y f
    exact h.iso.hom.naturality (terminalArrow X f))
  equivariant x := h.equivariant (terminalPoint X x)

instance onElementsFunctor_full : (onElementsFunctor X G).Full where
  map_surjective {P Q} h := ⟨fromElementsArrow X G h, by
    apply SheafTorsor.Arrow.ext
    ext x p
    rcases x with ⟨x,⟨⟩⟩
    rfl⟩

instance onElementsFunctor_faithful : (onElementsFunctor X G).Faithful where
  map_injective {P Q} {f g} h := by
    apply SheafTorsor.Arrow.ext
    ext x p
    exact congrArg (fun k => k.iso.hom.app (terminalPoint X x) p) h

theorem onElements_trivial : onElements X G (SheafTorsor.trivial G X) =
    SheafTorsor.trivial (group X G) (elementTerminal X) := rfl

/-- A global trivialization on the element site would trivialize the original torsor. -/
theorem onElements_nontrivial (P : SheafTorsor.Torsor G X)
    (h : ¬ Nonempty (SheafTorsor.trivial G X ⟶ P)) :
    ¬ Nonempty (SheafTorsor.trivial (group X G) (elementTerminal X) ⟶ onElements X G P) := by
  rintro ⟨e⟩
  exact h ⟨fromElementsArrow X G e⟩

end SquareKit.PrincipalSheafContext



namespace SquareKit.PrincipalSheafContext
open CategoryTheory Opposite
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable (X : Sheaf J (Type u)) {G : Sheaf J GrpCat.{u}} {M : Sheaf J (Type u)}
variable (a : SheafActionQuotient.Action G M)

/-- The target sheaf on the element site is pulled back along projection. -/
abbrev target : Sheaf (ElementSite.topology X.obj J) (Type u) :=
  ((ElementSite.projection X.obj).sheafPushforwardContinuous (Type u)
    (ElementSite.topology X.obj J) J).obj M

/-- The original action at each element-site stage. -/
def elementAction : SheafActionQuotient.Action (group X G) (target X (M := M)) where
  act x := a.act x.unop.unop.obj
  one_act x := a.one_act x.unop.unop.obj
  mul_act x := a.mul_act x.unop.unop.obj
  natural f := a.natural f.unop.unop.hom

/-- View an original quotient object over the terminal parameter of its element site. -/
def quotientOnElements (P : SheafActionQuotient.Object a X) :
    SheafActionQuotient.Object (elementAction X a) (elementTerminal X) where
  torsor := onElements X G P.torsor
  value x := P.value x.obj.unop.unop
  natural f := P.natural f.hom.unop.unop
  equivariant x := P.equivariant x.obj.unop.unop

/-- This presentation retains every compatible target-preserving arrow. -/
def quotientOnElementsFunctor : SheafActionQuotient.Object a X ⥤
    SheafActionQuotient.Object (elementAction X a) (elementTerminal X) where
  obj := quotientOnElements X a
  map h :=
    { torsorArrow := (onElementsFunctor X G).map h.torsorArrow
      preserves x := h.preserves x.obj.unop.unop }

/-- Evaluate at the unique terminal section to recover the original arrow. -/
def quotientFromElementsArrow {P Q : SheafActionQuotient.Object a X}
    (h : quotientOnElements X a P ⟶ quotientOnElements X a Q) : P ⟶ Q where
  torsorArrow := fromElementsArrow X G h.torsorArrow
  preserves x := h.preserves (terminalPoint X x)

instance quotientOnElementsFunctor_full : (quotientOnElementsFunctor X a).Full where
  map_surjective {P Q} h := ⟨quotientFromElementsArrow X a h, by
    apply SheafActionQuotient.Arrow.ext
    apply SheafTorsor.Arrow.ext
    ext x p
    rcases x with ⟨x,⟨⟩⟩
    rfl⟩

instance quotientOnElementsFunctor_faithful : (quotientOnElementsFunctor X a).Faithful where
  map_injective h := by
    apply SheafActionQuotient.Arrow.ext
    apply (onElementsFunctor X G).map_injective
    exact congrArg SheafActionQuotient.Arrow.torsorArrow h

end SquareKit.PrincipalSheafContext
