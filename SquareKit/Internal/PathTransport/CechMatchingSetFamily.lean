import SquareKit.Internal.PathTransport.CechMatching

/-! Independently specified matching values in a set-valued relative family.
The action on matching-context arrows is the original local family action. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.SetFamily
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
variable {D : Diagram.{u,v}} (L : D.localCategory ⥤ Type u)
variable (O : D.doubleCategory ⥤ Type u)
variable (first : L ⟶ D.first ⋙ O) (second : L ⟶ D.second ⋙ O)

/-- A local value and its equation along the actual selected overlap arrow. -/
def Fiber (d : Datum D) :=
  {x : L.obj d.localObject // O.map d.overlap.hom (first.app d.localObject x) =
    second.app d.localObject x}

/-- Matching-context arrows act by the local family's supplied action. -/
def map {d e : Datum D} (f : d ⟶ e) (x : Fiber L O first second d) :
    Fiber L O first second e := ⟨L.map f.localArrow x.val, by
  have h0 := ConcreteCategory.congr_hom (first.naturality f.localArrow) x.val
  have h1 := ConcreteCategory.congr_hom (second.naturality f.localArrow) x.val
  change first.app e.localObject (L.map f.localArrow x.val) =
    O.map (D.first.map f.localArrow) (first.app d.localObject x.val) at h0
  change second.app e.localObject (L.map f.localArrow x.val) =
    O.map (D.second.map f.localArrow) (second.app d.localObject x.val) at h1
  rw [h0, ← CategoryTheory.Functor.map_comp_apply, f.commutes,
    CategoryTheory.Functor.map_comp_apply, x.property, ← h1]⟩

/-- This is a natural family, rather than unrelated pointwise matching sets. -/
def family : Datum D ⥤ Type u where
  obj := Fiber L O first second
  map f := ↾(map L O first second f)
  map_id d := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (L.map_id d.localObject) x.val
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    exact ConcreteCategory.congr_hom (L.map_comp f.localArrow g.localArrow) x.val

/-- The forgetful comparison is natural on all actual local arrows. -/
def localComparison : family L O first second ⟶ Datum.localFunctor ⋙ L where
  app _ := ↾Subtype.val
  naturality {_ _} _ := rfl

end SquareKit.Internal.PathTransport.CechMatching.SetFamily
