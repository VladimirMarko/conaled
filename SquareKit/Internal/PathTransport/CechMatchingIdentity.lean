import SquareKit.Internal.PathTransport.CechMatching
import SquareKit.Internal.PathTransport.GroupoidIdentity

/-! Identity matching retains the selected local arrow and its overlap square.
Endpoint conjugation makes the identification natural in arbitrary parameters. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Identity
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v w z
variable {D : Diagram.{u,v}}

/-- An independent local path must commute with the two supplied overlaps. -/
def Fiber (d e : Datum D) :=
  {p : d.localObject ⟶ e.localObject //
    D.first.map p ≫ e.overlap.hom = d.overlap.hom ≫ D.second.map p}

def arrowEquiv (d e : Datum D) : Fiber d e ≃ (d ⟶ e) where
  toFun p := ⟨p.val, p.property⟩
  invFun p := ⟨p.localArrow, p.commutes⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {B : Type w} [Category.{z} B] (X Y : B ⥤ Datum D)

def family : B ⥤ Type u where
  obj b := Fiber (X.obj b) (Y.obj b)
  map f := ↾fun p => (arrowEquiv _ _).symm
    (inv (X.map f) ≫ arrowEquiv _ _ p ≫ Y.map f)
  map_id b := by
    ext p
    simp
  map_comp f g := by
    ext p
    simp [Category.assoc]

/-- This is a natural identification with the actual matching-groupoid arrows. -/
def comparison : family X Y ≅ GroupoidIdentity.family X Y :=
  NatIso.ofComponents (fun b => (arrowEquiv (X.obj b) (Y.obj b)).toIso) (by
    intro b c f
    rfl)

theorem map_localArrow {b c : B} (f : b ⟶ c) (p : Fiber (X.obj b) (Y.obj b)) :
    ((family X Y).map f p).val =
      inv (X.map f).localArrow ≫ p.val ≫ (Y.map f).localArrow := by
  change (inv (X.map f) ≫ arrowEquiv _ _ p ≫ Y.map f).localArrow = _
  simp only [Datum.comp_localArrow]
  change Datum.localFunctor.map (inv (X.map f)) ≫ p.val ≫ (Y.map f).localArrow = _
  rw [Functor.map_inv]
  rfl

/-- Reindexing changes the parameter without changing selected path data. -/
theorem family_reindex {B' : Type w} [Category.{z} B'] (σ : B' ⥤ B) :
    family (σ ⋙ X) (σ ⋙ Y) = σ ⋙ family X Y := rfl


variable {C : Type v} [Groupoid.{u} C]

/-- The actual restriction map acts on the selected path, not its isomorphism class. -/
def restriction (R : C ⥤ Datum D) (X Y : B ⥤ C) :
    GroupoidIdentity.family X Y ⟶ family (X ⋙ R) (Y ⋙ R) where
  app b := ↾fun p => (arrowEquiv _ _).symm (R.map p)
  naturality {b c} f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply (arrowEquiv _ _).injective
    change R.map (inv (X.map f) ≫ p ≫ Y.map f) =
      inv (R.map (X.map f)) ≫ R.map p ≫ R.map (Y.map f)
    simp only [Functor.map_comp, Functor.map_inv]

/-- Full faithfulness suffices to recover all matching identity paths naturally. -/
def restrictionIso (R : C ⥤ Datum D) [R.Full] [R.Faithful] (X Y : B ⥤ C) :
    GroupoidIdentity.family X Y ≅ family (X ⋙ R) (Y ⋙ R) :=
  NatIso.ofComponents (fun b => (((Functor.FullyFaithful.ofFullyFaithful R).homEquiv
    (X := X.obj b) (Y := Y.obj b)).trans (arrowEquiv _ _).symm).toIso)
    (fun f => (restriction R X Y).naturality f)

@[simp] theorem restrictionIso_hom (R : C ⥤ Datum D) [R.Full] [R.Faithful]
    (X Y : B ⥤ C) : (restrictionIso R X Y).hom = restriction R X Y := rfl


end SquareKit.Internal.PathTransport.CechMatching.Identity
