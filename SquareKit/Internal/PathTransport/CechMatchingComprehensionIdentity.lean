import SquareKit.Internal.PathTransport.CechMatchingComprehensionFiber
import SquareKit.Internal.PathTransport.CechMatchingIdentity

/-! Dependent identity matching uses vertical local arrows, with their overlap
square retained independently of a global extension. -/
noncomputable section
namespace SquareKit.Internal.PathTransport.CechMatching.Comprehension.Identity
open CategoryTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u w z
variable {D : StrictDiagram.{u,u}} {A : FamilyData D} {h : A.Coherence}
variable {d : Datum D.toDiagram}

/-- Both conditions are explicit: the matching square and identity base action. -/
def Paths (x y : Fiber A h d) :=
  {p : CechMatching.Identity.Fiber x.datum y.datum // p.val.base = 𝟙 d.localObject}

def arrowEquiv (x y : Fiber A h d) : Paths x y ≃ (x ⟶ y) where
  toFun p := ⟨CechMatching.Identity.arrowEquiv _ _ p.val, p.property⟩
  invFun p := ⟨(CechMatching.Identity.arrowEquiv _ _).symm p.matchingArrow, p.vertical⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {B : Type w} [Category.{z} B] (X Y : B ⥤ Fiber A h d)

def family : B ⥤ Type u where
  obj b := Paths (X.obj b) (Y.obj b)
  map f := ↾fun p => (arrowEquiv _ _).symm
    (inv (X.map f) ≫ arrowEquiv _ _ p ≫ Y.map f)
  map_id b := by
    ext p
    simp
  map_comp f g := by
    ext p
    simp [Category.assoc]

def comparison : family X Y ≅ GroupoidIdentity.family X Y :=
  NatIso.ofComponents (fun b => (arrowEquiv (X.obj b) (Y.obj b)).toIso) (by
    intro b c f
    rfl)

/-- This is endpoint conjugation by actual vertical local arrows. -/
theorem map_localArrow {b c : B} (f : b ⟶ c) (p : Paths (X.obj b) (Y.obj b)) :
    ((family X Y).map f p).val.val =
      inv (X.map f).matchingArrow.localArrow ≫ p.val.val ≫
        (Y.map f).matchingArrow.localArrow := by
  let F := Fiber.forget (A := A) (h := h) (d := d) ⋙ Datum.localFunctor
  change F.map (inv (X.map f) ≫ arrowEquiv _ _ p ≫ Y.map f) = _
  rw [Functor.map_comp, Functor.map_comp, Functor.map_inv]
  rfl

/-- Pulling back parameters retains the same selected vertical paths. -/
theorem family_reindex {B' : Type w} [Category.{z} B'] (σ : B' ⥤ B) :
    family (σ ⋙ X) (σ ⋙ Y) = σ ⋙ family X Y := rfl

variable {C : Type u} [Groupoid.{u} C]

def restriction (R : C ⥤ Fiber A h d) (X Y : B ⥤ C) :
    GroupoidIdentity.family X Y ⟶ family (X ⋙ R) (Y ⋙ R) where
  app b := ↾fun p => (arrowEquiv _ _).symm (R.map p)
  naturality {b c} f := by
    apply ConcreteCategory.hom_ext
    intro p
    apply (arrowEquiv _ _).injective
    change R.map (inv (X.map f) ≫ p ≫ Y.map f) =
      inv (R.map (X.map f)) ≫ R.map p ≫ R.map (Y.map f)
    simp only [Functor.map_comp, Functor.map_inv]

/-- Fully faithful relative restriction recovers every independently supplied
vertical path, naturally in its endpoints. -/
def restrictionIso (R : C ⥤ Fiber A h d) [R.Full] [R.Faithful] (X Y : B ⥤ C) :
    GroupoidIdentity.family X Y ≅ family (X ⋙ R) (Y ⋙ R) :=
  NatIso.ofComponents (fun b => (((Functor.FullyFaithful.ofFullyFaithful R).homEquiv
    (X := X.obj b) (Y := Y.obj b)).trans (arrowEquiv _ _).symm).toIso)
    (fun f => (restriction R X Y).naturality f)

@[simp] theorem restrictionIso_hom (R : C ⥤ Fiber A h d) [R.Full] [R.Faithful]
    (X Y : B ⥤ C) : (restrictionIso R X Y).hom = restriction R X Y := rfl

end SquareKit.Internal.PathTransport.CechMatching.Comprehension.Identity
