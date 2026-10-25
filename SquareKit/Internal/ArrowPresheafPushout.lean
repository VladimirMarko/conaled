import SquareKit.Internal.ArrowPresheaf
import SquareKit.Internal.ArrowPushout
import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory

/-! The pointwise switch is the pushout interpretation for a subterminal
presheaf. Local inhabitedness is an external predicate, not a claim that the
subterminal is complemented in a sheaf category. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SquareKit.Internal.ArrowPresheafPushout
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
universe v u w
variable {D : Type u} [Category.{v} D] (P : D ⥤ Type w)

def inhabited (X : D) : Prop := Nonempty (P.obj X)

theorem inhabited_map {X Y : D} (f : X ⟶ Y) : inhabited P X → inhabited P Y :=
  fun ⟨x⟩ => ⟨P.map f x⟩

/-- Pointwise interpretation by local inhabitedness of `P`. -/
def interpretation : Arrow (D ⥤ Type w) ⥤ (D ⥤ Type w) :=
  ArrowPresheaf.interpretation (inhabited P) (inhabited_map P)

variable (a : Arrow (D ⥤ Type w))

/-- The domain leg includes the unchanged part, applying the arrow on `P`. -/
def inl : a.left ⟶ (interpretation P).obj a where
  app X := by
    classical
    exact TypeCat.ofHom fun x => if h : inhabited P X then .inl ⟨a.hom.app X x, h⟩
      else .inr ⟨x, h⟩
  naturality {X Y} f := by
    classical
    ext x
    dsimp [interpretation, ArrowPresheaf.interpretation, ArrowPresheaf.object,
      ArrowPresheaf.restrict]
    by_cases hx : inhabited P X
    · have hy := inhabited_map P f hx
      simp only [dite_eq_left hx, dite_eq_left hy]
      congr 2
      exact types_congr_hom (a.hom.naturality f) x
    · by_cases hy : inhabited P Y <;> simp [hx, hy]

/-- On `P`, include the codomain element. -/
def inr : P ⊗ a.right ⟶ (interpretation P).obj a where
  app X := TypeCat.ofHom fun x => .inl ⟨x.2, ⟨x.1⟩⟩
  naturality {X Y} f := by ext x; rfl

theorem condition : snd P a.left ≫ inl P a = (P ◁ a.hom) ≫ inr P a := by
  classical
  ext X x
  dsimp [inl, inr]
  simp only [dite_eq_left (show inhabited P X from ⟨x.1⟩)]
  rfl

/-- The actual pushout cocone. -/
def cocone : PushoutCocone (snd P a.left) (P ◁ a.hom) :=
  PushoutCocone.mk (inl P a) (inr P a) (condition P a)

variable [∀ X, Subsingleton (P.obj X)]

/-- Descend a compatible pair by its selected branch. -/
def desc (s : PushoutCocone (snd P a.left) (P ◁ a.hom)) :
    (interpretation P).obj a ⟶ s.pt where
  app X := TypeCat.ofHom fun x => match x with
    | .inl x => s.inr.app X (Classical.choice x.property, x.val)
    | .inr x => s.inl.app X x.val
  naturality {X Y} f := by
    classical
    ext x
    cases x with
    | inl x =>
      change s.inr.app Y (_, a.right.map f x.val) = s.pt.map f (s.inr.app X (_, x.val))
      have h := types_congr_hom (s.inr.naturality f) (Classical.choice x.property, x.val)
      have eq : Classical.choice (inhabited_map P f x.property) = P.map f (Classical.choice x.property) :=
        Subsingleton.elim _ _
      rw [eq]
      exact h
    | inr x =>
      dsimp [interpretation, ArrowPresheaf.interpretation, ArrowPresheaf.object,
        ArrowPresheaf.restrict]
      by_cases hy : inhabited P Y
      · simp only [dite_eq_left hy]
        have c := types_congr_hom (congrArg (fun α => α.app Y) s.condition)
          (Classical.choice hy, a.left.map f x.val)
        have n := types_congr_hom (s.inl.naturality f) x.val
        exact c.symm.trans n
      · simp only [dite_eq_right hy]
        exact types_congr_hom (s.inl.naturality f) x.val

/-- The selected presheaf is a pushout, not merely an objectwise description. -/
def isColimit : IsColimit (cocone P a) :=
  PushoutCocone.IsColimit.mk (condition P a) (desc P a)
    (fun s => by
      classical
      ext X x
      dsimp [inl, desc]
      by_cases hx : inhabited P X
      · simp only [dite_eq_left hx]
        exact (types_congr_hom (congrArg (fun α => α.app X) s.condition)
          (Classical.choice hx, x)).symm
      · simp [hx])
    (fun s => by
      ext X x
      change s.inr.app X (_, x.2) = s.inr.app X x
      congr 1
      exact Prod.ext (Subsingleton.elim _ _) rfl)
    (fun s m hl hr => by
      ext X x
      cases x with
      | inl x =>
        exact types_congr_hom (congrArg (fun α => α.app X) hr) (Classical.choice x.property, x.val)
      | inr x =>
        have h := types_congr_hom (congrArg (fun α => α.app X) hl) x.val
        simpa [inl, desc, x.property] using h)

/-- The canonical comparison with the categorical pushout. -/
def comparison : (ArrowPushout.interpretation P).obj a ≅ (interpretation P).obj a :=
  (pushoutIsPushout (snd P a.left) (P ◁ a.hom)).coconePointUniqueUpToIso (isColimit P a)

@[reassoc (attr := simp)] theorem comparison_inl :
    pushout.inl (snd P a.left) (P ◁ a.hom) ≫ (comparison P a).hom = inl P a :=
  (pushoutIsPushout (snd P a.left) (P ◁ a.hom)).comp_coconePointUniqueUpToIso_hom
    (isColimit P a) WalkingSpan.left

@[reassoc (attr := simp)] theorem comparison_inr :
    pushout.inr (snd P a.left) (P ◁ a.hom) ≫ (comparison P a).hom = inr P a :=
  (pushoutIsPushout (snd P a.left) (P ◁ a.hom)).comp_coconePointUniqueUpToIso_hom
    (isColimit P a) WalkingSpan.right

variable {a}

omit [∀ X, Subsingleton (P.obj X)] in
@[reassoc] theorem inl_natural {b : Arrow (D ⥤ Type w)} (f : a ⟶ b) :
    f.left ≫ inl P b = inl P a ≫ (interpretation P).map f := by
  classical
  ext X x
  dsimp [inl, interpretation, ArrowPresheaf.interpretation, ArrowPresheaf.map]
  by_cases h : inhabited P X
  · simp only [dite_eq_left h]
    congr 2
    exact types_congr_hom (congrArg (fun α => α.app X) (Arrow.w f)) x
  · simp [h]

omit [∀ X, Subsingleton (P.obj X)] in
@[reassoc] theorem inr_natural {b : Arrow (D ⥤ Type w)} (f : a ⟶ b) :
    (P ◁ f.right) ≫ inr P b = inr P a ≫ (interpretation P).map f := by
  ext X x
  rfl

/-- The comparison is natural on all commutative squares. -/
def comparisonIso : ArrowPushout.interpretation P ≅ interpretation P :=
  NatIso.ofComponents (fun a => comparison P a) (by
    intro a b f
    apply pushout.hom_ext
    · simp only [ArrowPushout.inl_map_assoc, comparison_inl,
        comparison_inl_assoc]
      exact inl_natural P f
    · simp only [ArrowPushout.inr_map_assoc, comparison_inr,
        comparison_inr_assoc]
      exact inr_natural P f)

/-- The pushout construction is left exact for subterminal presheaves. -/
instance : PreservesFiniteLimits (ArrowPushout.interpretation P) := by
  let : PreservesFiniteLimits (interpretation P) :=
    show PreservesFiniteLimits (ArrowPresheaf.interpretation (inhabited P) (inhabited_map P)) from inferInstance
  exact preservesFiniteLimits_of_natIso (comparisonIso P).symm

end SquareKit.Internal.ArrowPresheafPushout

