import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Whiskering

/-! Coherent local families and their evaluation decoder.
An arrow `x ⟶ y` records a local view rooted at `x`, evaluated at `y`.
Restriction squares have invertible target maps; their images must be invertible.
All other squares and natural transformations retain arbitrary morphisms. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.CoherentFamilyClassification
open CategoryTheory CategoryTheory.Functor
universe u v a b u' v' u'' v''
variable (E : Type u) [Category.{v} E] (V : Type a) [Category.{b} V]

/-- Local diagrams whose restriction comparisons are invertible. -/
def Coherent : ObjectProperty (Arrow E ⥤ V) :=
  fun A => ∀ {x y : Arrow E} (f : x ⟶ y), IsIso f.right → IsIso (A.map f)

abbrev Code := (Coherent E V).FullSubcategory

/-- Evaluate a local diagram at the identity arrow of each object. -/
@[simps] def identityArrow : E ⥤ Arrow E where
  obj x := Arrow.mk (𝟙 x)
  map f := Arrow.homMk f f (by simp)

/-- Every local evaluation compares to the identity view at its target. -/
def evaluationArrow (f : Arrow E) : f ⟶ (identityArrow E).obj f.right :=
  Arrow.homMk f.hom (𝟙 _) (by change f.hom ≫ 𝟙 _ = f.hom ≫ 𝟙 _; rfl)

@[simp] theorem evaluationArrow_right (f : Arrow E) :
    (evaluationArrow E f).right = 𝟙 f.right := rfl

/-- Code a family by its values on targets, retaining all its morphisms. -/
def code : (E ⥤ V) ⥤ Code E V where
  obj A := ⟨Arrow.rightFunc ⋙ A, fun {_ _} f h => by
    have := h
    exact A.map_isIso f.right⟩
  map α := ObjectProperty.homMk (whiskerLeft Arrow.rightFunc α)

/-- The decoder is evaluation, with no supplied recovery theorem. -/
def decode : Code E V ⥤ (E ⥤ V) :=
  (Coherent E V).ι ⋙ (whiskeringLeft E (Arrow E) V).obj (identityArrow E)

@[simp] theorem decode_code : code E V ⋙ decode E V = 𝟭 (E ⥤ V) := rfl

/-- Recovery of arbitrary coherent code diagrams, derived from restriction squares. -/
noncomputable def recovery (A : Code E V) : A.obj ≅
    (code E V).obj ((decode E V).obj A) |>.obj :=
  NatIso.ofComponents (fun f => by
    letI : IsIso (A.obj.map (evaluationArrow E f)) := A.property (evaluationArrow E f) (by change IsIso (𝟙 f.right); infer_instance)
    exact @asIso _ _ _ _ (A.obj.map (evaluationArrow E f)) this) (by
      intro f g s
      change A.obj.map s ≫ A.obj.map (evaluationArrow E g) =
        A.obj.map (evaluationArrow E f) ≫ A.obj.map ((identityArrow E).map s.right)
      rw [← A.obj.map_comp, ← A.obj.map_comp]
      congr 1
      apply Arrow.hom_ext
      · change s.left ≫ g.hom = f.hom ≫ s.right
        exact s.w
      · change s.right ≫ 𝟙 _ = 𝟙 _ ≫ s.right
        simp)

/-- The comparison is natural in code morphisms, not merely an objectwise recovery. -/
noncomputable def recoveryIso : 𝟭 (Code E V) ≅ decode E V ⋙ code E V :=
  NatIso.ofComponents (fun A => (Coherent E V).isoMk (recovery E V A)) (by
    intro A B α
    apply ObjectProperty.hom_ext
    ext f
    exact (α.hom.naturality (evaluationArrow E f)).symm)

/-- Coherent local diagrams classify category-valued families, including arrows. -/
noncomputable def equivalence : Code E V ≌ (E ⥤ V) where
  functor := decode E V
  inverse := code E V
  unitIso := recoveryIso E V
  counitIso := Iso.refl _
  functor_unitIso_comp A := by
    ext x
    change A.obj.map (evaluationArrow E ((identityArrow E).obj x)) ≫ 𝟙 _ = 𝟙 _
    have h : evaluationArrow E ((identityArrow E).obj x) = 𝟙 _ := by
      apply Arrow.hom_ext <;> rfl
    rw [h]
    change A.obj.map (𝟙 ((identityArrow E).obj x)) ≫ 𝟙 _ = 𝟙 _
    rw [A.obj.map_id, Category.id_comp]

variable {E V}
variable {D : Type u'} [Category.{v'} D] {B : Type u''} [Category.{v''} B]

/-- Restriction retains coherent comparisons because functors preserve isomorphisms. -/
def reindex (F : D ⥤ E) : Code E V ⥤ Code D V where
  obj A := ⟨F.mapArrow ⋙ A.obj, fun {_ _} f h => by
    apply A.property
    change IsIso (F.map f.right)
    have := h
    infer_instance⟩
  map α := ObjectProperty.homMk (whiskerLeft F.mapArrow α.hom)

@[simp] theorem reindex_id : reindex (V := V) (𝟭 E) = 𝟭 (Code E V) := rfl
@[simp] theorem reindex_comp (F : D ⥤ E) (G : B ⥤ D) :
    reindex (V := V) (G ⋙ F) = reindex F ⋙ reindex G := rfl

/-- Coding commutes with restriction on objects and natural transformations. -/
theorem code_reindex (F : D ⥤ E) :
    code E V ⋙ reindex F = (whiskeringLeft D E V).obj F ⋙ code D V := rfl

/-- Identity views commute with a change of base up to the functor's identity law. -/
def identityComparison (F : D ⥤ E) :
    identityArrow D ⋙ F.mapArrow ≅ F ⋙ identityArrow E :=
  NatIso.ofComponents (fun x => Arrow.isoMk (Iso.refl _) (Iso.refl _) (by
    change 𝟙 (F.obj x) ≫ 𝟙 _ = F.map (𝟙 x) ≫ 𝟙 _
    simp)) (by
      intro x y f
      apply Arrow.hom_ext <;>
        change F.map f ≫ 𝟙 _ = 𝟙 _ ≫ F.map f <;> simp)

/-- The decoder is pseudonatural in arbitrary changes of base. -/
def decodeReindex (F : D ⥤ E) :
    reindex F ⋙ decode D V ≅ decode E V ⋙ (whiskeringLeft D E V).obj F :=
  NatIso.ofComponents (fun A => isoWhiskerRight (identityComparison F) A.obj) (by
    intro A B α
    ext x
    exact (α.hom.naturality ((identityComparison F).hom.app x)).symm)

@[simp] theorem identityComparison_id (x : E) :
    (identityComparison (𝟭 E)).hom.app x = 𝟙 _ := by
  apply Arrow.hom_ext <;> rfl

/-- The substitution comparison satisfies its unit law on the whole decoded family. -/
@[simp] theorem decodeReindex_id (A : Code E V) :
    (decodeReindex (𝟭 E)).hom.app A = 𝟙 _ := by
  ext x
  change A.obj.map ((identityComparison (𝟭 E)).hom.app x) = 𝟙 _
  rw [identityComparison_id]
  exact A.obj.map_id _

/-- Composition coherence of the identity-view comparisons. -/
theorem identityComparison_comp (F : D ⥤ E) (G : B ⥤ D) (x : B) :
    (identityComparison (G ⋙ F)).hom.app x =
      F.mapArrow.map ((identityComparison G).hom.app x) ≫
        (identityComparison F).hom.app (G.obj x) := by
  apply Arrow.hom_ext <;> change 𝟙 _ = F.map (𝟙 _) ≫ 𝟙 _ <;> simp

/-- Composition coherence of the decoder, retaining every component morphism. -/
theorem decodeReindex_comp (F : D ⥤ E) (G : B ⥤ D) (A : Code E V) (x : B) :
    ((decodeReindex (G ⋙ F)).hom.app A).app x =
      ((decodeReindex G).hom.app ((reindex F).obj A)).app x ≫
        ((decodeReindex F).hom.app A).app (G.obj x) := by
  change A.obj.map ((identityComparison (G ⋙ F)).hom.app x) =
    A.obj.map (F.mapArrow.map ((identityComparison G).hom.app x)) ≫
      A.obj.map ((identityComparison F).hom.app (G.obj x))
  rw [identityComparison_comp, A.obj.map_comp]

/-- Recovery itself respects substitution through the decoder comparison. -/
theorem recovery_reindex (F : D ⥤ E) (A : Code E V) (f : Arrow D) :
    (recovery D V ((reindex F).obj A)).hom.app f ≫
      ((decodeReindex F).hom.app A).app f.right =
        (recovery E V A).hom.app (F.mapArrow.obj f) := by
  change A.obj.map (F.mapArrow.map (evaluationArrow D f)) ≫
    A.obj.map ((identityComparison F).hom.app f.right) =
      A.obj.map (evaluationArrow E (F.mapArrow.obj f))
  rw [← A.obj.map_comp]
  congr 1
  apply Arrow.hom_ext
  · change F.map f.hom ≫ 𝟙 _ = F.map f.hom
    simp
  · change F.map (𝟙 _) ≫ 𝟙 _ = 𝟙 _
    simp

end SquareKit.CoherentFamilyClassification
