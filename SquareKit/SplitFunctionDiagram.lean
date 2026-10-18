import SquareKit.SplitPresheaf
import Mathlib.CategoryTheory.EqToHom

/-! Experimental restriction diagrams for split dependent functions. A diagram
retains the input family and dependent output over every outgoing restriction. -/
namespace SquareKit.SplitFunctionDiagram
open CategoryTheory ElementFamilies
universe u v w u' v'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
variable {F G : C ⥤ Type w}

@[simp] theorem elements_eqToHom {x y : F.Elements} (h : x = y) :
    (eqToHom h).hom = eqToHom (congrArg Functor.Elements.obj h) := by cases h; rfl

/-- The full restriction diagram of a section, including nonidentity arrows. -/
def restrictions (F : C ⥤ Type w) (x : F.Elements) : Under x.obj ⥤ F.Elements where
  obj f := F.elementsMk f.right (F.map f.hom x.val)
  map {f g} k := Functor.Elements.homMk k.right (by
    dsimp
    rw [← ConcreteCategory.comp_apply, ← F.map_comp, Under.w k])
  map_id f := by apply Functor.Elements.hom_ext; rfl
  map_comp f g := by apply Functor.Elements.hom_ext; rfl

/-- Substitution changes the presentation of the diagram by equality. -/
theorem restrictions_sub (σ : G ⟶ F) (x : G.Elements) :
    restrictions G x ⋙ σ.mapElements = restrictions F (σ.mapElements.obj x) := by
  refine CategoryTheory.Functor.ext (fun f => ?_) ?_
  ·
    change F.elementsMk f.right (σ.app f.right (G.map f.hom x.val)) =
      F.elementsMk f.right (F.map f.hom (σ.app x.obj x.val))
    congr 1
    exact NatTrans.naturality_apply σ f.hom x.val
  · intro f g k
    apply Functor.Elements.hom_ext
    simp only [Functor.comp_map, restrictions, Functor.Elements.comp_hom]
    erw [elements_eqToHom, elements_eqToHom]
    simp

/-- Lift a diagram of base sections to a diagram of their dependent values. -/
def totalDiagram (A : SplitPresheaf.Ty F) (K : D ⥤ F.Elements) :
    (K ⋙ A).Elements ⥤ (SplitPresheaf.Ext A).Elements where
  obj x := (SplitPresheaf.Ext A).elementsMk (K.obj x.obj).obj ⟨(K.obj x.obj).val, x.val⟩
  map {x y} f := Functor.Elements.homMk (K.map f.hom).hom (by
    apply total_ext F (K.map f.hom).map_val
    change A.map _ (A.map _ x.val) = y.val
    erw [← ConcreteCategory.comp_apply, ← A.map_comp]
    have h : along F (K.map f.hom).hom (K.obj x.obj).val ≫
        vertical F (K.map f.hom).map_val = K.map f.hom := by
      apply Functor.Elements.hom_ext
      simp [vertical]
    exact (congrArg (fun k => A.map k x.val) h).trans f.map_val)
  map_id x := by apply Functor.Elements.hom_ext; simp
  map_comp f g := by apply Functor.Elements.hom_ext; simp

/-- The dependent pair of restriction diagrams is independent of its context. -/
abbrev Tower (D : Type u') [Category.{v'} D] :=
  (A : D ⥤ Type w) × (A.Elements ⥤ Type w)

def diagram (A : SplitPresheaf.Ty F) (B : SplitPresheaf.Ty (SplitPresheaf.Ext A))
    (K : D ⥤ F.Elements) : Tower D := ⟨K ⋙ A, totalDiagram A K ⋙ B⟩

/-- Pulling both levels of a dependent diagram commutes with its formation. -/
theorem diagram_sub (A : SplitPresheaf.Ty F) (B : SplitPresheaf.Ty (SplitPresheaf.Ext A))
    (σ : G ⟶ F) (K : D ⥤ G.Elements) :
    diagram (SplitPresheaf.tySub A σ) (SplitPresheaf.tySub B (SplitPresheaf.lift A σ)) K =
      diagram A B (K ⋙ σ.mapElements) := rfl

/-- The actual compatible dependent sections of a context-independent tower. -/
abbrev Sections (T : Tower.{w} D) := SplitPresheaf.Tm T.2

/-- A Kripke function retains a dependent value at every restriction and input. -/
abbrev Value (A : SplitPresheaf.Ty F) (B : SplitPresheaf.Ty (SplitPresheaf.Ext A))
    (x : F.Elements) := Sections (diagram A B (restrictions F x))

theorem value_sub (A : SplitPresheaf.Ty F) (B : SplitPresheaf.Ty (SplitPresheaf.Ext A))
    (σ : G ⟶ F) (x : G.Elements) :
    Value (SplitPresheaf.tySub A σ) (SplitPresheaf.tySub B (SplitPresheaf.lift A σ)) x =
      Value A B (σ.mapElements.obj x) := by
  unfold Value
  rw [diagram_sub, restrictions_sub]


section Reindex
variable {E : Type*} [Category E]

/-- Change the base of a category of elements without changing its values. -/
def precompElements (L : E ⥤ D) (A : D ⥤ Type w) : (L ⋙ A).Elements ⥤ A.Elements where
  obj x := A.elementsMk (L.obj x.obj) x.val
  map f := Functor.Elements.homMk (L.map f.hom) f.map_val
  map_id x := by apply Functor.Elements.hom_ext; simp
  map_comp f g := by apply Functor.Elements.hom_ext; simp

def pullTower (L : E ⥤ D) (T : Tower.{w} D) : Tower E :=
  ⟨L ⋙ T.1, precompElements L T.1 ⋙ T.2⟩

def pullSections (L : E ⥤ D) (T : Tower.{w} D) (t : Sections T) : Sections (pullTower L T) where
  val x := t.val ((precompElements L T.1).obj x)
  natural f := t.natural ((precompElements L T.1).map f)

theorem diagram_precomp (A : SplitPresheaf.Ty F) (B : SplitPresheaf.Ty (SplitPresheaf.Ext A))
    (K : D ⥤ F.Elements) (L : E ⥤ D) :
    pullTower L (diagram A B K) = diagram A B (L ⋙ K) := rfl

end Reindex

/-- A restriction followed by another restriction is their composite diagram. -/
theorem restrictions_map {x y : F.Elements} (f : x ⟶ y) :
    Under.map f.hom ⋙ restrictions F x = restrictions F y := by
  refine CategoryTheory.Functor.ext (fun k => ?_) ?_
  · change F.elementsMk k.right (F.map (f.hom ≫ k.hom) x.val) =
      F.elementsMk k.right (F.map k.hom y.val)
    congr 1
    rw [F.map_comp, ConcreteCategory.comp_apply, f.map_val]
  · intro k l g
    apply Functor.Elements.hom_ext
    simp only [Functor.comp_map, restrictions, Functor.Elements.comp_hom]
    erw [elements_eqToHom, elements_eqToHom]
    simp

/-- Restrict a dependent function by retaining its values at all further arrows. -/
def restrict (A : SplitPresheaf.Ty F) (B : SplitPresheaf.Ty (SplitPresheaf.Ext A))
    {x y : F.Elements} (f : x ⟶ y) (t : Value A B x) : Value A B y :=
  cast (congrArg (fun K => Sections (diagram A B K)) (restrictions_map f))
    (pullSections (Under.map f.hom) (diagram A B (restrictions F x)) t)


theorem pullSections_heq {E : Type*} [Category E] (L : E ⥤ D)
    {T S : Tower.{w} D} (h : T = S) {t : Sections T} {s : Sections S} (ht : HEq t s) :
    HEq (pullSections L T t) (pullSections L S s) := by
  cases h
  cases ht
  rfl

theorem pullSections_functor_heq {E : Type*} [Category E] {L M : E ⥤ D}
    (h : L = M) (T : Tower.{w} D) (t : Sections T) :
    HEq (pullSections L T t) (pullSections M T t) := by cases h; rfl

theorem restrict_heq (A : SplitPresheaf.Ty F) (B : SplitPresheaf.Ty (SplitPresheaf.Ext A))
    {x y : F.Elements} (f : x ⟶ y) (t : Value A B x) :
    HEq (restrict A B f t)
      (pullSections (Under.map f.hom) (diagram A B (restrictions F x)) t) := cast_heq _ _

theorem restrict_id (A : SplitPresheaf.Ty F) (B : SplitPresheaf.Ty (SplitPresheaf.Ext A))
    (x : F.Elements) (t : Value A B x) : restrict A B (𝟙 x) t = t := by
  apply eq_of_heq
  exact (restrict_heq A B (𝟙 x) t).trans
    (pullSections_functor_heq (Under.mapId_eq x.obj) _ t)

theorem restrict_comp (A : SplitPresheaf.Ty F) (B : SplitPresheaf.Ty (SplitPresheaf.Ext A))
    {x y z : F.Elements} (f : x ⟶ y) (g : y ⟶ z) (t : Value A B x) :
    restrict A B g (restrict A B f t) = restrict A B (f ≫ g) t := by
  apply eq_of_heq
  refine (restrict_heq A B g (restrict A B f t)).trans ?_
  have ht : diagram A B (restrictions F y) =
      pullTower (Under.map f.hom) (diagram A B (restrictions F x)) :=
    (congrArg (diagram A B) (restrictions_map f)).symm
  refine (pullSections_heq (Under.map g.hom) ht (restrict_heq A B f t)).trans ?_
  exact (pullSections_functor_heq (Under.mapComp_eq f.hom g.hom).symm _ t).trans
    (restrict_heq A B (f ≫ g) t).symm

/-- Dependent natural functions form a family on the original context. -/
def pi (A : SplitPresheaf.Ty F) (B : SplitPresheaf.Ty (SplitPresheaf.Ext A)) :
    F.Elements ⥤ Type (max u v w) where
  obj := Value A B
  map f := ↾restrict A B f
  map_id x := by apply ConcreteCategory.hom_ext; intro t; exact restrict_id A B x t
  map_comp f g := by apply ConcreteCategory.hom_ext; intro t; exact (restrict_comp A B f g t).symm


theorem type_hom_hext {X Y X' Y' : Type w} (hx : X = X') (hy : Y = Y')
    (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : ∀ x x', HEq x x' → HEq (f x) (g x')) : HEq f g := by
  cases hx
  cases hy
  apply heq_of_eq
  apply ConcreteCategory.hom_ext
  intro x
  exact eq_of_heq (h x x HEq.rfl)

theorem restrict_sub (A : SplitPresheaf.Ty F) (B : SplitPresheaf.Ty (SplitPresheaf.Ext A))
    (σ : G ⟶ F) {x y : G.Elements} (f : x ⟶ y)
    (t : Value (SplitPresheaf.tySub A σ) (SplitPresheaf.tySub B (SplitPresheaf.lift A σ)) x)
    (s : Value A B (σ.mapElements.obj x)) (h : HEq t s) :
    HEq (restrict (SplitPresheaf.tySub A σ) (SplitPresheaf.tySub B (SplitPresheaf.lift A σ)) f t)
      (restrict A B (σ.mapElements.map f) s) := by
  refine (restrict_heq _ _ f t).trans ?_
  have hd : diagram (SplitPresheaf.tySub A σ) (SplitPresheaf.tySub B (SplitPresheaf.lift A σ))
      (restrictions G x) = diagram A B (restrictions F (σ.mapElements.obj x)) := by
    rw [diagram_sub, restrictions_sub]
  exact (pullSections_heq (Under.map f.hom) hd h).trans
    (restrict_heq A B (σ.mapElements.map f) s).symm

/-- Strict stability is a proved equality of functors, not an isomorphism. -/
theorem pi_sub (A : SplitPresheaf.Ty F) (B : SplitPresheaf.Ty (SplitPresheaf.Ext A))
    (σ : G ⟶ F) :
    pi (SplitPresheaf.tySub A σ) (SplitPresheaf.tySub B (SplitPresheaf.lift A σ)) =
      σ.mapElements ⋙ pi A B := by
  apply CategoryTheory.Functor.hext (value_sub A B σ)
  intro x y f
  apply type_hom_hext (value_sub A B σ x) (value_sub A B σ y)
  exact restrict_sub A B σ f


/-- Read a dependent term along a whole restriction diagram. -/
def abstractValue (A : SplitPresheaf.Ty F) {B : SplitPresheaf.Ty (SplitPresheaf.Ext A)}
    (t : SplitPresheaf.Tm B) (K : D ⥤ F.Elements) : Sections (diagram A B K) where
  val x := t.val ((totalDiagram A K).obj x)
  natural f := t.natural ((totalDiagram A K).map f)

theorem abstractValue_heq (A : SplitPresheaf.Ty F) {B : SplitPresheaf.Ty (SplitPresheaf.Ext A)}
    (t : SplitPresheaf.Tm B) {K L : D ⥤ F.Elements} (h : K = L) :
    HEq (abstractValue A t K) (abstractValue A t L) := by cases h; rfl

variable {F : C ⥤ Type (max u v)}
/-- Abstraction retains all restriction values of the body. -/
def lam (A : SplitPresheaf.Ty F) {B : SplitPresheaf.Ty (SplitPresheaf.Ext A)}
    (t : SplitPresheaf.Tm B) : SplitPresheaf.Tm (pi A B) where
  val x := abstractValue A t (restrictions F x)
  natural f := by
    apply eq_of_heq
    exact (restrict_heq A B f _).trans (abstractValue_heq A t (restrictions_map f))

end SquareKit.SplitFunctionDiagram
