import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo

/-! Strict natural transformations between strict higher functors.
The component is a 1-arrow; its action on fiber 2-cells is retained through
the naturality equation. This is structural family data, not an eliminator.
-/
namespace SquareKit.Internal.PathTransport.StrictTwoTransformation
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w' u'' v'' w''
variable {A : Type u} [Bicategory.{w,v} A] [Bicategory.Strict A]
variable {B : Type u'} [Bicategory.{w',v'} B] [Bicategory.Strict B]

/-- Naturality is strict at arrows and coherent at genuine 2-cells. -/
structure Trans (F G : StrictPseudofunctor A B) where
  app (a : A) : F.obj a ⟶ G.obj a
  naturality {a b : A} (f : a ⟶ b) : F.map f ≫ app b = app a ≫ G.map f
  naturality₂ {a b : A} {f g : a ⟶ b} (α : f ⟶ g) :
    F.map₂ α ▷ app b ≫ eqToHom (naturality g) =
      eqToHom (naturality f) ≫ app a ◁ G.map₂ α

/-- The unit and composition coherence follow from strictness, rather than
being additional requirements on the transformation. -/
def Trans.toStrong {F G : StrictPseudofunctor A B} (η : Trans F G) :
    Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor where
  app := η.app
  naturality f := eqToIso (η.naturality f)
  naturality_naturality := η.naturality₂
  naturality_id a := by
    simp [F.mapId_eq_eqToIso, G.mapId_eq_eqToIso, whiskerLeft_eqToHom,
      eqToHom_whiskerRight, Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso]
  naturality_comp f g := by
    simp [F.mapComp_eq_eqToIso, G.mapComp_eq_eqToIso, whiskerLeft_eqToHom,
      eqToHom_whiskerRight, Strict.associator_eqToIso]

omit [Bicategory.Strict A] [Bicategory.Strict B] in
/-- Strict transformations are determined by their components. -/
@[ext] theorem Trans.ext {F G : StrictPseudofunctor A B} {η θ : Trans F G}
    (h : ∀ a, η.app a = θ.app a) : η = θ := by
  cases η; cases θ
  simp_all [mk.injEq, funext_iff]

/-- Identity preserves strict naturality, including its 2-cell equation. -/
def Trans.id (F : StrictPseudofunctor A B) : Trans F F where
  app a := 𝟙 (F.obj a)
  naturality f := by simp
  naturality₂ _ := by simp [Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso]


/-- Composition pastes the strict components; its 2-cell law follows from
pasting strong transformations and strict associativity. -/
def Trans.comp {F G H : StrictPseudofunctor A B} (η : Trans F G) (θ : Trans G H) :
    Trans F H where
  app a := η.app a ≫ θ.app a
  naturality f := by rw [← Category.assoc, η.naturality, Category.assoc,
    θ.naturality, Category.assoc]
  naturality₂ α := by
    simpa [Pseudofunctor.StrongTrans.vcomp, Pseudofunctor.StrongTrans.mkOfOplax,
      Pseudofunctor.StrongTrans.toOplax, Oplax.StrongTrans.vcomp, Oplax.StrongTrans.mkOfOplax,
      Oplax.OplaxTrans.vcomp, Trans.toStrong,
      Strict.associator_eqToIso, whiskerLeft_eqToHom, eqToHom_whiskerRight] using
      (Pseudofunctor.StrongTrans.vcomp η.toStrong θ.toStrong).naturality_naturality α

/-- The ordinary category retains strict higher functors and their strict
transformations. It does not identify the target's genuine 2-cells. -/
instance transformationCategory : Category (StrictPseudofunctor A B) where
  Hom := Trans
  id := Trans.id
  comp := Trans.comp
  id_comp _ := Trans.ext (fun _ => Category.id_comp _)
  comp_id _ := Trans.ext (fun _ => Category.comp_id _)
  assoc _ _ _ := Trans.ext (fun _ => Category.assoc _ _ _)

@[simp] theorem Trans.comp_app {F G H : StrictPseudofunctor A B}
    (η : F ⟶ G) (θ : G ⟶ H) (a : A) : (η ≫ θ).app a = η.app a ≫ θ.app a := rfl

@[simp] theorem Trans.id_app (F : StrictPseudofunctor A B) (a : A) :
    (𝟙 F : F ⟶ F).app a = 𝟙 (F.obj a) := rfl

/-- Evaluating transport at a fixed fiber object produces the functor needed
by the general Grothendieck hom-category. -/
def evaluation (a : A) : StrictPseudofunctor A B ⥤ B where
  obj F := F.obj a
  map η := η.app a

/-- Moving the evaluated fiber object is natural in the transport functor. -/
def evaluationMap {a b : A} (f : a ⟶ b) : evaluation (B := B) a ⟶ evaluation b where
  app F := F.map f
  naturality _ _ η := (η.naturality f).symm

variable {C : Type u''} [Bicategory.{w'',v''} C] [Bicategory.Strict C]

/-- Precomposition retains the entire 2-cell naturality equation. -/
def Trans.whiskerLeft (F : StrictPseudofunctor A B)
    {G H : StrictPseudofunctor B C} (η : Trans G H) : Trans (F.comp G) (F.comp H) where
  app a := η.app (F.obj a)
  naturality f := η.naturality (F.map f)
  naturality₂ α := η.naturality₂ (F.map₂ α)

/-- Postcomposition maps both components and their genuine 2-cell equations. -/
def Trans.whiskerRight {F G : StrictPseudofunctor A B} (η : Trans F G)
    (H : StrictPseudofunctor B C) : Trans (F.comp H) (G.comp H) where
  app a := H.map (η.app a)
  naturality f := by
    change H.map (F.map f) ≫ H.map (η.app _) = H.map (η.app _) ≫ H.map (G.map f)
    rw [← H.map_comp, η.naturality, H.map_comp]
  naturality₂ {a b} {f g} α := by
    have h := congrArg H.map₂ (η.naturality₂ α)
    simp only [PrelaxFunctor.map₂_comp, PrelaxFunctor.map₂_eqToHom,
      Pseudofunctor.map₂_whisker_left, Pseudofunctor.map₂_whisker_right,
      H.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv] at h
    have k := congrArg (fun p =>
      eqToHom (H.map_comp (F.map f) (η.app b)).symm ≫ p ≫
        eqToHom (H.map_comp (η.app a) (G.map g))) h
    simpa using k

omit [Bicategory.Strict A] [Bicategory.Strict B] in
/-- The coherence isomorphisms of a strict functor are forced by its action. -/
theorem functor_ext {F G : StrictPseudofunctor A B}
    (h : F.toPrelaxFunctor = G.toPrelaxFunctor) : F = G := by
  rcases F with ⟨⟨⟨F, Fi, Fc, _, _, _, _, _⟩, _, Fi_eq⟩, _, Fc_eq⟩
  rcases G with ⟨⟨⟨G, Gi, Gc, _, _, _, _, _⟩, _, Gi_eq⟩, _, Gc_eq⟩
  change F = G at h
  subst G
  have hi : Fi = Gi := funext (fun a => (Fi_eq a).trans (Gi_eq a).symm)
  have hc : @Fc = @Gc := by
    funext a b c f g
    exact (Fc_eq f g).trans (Gc_eq f g).symm
  subst Gi
  subst Gc
  rfl

theorem functor_id_comp (F : StrictPseudofunctor A B) :
    (StrictPseudofunctor.id A).comp F = F := functor_ext rfl

theorem functor_comp_id (F : StrictPseudofunctor A B) :
    F.comp (StrictPseudofunctor.id B) = F := functor_ext rfl

@[simp] theorem Trans.eqToHom_app {F G : StrictPseudofunctor A B} (h : F = G) (a : A) :
    (eqToHom h : F ⟶ G).app a = eqToHom (congrArg (fun K => K.obj a) h) := by
  cases h
  rfl

end SquareKit.Internal.PathTransport.StrictTwoTransformation
