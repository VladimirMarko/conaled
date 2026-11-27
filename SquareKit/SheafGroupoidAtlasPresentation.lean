import SquareKit.SheafGroupoidAtlas

/-! Actual atlas groupoids compared with their full coordinate presentations. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Chart
open CategoryTheory Opposite
open scoped CategoryTheory.Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Operations J} [G.Laws] {U : Sheaf J (Type (max u v))}
variable {p : U ⟶ G.objects} (D : Chart G p p)
variable {X Y : Sheaf J (Type (max u v))}

/-- The atlas groupoid retains exactly the existing objects and full coordinate arrows. -/
def atlasToChart : D.atlasOperations.Object X ⥤ D.Object X where
  obj m := ⟨m.map⟩
  map f := D.atlasArrowEquiv _ _ f
  map_id := D.atlasArrowEquiv_ident
  map_comp := D.atlasArrowEquiv_comp

def chartToAtlas : D.Object X ⥤ D.atlasOperations.Object X where
  obj m := ⟨m.map⟩
  map f := (D.atlasArrowEquiv _ _).symm f
  map_id m := by
    apply Operations.Arrow.ext
    exact congrArg Subtype.val (D.atlasArrowEquiv_ident ⟨m.map⟩).symm
  map_comp {m n q} f g := by
    apply Operations.Arrow.ext
    exact congrArg Subtype.val (D.atlasArrowEquiv_comp
      ((D.atlasArrowEquiv ⟨m.map⟩ ⟨n.map⟩).symm f)
      ((D.atlasArrowEquiv ⟨n.map⟩ ⟨q.map⟩).symm g)).symm

def atlasPresentationEquivalence : D.atlasOperations.Object X ≌ D.Object X where
  functor := D.atlasToChart
  inverse := D.chartToAtlas
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simp] theorem atlasToChart_restriction (r : Y ⟶ X) :
    D.atlasOperations.restriction r ⋙ D.atlasToChart = D.atlasToChart ⋙ D.restriction r := rfl

@[simp] theorem chartToAtlas_restriction (r : Y ⟶ X) :
    D.restriction r ⋙ D.chartToAtlas = D.chartToAtlas ⋙ D.atlasOperations.restriction r := rfl

def atlasPresentation : D.atlasOperations.pseudofunctor ⟶ D.pseudofunctor where
  app X := (D.atlasToChart (X := X.as.unop)).toCatHom
  naturality _ := Iso.refl _
  naturality_naturality := by
    intro X Y f g h
    obtain rfl := LocallyDiscrete.eq_of_hom h
    have hh : h = 𝟙 f := Subsingleton.elim _ _
    subst h
    simp only [PrelaxFunctor.map₂_id]
    apply Cat.Hom₂.ext
    ext m
    simp
  naturality_id X := by
    cases X
    apply Cat.Hom₂.ext
    ext m
    dsimp [pseudofunctor, functor, Operations.pseudofunctor, Operations.functor,
      Functor.toPseudofunctor']
    simp
    exact ((D.atlasToChart).map_id _).symm
  naturality_comp f g := by
    cases f
    cases g
    apply Cat.Hom₂.ext
    ext m
    dsimp [pseudofunctor, functor, Operations.pseudofunctor, Operations.functor,
      Functor.toPseudofunctor']
    simp
    exact ((D.atlasToChart).map_id _).symm

def atlasPresentationInverse : D.pseudofunctor ⟶ D.atlasOperations.pseudofunctor where
  app X := (D.chartToAtlas (X := X.as.unop)).toCatHom
  naturality _ := Iso.refl _
  naturality_naturality := by
    intro X Y f g h
    obtain rfl := LocallyDiscrete.eq_of_hom h
    have hh : h = 𝟙 f := Subsingleton.elim _ _
    subst h
    simp only [PrelaxFunctor.map₂_id]
    apply Cat.Hom₂.ext
    ext m
    simp
  naturality_id X := by
    cases X
    apply Cat.Hom₂.ext
    ext m
    dsimp [pseudofunctor, functor, Operations.pseudofunctor, Operations.functor,
      Functor.toPseudofunctor']
    simp
    exact ((D.chartToAtlas).map_id _).symm
  naturality_comp f g := by
    cases f
    cases g
    apply Cat.Hom₂.ext
    ext m
    dsimp [pseudofunctor, functor, Operations.pseudofunctor, Operations.functor,
      Functor.toPseudofunctor']
    simp
    exact ((D.chartToAtlas).map_id _).symm

@[simp] theorem atlasToChart_chartToAtlas : D.atlasToChart (X := X) ⋙ D.chartToAtlas = 𝟭 _ := rfl
@[simp] theorem chartToAtlas_atlasToChart : D.chartToAtlas (X := X) ⋙ D.atlasToChart = 𝟭 _ := rfl

variable {V W : Sheaf J (Type (max u v))} {q : V ⟶ G.objects} {s : W ⟶ G.objects}
variable (E : Chart G q q) (F : Chart G s s)

/-- The input map changes the object lifts and reconstructs the full arrow coordinates. -/
def representedMapFunctor (r : U ⟶ V) (comm : r ≫ q = p) :
    D.atlasOperations.Object X ⥤ E.atlasOperations.Object X :=
  D.atlasToChart ⋙ D.atlasMap E r comm ⋙ E.chartToAtlas

/-- This is a map of the actual input groupoids, before any completion is formed. -/
def representedMap (r : U ⟶ V) (comm : r ≫ q = p) :
    D.atlasOperations.pseudofunctor ⟶ E.atlasOperations.pseudofunctor :=
  (D.atlasPresentation ≫ D.atlasTransformation E r comm) ≫ E.atlasPresentationInverse

@[simp] theorem representedMap_object (r : U ⟶ V) (comm : r ≫ q = p)
    (m : D.atlasOperations.Object X) : ((D.representedMapFunctor E r comm).obj m).map = m.map ≫ r := rfl

/-- The map preserves the ambient arrow, including arrows between different lifts. -/
theorem representedMap_arrow (r : U ⟶ V) (comm : r ≫ q = p)
    {m n : D.atlasOperations.Object X} (f : m ⟶ n) :
    ((D.representedMapFunctor E r comm).map f).map ≫ E.assembly = f.map ≫ D.assembly := by
  exact D.atlasMap_recovery (T := X) E r comm
    (m := (D.atlasToChart (X := X)).obj m) (n := (D.atlasToChart (X := X)).obj n)
    (D.atlasArrowEquiv m n f)

@[simp] theorem representedMapFunctor_id :
    D.representedMapFunctor (X := X) D (𝟙 U) (Category.id_comp p) = 𝟭 _ := by
  unfold representedMapFunctor
  rw [atlasMap_id]
  rfl

@[simp] theorem representedMapFunctor_comp (r : U ⟶ V) (comm : r ≫ q = p)
    (t : V ⟶ W) (comm' : t ≫ s = q) :
    D.representedMapFunctor (X := X) E r comm ⋙ E.representedMapFunctor F t comm' =
      D.representedMapFunctor F (r ≫ t) (by rw [Category.assoc, comm', comm]) := by
  change D.atlasToChart ⋙ D.atlasMap E r comm ⋙
    (E.chartToAtlas ⋙ E.atlasToChart) ⋙ E.atlasMap F t comm' ⋙ F.chartToAtlas = _
  rw [chartToAtlas_atlasToChart, Functor.id_comp]
  change D.atlasToChart ⋙ (D.atlasMap E r comm ⋙ E.atlasMap F t comm') ⋙ F.chartToAtlas = _
  rw [atlasMap_comp]
  rfl

@[simp] theorem representedMapFunctor_restriction (r : U ⟶ V) (comm : r ≫ q = p)
    (k : Y ⟶ X) :
    D.representedMapFunctor E r comm ⋙ E.atlasOperations.restriction k =
      D.atlasOperations.restriction k ⋙ D.representedMapFunctor E r comm := by
  change D.atlasToChart ⋙ D.atlasMap E r comm ⋙
    (E.chartToAtlas ⋙ E.atlasOperations.restriction k) = _
  rw [← chartToAtlas_restriction]
  change D.atlasToChart ⋙ (D.atlasMap E r comm ⋙ E.restriction k) ⋙ E.chartToAtlas = _
  rw [atlasMap_restriction]
  rfl

/-- Identity of actual atlas maps, as an invertible modification. -/
def representedMap_id : D.representedMap D (𝟙 U) (Category.id_comp p) ≅
    𝟙 D.atlasOperations.pseudofunctor :=
  Pseudofunctor.StrongTrans.isoMk (fun X => Cat.Hom.isoMk
    (eqToIso (D.representedMapFunctor_id (X := X.as.unop)))) (by
      intro X Y f
      cases X
      cases Y
      cases f
      apply Cat.Hom₂.ext
      ext m
      dsimp [representedMap, atlasPresentation, atlasPresentationInverse,
        atlasTransformation, atlasNaturality, Pseudofunctor.StrongTrans.vcomp,
        Pseudofunctor.StrongTrans.id, Cat.Hom.isoMk]
      simp
      repeat' first
        | erw [CategoryTheory.Functor.map_id]
        | erw [Category.comp_id]
      all_goals rfl)

/-- Composition of actual atlas maps, before passing to completed bundles. -/
def representedMap_comp (r : U ⟶ V) (comm : r ≫ q = p)
    (t : V ⟶ W) (comm' : t ≫ s = q) :
    D.representedMap E r comm ≫ E.representedMap F t comm' ≅
      D.representedMap F (r ≫ t) (by rw [Category.assoc, comm', comm]) :=
  Pseudofunctor.StrongTrans.isoMk (fun X => Cat.Hom.isoMk
    (eqToIso (D.representedMapFunctor_comp (X := X.as.unop) E F r comm t comm'))) (by
      intro X Y f
      cases X
      cases Y
      cases f
      apply Cat.Hom₂.ext
      ext m
      dsimp [representedMap, atlasPresentation, atlasPresentationInverse,
        atlasTransformation, atlasNaturality, Pseudofunctor.StrongTrans.vcomp,
        Cat.Hom.isoMk]
      simp
      repeat' first
        | erw [CategoryTheory.Functor.map_id]
        | erw [Category.comp_id]
      all_goals rfl)

end SquareKit.SheafGroupoid.Chart
