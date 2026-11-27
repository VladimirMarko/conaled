import SquareKit.SheafGroupoidChart
import SquareKit.Internal.PseudofunctorCoherence

/-! A full arrow chart over an object atlas gives a groupoid presentation.
Its comparison remembers reconstructed arrows and the actual object atlas map. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoid.Chart
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Pseudofunctor.StrongTrans
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Operations J} [G.Laws]
  {U T S R : Sheaf J (Type (max u v))} {u : U ⟶ G.objects} (D : Chart G u u)

/-- An object remembers its chosen lift into the object atlas. -/
structure Object (D : Chart G u u) (T : Sheaf J (Type (max u v))) :
    Type (max (u + 1) (v + 1)) where
  map : T ⟶ U

instance : Category (D.Object T) where
  Hom m n := D.Arrow m.map n.map
  id m := ident D m.map
  comp f g := D.comp D D f g
  id_comp := ident_comp D D
  comp_id := comp_ident D D
  assoc := assoc D D D D D D

instance : Groupoid (D.Object T) where
  inv f := D.inverse D f
  inv_comp := inverse_comp D D D
  comp_inv := comp_inverse D D D

/-- The functor recovers actual arrows over the object atlas. -/
def toGroupoid : D.Object T ⥤ G.Object T where
  obj m := ⟨m.map ≫ u⟩
  map f := D.arrowEquiv _ _ f
  map_id m := ident_recovery D m.map
  map_comp f g := comp_recovery D D D f g

def fullyFaithful : (toGroupoid (T := T) D).FullyFaithful where
  preimage := (D.arrowEquiv _ _).symm
  map_preimage f := (D.arrowEquiv _ _).apply_symm_apply f
  preimage_map f := (D.arrowEquiv _ _).symm_apply_apply f

def restriction (r : S ⟶ T) : D.Object T ⥤ D.Object S where
  obj m := ⟨r ≫ m.map⟩
  map f := D.restrict r f
  map_id m := restrict_ident D r m.map
  map_comp f g := restrict_comp D D D r f g

@[simp] theorem restriction_id : restriction D (𝟙 T) = 𝟭 (D.Object T) := rfl
@[simp] theorem restriction_comp (r : S ⟶ T) (s : R ⟶ S) :
    restriction D r ⋙ restriction D s = restriction D (s ≫ r) := rfl

@[simp] theorem toGroupoid_restriction (r : S ⟶ T) :
    restriction D r ⋙ toGroupoid D = toGroupoid D ⋙ Operations.restriction G r := rfl

def functor : (Sheaf J (Type (max u v)))ᵒᵖ ⥤ Cat where
  obj T := Cat.of (D.Object T.unop)
  map r := (restriction D r.unop).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev pseudofunctor := (functor D).toPseudofunctor'

def transformation : Pseudofunctor.StrongTrans (pseudofunctor D) (Operations.pseudofunctor G) where
  app X := (toGroupoid (T := X.as.unop) D).toCatHom
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
    exact ((toGroupoid D).map_id _).symm
  naturality_comp {X Y Z} f g := by
    cases X
    cases Y
    cases Z
    rcases f with ⟨f⟩
    rcases g with ⟨g⟩
    apply Cat.Hom₂.ext
    ext m
    dsimp [pseudofunctor, functor, Operations.pseudofunctor, Operations.functor,
      Functor.toPseudofunctor']
    simp
    dsimp [pseudofunctorOfIsLocallyDiscrete, LocallyDiscrete.categoryStruct,
      locallyDiscreteBicategory, CategoryStruct.comp]
    apply Operations.Arrow.ext
    exact congrArg Operations.Arrow.map (ident_recovery D ((g.unop ≫ f.unop) ≫ m.map)).symm

variable (E F : Chart G u u)

/-- Independently chosen arrow coordinates give the same presentation over an atlas. -/
def changeFunctor : D.Object T ⥤ E.Object T where
  obj m := ⟨m.map⟩
  map f := D.comparison E _ _ f
  map_id m := comparison_ident D E m.map
  map_comp f g := comparison_comp D E D E D E f g

@[simp] theorem changeFunctor_toGroupoid :
    changeFunctor (T := T) D E ⋙ toGroupoid E = toGroupoid D := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro m; rfl
  intro m n f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact comparison_recovery D E m.map n.map f

@[simp] theorem changeFunctor_self : changeFunctor (T := T) D D = 𝟭 (D.Object T) := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro m; rfl
  intro m n f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (D.arrowEquiv m.map n.map).symm_apply_apply f

@[simp] theorem changeFunctor_comp :
    changeFunctor (T := T) D E ⋙ changeFunctor E F = changeFunctor D F := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro m; rfl
  intro m n f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact comparison_trans D E F m.map n.map f

@[simp] theorem changeFunctor_restriction (r : S ⟶ T) :
    changeFunctor D E ⋙ restriction E r = restriction D r ⋙ changeFunctor D E := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro m; rfl
  intro m n f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change E.restrict r (D.comparison E _ _ f) = D.comparison E _ _ (D.restrict r f)
  apply (E.arrowEquiv _ _).injective
  simp only [arrowEquiv_restrict, comparison_recovery]

/-- The equivalence keeps atlas objects and reconstructs the same actual arrows. -/
def changeEquivalence : D.Object T ≌ E.Object T where
  functor := changeFunctor D E
  inverse := changeFunctor E D
  unitIso := eqToIso (by rw [changeFunctor_comp, changeFunctor_self])
  counitIso := eqToIso (by rw [changeFunctor_comp, changeFunctor_self])

/-- Changing coordinates commutes with every parameter restriction. -/
def changeNaturality (r : S ⟶ T) :
    restriction D r ⋙ changeFunctor D E ≅ changeFunctor D E ⋙ restriction E r :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro m n f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    change D.comparison E _ _ (D.restrict r f) = E.restrict r (D.comparison E _ _ f)
    apply (E.arrowEquiv _ _).injective
    simp only [arrowEquiv_restrict, comparison_recovery])

/-- The presentation equivalence is natural over all parameter sheaves. -/
def changeTransformation : Pseudofunctor.StrongTrans (pseudofunctor D) (pseudofunctor E) where
  app X := (changeFunctor (T := X.as.unop) D E).toCatHom
  naturality f := Cat.Hom.isoMk (changeNaturality D E f.as.unop)
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
    dsimp [pseudofunctor, functor, Functor.toPseudofunctor', changeNaturality]
    dsimp [pseudofunctorOfIsLocallyDiscrete, locallyDiscreteBicategory, LocallyDiscrete.categoryStruct,
      CategoryStruct.id, Cat.Hom.isoMk]
    simp
    rfl
  naturality_comp f g := by
    rcases f with ⟨f⟩
    cases g
    apply Cat.Hom₂.ext
    ext m
    dsimp [pseudofunctor, functor, Functor.toPseudofunctor', changeNaturality]
    dsimp [pseudofunctorOfIsLocallyDiscrete, locallyDiscreteBicategory, LocallyDiscrete.categoryStruct,
      CategoryStruct.comp, Cat.Hom.isoMk]
    simp

/-- Coordinate change preserves the actual-arrow comparison as a strong transformation. -/
def changeTransformation_toGroupoid :
    PseudofunctorCoherence.ModificationIso
      (Pseudofunctor.StrongTrans.vcomp (changeTransformation D E) (transformation E))
      (transformation D) :=
  Pseudofunctor.StrongTrans.isoMk (fun _ => Cat.Hom.isoMk
    (NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro m n f
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      exact comparison_recovery D E m.map n.map f))) (by
    intro X Y f
    rcases f with ⟨f⟩
    apply Cat.Hom₂.ext
    ext m
    dsimp [changeTransformation, transformation, changeNaturality,
      Pseudofunctor.StrongTrans.vcomp, Pseudofunctor.StrongTrans.toOplax,
      Oplax.StrongTrans.toOplax, Cat.Hom.isoMk, pseudofunctor, functor,
      Operations.pseudofunctor, Operations.functor, Functor.toPseudofunctor',
      pseudofunctorOfIsLocallyDiscrete]
    simp
    erw [(Operations.restriction G f.unop).map_id, Category.comp_id])

/-- Changing a chart to itself gives the identity presentation transformation. -/
def changeTransformation_self : PseudofunctorCoherence.ModificationIso (changeTransformation D D)
    (Pseudofunctor.StrongTrans.id (pseudofunctor D)) :=
  Pseudofunctor.StrongTrans.isoMk (fun _ => Cat.Hom.isoMk
    (NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro m n f
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      exact (D.arrowEquiv m.map n.map).symm_apply_apply f))) (by
    intro X Y f
    apply Cat.Hom₂.ext
    ext m
    dsimp [changeTransformation, changeNaturality, Pseudofunctor.StrongTrans.id, Cat.Hom.isoMk]
    simp
    rfl)

/-- Successive independent coordinate changes agree with the direct change. -/
def changeTransformation_comp :
    PseudofunctorCoherence.ModificationIso
      (Pseudofunctor.StrongTrans.vcomp (changeTransformation D E) (changeTransformation E F))
      (changeTransformation D F) :=
  Pseudofunctor.StrongTrans.isoMk (fun _ => Cat.Hom.isoMk
    (NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro m n f
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      exact comparison_trans D E F m.map n.map f))) (by
    intro X Y f
    rcases f with ⟨f⟩
    apply Cat.Hom₂.ext
    ext m
    dsimp [changeTransformation, changeNaturality, Pseudofunctor.StrongTrans.vcomp,
      Pseudofunctor.StrongTrans.toOplax, Oplax.StrongTrans.toOplax,
      Cat.Hom.isoMk, pseudofunctor, functor, Functor.toPseudofunctor',
      pseudofunctorOfIsLocallyDiscrete]
    simp
    erw [(restriction F f.unop).map_id, Category.comp_id])

@[simp] theorem changeTransformation_toGroupoid_hom_app
    (X : LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ) (m : D.Object X.as.unop) :
    ((changeTransformation_toGroupoid D E).hom.as.app X).toNatTrans.app m =
      𝟙 ((toGroupoid D).obj m) := rfl

@[simp] theorem changeTransformation_self_hom_app
    (X : LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ) (m : D.Object X.as.unop) :
    ((changeTransformation_self D).hom.as.app X).toNatTrans.app m = 𝟙 m := rfl

@[simp] theorem changeTransformation_comp_hom_app
    (X : LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ) (m : D.Object X.as.unop) :
    ((changeTransformation_comp D E F).hom.as.app X).toNatTrans.app m =
      𝟙 ((changeFunctor D F).obj m) := rfl

end SquareKit.SheafGroupoid.Chart

namespace SquareKit.SheafGroupoid.Chart
open CategoryTheory CategoryTheory.Limits Opposite
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Operations J} [G.Laws]
  {U T S : Sheaf J (Type (max u v))} {u : U ⟶ G.objects} (D : Chart G u u)
section AtlasMap
variable {V W : Sheaf J (Type (max u v))} {q : V ⟶ G.objects} {p : W ⟶ G.objects}
  (E : Chart G q q) (F : Chart G p p)

/-- A commuting atlas square changes lifts and reconstructs the same actual arrows. -/
def atlasMap (r : U ⟶ V) (comm : r ≫ q = u) : D.Object T ⥤ E.Object T where
  obj m := ⟨m.map ≫ r⟩
  map f := E.fullyFaithful.preimage {
    map := (D.toGroupoid.map f).map
    source := by simpa only [toGroupoid, Category.assoc, comm] using (D.toGroupoid.map f).source
    target := by simpa only [toGroupoid, Category.assoc, comm] using (D.toGroupoid.map f).target }
  map_id m := by
    apply E.fullyFaithful.map_injective
    rw [E.fullyFaithful.map_preimage, E.toGroupoid.map_id]
    apply Operations.Arrow.ext
    change (D.toGroupoid.map (𝟙 m)).map = _
    rw [D.toGroupoid.map_id]
    change (m.map ≫ u) ≫ G.unit = ((m.map ≫ r) ≫ q) ≫ G.unit
    rw [Category.assoc m.map r q, comm]
  map_comp f g := by
    apply E.fullyFaithful.map_injective
    rw [E.fullyFaithful.map_preimage, E.toGroupoid.map_comp,
      E.fullyFaithful.map_preimage, E.fullyFaithful.map_preimage]
    apply Operations.Arrow.ext
    change (D.toGroupoid.map (f ≫ g)).map = _
    rw [D.toGroupoid.map_comp]
    rfl

@[simp] theorem atlasMap_recovery (r : U ⟶ V) (comm : r ≫ q = u)
    {m n : D.Object T} (f : m ⟶ n) :
    ((E.toGroupoid).map ((D.atlasMap E r comm).map f)).map = (D.toGroupoid.map f).map := by
  change (E.toGroupoid.map (E.fullyFaithful.preimage _)).map = _
  rw [E.fullyFaithful.map_preimage]


@[simp] theorem atlasMap_toGroupoid (r : U ⟶ V) (comm : r ≫ q = u) :
    D.atlasMap (T := T) E r comm ⋙ E.toGroupoid = D.toGroupoid := by
  subst u
  apply CategoryTheory.Functor.ext
  case h_obj => intro m; rfl
  intro m n f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply Operations.Arrow.ext
  exact atlasMap_recovery D E r rfl f

@[simp] theorem atlasMap_id : D.atlasMap (T := T) D (𝟙 U) (Category.id_comp u) = 𝟭 _ := by
  apply CategoryTheory.Functor.ext
  case h_obj => intro m; rfl
  intro m n f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply (D.fullyFaithful).map_injective
  apply Operations.Arrow.ext
  exact atlasMap_recovery D D _ _ f

@[simp] theorem atlasMap_comp (r : U ⟶ V) (comm : r ≫ q = u)
    (s : V ⟶ W) (comm' : s ≫ p = q) :
    D.atlasMap (T := T) E r comm ⋙ E.atlasMap F s comm' =
      D.atlasMap F (r ≫ s) (by rw [Category.assoc, comm', comm]) := by
  subst u
  subst q
  apply CategoryTheory.Functor.ext
  case h_obj => intro m; rfl
  intro m n f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply F.fullyFaithful.map_injective
  apply Operations.Arrow.ext
  simp only [Functor.comp_map, atlasMap_recovery]

@[simp] theorem atlasMap_restriction (r : U ⟶ V) (comm : r ≫ q = u) (s : S ⟶ T) :
    D.atlasMap E r comm ⋙ E.restriction s = D.restriction s ⋙ D.atlasMap E r comm := by
  subst u
  apply CategoryTheory.Functor.ext
  case h_obj => intro m; rfl
  intro m n f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply E.fullyFaithful.map_injective
  apply Operations.Arrow.ext
  change (s ≫ ((E.toGroupoid).map ((D.atlasMap E r rfl).map f)).map) = _
  simp only [Functor.comp_map, atlasMap_recovery]
  rfl

/-- The atlas comparison reconstructs the same ambient objects and arrows. -/
def atlasToGroupoid (r : U ⟶ V) (comm : r ≫ q = u) :
    D.atlasMap (T := T) E r comm ⋙ E.toGroupoid ≅ D.toGroupoid := by
  subst u
  exact NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro m n f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    apply Operations.Arrow.ext
    exact atlasMap_recovery D E r rfl f)

/-- The substitution comparison has identity components on atlas lifts. -/
def atlasNaturality (r : U ⟶ V) (comm : r ≫ q = u) (s : S ⟶ T) :
    D.restriction s ⋙ D.atlasMap E r comm ≅ D.atlasMap E r comm ⋙ E.restriction s := by
  exact NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro m n f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    apply E.fullyFaithful.map_injective
    apply Operations.Arrow.ext
    change ((E.toGroupoid).map ((D.atlasMap E r comm).map ((D.restriction s).map f))).map =
      s ≫ ((E.toGroupoid).map ((D.atlasMap E r comm).map f)).map
    simp only [atlasMap_recovery]
    rfl)

/-- Atlas changes commute with parameter substitution on the full presentation. -/
def atlasTransformation (r : U ⟶ V) (comm : r ≫ q = u) :
    Pseudofunctor.StrongTrans D.pseudofunctor E.pseudofunctor where
  app := fun X => (D.atlasMap (T := X.as.unop) E r comm).toCatHom
  naturality := fun f => Cat.Hom.isoMk (D.atlasNaturality E r comm f.as.unop)
  naturality_naturality := by
      intro X Y f g h
      obtain rfl := LocallyDiscrete.eq_of_hom h
      have hh : h = 𝟙 f := Subsingleton.elim _ _
      subst h
      simp only [PrelaxFunctor.map₂_id]
      apply Cat.Hom₂.ext
      ext m
      simp
  naturality_id := by
      intro X
      cases X
      apply Cat.Hom₂.ext
      ext m
      dsimp [pseudofunctor, functor, Functor.toPseudofunctor', atlasNaturality]
      simp
      erw [(D.atlasMap E r comm).map_id, Category.id_comp]
      rfl
  naturality_comp := by
      intro X Y Z f g
      cases X; cases Y; cases Z
      rcases f with ⟨f⟩; rcases g with ⟨g⟩
      apply Cat.Hom₂.ext
      ext m
      dsimp [pseudofunctor, functor, Functor.toPseudofunctor', atlasNaturality]
      simp
      dsimp [pseudofunctorOfIsLocallyDiscrete, locallyDiscreteBicategory,
        LocallyDiscrete.categoryStruct, CategoryStruct.comp]
      erw [(D.atlasMap E r comm).map_id, (E.restriction g.unop).map_id]
      simp only [Category.id_comp]
      rfl

/-- The atlas map preserves the actual-arrow interpretation, including substitution. -/
def atlasTransformation_toGroupoid (r : U ⟶ V) (comm : r ≫ q = u) :
    PseudofunctorCoherence.ModificationIso
      (Pseudofunctor.StrongTrans.vcomp (D.atlasTransformation E r comm) E.transformation)
      D.transformation := by
  exact Pseudofunctor.StrongTrans.isoMk
    (fun X => Cat.Hom.isoMk (D.atlasToGroupoid (T := X.as.unop) E r comm)) (by
    subst u
    intro X Y f
    rcases f with ⟨f⟩
    apply Cat.Hom₂.ext
    ext m
    dsimp [atlasTransformation, atlasNaturality, atlasToGroupoid, transformation, Pseudofunctor.StrongTrans.vcomp,
      Pseudofunctor.StrongTrans.toOplax, Oplax.StrongTrans.toOplax, Cat.Hom.isoMk,
      pseudofunctor, functor, Operations.pseudofunctor, Operations.functor,
      Functor.toPseudofunctor', pseudofunctorOfIsLocallyDiscrete]
    simp
    erw [(Operations.restriction G f.unop).map_id, Category.comp_id])

/-- The identity atlas square induces the identity presentation transformation. -/
def atlasTransformation_id :
    PseudofunctorCoherence.ModificationIso
      (D.atlasTransformation D (𝟙 U) (Category.id_comp u))
      (Pseudofunctor.StrongTrans.id D.pseudofunctor) :=
  Pseudofunctor.StrongTrans.isoMk (fun _ => Cat.Hom.isoMk
    (NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro m n f
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      apply D.fullyFaithful.map_injective
      apply Operations.Arrow.ext
      exact atlasMap_recovery D D _ _ f))) (by
    intro X Y f
    apply Cat.Hom₂.ext
    ext m
    dsimp [atlasTransformation, atlasNaturality, Pseudofunctor.StrongTrans.id, Cat.Hom.isoMk]
    simp
    rfl)

/-- Composing actual atlas squares gives the composite presentation transformation. -/
def atlasTransformation_comp (r : U ⟶ V) (comm : r ≫ q = u)
    (s : V ⟶ W) (comm' : s ≫ p = q) :
    PseudofunctorCoherence.ModificationIso
      (Pseudofunctor.StrongTrans.vcomp (D.atlasTransformation E r comm)
        (E.atlasTransformation F s comm'))
      (D.atlasTransformation F (r ≫ s) (by rw [Category.assoc, comm', comm])) :=
  Pseudofunctor.StrongTrans.isoMk (fun _ => Cat.Hom.isoMk
    (NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro m n f
      simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
      apply F.fullyFaithful.map_injective
      apply Operations.Arrow.ext
      change (F.toGroupoid.map ((E.atlasMap F s comm').map
        ((D.atlasMap E r comm).map f))).map = _
      simp only [atlasMap_recovery]))) (by
    intro X Y f
    rcases f with ⟨f⟩
    apply Cat.Hom₂.ext
    ext m
    dsimp [atlasTransformation, atlasNaturality, Pseudofunctor.StrongTrans.vcomp,
      Pseudofunctor.StrongTrans.toOplax, Oplax.StrongTrans.toOplax, Cat.Hom.isoMk,
      pseudofunctor, functor, Functor.toPseudofunctor', pseudofunctorOfIsLocallyDiscrete]
    simp
    erw [(F.restriction f.unop).map_id, Category.comp_id])

open scoped CategoryTheory.Pseudofunctor.StrongTrans in
@[simp] theorem atlasTransformation_id_hom_app
    (X : LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ) (m : D.Object X.as.unop) :
    ((D.atlasTransformation_id).hom.as.app X).toNatTrans.app m = 𝟙 m := rfl

open scoped CategoryTheory.Pseudofunctor.StrongTrans in
@[simp] theorem atlasTransformation_comp_hom_app
    (r : U ⟶ V) (comm : r ≫ q = u) (s : V ⟶ W) (comm' : s ≫ p = q)
    (X : LocallyDiscrete (Sheaf J (Type (max u v)))ᵒᵖ) (m : D.Object X.as.unop) :
    ((D.atlasTransformation_comp E F r comm s comm').hom.as.app X).toNatTrans.app m =
      𝟙 ((D.atlasMap F (r ≫ s) (by rw [Category.assoc, comm', comm])).obj m) := rfl

end AtlasMap

end SquareKit.SheafGroupoid.Chart
