import SquareKit.SheafGroupoid
import SquareKit.SheafActionPresentation
import SquareKit.SheafRelation

/-! The represented action groupoid and its full inverse-label recovery. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SquareKit.SheafGroupoidAction
open CategoryTheory CategoryTheory.Limits Opposite SheafTorsor
universe u v
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G : Sheaf J GrpCat.{max u v}} {M : Sheaf J (Type (max u v))}
variable (a : SheafActionQuotient.Action G M)

abbrev arrows := SheafRelation.product (groupSheaf G) M
abbrev label : arrows (G := G) (M := M) ⟶ groupSheaf G := SheafRelation.fst _ _
abbrev source : arrows (G := G) (M := M) ⟶ M := SheafRelation.snd _ _
def target : arrows (G := G) (M := M) ⟶ M := a.onMap label source

def unit : M ⟶ arrows (G := G) (M := M) := SheafRelation.lift (labelOne M) (𝟙 M)
def inverse : arrows (G := G) (M := M) ⟶ arrows (G := G) (M := M) :=
  SheafRelation.lift (labelInv label) (target a)
def comp : pullback (target a) (source (G := G)) ⟶ arrows (G := G) (M := M) :=
  SheafRelation.lift
    (labelMul (pullback.snd (target a) source ≫ label)
      (pullback.fst (target a) source ≫ label))
    (pullback.fst (target a) source ≫ source)

@[simp] theorem lift_label {X : Sheaf J (Type (max u v))}
    (g : X ⟶ groupSheaf G) (m : X ⟶ M) :
    SheafRelation.lift g m ≫ label = g := rfl
@[simp] theorem lift_source {X : Sheaf J (Type (max u v))}
    (g : X ⟶ groupSheaf G) (m : X ⟶ M) :
    SheafRelation.lift g m ≫ source = m := rfl
@[simp] theorem lift_target {X : Sheaf J (Type (max u v))}
    (g : X ⟶ groupSheaf G) (m : X ⟶ M) :
    SheafRelation.lift g m ≫ target a = a.onMap g m := rfl

theorem comp_target : comp a ≫ target a = pullback.snd (target a) source ≫ target a := by
  have hw := pullback.condition (f := target a) (g := source (G := G))
  ext U z
  have hz := congrArg (fun k => k.hom.app U z) hw
  let f := (pullback.fst (target a) source).hom.app U z
  let g := (pullback.snd (target a) source).hom.app U z
  change a.act U f.1 f.2 = g.2 at hz
  change a.act U ((show G.obj.obj U from g.1) * (show G.obj.obj U from f.1)) f.2 =
    a.act U g.1 g.2
  rw [a.mul_act, hz]

/-- These are the actual action operations, before deriving their groupoid laws. -/
abbrev operations : SheafGroupoid.Operations J where
  objects := M
  arrows := arrows
  source := source
  target := target a
  unit := unit
  inverse := inverse a
  comp := comp a
  unit_source := rfl
  unit_target := by ext U x; exact a.one_act U x
  inverse_source := rfl
  inverse_target := by
    ext U x
    change a.act U ((show G.obj.obj U from x.1)⁻¹) (a.act U x.1 x.2) = x.2
    rw [← a.mul_act, inv_mul_cancel, a.one_act]
  comp_source := rfl
  comp_target := comp_target a

variable {X Y : Sheaf J (Type (max u v))}

/-- Geometric label g:x→g•x becomes the regular left-torsor label g⁻¹. -/
def toPresentationArrow {m n : (operations a).Object X}
    (f : (operations a).Arrow m n) :
    SheafActionPresentation.Arrow a ⟨m.map⟩ ⟨n.map⟩ where
  label := labelInv (f.map ≫ label)
  relation := by
    ext U z
    have hs := congrArg (fun k => k.hom.app U z) f.source
    have ht := congrArg (fun k => k.hom.app U z) f.target
    change (f.map.hom.app U z).2 = m.map.hom.app U z at hs
    change a.act U (f.map.hom.app U z).1 (f.map.hom.app U z).2 = n.map.hom.app U z at ht
    change a.act U ((show G.obj.obj U from (f.map.hom.app U z).1)⁻¹)
      (n.map.hom.app U z) = m.map.hom.app U z
    rw [← ht, ← a.mul_act, inv_mul_cancel, a.one_act, hs]

def fromPresentationArrow {m n : (operations a).Object X}
    (f : SheafActionPresentation.Arrow a ⟨m.map⟩ ⟨n.map⟩) :
    (operations a).Arrow m n where
  map := SheafRelation.lift (labelInv f.label) m.map
  source := rfl
  target := by
    ext U z
    have hf := congrArg (fun k => k.hom.app U z) f.relation
    change a.act U (f.label.hom.app U z) (n.map.hom.app U z) = m.map.hom.app U z at hf
    change a.act U ((show G.obj.obj U from f.label.hom.app U z)⁻¹)
      (m.map.hom.app U z) = n.map.hom.app U z
    rw [← hf, ← a.mul_act, inv_mul_cancel, a.one_act]

/-- Full arrow recovery holds for every parameter sheaf, including varying labels. -/
def arrowEquiv (m n : (operations a).Object X) :
    (operations a).Arrow m n ≃ SheafActionPresentation.Arrow a ⟨m.map⟩ ⟨n.map⟩ where
  toFun := toPresentationArrow a
  invFun := fromPresentationArrow a
  left_inv f := by
    apply SheafGroupoid.Operations.Arrow.ext
    ext U z
    apply Prod.ext
    · exact inv_inv (show G.obj.obj U from (f.map.hom.app U z).1)
    · exact (congrArg (fun k => k.hom.app U z) f.source).symm
  right_inv f := by
    apply SheafActionPresentation.Arrow.ext
    exact labelInv_inv f.label

@[simp] theorem toPresentationArrow_ident (m : (operations a).Object X) :
    toPresentationArrow a (.ident _ m) = 𝟙 (SheafActionPresentation.Object.mk m.map) := by
  apply SheafActionPresentation.Arrow.ext
  ext U z
  exact inv_one (G := G.obj.obj U)

@[simp] theorem toPresentationArrow_comp {m n p : (operations a).Object X}
    (f : (operations a).Arrow m n) (g : (operations a).Arrow n p) :
    toPresentationArrow a (f.comp _ g) =
      SheafActionPresentation.Arrow.comp (toPresentationArrow a f) (toPresentationArrow a g) := by
  apply SheafActionPresentation.Arrow.ext
  change labelInv ((pullback.lift f.map g.map _ ≫ comp a) ≫ label) =
    labelMul (labelInv (f.map ≫ label)) (labelInv (g.map ≫ label))
  have hh : (pullback.lift f.map g.map (f.target.trans g.source.symm) ≫ comp a) ≫ label =
      labelMul (g.map ≫ label) (f.map ≫ label) := by
    change pullback.lift f.map g.map _ ≫ labelMul _ _ = _
    rw [labelMul_precomp]
    simp only [← Category.assoc, pullback.lift_fst, pullback.lift_snd]
  rw [hh, labelInv_mul_rev]

@[simp] theorem toPresentationArrow_inverse {m n : (operations a).Object X}
    (f : (operations a).Arrow m n) :
    toPresentationArrow a (f.inverse _) = SheafActionPresentation.Arrow.inverse (toPresentationArrow a f) := rfl

instance laws : (operations a).Laws where
  id_comp f := (arrowEquiv a _ _).injective (by
    change toPresentationArrow a _ = toPresentationArrow a _
    rw [toPresentationArrow_comp, toPresentationArrow_ident]
    apply SheafActionPresentation.Arrow.ext
    exact labelOne_mul _)
  comp_id f := (arrowEquiv a _ _).injective (by
    change toPresentationArrow a _ = toPresentationArrow a _
    rw [toPresentationArrow_comp, toPresentationArrow_ident]
    apply SheafActionPresentation.Arrow.ext
    exact labelMul_one _)
  assoc f g h := (arrowEquiv a _ _).injective (by
    change toPresentationArrow a _ = toPresentationArrow a _
    simp only [toPresentationArrow_comp]
    apply SheafActionPresentation.Arrow.ext
    exact labelMul_assoc _ _ _)
  inv_comp f := (arrowEquiv a _ _).injective (by
    change toPresentationArrow a _ = toPresentationArrow a _
    rw [toPresentationArrow_comp, toPresentationArrow_inverse, toPresentationArrow_ident]
    apply SheafActionPresentation.Arrow.ext
    exact labelInv_mul _)
  comp_inv f := (arrowEquiv a _ _).injective (by
    change toPresentationArrow a _ = toPresentationArrow a _
    rw [toPresentationArrow_comp, toPresentationArrow_inverse, toPresentationArrow_ident]
    apply SheafActionPresentation.Arrow.ext
    exact labelMul_inv _)

def groupoid : SheafGroupoid J := { toOperations := operations a, lawful := laws a }

def toPresentation : (operations a).Object X ⥤ SheafActionPresentation.Object a X where
  obj m := ⟨m.map⟩
  map := toPresentationArrow a
  map_id := toPresentationArrow_ident a
  map_comp := toPresentationArrow_comp a

def fullyFaithful : (toPresentation (X := X) a).FullyFaithful where
  preimage := fromPresentationArrow a
  map_preimage f := (arrowEquiv a _ _).apply_symm_apply f
  preimage_map f := (arrowEquiv a _ _).symm_apply_apply f

@[simp] theorem toPresentation_restriction (r : Y ⟶ X) :
    (operations a).restriction r ⋙ toPresentation a =
      toPresentation a ⋙ SheafActionPresentation.restriction a r := rfl

/-- The full arrow comparison is compatible with every parameter map. -/
def transformation : Pseudofunctor.StrongTrans (operations a).pseudofunctor
    (SheafActionPresentation.pseudofunctor a) where
  app X := (toPresentation (X := X.as.unop) a).toCatHom
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
    dsimp [SheafGroupoid.Operations.pseudofunctor, SheafGroupoid.Operations.functor,
      SheafActionPresentation.pseudofunctor, SheafActionPresentation.functor,
      Functor.toPseudofunctor']
    simp
    exact ((toPresentation a).map_id _).symm
  naturality_comp f g := by
    cases f
    cases g
    apply Cat.Hom₂.ext
    ext m
    dsimp [SheafGroupoid.Operations.pseudofunctor, SheafGroupoid.Operations.functor,
      SheafActionPresentation.pseudofunctor, SheafActionPresentation.functor,
      Functor.toPseudofunctor']
    simp
    exact ((toPresentation a).map_id _).symm

end SquareKit.SheafGroupoidAction
