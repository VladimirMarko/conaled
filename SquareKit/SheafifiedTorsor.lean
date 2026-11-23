import SquareKit.ElementSiteLocalEquivalence
import SquareKit.SheafTorsor
import SquareKit.SheafifiedYoneda

/-! Recovering maps of sheaf families from locally bijective presheaf presentations. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.SheafTorsor.LocalPresentation
open CategoryTheory Opposite
universe u
variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable {X : Sheaf J (Type u)} {P : Cᵒᵖ ⥤ Type u} (η : P ⟶ X.obj)
variable [Presheaf.IsLocallyInjective J η] [Presheaf.IsLocallySurjective J η]

def homEquiv (A B : SplitSheaf.Ty X) :
    (η.mapElements ⋙ A.family ⟶ η.mapElements ⋙ B.family) ≃ (A.family ⟶ B.family) := by
  let e := CategoryTheory.Functor.IsCoverDense.restrictHomEquivHom
    (G := ElementSite.mapSite η) (K := ElementSite.topology X.obj J)
    (ℱ := (SplitSheaf.elementSheaf A).obj) (ℱ' := SplitSheaf.elementSheaf B)
  let lift (h : η.mapElements ⋙ A.family ⟶ η.mapElements ⋙ B.family) :
      (ElementSite.mapSite η).op ⋙ (SplitSheaf.elementSheaf A).obj ⟶
        (ElementSite.mapSite η).op ⋙ (SplitSheaf.elementSheaf B).obj :=
    { app := fun x => h.app x.unop.unop
      naturality := fun {_ _} f => h.naturality f.unop.unop }
  refine
    { toFun := fun h =>
        { app := fun x => (e (lift h)).app (op (op x))
          naturality := fun {_ _} f => (e (lift h)).naturality f.op.op }
      invFun := Functor.whiskerLeft η.mapElements
      left_inv := ?_
      right_inv := ?_ }
  · intro h
    ext x p
    exact congrArg (fun k => k.app (op (op x)) p) (e.symm_apply_apply (lift h))
  · intro h
    ext x p
    exact congrArg (fun k => k.app (op (op x)) p) (e.apply_symm_apply
      { app := fun x => h.app x.unop.unop
        naturality := fun {_ _} f => h.naturality f.unop.unop })

@[simp] theorem homEquiv_symm_apply (A B : SplitSheaf.Ty X) (h : A.family ⟶ B.family) :
    (homEquiv η A B).symm h = Functor.whiskerLeft η.mapElements h := rfl

@[simp] theorem restrict_extend (A B : SplitSheaf.Ty X)
    (h : η.mapElements ⋙ A.family ⟶ η.mapElements ⋙ B.family) :
    Functor.whiskerLeft η.mapElements (homEquiv η A B h) = h :=
  (homEquiv η A B).symm_apply_apply h

def extendIso (A B : SplitSheaf.Ty X)
    (h : η.mapElements ⋙ A.family ≅ η.mapElements ⋙ B.family) : A.family ≅ B.family where
  hom := homEquiv η A B h.hom
  inv := homEquiv η B A h.inv
  hom_inv_id := by
    apply (homEquiv η A A).symm.injective
    simp only [homEquiv_symm_apply, Functor.whiskerLeft_comp, restrict_extend,
      h.hom_inv_id]
    rfl
  inv_hom_id := by
    apply (homEquiv η B B).symm.injective
    simp only [homEquiv_symm_apply, Functor.whiskerLeft_comp, restrict_extend,
      h.inv_hom_id]
    rfl

omit [Presheaf.IsLocallyInjective J η] in
theorem equivariant_of_restriction {G : Sheaf J GrpCat.{u}} {A B : Torsor G X}
    (h : A.family.family ⟶ B.family.family)
    (hh : ∀ (y : P.Elements) (g : G.obj.obj y.obj) (p),
      h.app (η.mapElements.obj y) (A.act (η.mapElements.obj y) g p) =
        B.act (η.mapElements.obj y) g (h.app (η.mapElements.obj y) p)) :
    ∀ (x : X.obj.Elements) (g : G.obj.obj x.obj) (p),
      h.app x (A.act x g p) = B.act x g (h.app x p) := by
  intro x g p
  apply CategoryTheory.Functor.IsCoverDense.ext (ElementSite.mapSite η)
    (SplitSheaf.elementSheaf B.family) (op x)
  intro y f
  change B.family.family.map f.unop (h.app x (A.act x g p)) =
    B.family.family.map f.unop (B.act x g (h.app x p))
  rw [← NatTrans.naturality_apply, A.natural, B.natural, ← NatTrans.naturality_apply]
  exact hh y.unop _ _

def extendArrow {G : Sheaf J GrpCat.{u}} (A B : Torsor G X)
    (h : η.mapElements ⋙ A.family.family ≅ η.mapElements ⋙ B.family.family)
    (hh : ∀ (y : P.Elements) (g : G.obj.obj y.obj) (p),
      h.hom.app y (A.act (η.mapElements.obj y) g p) =
        B.act (η.mapElements.obj y) g (h.hom.app y p)) : A ⟶ B where
  iso := extendIso η A.family B.family h
  equivariant := by
    apply equivariant_of_restriction η
    intro y g p
    have hr := restrict_extend η A.family B.family h.hom
    have hc (q) : (homEquiv η A.family B.family h.hom).app (η.mapElements.obj y) q =
        h.hom.app y q := congrArg (fun k => k.app y q) hr
    change (homEquiv η A.family B.family h.hom).app (η.mapElements.obj y) _ =
      B.act (η.mapElements.obj y) g
        ((homEquiv η A.family B.family h.hom).app (η.mapElements.obj y) p)
    rw [hc, hc]
    exact hh y g p

theorem extendArrow_restrict {G : Sheaf J GrpCat.{u}} (A B : Torsor G X)
    (h : η.mapElements ⋙ A.family.family ≅ η.mapElements ⋙ B.family.family)
    (hh : ∀ (y : P.Elements) (g : G.obj.obj y.obj) (p),
      h.hom.app y (A.act (η.mapElements.obj y) g p) =
        B.act (η.mapElements.obj y) g (h.hom.app y p)) :
    Functor.whiskerLeft η.mapElements (extendArrow η A B h hh).iso.hom = h.hom :=
  restrict_extend η A.family B.family h.hom

theorem arrow_ext {G : Sheaf J GrpCat.{u}} {A B : Torsor G X} {f g : A ⟶ B}
    (h : Functor.whiskerLeft η.mapElements f.iso.hom =
      Functor.whiskerLeft η.mapElements g.iso.hom) : f = g := by
  apply Arrow.ext
  exact (homEquiv η A.family B.family).symm.injective h

end SquareKit.SheafTorsor.LocalPresentation
