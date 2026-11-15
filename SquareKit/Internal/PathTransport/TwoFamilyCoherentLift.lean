import SquareKit.Internal.PathTransport.TwoFamilySigmaCells
import SquareKit.Internal.PathTransport.TwoStrongTransport
namespace SquareKit.Internal.PathTransport.TwoFamily
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u v w u' v' w' uE vE wE
variable {Γ : Type u} [Bicategory.{w,v} Γ] [Strict Γ]
variable {Δ : Type u'} [Bicategory.{w',v'} Δ] [Strict Δ]
variable {F G : StrictPseudofunctor Γ Δ}
variable (η : Pseudofunctor.StrongTrans F.toPseudofunctor G.toPseudofunctor)
variable (E : Family.{u',v',w',uE,vE,wE} Δ)
abbrev coherentLiftLeft := reindexHigher E F
abbrev coherentLiftRight := (StrongMap.toHigher (strongPostcomp η E)).comp (reindexHigher E G)
def coherentLiftApp (x : Total (reindex F E)) :
    (coherentLiftLeft (F := F) E).obj x ⟶ (coherentLiftRight η E).obj x :=
  cartesianLift E (η.app x.base) x.fiber

theorem coherentLiftPrefix {γ δ : Γ} (f : γ ⟶ δ) (a : E.obj (F.obj γ)) :
    (E.map₂ (η.naturality f).hom).app a ≫
      compBoundary E (η.app γ) (G.map f) a ≫
      ((strongPostcomp η E).naturality f).inv.app a =
        compBoundary E (F.map f) (η.app δ) a := by
  simp only [strongPostcomp, Iso.trans_inv, Iso.symm_inv]
  rw [E.mapComp_eq_eqToIso, E.mapComp_eq_eqToIso]
  simp only [eqToIso.hom, eqToIso.inv]
  repeat rw [StrictTwoTransformation.Trans.comp_app]
  simp only [StrongMap.classifier_eqToHom_app, compBoundary, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have h := congrArg (fun θ => θ.app a) (E.map₂Iso (η.naturality f)).hom_inv_id
  change (E.map₂ (η.naturality f).hom).app a ≫
      (E.map₂ (η.naturality f).inv).app a = 𝟙 _ at h
  change (E.map₂ (η.naturality f).hom).app a ≫
    (E.map₂ (η.naturality f).inv).app a ≫ _ = _
  rw [← Category.assoc, h, Category.id_comp]

theorem coherentLiftBoundary {x y : Total (reindex F E)} (p : x ⟶ y) :
    ((coherentLiftLeft (F := F) E).map p ≫ coherentLiftApp η E y).fiber =
      (E.map₂ (η.naturality p.base).hom).app x.fiber ≫
        (coherentLiftApp η E x ≫ (coherentLiftRight η E).map p).fiber := by
  change compBoundary E (F.map p.base) (η.app y.base) x.fiber ≫
      (E.map (η.app y.base)).map p.fiber ≫ 𝟙 _ =
    (E.map₂ (η.naturality p.base).hom).app x.fiber ≫
      compBoundary E (η.app x.base) (G.map p.base) x.fiber ≫
      (E.map (G.map p.base)).map (𝟙 _) ≫
      ((strongPostcomp η E).naturality p.base).inv.app x.fiber ≫
      (E.map (η.app y.base)).map p.fiber
  simp only [Category.comp_id, (E.map (G.map p.base)).map_id, Category.id_comp]
  simp only [strongPostcomp, Iso.trans_inv, Iso.symm_inv]
  rw [E.mapComp_eq_eqToIso, E.mapComp_eq_eqToIso]
  simp only [eqToIso.hom, eqToIso.inv]
  repeat rw [StrictTwoTransformation.Trans.comp_app]
  simp only [StrongMap.classifier_eqToHom_app, compBoundary, Category.assoc,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have h := congrArg (fun θ => θ.app x.fiber) (E.map₂Iso (η.naturality p.base)).hom_inv_id
  change (E.map₂ (η.naturality p.base).hom).app x.fiber ≫
      (E.map₂ (η.naturality p.base).inv).app x.fiber = 𝟙 _ at h
  change _ = (E.map₂ (η.naturality p.base).hom).app x.fiber ≫
    (E.map₂ (η.naturality p.base).inv).app x.fiber ≫ _
  rw [← Category.assoc, h, Category.id_comp]
def coherentLiftCell {x y : Total (reindex F E)} (p : x ⟶ y) :
    (coherentLiftLeft (F := F) E).map p ≫ coherentLiftApp η E y ⟶
      coherentLiftApp η E x ≫ (coherentLiftRight η E).map p :=
  ⟨(η.naturality p.base).hom, eqToHom (coherentLiftBoundary η E p)⟩

private theorem totalCellComp_base {x y : Total E} {p q r : x ⟶ y}
    (α : p ⟶ q) (β : q ⟶ r) : (α ≫ β).base = α.base ≫ β.base := rfl

private theorem totalCellCast_base {x y : Total E} {p q : x ⟶ y} (h : p = q) :
    (eqToHom h).base = eqToHom (congrArg (fun r : x ⟶ y => r.base) h) := by
  cases h
  rfl
private theorem totalWhiskerLeft_base {x y z : Total E} (p : x ⟶ y)
    {q r : y ⟶ z} (α : q ⟶ r) : (p ◁ α).base = p.base ◁ α.base := rfl
private theorem totalWhiskerRight_base {x y z : Total E} {p q : x ⟶ y}
    (α : p ⟶ q) (r : y ⟶ z) : (α ▷ r).base = α.base ▷ r.base := rfl

theorem coherentLiftCell_base {x y : Total (reindex F E)} (p : x ⟶ y) :
    (coherentLiftCell η E p).base = (η.naturality p.base).hom := rfl

theorem coherentLiftCell_equalityFiber {x y : Total (reindex F E)} (p : x ⟶ y) :
    EqualityFiber E (coherentLiftCell η E p) := ⟨coherentLiftBoundary η E p, rfl⟩

theorem coherentLiftCell_id (x : Total (reindex F E)) :
    coherentLiftCell η E (𝟙 x) ≫ coherentLiftApp η E x ◁
      ((coherentLiftRight η E).mapId x).hom =
    ((coherentLiftLeft (F := F) E).mapId x).hom ▷ coherentLiftApp η E x ≫
      (λ_ (coherentLiftApp η E x)).hom ≫ (ρ_ (coherentLiftApp η E x)).inv := by
  simp only [(coherentLiftRight η E).mapId_eq_eqToIso,
    (coherentLiftLeft (F := F) E).mapId_eq_eqToIso,
    Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv]
  apply equalityFiber_ext E
  · simp only [totalCellComp_base,
      totalWhiskerLeft_base, totalWhiskerRight_base, totalCellCast_base,
      coherentLiftCell_base]
    have h := η.naturality_id x.base
    simp only [F.mapId_eq_eqToIso, G.mapId_eq_eqToIso, Strict.leftUnitor_eqToIso,
      Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv, whiskerLeft_eqToHom,
      eqToHom_whiskerRight] at h
    exact h
  · exact equalityFiber_comp E (coherentLiftCell_equalityFiber η E (𝟙 x))
      (equalityFiber_whiskerLeft E _ (equalityFiber_cast E _))
  · exact equalityFiber_comp E (equalityFiber_whiskerRight E (equalityFiber_cast E _) _)
      (equalityFiber_comp E (equalityFiber_cast E _) (equalityFiber_cast E _))
theorem coherentLiftCell_comp {x y z : Total (reindex F E)} (p : x ⟶ y) (q : y ⟶ z) :
    coherentLiftCell η E (p ≫ q) ≫ coherentLiftApp η E x ◁
      ((coherentLiftRight η E).mapComp p q).hom =
    ((coherentLiftLeft (F := F) E).mapComp p q).hom ▷ coherentLiftApp η E z ≫
      (α_ _ _ _).hom ≫ (coherentLiftLeft (F := F) E).map p ◁ coherentLiftCell η E q ≫
      (α_ _ _ _).inv ≫ coherentLiftCell η E p ▷ (coherentLiftRight η E).map q ≫
      (α_ _ _ _).hom := by
  simp only [(coherentLiftRight η E).mapComp_eq_eqToIso,
    (coherentLiftLeft (F := F) E).mapComp_eq_eqToIso,
    Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv]
  apply equalityFiber_ext E
  · simp only [totalCellComp_base, totalWhiskerLeft_base, totalWhiskerRight_base,
      totalCellCast_base, coherentLiftCell_base]
    have h := η.naturality_comp p.base q.base
    simp only [F.mapComp_eq_eqToIso, G.mapComp_eq_eqToIso,
      Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv] at h
    exact h
  · exact equalityFiber_comp E (coherentLiftCell_equalityFiber η E (p ≫ q))
      (equalityFiber_whiskerLeft E _ (equalityFiber_cast E _))
  · exact equalityFiber_comp E
      (equalityFiber_whiskerRight E (equalityFiber_cast E _) _)
      (equalityFiber_comp E (equalityFiber_cast E _)
        (equalityFiber_comp E (equalityFiber_whiskerLeft E _ (coherentLiftCell_equalityFiber η E q))
          (equalityFiber_comp E (equalityFiber_cast E _)
            (equalityFiber_comp E (equalityFiber_whiskerRight E (coherentLiftCell_equalityFiber η E p) _)
              (equalityFiber_cast E _)))))

private theorem coherentLift_left_fiber_heq {x y : Total (reindex F E)}
    {p q : x ⟶ y} (α : p ⟶ q) :
    HEq (((coherentLiftLeft (F := F) E).map₂ α ▷ coherentLiftApp η E y ≫
      coherentLiftCell η E q).fiber) ((E.map (η.app y.base)).map₂ α.fiber) := by
  rw [fiber_comp]
  change HEq ((((coherentLiftLeft (F := F) E).map₂ α ▷ coherentLiftApp η E y).fiber) ≫
    _ ◁ eqToHom (coherentLiftBoundary η E q) ≫ eqToHom _) _
  simp only [Bicategory.whiskerLeft_eqToHom, eqToHom_trans,
    ← Category.assoc, comp_eqToHom_heq_iff]
  refine HEq.trans (comp_eqToHom_heq _ _) ?_
  change HEq (eqToHom _ ≫ (compBoundary E _ _ _ ◁
    (E.map (η.app y.base)).map₂ α.fiber) ▷ (𝟙 _) ≫ eqToHom _) _
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
    Bicategory.whiskerRight_id, Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv]
  refine HEq.trans (eqToHom_comp_heq _ _) ?_
  refine HEq.trans (comp_eqToHom_heq _ _) ?_
  refine HEq.trans (eqToHom_comp_heq _ _) ?_
  refine HEq.trans (comp_eqToHom_heq _ _) ?_
  exact eqToHom_left_heq (B := E.obj (G.obj y.base)) _ _
private theorem coherentLift_right_fiber_heq {x y : Total (reindex F E)}
    {p q : x ⟶ y} (α : p ⟶ q) :
    HEq ((coherentLiftCell η E p ≫ coherentLiftApp η E x ◁
      (coherentLiftRight η E).map₂ α).fiber) ((E.map (η.app y.base)).map₂ α.fiber) := by
  rw [fiber_comp]
  change HEq (eqToHom (coherentLiftBoundary η E p) ≫ (E.map₂ (η.naturality p.base).hom).app x.fiber ◁
    (_) ≫ eqToHom _) _
  refine HEq.trans (eqToHom_comp_heq _ _) ?_
  refine HEq.trans (comp_eqToHom_heq _ _) ?_
  change HEq ((E.map₂ (η.naturality p.base).hom).app x.fiber ◁
    (compBoundary E (η.app x.base) (G.map p.base) x.fiber ◁
      ((E.map (G.map p.base)).map (𝟙 _) ◁
        (((strongPostcomp η E).naturality p.base).inv.app x.fiber ◁
          (E.map (η.app y.base)).map₂ α.fiber ≫ eqToHom _)) ≫ eqToHom _)) _
  simp only [Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans,
    eqToHom_comp_heq_iff, comp_eqToHom_heq_iff]
  refine HEq.trans (comp_eqToHom_heq _ _) ?_
  rw [(E.map (G.map p.base)).map_id]
  simp only [Bicategory.id_whiskerLeft, Strict.leftUnitor_eqToIso, eqToIso.hom, eqToIso.inv,
    Bicategory.whiskerLeft_comp, Bicategory.whiskerLeft_eqToHom, Category.assoc, eqToHom_trans]
  refine HEq.trans (eqToHom_comp_heq _ _) ?_
  refine HEq.trans (comp_eqToHom_heq _ _) ?_
  simp only [nested_whiskerLeft, Bicategory.whiskerLeft_comp,
    Bicategory.whiskerLeft_eqToHom, Category.assoc, eqToHom_trans]
  refine HEq.trans (eqToHom_comp_heq _ _) ?_
  refine HEq.trans (eqToHom_comp_heq _ _) ?_
  refine HEq.trans (comp_eqToHom_heq _ _) ?_
  rw [coherentLiftPrefix]
  exact eqToHom_left_heq (B := E.obj (G.obj y.base)) _ _

theorem coherentLiftCell_naturality {x y : Total (reindex F E)}
    {p q : x ⟶ y} (α : p ⟶ q) :
    (coherentLiftLeft (F := F) E).map₂ α ▷ coherentLiftApp η E y ≫
      coherentLiftCell η E q = coherentLiftCell η E p ≫ coherentLiftApp η E x ◁
        (coherentLiftRight η E).map₂ α := by
  refine Pseudofunctor.CoGrothendieck.Hom.ext _ _ (η.naturality_naturality α.base) ?_
  apply eq_of_heq
  exact (coherentLift_left_fiber_heq η E α).trans
    ((coherentLift_right_fiber_heq η E α).symm.trans (comp_eqToHom_heq _ _).symm)

noncomputable def coherentLift [IsLocallyGroupoid Δ]
    [∀ δ, IsLocallyGroupoid (E.obj δ)] :
    Pseudofunctor.StrongTrans (coherentLiftLeft (F := F) E).toPseudofunctor
      (coherentLiftRight η E).toPseudofunctor where
  app := coherentLiftApp η E
  naturality p := asIso (coherentLiftCell η E p)
  naturality_naturality α := coherentLiftCell_naturality η E α
  naturality_id x := coherentLiftCell_id η E x
  naturality_comp p q := coherentLiftCell_comp η E p q

end SquareKit.Internal.PathTransport.TwoFamily
