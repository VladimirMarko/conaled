import SquareKit.Internal.PathTransport.StrictTwoCategory
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.Bicategory.LocallyGroupoid
import Mathlib.CategoryTheory.Bicategory.Adjunction.Mate

/-! Transport of identity fibers retains all fiber 2-cells as arrows of the
hom-groupoid. Endpoint comparison uses strict inverses of 1-arrows. -/
namespace SquareKit.Internal.PathTransport.TwoIdentityTransport
open CategoryTheory Bicategory
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v w u' v' w'
variable {A : Type u} [Bicategory.{w,v} A] [Bicategory.Strict A]
variable {B : Type u'} [Bicategory.{w',v'} B] [Bicategory.Strict B]

/-- Transport a path by the strict fiber functor and the two endpoint arrows. -/
noncomputable def homTransport (F : StrictPseudofunctor A B) {a a' : A} {b b' : B}
    (u : F.obj a ⟶ b) [IsIso u] (v : F.obj a' ⟶ b') : (a ⟶ a') ⥤ (b ⟶ b') :=
  F.mapFunctor a a' ⋙ postcomp _ v ⋙ precomp _ (inv u)

/-- The inverse mate of an endpoint cell. The input cell remains genuine
2-dimensional data; no equality of its boundary arrows is assumed. -/
noncomputable def inverseMate [Bicategory.IsLocallyGroupoid B]
    {a a' b : B} {u : a ⟶ b} {u' : a' ⟶ b} [IsIso u] [IsIso u']
    {h : a ⟶ a'} (ρ : u ⟶ h ≫ u') : inv u ≫ h ⟶ inv u' :=
  eqToHom (by simp [Category.assoc]) ≫
    (inv u ◁ inv ρ) ▷ inv u' ≫ eqToHom (by simp)

/-- A strict inverse supplies an adjunction with equality unit and counit. -/
noncomputable def inverseAdjunction {a b : B} (u : a ⟶ b) [IsIso u] :
    Adjunction u (inv u) where
  unit := eqToHom (IsIso.hom_inv_id u).symm
  counit := eqToHom (IsIso.inv_hom_id u)
  left_triangle := by
    simp [leftZigzag, bicategoricalComp, Strict.associator_eqToIso,
      Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso]
  right_triangle := by
    simp [rightZigzag, bicategoricalComp, Strict.associator_eqToIso,
      Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso]
/-- Endpoint inversion is the bicategorical mate correspondence. -/
theorem inverseMate_eq_mate [Bicategory.IsLocallyGroupoid B]
    {a a' b : B} {u : a ⟶ b} {u' : a' ⟶ b} [IsIso u] [IsIso u']
    {h : a ⟶ a'} (ρ : u ⟶ h ≫ u') :
    inverseMate ρ = mateEquiv (inverseAdjunction u) (inverseAdjunction u')
      (inv ρ ≫ eqToHom (Category.comp_id u).symm) ≫ eqToHom (Category.id_comp _) := by
  rw [mateEquiv_apply, Adjunction.homEquiv₁_apply, Adjunction.homEquiv₂_apply]
  simp only [inverseMate,
    inverseAdjunction, Strict.associator_eqToIso, Strict.leftUnitor_eqToIso,
    Strict.rightUnitor_eqToIso]
  simp only [eqToIso.hom, eqToIso.inv, whiskerLeft_comp, comp_whiskerRight,
    whiskerLeft_eqToHom, eqToHom_whiskerRight, Category.assoc, eqToHom_trans_assoc,
    eqToHom_trans]
  simp only [whisker_assoc, Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv,
    Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
/-- Inverse mates preserve vertical pasting of endpoint squares. -/
theorem inverseMate_comp [Bicategory.IsLocallyGroupoid B]
    {a a' a'' b : B} {u : a ⟶ b} {u' : a' ⟶ b} {u'' : a'' ⟶ b}
    [IsIso u] [IsIso u'] [IsIso u'']
    {h : a ⟶ a'} {k : a' ⟶ a''}
    (ρ : u ⟶ h ≫ u') (σ : u' ⟶ k ≫ u'') :
    inverseMate (ρ ≫ h ◁ σ ≫ eqToHom (Category.assoc _ _ _).symm) =
      eqToHom (Category.assoc _ _ _).symm ≫ inverseMate ρ ▷ k ≫ inverseMate σ := by
  have hp := mateEquiv_vcomp (inverseAdjunction u) (inverseAdjunction u')
    (inverseAdjunction u'') (inv ρ ≫ eqToHom (Category.comp_id u).symm)
    (inv σ ≫ eqToHom (Category.comp_id u').symm)
  simp only [leftAdjointSquare.vcomp, rightAdjointSquare.vcomp,
    Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv,
    whiskerLeft_comp, comp_whiskerRight, whiskerLeft_eqToHom,
    eqToHom_whiskerRight, Category.assoc, eqToHom_trans_assoc,
    eqToHom_trans] at hp
  simp only [id_whiskerLeft, whiskerRight_id, Strict.leftUnitor_eqToIso,
    Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans] at hp
  simp only [inverseMate_eq_mate, IsIso.inv_comp, inv_eqToHom, inv_whiskerLeft, Category.assoc]
  simp only [comp_whiskerRight, eqToHom_whiskerRight, Category.assoc]
  have hp' := congrArg (fun z => z ≫ eqToHom (by simp : (𝟙 b ≫ 𝟙 b) ≫ inv u'' = inv u'')) hp
  simp only [mateEquiv_apply, Adjunction.homEquiv₁_apply, Adjunction.homEquiv₂_apply,
    inverseAdjunction, Strict.associator_eqToIso, Strict.leftUnitor_eqToIso,
    Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv, whiskerLeft_comp,
    comp_whiskerRight, whiskerLeft_eqToHom, eqToHom_whiskerRight, Category.assoc,
    eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl, Category.id_comp] at hp' ⊢
  exact hp'

/-- An ordinary functor between hom-groupoids acts strictly on their locally
discrete embeddings. It preserves the hom-groupoid arrows, which are the
original fiber's genuine 2-cells. -/
def locallyDiscreteFunctor {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) :
    StrictPseudofunctor (LocallyDiscrete C) (LocallyDiscrete D) where
  __ := F.toPseudofunctor
  map_id x := by apply Discrete.ext; exact F.map_id x.as
  map_comp f g := by apply Discrete.ext; exact F.map_comp f.as g.as
  mapId_eq_eqToIso x := by apply Iso.ext; apply Subsingleton.elim
  mapComp_eq_eqToIso f g := by apply Iso.ext; apply Subsingleton.elim

/-- Strict higher naturality induces a natural transformation on the full
hom-categories, using its 2-cell equation as ordinary naturality. -/
def homNaturality {F G : StrictPseudofunctor A B} (η : StrictTwoTransformation.Trans F G)
    (a a' : A) : F.mapFunctor a a' ⋙ postcomp _ (η.app a') ⟶
      G.mapFunctor a a' ⋙ precomp _ (η.app a) where
  app p := eqToHom (η.naturality p)
  naturality _ _ α := η.naturality₂ α

/-- The endpoint-cell pasting gives an actual natural transformation between
identity transports, including naturality at every genuine fiber 2-cell. -/
noncomputable def homComparison [Bicategory.IsLocallyGroupoid B]
    {F G : StrictPseudofunctor A B} (η : StrictTwoTransformation.Trans F G)
    {a a' : A} {b b' : B} {u : F.obj a ⟶ b} {u' : G.obj a ⟶ b}
    [IsIso u] [IsIso u'] {v : F.obj a' ⟶ b'} {v' : G.obj a' ⟶ b'}
    (ρ : u ⟶ η.app a ≫ u') (σ : v ⟶ η.app a' ≫ v') :
    homTransport F u v ⟶ homTransport G u' v' :=
  CategoryTheory.Functor.whiskerRight
    (CategoryTheory.Functor.whiskerLeft (F.mapFunctor a a') ((postcomposing _ _ _).map σ) ≫
      CategoryTheory.Functor.whiskerLeft (F.mapFunctor a a')
        (associatorNatIsoLeft _ (η.app a') v').inv ≫
      CategoryTheory.Functor.whiskerRight (homNaturality η a a') (postcomp _ v') ≫
      CategoryTheory.Functor.whiskerLeft (G.mapFunctor a a')
        (associatorNatIsoMiddle (η.app a) v').hom)
    (precomp _ (inv u)) ≫
  CategoryTheory.Functor.whiskerLeft (G.mapFunctor a a' ⋙ postcomp _ v')
    (associatorNatIsoRight (inv u) (η.app a) b').inv ≫
  CategoryTheory.Functor.whiskerLeft (G.mapFunctor a a' ⋙ postcomp _ v')
    ((precomposing _ _ _).map (inverseMate ρ))

/-- A natural transformation of hom-groupoids is a strict higher
transformation between their locally discrete embeddings. -/
def locallyDiscreteTrans {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (η : F ⟶ G) :
    StrictTwoTransformation.Trans (locallyDiscreteFunctor F) (locallyDiscreteFunctor G) where
  app a := Discrete.mk (η.app a.as)
  naturality f := Discrete.ext (η.naturality f.as)
  naturality₂ _ := Subsingleton.elim _ _

theorem homComparison_id [Bicategory.IsLocallyGroupoid B]
    (F : StrictPseudofunctor A B) {a a' : A} {b b' : B}
    (u : F.obj a ⟶ b) [IsIso u] (v : F.obj a' ⟶ b') :
    homComparison (StrictTwoTransformation.Trans.id F)
      (eqToHom (Category.id_comp u).symm) (eqToHom (Category.id_comp v).symm) =
        𝟙 (homTransport F u v) := by
  ext p
  simp [homComparison, homNaturality, inverseMate, StrictTwoTransformation.Trans.id,
    Strict.associator_eqToIso, Strict.leftUnitor_eqToIso, Strict.rightUnitor_eqToIso]

/-- Vertical pasting of endpoint comparisons has the composite action on
the complete hom-groupoid. -/
theorem homComparison_comp [Bicategory.IsLocallyGroupoid B]
    {F G H : StrictPseudofunctor A B}
    (η : StrictTwoTransformation.Trans F G) (θ : StrictTwoTransformation.Trans G H)
    {a a' : A} {b b' : B}
    {u : F.obj a ⟶ b} {u' : G.obj a ⟶ b} {u'' : H.obj a ⟶ b}
    [IsIso u] [IsIso u'] [IsIso u'']
    {v : F.obj a' ⟶ b'} {v' : G.obj a' ⟶ b'} {v'' : H.obj a' ⟶ b'}
    (ρ : u ⟶ η.app a ≫ u') (ρ' : u' ⟶ θ.app a ≫ u'')
    (σ : v ⟶ η.app a' ≫ v') (σ' : v' ⟶ θ.app a' ≫ v'') :
    homComparison (η.comp θ)
      (ρ ≫ η.app a ◁ ρ' ≫ eqToHom (Category.assoc _ _ _).symm)
      (σ ≫ η.app a' ◁ σ' ≫ eqToHom (Category.assoc _ _ _).symm) =
      homComparison η ρ σ ≫ homComparison θ ρ' σ' := by
  ext p
  simp [homComparison, homNaturality, inverseMate_comp, StrictTwoTransformation.Trans.comp,
    Strict.associator_eqToIso]


  have hx := whisker_exchange (inverseMate ρ) (G.map p ◁ σ')
  simp only [comp_whiskerLeft, whiskerRight_comp, Strict.associator_eqToIso,
    eqToIso.hom, eqToIso.inv, Category.assoc, eqToHom_trans_assoc, eqToHom_trans] at hx
  apply congrArg (fun z => (inv u ◁ F.map p ◁ σ) ≫ z)
  have he := congrArg (fun z => inv u ◁ z)
    (whisker_exchange (eqToHom (η.naturality p)) σ')
  have ht := congrArg (fun z => z ▷ v'')
    (whisker_exchange (inverseMate ρ) (eqToHom (θ.naturality p)))
  simp only [comp_whiskerLeft, whiskerRight_comp, whiskerLeft_comp, comp_whiskerRight,
    whiskerLeft_eqToHom, eqToHom_whiskerRight, Strict.associator_eqToIso,
    eqToIso.hom, eqToIso.inv, Category.assoc, eqToHom_trans_assoc, eqToHom_trans] at he ht
  have he' := heq_of_eq he
  have ht' := heq_of_eq ht
  simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
    heq_eqToHom_comp_iff, heq_comp_eqToHom_iff] at he' ht'
  have he'' : inv u ◁ F.map p ◁ η.app a' ◁ σ' =
      eqToHom (by simpa only [Category.assoc] using congrArg (fun z => inv u ≫ (z ≫ v')) (η.naturality p)) ≫
      inv u ◁ η.app a ◁ G.map p ◁ σ' ≫
      eqToHom (by simpa only [Category.assoc] using congrArg (fun z => inv u ≫ (z ≫ (θ.app a' ≫ v''))) (η.naturality p).symm) :=
    (conj_eqToHom_iff_heq' _ _ _ _).2 he'
  have ht'' : inverseMate ρ ▷ θ.app a ▷ H.map p ▷ v'' =
      eqToHom (by simpa only [Category.assoc] using congrArg (fun z => (inv u ≫ η.app a) ≫ (z ≫ v'')) (θ.naturality p).symm) ≫
      inverseMate ρ ▷ G.map p ▷ θ.app a' ▷ v'' ≫
      eqToHom (by simpa only [Category.assoc] using congrArg (fun z => inv u' ≫ (z ≫ v'')) (θ.naturality p)) :=
    (conj_eqToHom_iff_heq' _ _ _ _).2 ht'
  rw [he'', ht'']
  simp only [Category.assoc, eqToHom_trans_assoc]
  have hx' := congrArg (fun z =>
    eqToHom (by simpa only [Category.assoc] using congrArg (fun z => inv u ≫ (z ≫ v')) (η.naturality p)) ≫ z ≫
      eqToHom (by simpa only [Category.assoc] using congrArg (fun z => inv u' ≫ (z ≫ v'')) (θ.naturality p)) ≫
      inverseMate ρ' ▷ H.map p ▷ v'' ≫ eqToHom (Category.assoc (inv u'') (H.map p) v'')) hx
  simpa only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans] using hx'


/-- The locally discrete embedding preserves every ordinary category arrow
as a 1-arrow; only its next dimension is discrete. -/
def locallyDiscreteEmbedding : StrictPseudofunctor Cat StrictTwoCategory :=
  StrictPseudofunctor.mk'' {
    obj := fun C => ⟨LocallyDiscrete C⟩
    map := fun F => locallyDiscreteFunctor F.toFunctor
    map₂ := fun η => locallyDiscreteTrans η.toNatTrans
    map₂_id := fun F => by apply StrictTwoTransformation.Trans.ext; intro a; rfl
    map₂_comp := fun η θ => by apply StrictTwoTransformation.Trans.ext; intro a; rfl
    map_id := fun C => by
      apply StrictTwoTransformation.functor_ext
      dsimp only [locallyDiscreteFunctor, Functor.toPseudofunctor,
        pseudofunctorOfIsLocallyDiscrete, StrictPseudofunctor.id,
        StrictlyUnitaryPseudofunctor.id, Pseudofunctor.id, PrelaxFunctor.id]
      congr 2
      funext a b f g η
      exact Subsingleton.elim _ _
    map_comp := fun F G => StrictTwoTransformation.functor_ext rfl
    map₂_whisker_left := fun F G H η => by
      apply StrictTwoTransformation.Trans.ext; intro a
      repeat rw [StrictTwoTransformation.Trans.comp_app]
      repeat rw [StrictTwoTransformation.Trans.eqToHom_app]
      change (show (LocallyDiscrete.mk (G.toFunctor.obj (F.toFunctor.obj a.as))) ⟶
        (LocallyDiscrete.mk (H.toFunctor.obj (F.toFunctor.obj a.as))) from
        Discrete.mk (η.toNatTrans.app (F.toFunctor.obj a.as))) =
        𝟙 _ ≫ (show _ ⟶ _ from Discrete.mk (η.toNatTrans.app (F.toFunctor.obj a.as))) ≫ 𝟙 _
      simp
    map₂_whisker_right := fun {a b c} {G H} η F => by
      apply StrictTwoTransformation.Trans.ext; intro a
      repeat rw [StrictTwoTransformation.Trans.comp_app]
      repeat rw [StrictTwoTransformation.Trans.eqToHom_app]
      change (show (LocallyDiscrete.mk (F.toFunctor.obj (G.toFunctor.obj a.as))) ⟶
        (LocallyDiscrete.mk (F.toFunctor.obj (H.toFunctor.obj a.as))) from
        Discrete.mk (F.toFunctor.map (η.toNatTrans.app a.as))) =
        𝟙 _ ≫ (show _ ⟶ _ from Discrete.mk (F.toFunctor.map (η.toNatTrans.app a.as))) ≫ 𝟙 _
      simp
  }

section TransportComposition
universe u'' v'' w''
variable {C : Type u''} [Bicategory.{w'',v''} C] [Bicategory.Strict C]

/-- Strict higher functors preserve strict invertibility of 1-arrows. -/
instance strictMapIsIso (G : StrictPseudofunctor B C) {a b : B}
    (u : a ⟶ b) [IsIso u] : IsIso (G.map u) := by
  change IsIso (G.toFunctor.map u)
  infer_instance

/-- Transport along successive fiber functors and endpoint arrows composes exactly. -/
theorem homTransport_comp (F : StrictPseudofunctor A B) (G : StrictPseudofunctor B C)
    {a a' : A} {b b' : B} {c c' : C}
    (u : F.obj a ⟶ b) [IsIso u] (v : F.obj a' ⟶ b')
    (u' : G.obj b ⟶ c) [IsIso u'] (v' : G.obj b' ⟶ c')
    :
    homTransport (F.comp G) (G.map u ≫ u') (G.map v ≫ v') =
      homTransport F u v ⋙ homTransport G u' v' := by
  have hi : G.map (inv u) = inv (G.map u) := G.toFunctor.map_inv u
  refine Functor.ext (fun p => ?_) (fun p q α => ?_)
  · change inv (G.map u ≫ u') ≫ (G.map (F.map p) ≫ (G.map v ≫ v')) =
      inv u' ≫ (G.map (inv u ≫ (F.map p ≫ v)) ≫ v')
    simp only [G.map_comp, Category.assoc, IsIso.inv_comp, hi]
  · change inv (G.map u ≫ u') ◁ G.map₂ (F.map₂ α) ▷ (G.map v ≫ v') =
      eqToHom _ ≫ inv u' ◁ G.map₂ (inv u ◁ F.map₂ α ▷ v) ▷ v' ≫ eqToHom _
    simp only [Pseudofunctor.map₂_whisker_left, Pseudofunctor.map₂_whisker_right,
      G.mapComp_eq_eqToIso, eqToIso.hom, eqToIso.inv,
      whiskerLeft_comp, comp_whiskerRight, whiskerLeft_eqToHom, eqToHom_whiskerRight,
      Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    simp only [whiskerRight_comp, whisker_assoc,
      Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv, whiskerLeft_comp,
      whiskerLeft_eqToHom, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
    apply eq_of_heq
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    have hc {x y z : C} {f g : x ⟶ y} (e : f = g) {k l : y ⟶ z} (β : k ⟶ l) :
        HEq (f ◁ β) (g ◁ β) := by cases e; rfl
    have he : inv (G.map u ≫ u') = inv u' ≫ G.map (inv u) := by
      simp only [IsIso.inv_comp, hi]
    have h₁ := hc he (G.map₂ (F.map₂ α) ▷ G.map v ▷ v')
    have h₂ := heq_of_eq (comp_whiskerLeft (inv u') (G.map (inv u))
      (G.map₂ (F.map₂ α) ▷ G.map v ▷ v'))
    simp only [Strict.associator_eqToIso, eqToIso.hom, eqToIso.inv,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff] at h₂
    exact h₁.trans h₂
/-- Identity functor and identity endpoints induce identity on the full hom-category. -/
theorem homTransport_id (a a' : A) :
    @homTransport A _ A _ _ (StrictPseudofunctor.id A) a a' a a'
      (𝟙 a) (inferInstanceAs (IsIso (𝟙 a : a ⟶ a))) (𝟙 a') = 𝟭 (a ⟶ a') := by
  refine Functor.ext (fun p => ?_) (fun p q α => ?_)
  · change inv (𝟙 a) ≫ (p ≫ 𝟙 a') = p
    simp
  · change inv (𝟙 a) ◁ α ▷ 𝟙 a' = eqToHom _ ≫ α ≫ eqToHom _
    simp only [whiskerRight_id, Strict.rightUnitor_eqToIso, eqToIso.hom, eqToIso.inv,
      whiskerLeft_comp, whiskerLeft_eqToHom]
    apply eq_of_heq
    simp only [eqToHom_comp_heq_iff, comp_eqToHom_heq_iff,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff]
    have hc {x y z : A} {f g : x ⟶ y} (e : f = g) {k l : y ⟶ z} (β : k ⟶ l) :
        HEq (f ◁ β) (g ◁ β) := by cases e; rfl
    have h₁ := hc (IsIso.inv_id (X := a)) α
    have h₂ := heq_of_eq (id_whiskerLeft α)
    simp only [Strict.leftUnitor_eqToIso, eqToIso.hom, eqToIso.inv,
      heq_eqToHom_comp_iff, heq_comp_eqToHom_iff] at h₂
    exact h₁.trans h₂

end TransportComposition

end SquareKit.Internal.PathTransport.TwoIdentityTransport
