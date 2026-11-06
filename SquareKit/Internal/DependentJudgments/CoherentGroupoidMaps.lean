import SquareKit.Internal.PathTransport.SectionNormalization
import SquareKit.Internal.PathTransport.GroupoidElimination

/-! Display comparisons over equivalent ordinary groupoid contexts. Projection
compatibility is a natural isomorphism, not an equality of chosen lift data. -/
noncomputable section
namespace SquareKit.Internal.DependentJudgments.CoherentGroupoidMaps
open CategoryTheory CategoryTheory.Functor
open SquareKit.Internal.PathTransport.GroupoidModel
open SquareKit.Internal.PathTransport.GroupoidModel.ContextualElimination
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {Γ Δ Θ : Grpd.{u,u}}
variable {A : Γ ⥤ Grpd.{u,u}} {B : Δ ⥤ Grpd.{u,u}} {C : Θ ⥤ Grpd.{u,u}}

/-- A comparison carries an actual functor of displayed groupoids and its
projection coherence. It need not preserve the chosen horizontal lifts strictly. -/
structure DisplayMap (A : Γ ⥤ Grpd.{u,u}) (B : Δ ⥤ Grpd.{u,u}) where
  context : Γ ≌ Δ
  total : Extend A ⥤ Extend B
  over : total ⋙ weaken B ≅ weaken A ⋙ context.functor

namespace DisplayMap

def identity (A : Γ ⥤ Grpd.{u,u}) : DisplayMap A A where
  context := CategoryTheory.Equivalence.refl
  total := 𝟭 (Extend A)
  over := Iso.refl _

def compose (f : DisplayMap A B) (g : DisplayMap B C) : DisplayMap A C where
  context := f.context.trans g.context
  total := f.total ⋙ g.total
  over := isoWhiskerLeft f.total g.over ≪≫ isoWhiskerRight f.over g.context.functor

/-- The unnormalized image retains the chosen projection comparison. -/
def image (f : DisplayMap A B) (s : Section A) : Δ ⥤ Extend B :=
  f.context.inverse ⋙ s.lift ⋙ f.total

def imageOver (f : DisplayMap A B) (s : Section A) :
    f.image s ⋙ weaken B ≅ 𝟭 Δ :=
  isoWhiskerLeft (f.context.inverse ⋙ s.lift) f.over ≪≫ f.context.counitIso

/-- Normalize only the projection; the resulting section retains its fiber arrows. -/
def term (f : DisplayMap A B) (s : Section A) : Section B :=
  Section.ofOver (normalize (f.image s) (f.imageOver s)) (normalize_over _ _)

def termComparison (f : DisplayMap A B) (s : Section A) :
    (f.term s).lift ≅ f.image s :=
  eqToIso (Section.ofOver_lift _ _) ≪≫ normalizeComparison _ _

theorem term_identity (s : Section A) : (identity A).term s = s := by
  apply Section.lift_injective
  rw [term, Section.ofOver_lift]
  have h : (identity A).imageOver s = Iso.refl _ := by
    ext γ
    simp [imageOver, identity, image, weaken, Section.lift]
  rw [h]
  exact normalize_refl _

/-- The comparison for sequential term transport is built from the two
normalization comparisons and the composed context equivalence. -/
def termCompose (f : DisplayMap A B) (g : DisplayMap B C) (s : Section A) :
    (g.term (f.term s)).lift ≅ ((f.compose g).term s).lift :=
  g.termComparison (f.term s) ≪≫
    isoWhiskerLeft g.context.inverse (isoWhiskerRight (f.termComparison s) g.total) ≪≫
    ((f.compose g).termComparison s).symm

/-- Substitution of a transported section retains the same comparison arrows. -/
def termSubstitution (f : DisplayMap A B) (s : Section A) (σ : Θ ⥤ Δ) :
    pair B σ ((f.term s).reindex σ) ≅ σ ⋙ f.image s :=
  isoWhiskerLeft σ (f.termComparison s)

/-- Normalize after substitution or reindex the normalized section: the total
functors agree strictly. Thus substitution transports the chosen comparison,
not merely an independently chosen isomorphic section. -/
theorem normalize_substitution (f : DisplayMap A B) (s : Section A) (σ : Θ ⥤ Δ) :
    normalize (σ ⋙ f.image s) (isoWhiskerLeft σ (f.imageOver s)) =
      pair B σ ((f.term s).reindex σ) := by
  rw [normalize_precomp]
  change σ ⋙ normalize (f.image s) (f.imageOver s) = σ ⋙ (f.term s).lift
  rw [term, Section.ofOver_lift]

/-- Repeated substitution does not introduce a new comparison choice. -/
theorem termSubstitution_twice {Ξ : Grpd.{u,u}} (f : DisplayMap A B)
    (s : Section A) (σ : Θ ⥤ Δ) (τ : Ξ ⥤ Θ) :
    isoWhiskerLeft τ (f.termSubstitution s σ) =
      f.termSubstitution s (τ ⋙ σ) := rfl

/-- The sequential comparison commutes with the normalization comparisons. -/
theorem termCompose_triangle (f : DisplayMap A B) (g : DisplayMap B C)
    (s : Section A) :
    f.termCompose g s ≪≫ (f.compose g).termComparison s =
      g.termComparison (f.term s) ≪≫
        isoWhiskerLeft g.context.inverse (isoWhiskerRight (f.termComparison s) g.total) := by
  simp [termCompose]

/-- Reindexing the composition triangle preserves its selected comparison. -/
theorem termCompose_substitution (f : DisplayMap A B) (g : DisplayMap B C)
    (s : Section A) {Ξ : Grpd.{u,u}} (σ : Ξ ⥤ Θ) :
    isoWhiskerLeft σ (f.termCompose g s) ≪≫ (f.compose g).termSubstitution s σ =
      isoWhiskerLeft σ (g.termComparison (f.term s) ≪≫
        isoWhiskerLeft g.context.inverse (isoWhiskerRight (f.termComparison s) g.total)) := by
  change isoWhiskerLeft σ (f.termCompose g s) ≪≫
    isoWhiskerLeft σ ((f.compose g).termComparison s) = _
  rw [← isoWhiskerLeft_trans, termCompose_triangle]

/-- Change the context presentation along an equivalence. The displayed family
is pulled back, while the total functor retains its original fiber data. -/
def changeBase (e : Γ ≌ Δ) (B : Δ ⥤ Grpd.{u,u}) : DisplayMap (e.functor ⋙ B) B where
  context := e
  total := Grothendieck.pre (B ⋙ Grpd.forgetToCat) e.functor
  over := Iso.refl _

/-- Transport a section comparison, retaining its natural-isomorphism data. -/
def mapComparison (f : DisplayMap A B) {s t : Section A} (α : s.lift ≅ t.lift) :
    (f.term s).lift ≅ (f.term t).lift :=
  f.termComparison s ≪≫
    isoWhiskerLeft f.context.inverse (isoWhiskerRight α f.total) ≪≫
      (f.termComparison t).symm

theorem mapComparison_identity (f : DisplayMap A B) (s : Section A) :
    f.mapComparison (Iso.refl s.lift) = Iso.refl (f.term s).lift := by
  ext x
  simp only [mapComparison, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    isoWhiskerLeft_hom, whiskerLeft_app, isoWhiskerRight_hom, whiskerRight_app,
    Iso.refl_hom, NatTrans.id_app]
  rw [f.total.map_id]
  change (f.termComparison s).hom.app x ≫ 𝟙 ((f.image s).obj x) ≫
    (f.termComparison s).inv.app x = 𝟙 _
  simp

theorem mapComparison_comp (f : DisplayMap A B) {s t v : Section A}
    (α : s.lift ≅ t.lift) (β : t.lift ≅ v.lift) :
    f.mapComparison (α ≪≫ β) = f.mapComparison α ≪≫ f.mapComparison β := by
  ext x
  simp [mapComparison]

/-- Strict natural family maps are a specialization of display comparisons. -/
def ofNatural {A B : Γ ⥤ Grpd.{u,u}} (α : A ⟶ B) : DisplayMap A B where
  context := CategoryTheory.Equivalence.refl
  total := Grothendieck.map (whiskerRight α Grpd.forgetToCat)
  over := Iso.refl _

theorem ofNatural_term_lift {A B : Γ ⥤ Grpd.{u,u}} (α : A ⟶ B) (s : Section A) :
    ((ofNatural α).term s).lift = s.lift ⋙ (ofNatural α).total := by
  rw [term, Section.ofOver_lift]
  have h : (ofNatural α).imageOver s = Iso.refl _ := by
    ext γ
    simp [imageOver, ofNatural, image, weaken, Section.lift]
  rw [h]
  exact normalize_refl _

/-- Naturally isomorphic substitutions compare their pulled-back families by
actual fiber functors. The isomorphism may carry nontrivial path data. -/
def substitution {A : Γ ⥤ Grpd.{u,u}} (σ τ : Δ ⥤ Γ) (α : σ ≅ τ) :
    DisplayMap (σ ⋙ A) (τ ⋙ A) :=
  ofNatural (whiskerRight α.hom A)

def reindex {A B : Γ ⥤ Grpd.{u,u}} (α : A ⟶ B) (σ : Δ ⥤ Γ) :
    DisplayMap (σ ⋙ A) (σ ⋙ B) := ofNatural (whiskerLeft σ α)

theorem reindex_term {A B : Γ ⥤ Grpd.{u,u}} (α : A ⟶ B) (σ : Δ ⥤ Γ)
    (s : Section A) :
    (reindex α σ).term (s.reindex σ) = ((ofNatural α).term s).reindex σ := by
  apply Section.ext_of_pair σ
  change ((ofNatural (whiskerLeft σ α)).term (s.reindex σ)).lift ⋙
      Grothendieck.pre (B ⋙ Grpd.forgetToCat) σ =
    σ ⋙ ((ofNatural α).term s).lift
  rw [ofNatural_term_lift, ofNatural_term_lift]
  rfl

/-- Family comparison after two substitutions uses the same components. -/
theorem reindex_twice {A B : Γ ⥤ Grpd.{u,u}} (α : A ⟶ B)
    (σ : Δ ⥤ Γ) (τ : Θ ⥤ Δ) :
    reindex (whiskerLeft σ α) τ = reindex α (τ ⋙ σ) := rfl

/-- Extend a comparison of restrictions along an equivalence. The actual
counit transports the comparison to each object, retaining its arrow data. -/
def extendComparison {R X Y : Type u} [Category.{u} R] [Category.{u} X] [Category.{u} Y]
    (e : R ≌ X) {f g : X ⥤ Y} (α : e.functor ⋙ f ≅ e.functor ⋙ g) : f ≅ g :=
  isoWhiskerRight e.counitIso.symm f ≪≫ isoWhiskerLeft e.inverse α ≪≫
    isoWhiskerRight e.counitIso g

/-- A comparison of chosen J branches is enough to construct the comparison
of eliminations. The family/display map and the root square are primitive;
compatibility of the completed J terms is not a field. -/
def eliminationComparison {R S : Grpd.{u,u}}
    (e : NormalizedEquivalence (Cat.of R) (Cat.of Γ))
    (r : NormalizedEquivalence (Cat.of S) (Cat.of Δ))
    (f : DisplayMap A B) (h : S ⥤ R)
    (root : r.equiv.functor ⋙ f.context.inverse ≅ h ⋙ e.equiv.functor)
    (d : Section (e.equiv.functor ⋙ A)) (d' : Section (r.equiv.functor ⋙ B))
    (branch : h ⋙ pair A e.equiv.functor d ⋙ f.total ≅ pair B r.equiv.functor d') :
    (f.term (eliminateSection e A d)).lift ≅ (eliminateSection r B d').lift := by
  apply extendComparison r.equiv
  refine isoWhiskerLeft r.equiv.functor (f.termComparison _) ≪≫ ?_
  refine isoWhiskerRight root ((eliminateSection e A d).lift ⋙ f.total) ≪≫ ?_
  have he : e.equiv.functor ⋙ (eliminateSection e A d).lift = pair A e.equiv.functor d := by
    change pair A e.equiv.functor ((eliminateSection e A d).reindex e.equiv.functor) = _
    exact congrArg (pair A e.equiv.functor) (eliminateSection_beta e A d)
  have hr : r.equiv.functor ⋙ (eliminateSection r B d').lift = pair B r.equiv.functor d' := by
    change pair B r.equiv.functor ((eliminateSection r B d').reindex r.equiv.functor) = _
    exact congrArg (pair B r.equiv.functor) (eliminateSection_beta r B d')
  exact isoWhiskerLeft h (isoWhiskerRight (eqToIso he) f.total) ≪≫ branch ≪≫ (eqToIso hr).symm

/-- Naturality of chosen contextual elimination for a family transformation.
Branch compatibility is constructed from the same transformation. -/
def naturalEliminationComparison {R : Grpd.{u,u}} {A B : Γ ⥤ Grpd.{u,u}}
    (e : NormalizedEquivalence (Cat.of R) (Cat.of Γ)) (α : A ⟶ B)
    (d : Section (e.equiv.functor ⋙ A)) :
    ((ofNatural α).term (eliminateSection e A d)).lift ≅
      (eliminateSection e B ((reindex α e.equiv.functor).term d)).lift := by
  apply eliminationComparison e e (ofNatural α) (𝟭 R) (Iso.refl _) d
  apply eqToIso
  change pair A e.equiv.functor d ⋙ (ofNatural α).total =
    ((ofNatural (whiskerLeft e.equiv.functor α)).term d).lift ⋙
      Grothendieck.pre (B ⋙ Grpd.forgetToCat) e.equiv.functor
  rw [ofNatural_term_lift]
  rfl

/-- Reassociate the same raw image using its two normalization comparisons. -/
def termAssociator (f : DisplayMap A B) (g : DisplayMap B C) {Ξ : Grpd.{u,u}} {D : Ξ ⥤ Grpd.{u,u}} (h : DisplayMap C D)
    (s : Section A) :
    (((f.compose g).compose h).term s).lift ≅ ((f.compose (g.compose h)).term s).lift :=
  ((f.compose g).compose h).termComparison s ≪≫
    ((f.compose (g.compose h)).termComparison s).symm

/-- The two orders of composing three term comparisons agree. -/
theorem termCompose_assoc (f : DisplayMap A B) (g : DisplayMap B C) {Ξ : Grpd.{u,u}} {D : Ξ ⥤ Grpd.{u,u}} (h : DisplayMap C D)
    (s : Section A) :
    h.mapComparison (f.termCompose g s) ≪≫ (f.compose g).termCompose h s ≪≫
      termAssociator f g h s =
        g.termCompose h (f.term s) ≪≫ f.termCompose (g.compose h) s := by
  ext x
  simp [mapComparison, termCompose, termAssociator, compose]
/-- The chosen unitor retains the identity map's normalization comparison. -/
def termIdentity (s : Section A) : ((identity A).term s).lift ≅ s.lift :=
  (identity A).termComparison s

/-- Remove an identity source display map through the common raw image. -/
def termLeftUnit (f : DisplayMap A B) (s : Section A) :
    (((identity A).compose f).term s).lift ≅ (f.term s).lift :=
  ((identity A).compose f).termComparison s ≪≫ (f.termComparison s).symm

/-- Remove an identity target display map through the common raw image. -/
def termRightUnit (f : DisplayMap A B) (s : Section A) :
    ((f.compose (identity B)).term s).lift ≅ (f.term s).lift :=
  (f.compose (identity B)).termComparison s ≪≫ (f.termComparison s).symm

/-- Left unit compatibility for the chosen composition and unit comparisons. -/
theorem termCompose_leftUnit (f : DisplayMap A B) (s : Section A) :
    (identity A).termCompose f s ≪≫ termLeftUnit f s =
      f.mapComparison (termIdentity s) := by
  ext x
  simp [termCompose, termLeftUnit, mapComparison, termIdentity]

/-- Right unit compatibility for the chosen composition and unit comparisons. -/
theorem termCompose_rightUnit (f : DisplayMap A B) (s : Section A) :
    f.termCompose (identity B) s ≪≫ termRightUnit f s =
      termIdentity (f.term s) := by
  ext x
  simp [termCompose, termRightUnit, termIdentity, identity]
  exact Category.comp_id _


end DisplayMap
end SquareKit.Internal.DependentJudgments.CoherentGroupoidMaps
