import SquareKit.CoGrothendieckTransport
import SquareKit.Internal.CoherentSheafOver
import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
/-! Coherent local presentations and slice sheaves have equivalent total categories
over contexts. The faithful decoder transports sheaf pullback coherence to the
existing code comparisons; total recovery retains arbitrary fibre maps. -/
noncomputable section
set_option autoImplicit false
namespace SquareKit.CoherentSheafOver
open CategoryTheory Opposite
universe u v w a b
variable {B : Type u} [Category.{v} B] {D : Type a} [Category.{b} D]
variable (G : B ⥤ D) (J : GrothendieckTopology D) [G.Full] [G.Faithful]
variable [∀ Γ : D, (CostructuredArrow.toOver G Γ).IsCoverDense (J.over Γ)]
variable [∀ (Γ : D) (X : (Over Γ)ᵒᵖ),
  Limits.HasLimitsOfShape (StructuredArrow X (CostructuredArrow.toOver G Γ).op) (Type w)]
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[reassoc] theorem decodeReindex_comp_hom {Γ Δ Θ : D} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (A : LocalCode.{u,v,w} G J Γ) :
    (sheafOverClassification G J Θ).functor.map ((reindexComp G J σ τ).hom.app A) =
      (decodeReindex G J τ).hom.app ((reindex G J σ).obj A) ≫
        (J.overMapPullback (Type w) τ).map ((decodeReindex G J σ).hom.app A) ≫
        (J.overMapPullbackComp (Type w) τ σ).hom.app
          ((sheafOverClassification G J Γ).functor.obj A) ≫
        (decodeReindex G J (τ ≫ σ)).inv.app A := by
  apply (cancel_mono ((decodeReindex G J (τ ≫ σ)).hom.app A)).mp
  simpa using decodeReindex_comp G J σ τ A

@[reassoc] theorem decodeReindex_comp_inv {Γ Δ Θ : D} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (A : LocalCode.{u,v,w} G J Γ) :
    (sheafOverClassification G J Θ).functor.map ((reindexComp G J σ τ).inv.app A) =
      (decodeReindex G J (τ ≫ σ)).hom.app A ≫
        (J.overMapPullbackComp (Type w) τ σ).inv.app
          ((sheafOverClassification G J Γ).functor.obj A) ≫
        (J.overMapPullback (Type w) τ).map ((decodeReindex G J σ).inv.app A) ≫
        (decodeReindex G J τ).inv.app ((reindex G J σ).obj A) := by
  apply (cancel_epi ((sheafOverClassification G J Θ).functor.map
    ((reindexComp G J σ τ).hom.app A))).mp
  simp only [← Functor.map_comp, Iso.hom_inv_id_app]
  rw [decodeReindex_comp_hom]
  simp [← Functor.map_comp_assoc, Category.assoc]

@[reassoc] theorem decodeReindex_map {Γ Δ : D} (σ : Δ ⟶ Γ)
    {A B : LocalCode.{u,v,w} G J Γ} (f : A ⟶ B) :
    (sheafOverClassification G J Δ).functor.map ((reindex G J σ).map f) =
      (decodeReindex G J σ).hom.app A ≫
        (J.overMapPullback (Type w) σ).map ((sheafOverClassification G J Γ).functor.map f) ≫
        (decodeReindex G J σ).inv.app B := by
  apply (cancel_mono ((decodeReindex G J σ).hom.app B)).mp
  simpa using (decodeReindex G J σ).hom.naturality f

theorem decodeReindex_eqToHom {Γ Δ : D} {σ τ : Δ ⟶ Γ} (h : σ = τ)
    (A : LocalCode.{u,v,w} G J Γ) :
    (sheafOverClassification G J Δ).functor.map
      (eqToHom (congrArg (fun s => (reindex G J s).obj A) h)) =
      (decodeReindex G J σ).hom.app A ≫
        eqToHom (congrArg (fun s => (J.overMapPullback (Type w) s).obj
          ((sheafOverClassification G J Γ).functor.obj A)) h) ≫
        (decodeReindex G J τ).inv.app A := by
  subst τ
  simp

/-- The chosen reindexing, identity and composition comparisons form a
pseudofunctor. Coherence follows by applying the faithful sheaf decoder. -/
@[simps! obj map mapId mapComp]
def codePseudofunctor : Pseudofunctor (LocallyDiscrete Dᵒᵖ) Cat :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Cat.of (LocalCode.{u,v,w} G J X.unop))
    (fun f ↦ (reindex G J f.unop).toCatHom)
    (fun X ↦ Cat.Hom.isoMk (reindexId G J X.unop))
    (fun f g ↦ Cat.Hom.isoMk (reindexComp G J f.unop g.unop).symm)
    (fun f g h ↦ by
      ext1
      ext A
      apply (sheafOverClassification G J _).functor.map_injective
      dsimp
      simp only [Category.id_comp, Functor.map_comp]
      simp only [decodeReindex_comp_inv, decodeReindex_comp_hom, decodeReindex_map,
        Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
      simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app,
        Iso.inv_hom_id_app_assoc]
      simp only [Functor.map_comp, Category.assoc]
      simp only [Functor.comp_obj]
      rw [(J.overMapPullback (Type w) h.unop).map_id]
      simp only [Category.id_comp]
      have hn := (J.overMapPullbackComp (Type w) h.unop g.unop).hom.naturality
        ((decodeReindex G J f.unop).inv.app A)
      dsimp at hn
      rw [reassoc_of% hn]
      simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
      simp only [Functor.comp_obj]
      rw [(J.overMapPullback (Type w) (h.unop ≫ g.unop)).map_id]
      simp only [Category.id_comp]
      have hc := congrArg (fun n => n.app ((sheafOverClassification G J _).functor.obj A))
        (J.overMapPullback_assoc (Type w) h.unop g.unop f.unop)
      dsimp at hc
      simp only [Category.id_comp] at hc
      rw [reassoc_of% hc]
      simp only [GrothendieckTopology.overMapPullbackCongr_eq_eqToIso,
        eqToIso.hom, eqToHom_app, Cat.eqToHom_app]
      exact (decodeReindex_eqToHom G J (Category.assoc _ _ _).symm A).symm)
    (fun f ↦ by
      ext1
      ext A
      apply (sheafOverClassification G J _).functor.map_injective
      dsimp
      simp only [Functor.map_comp, Category.comp_id, decodeReindex_comp_inv,
        decodeReindex_map, decodeReindex_id, Functor.map_comp, Category.assoc,
        Iso.inv_hom_id_app_assoc]
      simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app_assoc]
      have hc := congrArg (fun n => n.app ((sheafOverClassification G J _).functor.obj A))
        (J.overMapPullback_comp_id (Type w) f.unop)
      dsimp at hc
      simp only [Category.comp_id] at hc
      rw [reassoc_of% hc]
      simp only [GrothendieckTopology.overMapPullbackCongr_eq_eqToIso,
        eqToIso.hom, eqToHom_app, Cat.eqToHom_app]
      exact (decodeReindex_eqToHom G J (Category.comp_id _) A).symm)
    (fun f ↦ by
      ext1
      ext A
      apply (sheafOverClassification G J _).functor.map_injective
      dsimp
      simp only [Functor.map_comp, Category.comp_id, decodeReindex_comp_inv,
        decodeReindex_id, Functor.map_comp, Category.assoc,
        Iso.inv_hom_id_app_assoc]
      have hn := (J.overMapPullbackId (Type w) _).hom.naturality
        ((decodeReindex G J f.unop).inv.app A)
      dsimp at hn
      rw [hn]
      have hc := congrArg (fun n => n.app ((sheafOverClassification G J _).functor.obj A))
        (J.overMapPullback_id_comp (Type w) f.unop)
      dsimp at hc
      simp only [Category.comp_id] at hc
      rw [reassoc_of% hc]
      simp only [GrothendieckTopology.overMapPullbackCongr_eq_eqToIso,
        eqToIso.hom, eqToHom_app, Cat.eqToHom_app]
      exact (decodeReindex_eqToHom G J (Category.id_comp _) A).symm)

/-- Total local presentations, with an arbitrary fibre map over each base map. -/
abbrev CodeTotal := Pseudofunctor.CoGrothendieck (codePseudofunctor.{u,v,w} G J)

/-- Sheaves on slice sites, including maps over changing contexts. -/
abbrev SheafTotal := Pseudofunctor.CoGrothendieck (J.pseudofunctorOver (Type w))

/-- The native local presentation category is the fibre of its total projection. -/
def codeFiberEquivalence (Γ : D) :
    LocalCode.{u,v,w} G J Γ ≌
      (Pseudofunctor.CoGrothendieck.forget (codePseudofunctor G J)).Fiber Γ :=
  (HasFibers.inducedFunctor
    (Pseudofunctor.CoGrothendieck.forget (codePseudofunctor G J)) Γ).asEquivalence

/-- The original slice sheaves are the fibre of the sheaf total projection. -/
def sheafFiberEquivalence (Γ : D) :
    Sheaf (J.over Γ) (Type w) ≌
      (Pseudofunctor.CoGrothendieck.forget (J.pseudofunctorOver (Type w))).Fiber Γ :=
  (HasFibers.inducedFunctor
    (Pseudofunctor.CoGrothendieck.forget (J.pseudofunctorOver (Type w))) Γ).asEquivalence

/-- Decoding commutes with the chosen substitution, including identity and
composition; these laws are consequences of the existing decoder equations. -/
def decodeComparison :
    CoGrothendieckTransport.Comparison
      (F := codePseudofunctor.{u,v,w} G J) (G := J.pseudofunctorOver (Type w))
      (fun Γ => (sheafOverClassification G J Γ).functor) where
  naturality σ := decodeReindex G J σ
  naturality_id Γ A := by
    change (sheafOverClassification G J Γ).functor.map ((reindexId G J Γ).inv.app A) ≫
      (decodeReindex G J (𝟙 Γ)).hom.app A =
      (J.overMapPullbackId (Type w) Γ).inv.app
        ((sheafOverClassification G J Γ).functor.obj A)
    apply (cancel_epi ((sheafOverClassification G J Γ).functor.map
      ((reindexId G J Γ).hom.app A))).mp
    simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
    rw [decodeReindex_id]
    simp
  naturality_comp σ τ A := decodeReindex_comp G J τ σ A

/-- Decode every native base-changing arrow through the original decoder. -/
def totalDecode : CodeTotal.{u,v,w} G J ⥤ SheafTotal.{w} J :=
  CoGrothendieckTransport.map (decodeComparison G J)

@[simp] theorem totalDecode_projection :
    totalDecode.{u,v,w} G J ⋙
        Pseudofunctor.CoGrothendieck.forget (J.pseudofunctorOver (Type w)) =
      Pseudofunctor.CoGrothendieck.forget (codePseudofunctor G J) := rfl

@[simp] theorem totalDecode_map_base {A B : CodeTotal.{u,v,w} G J} (f : A ⟶ B) :
    ((totalDecode G J).map f).base = f.base := rfl

/-- The decoded map retains its entire fibre map, with the existing substitution
comparison applied at the target. -/
@[simp] theorem totalDecode_map_fiber {A B : CodeTotal.{u,v,w} G J} (f : A ⟶ B) :
    ((totalDecode G J).map f).fiber =
      (sheafOverClassification G J A.base).functor.map f.fiber ≫
        (decodeReindex G J f.base).hom.app B.fiber := rfl

/-- Native maps are recovered over each fixed context map, without requiring
the fibre map to be invertible. -/
def decodeHomEquiv {Γ Δ : D} (σ : Δ ⟶ Γ)
    (A : LocalCode.{u,v,w} G J Δ) (B : LocalCode.{u,v,w} G J Γ) :
    (A ⟶ (reindex G J σ).obj B) ≃
      ((sheafOverClassification G J Δ).functor.obj A ⟶
        (J.overMapPullback (Type w) σ).obj ((sheafOverClassification G J Γ).functor.obj B)) :=
  CoGrothendieckTransport.fiberHomEquiv (decodeComparison G J)
    (fun Γ => (sheafOverClassification G J Γ).fullyFaithfulFunctor) σ A B

@[simp] theorem totalDecode_obj_base (A : CodeTotal.{u,v,w} G J) :
    ((totalDecode G J).obj A).base = A.base := rfl

@[simp] theorem totalDecode_obj_fiber (A : CodeTotal.{u,v,w} G J) :
    ((totalDecode G J).obj A).fiber =
      (sheafOverClassification G J A.base).functor.obj A.fiber := rfl

/-- The inverse substitution comparison and its coherence are derived from
`decodeComparison` and the original fibre equivalences. -/
def codeComparison :
    CoGrothendieckTransport.Comparison
      (F := J.pseudofunctorOver (Type w)) (G := codePseudofunctor.{u,v,w} G J)
      (fun Γ => (sheafOverClassification G J Γ).inverse) :=
  CoGrothendieckTransport.inverseComparison
    (F := codePseudofunctor G J) (G := J.pseudofunctorOver (Type w))
    (fun Γ => sheafOverClassification G J Γ) (decodeComparison G J)

/-- Encoding commutes with substitution through the inverse equivalence square. -/
def codeReindex {Γ Δ : D} (σ : Δ ⟶ Γ) :
    J.overMapPullback (Type w) σ ⋙ (sheafOverClassification G J Δ).inverse ≅
      (sheafOverClassification G J Γ).inverse ⋙ reindex G J σ :=
  (codeComparison G J).naturality σ

theorem codeReindex_id (Γ : D) (A : Sheaf (J.over Γ) (Type w)) :
    (sheafOverClassification G J Γ).inverse.map
        ((J.overMapPullbackId (Type w) Γ).inv.app A) ≫
      (codeReindex G J (𝟙 Γ)).hom.app A =
      (reindexId G J Γ).inv.app ((sheafOverClassification G J Γ).inverse.obj A) :=
  (codeComparison G J).naturality_id Γ A

theorem codeReindex_comp {Γ Δ Θ : D} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (A : Sheaf (J.over Γ) (Type w)) :
    (sheafOverClassification G J Θ).inverse.map
        ((J.overMapPullbackComp (Type w) τ σ).hom.app A) ≫
      (codeReindex G J (τ ≫ σ)).hom.app A =
      (codeReindex G J τ).hom.app ((J.overMapPullback (Type w) σ).obj A) ≫
        (reindex G J τ).map ((codeReindex G J σ).hom.app A) ≫
        (reindexComp G J σ τ).hom.app ((sheafOverClassification G J Γ).inverse.obj A) :=
  (codeComparison G J).naturality_comp τ σ A

/-- The inverse comparison respects the original fibre counits. -/
@[reassoc] theorem codeReindex_counit {Γ Δ : D} (σ : Δ ⟶ Γ)
    (A : Sheaf (J.over Γ) (Type w)) :
    (sheafOverClassification G J Δ).counitIso.inv.app
        ((J.overMapPullback (Type w) σ).obj A) ≫
      (sheafOverClassification G J Δ).functor.map ((codeReindex G J σ).hom.app A) =
      (J.overMapPullback (Type w) σ).map ((sheafOverClassification G J Γ).counitIso.inv.app A) ≫
        (decodeReindex G J σ).inv.app ((sheafOverClassification G J Γ).inverse.obj A) :=
  CoGrothendieckTransport.inverseNaturality_counit
    (F := codePseudofunctor G J) (G := J.pseudofunctorOver (Type w))
    (fun Γ => sheafOverClassification G J Γ) (decodeComparison G J) σ A

/-- The inverse comparison respects the original fibre units. -/
theorem codeReindex_unit {Γ Δ : D} (σ : Δ ⟶ Γ) (A : LocalCode.{u,v,w} G J Γ) :
    (sheafOverClassification G J Δ).inverse.map ((decodeReindex G J σ).inv.app A) ≫
      (sheafOverClassification G J Δ).unitIso.inv.app ((reindex G J σ).obj A) =
      (codeReindex G J σ).hom.app ((sheafOverClassification G J Γ).functor.obj A) ≫
        (reindex G J σ).map ((sheafOverClassification G J Γ).unitIso.inv.app A) :=
  CoGrothendieckTransport.inverseNaturality_unit
    (F := codePseudofunctor G J) (G := J.pseudofunctorOver (Type w))
    (fun Γ => sheafOverClassification G J Γ) (decodeComparison G J) σ A

/-- Encode all sheaf maps using the original inverse in each native fibre. -/
def totalCode : SheafTotal.{w} J ⥤ CodeTotal.{u,v,w} G J :=
  CoGrothendieckTransport.inverse (fun Γ => sheafOverClassification G J Γ) (decodeComparison G J)

/-- The native inverse is exactly the total map of the coherent inverse comparison. -/
theorem totalCode_eq_map : totalCode.{u,v,w} G J =
    CoGrothendieckTransport.map (codeComparison G J) :=
  CoGrothendieckTransport.inverse_eq_map
    (F := codePseudofunctor G J) (G := J.pseudofunctorOver (Type w))
    (fun Γ => sheafOverClassification G J Γ) (decodeComparison G J)

/-- Encoding keeps the actual base arrow and applies the inverse to its entire
fibre map, followed by the derived substitution comparison. -/
theorem totalCode_map {A B : SheafTotal.{w} J} (f : A ⟶ B) :
    (totalCode.{u,v,w} G J).map f =
      ⟨f.base, (sheafOverClassification G J A.base).inverse.map f.fiber ≫
        (codeReindex G J f.base).hom.app B.fiber⟩ :=
  CoGrothendieckTransport.inverse_map
    (F := codePseudofunctor G J) (G := J.pseudofunctorOver (Type w))
    (fun Γ => sheafOverClassification G J Γ) (decodeComparison G J) f

/-- The original fibre units recover local presentations over the same context. -/
def totalRecovery : 𝟭 (CodeTotal.{u,v,w} G J) ≅ totalDecode G J ⋙ totalCode G J :=
  CoGrothendieckTransport.unitIso
    (F := codePseudofunctor G J) (G := J.pseudofunctorOver (Type w))
    (fun Γ => sheafOverClassification G J Γ) (decodeComparison G J)

/-- The original fibre counits recover sheaves over the same context. -/
def totalCounit : totalCode.{u,v,w} G J ⋙ totalDecode G J ≅ 𝟭 (SheafTotal.{w} J) :=
  CoGrothendieckTransport.counitIso
    (F := codePseudofunctor G J) (G := J.pseudofunctorOver (Type w))
    (fun Γ => sheafOverClassification G J Γ) (decodeComparison G J)

/-- Local sheaf presentations and slice sheaves have equivalent total categories,
including arbitrary fibre maps and their context changes. -/
def totalEquivalence : CodeTotal.{u,v,w} G J ≌ SheafTotal.{w} J :=
  CoGrothendieckTransport.equivalence (fun Γ => sheafOverClassification G J Γ) (decodeComparison G J)

@[simp] theorem totalCode_projection :
    totalCode.{u,v,w} G J ⋙ Pseudofunctor.CoGrothendieck.forget (codePseudofunctor G J) =
      Pseudofunctor.CoGrothendieck.forget (J.pseudofunctorOver (Type w)) :=
  CoGrothendieckTransport.inverse_comp_forget _ _

@[simp] theorem totalCode_obj_base (A : SheafTotal.{w} J) :
    ((totalCode.{u,v,w} G J).obj A).base = A.base := rfl

@[simp] theorem totalCode_obj_fiber (A : SheafTotal.{w} J) :
    ((totalCode.{u,v,w} G J).obj A).fiber =
      (sheafOverClassification G J A.base).inverse.obj A.fiber := rfl

@[simp] theorem totalCode_map_base {A B : SheafTotal.{w} J} (f : A ⟶ B) :
    ((totalCode.{u,v,w} G J).map f).base = f.base :=
  CoGrothendieckTransport.inverse_map_base _ _ f

/-- Total recovery is precisely the original fibre unit included vertically. -/
theorem totalRecovery_hom_app (A : CodeTotal.{u,v,w} G J) :
    (totalRecovery G J).hom.app A =
      (Pseudofunctor.CoGrothendieck.ι (codePseudofunctor G J) A.base).map
        ((sheafOverClassification G J A.base).unitIso.hom.app A.fiber) :=
  CoGrothendieckTransport.unitIso_hom_app _ _ A

/-- The original sheaf counit is included vertically in the total category. -/
theorem totalCounit_hom_app (A : SheafTotal.{w} J) :
    (totalCounit.{u,v,w} G J).hom.app A =
      (Pseudofunctor.CoGrothendieck.ι (J.pseudofunctorOver (Type w)) A.base).map
        ((sheafOverClassification G J A.base).counitIso.hom.app A.fiber) := rfl

/-- The whole recovery isomorphism is the original fibre unit. -/
theorem totalRecovery_app (A : CodeTotal.{u,v,w} G J) :
    (totalRecovery G J).app A =
      (Pseudofunctor.CoGrothendieck.ι (codePseudofunctor G J) A.base).mapIso
        ((sheafOverClassification G J A.base).unitIso.app A.fiber) :=
  CoGrothendieckTransport.unitIso_app _ _ A

/-- The whole counit isomorphism is the original fibre counit. -/
theorem totalCounit_app (A : SheafTotal.{w} J) :
    (totalCounit.{u,v,w} G J).app A =
      (Pseudofunctor.CoGrothendieck.ι (J.pseudofunctorOver (Type w)) A.base).mapIso
        ((sheafOverClassification G J A.base).counitIso.app A.fiber) := rfl

@[simp] theorem totalRecovery_base (A : CodeTotal.{u,v,w} G J) :
    ((totalRecovery G J).hom.app A).base = 𝟙 A.base := rfl

@[simp] theorem totalRecovery_inv_base (A : CodeTotal.{u,v,w} G J) :
    ((totalRecovery G J).inv.app A).base = 𝟙 A.base := rfl

@[simp] theorem totalCounit_base (A : SheafTotal.{w} J) :
    ((totalCounit.{u,v,w} G J).hom.app A).base = 𝟙 A.base := rfl

@[simp] theorem totalCounit_inv_base (A : SheafTotal.{w} J) :
    ((totalCounit.{u,v,w} G J).inv.app A).base = 𝟙 A.base := rfl

/-- The triangle identity holds for the original unit, so the packaged equivalence
uses it directly and its unit remains vertical. -/
@[simp] theorem totalEquivalence_unit_base (A : CodeTotal.{u,v,w} G J) :
    ((totalEquivalence G J).unitIso.hom.app A).base = 𝟙 A.base := rfl

@[simp] theorem totalEquivalence_counit_base (A : SheafTotal.{w} J) :
    ((totalEquivalence.{u,v,w} G J).counitIso.hom.app A).base = 𝟙 A.base := rfl

@[simp] theorem totalEquivalence_unit_inv_base (A : CodeTotal.{u,v,w} G J) :
    ((totalEquivalence G J).unitIso.inv.app A).base = 𝟙 A.base := rfl

@[simp] theorem totalEquivalence_counit_inv_base (A : SheafTotal.{w} J) :
    ((totalEquivalence.{u,v,w} G J).counitIso.inv.app A).base = 𝟙 A.base := rfl

/-- Restricting the total decoder to a context gives the original decoder on maps. -/
theorem totalDecode_map_ι (Γ : D) {A B : LocalCode.{u,v,w} G J Γ} (f : A ⟶ B) :
    (totalDecode G J).map ((Pseudofunctor.CoGrothendieck.ι (codePseudofunctor G J) Γ).map f) =
      (Pseudofunctor.CoGrothendieck.ι (J.pseudofunctorOver (Type w)) Γ).map
        ((sheafOverClassification G J Γ).functor.map f) :=
  CoGrothendieckTransport.map_ι_map (decodeComparison G J) Γ f

/-- Restricting the total encoder to a context gives the original inverse on maps. -/
theorem totalCode_map_ι (Γ : D) {A B : Sheaf (J.over Γ) (Type w)} (f : A ⟶ B) :
    (totalCode.{u,v,w} G J).map
        ((Pseudofunctor.CoGrothendieck.ι (J.pseudofunctorOver (Type w)) Γ).map f) =
      (Pseudofunctor.CoGrothendieck.ι (codePseudofunctor G J) Γ).map
        ((sheafOverClassification G J Γ).inverse.map f) := by
  apply (CoGrothendieckTransport.fullyFaithful (decodeComparison G J)
    (fun Γ => (sheafOverClassification G J Γ).fullyFaithfulFunctor)).map_injective
  change (CoGrothendieckTransport.map (decodeComparison G J)).map
    ((CoGrothendieckTransport.inverse _ (decodeComparison G J)).map _) = _
  simp only [CoGrothendieckTransport.inverse, Functor.FullyFaithful.map_preimage,
    CoGrothendieckTransport.map_ι_map]
  simp [CoGrothendieckTransport.counitApp, Equivalence.fun_inv_map]

/-- Decoding preserves the universal property of every cartesian arrow. -/
theorem totalDecode_cartesian {A B : CodeTotal.{u,v,w} G J} (f : A ⟶ B)
    [(Pseudofunctor.CoGrothendieck.forget (codePseudofunctor G J)).IsCartesian f.base f] :
    (Pseudofunctor.CoGrothendieck.forget (J.pseudofunctorOver (Type w))).IsCartesian
      f.base ((totalDecode G J).map f) :=
  CoGrothendieckTransport.map_cartesian (decodeComparison G J) f

/-- Encoding preserves arbitrary cartesian arrows as well. -/
theorem totalCode_cartesian {A B : SheafTotal.{w} J} (f : A ⟶ B)
    [(Pseudofunctor.CoGrothendieck.forget (J.pseudofunctorOver (Type w))).IsCartesian f.base f] :
    (Pseudofunctor.CoGrothendieck.forget (codePseudofunctor.{u,v,w} G J)).IsCartesian
      f.base ((totalCode G J).map f) :=
  CoGrothendieckTransport.inverse_cartesian
    (F := codePseudofunctor G J) (G := J.pseudofunctorOver (Type w))
    (fun Γ => sheafOverClassification G J Γ) (decodeComparison G J) f

end SquareKit.CoherentSheafOver
