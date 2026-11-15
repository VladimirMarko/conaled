import SquareKit.Internal.Cubical.GlueFilling
import SquareKit.Internal.Cubical.FillingTransportLaws
import SquareKit.Internal.Cubical.GlueSubstitution
import SquareKit.Internal.Cubical.ScaledBoxMap

/-! Restrict the selected face filler to lines wholly inside the gluing face. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.Glue
open CategoryTheory
universe u

variable {Γ Δ : Context.{u}} (φ : Cofibration Γ)
  (A : Family Γ) (T : Family (restrictContext φ))
  (e : T ⟶ reindex A (restrictInclusion φ))
  (p : total (interval Δ) ⟶ Γ)

/-- A line on the universal face stays inside the original gluing face. -/
def wholeFaceLine : total (interval (restrictContext (intervalAll (φ.reindex p)))) ⟶
    restrictContext φ where
  app I := TypeCat.ofHom (fun z => ⟨p.app I ⟨z.1.val,z.2⟩,
    intervalAll_specialize (φ.reindex p) (Δ.elementsMk I z.1.val) z.1.property z.2⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    exact p.naturality_apply f ⟨z.1.val,z.2⟩

theorem wholeFaceLine_inclusion :
    wholeFaceLine φ p ≫ restrictInclusion φ =
      liftSub (interval Δ) (restrictInclusion (intervalAll (φ.reindex p))) ≫ p := rfl

/-- The full-face equality transports the whole chosen filler, including its tube. -/
noncomputable def wholeFaceIso :
    reindex (family φ A T e)
      (liftSub (interval Δ) (restrictInclusion (intervalAll (φ.reindex p))) ≫ p) ≅
    reindex T (wholeFaceLine φ p) :=
  eqToIso (congrArg (fun B => reindex B (wholeFaceLine φ p)) (family_full φ A T e))

noncomputable def selectedFaceFill (F : Filling T) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) p) ψ) :
    Term (reindex (family φ A T e)
      (liftSub (interval Δ) (restrictInclusion (intervalAll (φ.reindex p))) ≫ p)) :=
  Term.map (wholeFaceIso φ A T e p).inv
    (F.fill (wholeFaceLine φ p) (ψ.reindex (restrictInclusion (intervalAll (φ.reindex p))))
      ((b.reindex (restrictInclusion (intervalAll (φ.reindex p)))).map
        (wholeFaceIso φ A T e p).hom))

noncomputable def selectedFaceTube (F : Filling T) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) p) ψ) :
    PartialSection (reindex (family φ A T e) p)
      ((intervalAll (φ.reindex p)).reindex (projection (interval Δ))) :=
  PartialSection.ofRestricted
    ((selectedFaceFill φ A T e p F ψ b).reindex (restrictedInterval (intervalAll (φ.reindex p))))

theorem selectedFaceFill_fills (F : Filling T) (hF : F.Lawful) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) p) ψ) :
    (b.reindex (restrictInclusion (intervalAll (φ.reindex p)))).Fills
      (selectedFaceFill φ A T e p F ψ b) := by
  let i := restrictInclusion (intervalAll (φ.reindex p))
  let q := wholeFaceIso φ A T e p
  have h := hF.fills (wholeFaceLine φ p) (ψ.reindex i) ((b.reindex i).map q.hom)
  constructor
  · apply Term.ext
    intro x
    exact (congrArg (q.inv.app ((endpointSub _ false).mapElements.obj x))
      (congrArg (fun t => t.val x) h.1)).trans
        (congrArg (fun f => f.app ((endpointSub _ false).mapElements.obj x)
          ((b.reindex i).base.val x)) q.hom_inv_id)
  · intro x hx
    exact (congrArg (q.inv.app x) (h.2 x hx)).trans
      (congrArg (fun f => f.app x ((b.reindex i).tube.val x hx)) q.hom_inv_id)

theorem selectedFaceTube_compatible (F : Filling T) (hF : F.Lawful) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) p) ψ) :
    b.tube.Compatible (selectedFaceTube φ A T e p F ψ b) := by
  intro x hp hq
  rcases x with @⟨I,⟨γ,r⟩⟩
  exact ((selectedFaceFill_fills φ A T e p F hF ψ b).2
    ((total (interval (restrictContext (intervalAll (φ.reindex p))))).elementsMk I
      ⟨⟨γ,hq⟩,r⟩) hp).symm

theorem selectedFaceTube_zero (F : Filling T) (hF : F.Lawful) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) p) ψ)
    (x : Δ.Elements) (hx : (intervalAll (φ.reindex p)).full x) :
    (selectedFaceTube φ A T e p F ψ b).val ((endpointSub Δ false).mapElements.obj x) hx =
      b.base.val x := by
  exact congrArg (fun t => t.val
    ((restrictContext (intervalAll (φ.reindex p))).elementsMk x.obj ⟨x.val,hx⟩))
    (selectedFaceFill_fills φ A T e p F hF ψ b).1

/-- A preliminary lawful filler can be repaired to retain the selected whole face filler. -/
noncomputable def preserveSelectedFace (F : Filling T) (hF : F.Lawful)
    (H : Filling (family φ A T e)) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) p) ψ) : Term (reindex (family φ A T e) p) :=
  H.fill p (ψ.join (intervalAll (φ.reindex p)))
    (addTube b (selectedFaceTube φ A T e p F ψ b)
      (selectedFaceTube_compatible φ A T e p F hF ψ b)
      (selectedFaceTube_zero φ A T e p F hF ψ b))

theorem preserveSelectedFace_fills (F : Filling T) (hF : F.Lawful)
    (H : Filling (family φ A T e)) (hH : H.Lawful) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) p) ψ) :
    b.Fills (preserveSelectedFace φ A T e p F hF H ψ b) := by
  let t := selectedFaceTube φ A T e p F ψ b
  let h := selectedFaceTube_compatible φ A T e p F hF ψ b
  let h₀ := selectedFaceTube_zero φ A T e p F hF ψ b
  have hf := hH.fills p (ψ.join (intervalAll (φ.reindex p))) (addTube b t h h₀)
  constructor
  · exact hf.1
  · intro x hx
    have hu : ((ψ.join (intervalAll (φ.reindex p))).reindex (projection (interval Δ))).full x :=
      (Cofibration.full_join ψ (intervalAll (φ.reindex p))
        ((projection (interval Δ)).mapElements.obj x)).mpr (Or.inl hx)
    exact (hf.2 x hu).trans (glueValue_left b.tube t x hu hx)

theorem preserveSelectedFace_whole (F : Filling T) (hF : F.Lawful)
    (H : Filling (family φ A T e)) (hH : H.Lawful) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) p) ψ)
    (x : (total (interval Δ)).Elements)
    (hx : ((intervalAll (φ.reindex p)).reindex (projection (interval Δ))).full x) :
    (preserveSelectedFace φ A T e p F hF H ψ b).val x =
      (selectedFaceTube φ A T e p F ψ b).val x hx :=
  addTube_preserves_whole H hH p b (selectedFaceTube φ A T e p F ψ b)
    (selectedFaceTube_compatible φ A T e p F hF ψ b)
    (selectedFaceTube_zero φ A T e p F hF ψ b) x hx

/-- The cap and original tube together form the boundary to preserve. -/
noncomputable def boxPartial {Θ : Context.{u}} {B : Family (total (interval Θ))}
    {ψ : Cofibration Θ} (b : OpenBox B ψ) : PartialSection B (scaledFace ψ) :=
  b.tube.glue (endpointSection B false b.base) b.endpoint_compatible

theorem boxPartial_image_filled {Θ : Context.{u}} {B C : Family (total (interval Θ))}
    (η : B ⟶ C) {ψ : Cofibration Θ} (b : OpenBox B ψ) (a : Term C)
    (ha : (b.map η).Fills a) :
    (boxPartial b).map η = PartialSection.ofTerm (scaledFace ψ) a := by
  apply PartialSection.ext
  intro x hx
  rcases (Cofibration.full_join _ _ x).mp hx with ht | hc
  · exact (congrArg (η.app x)
      (glueValue_left b.tube (endpointSection B false b.base) x hx ht)).trans (ha.2 x ht).symm
  · rcases x with @⟨I,⟨γ,r⟩⟩
    have hr := (Cofibration.full_endpoint (generic (interval Θ)) false
      ((total (interval Θ)).elementsMk I ⟨γ,r⟩)).mp hc
    change r = (endpoint Θ false).val (Θ.elementsMk I γ) at hr
    subst r
    have he := eq_of_heq (endpointSection_val B false b.base _ hc)
    exact (congrArg (η.app _) ((glueValue_right b.tube (endpointSection B false b.base)
      b.endpoint_compatible _ hx hc).trans he)).trans
        (congrArg (fun t => t.val (Θ.elementsMk I γ)) ha.1).symm

theorem fills_of_boxPartial {Θ : Context.{u}} {B : Family (total (interval Θ))}
    {ψ : Cofibration Θ} (b : OpenBox B ψ) (a : Term B)
    (h : ∀ x hx, a.val x = (boxPartial b).val x hx) : b.Fills a := by
  constructor
  · apply Term.ext
    intro x
    let y := (endpointSub Θ false).mapElements.obj x
    have hz : (intervalFace Θ false).full y :=
      (Cofibration.full_endpoint (generic (interval Θ)) false y).mpr rfl
    have hu : (scaledFace ψ).full y := (Cofibration.full_join _ _ y).mpr (Or.inr hz)
    exact (h y hu).trans ((glueValue_right b.tube (endpointSection B false b.base)
      b.endpoint_compatible y hu hz).trans (eq_of_heq (endpointSection_val B false b.base y hz)))
  · intro x hx
    have hu : (scaledFace ψ).full x := (Cofibration.full_join _ _ x).mpr (Or.inl hx)
    exact (h x hu).trans (glueValue_left b.tube (endpointSection B false b.base) x hu hx)

theorem partialGlue_map {Θ : Context.{u}} {B C : Family Θ} (η : B ⟶ C)
    {ψ χ : Cofibration Θ} (b : PartialSection B ψ) (c : PartialSection B χ)
    (h : b.Compatible c) :
    (b.glue c h).map η = (b.map η).glue (c.map η) (fun x hp hq => congrArg (η.app x) (h x hp hq)) := by
  apply PartialSection.ext
  intro x hx
  rcases (Cofibration.full_join ψ χ x).mp hx with hp | hq
  · exact (congrArg (η.app x) (glueValue_left b c x hx hp)).trans
      (glueValue_left (b.map η) (c.map η) x hx hp).symm
  · exact (congrArg (η.app x) (glueValue_right b c h x hx hq)).trans
      (glueValue_right (b.map η) (c.map η) (fun y hp hq => congrArg (η.app y) (h y hp hq)) x hx hq).symm

theorem boxPartial_map {Θ : Context.{u}} {B C : Family (total (interval Θ))}
    (η : B ⟶ C) {ψ : Cofibration Θ} (b : OpenBox B ψ) :
    boxPartial (b.map η) = (boxPartial b).map η :=
  (PartialSection.glue_congr rfl (endpointSection_map η false b.base) _ _).trans
    (partialGlue_map η b.tube (endpointSection B false b.base) b.endpoint_compatible).symm

theorem boxPartial_reindex {Θ Λ : Context.{u}} {B : Family (total (interval Θ))}
    {ψ : Cofibration Θ} (b : OpenBox B ψ) (σ : Λ ⟶ Θ) :
    boxPartial (b.reindex σ) = (boxPartial b).reindex (liftSub (interval Θ) σ) :=
  ((PartialSection.glue_reindex b.tube (endpointSection B false b.base) b.endpoint_compatible
    (liftSub (interval Θ) σ)).trans
      (PartialSection.glue_congr rfl (endpointSection_reindex B false b.base σ) _ _)).symm

noncomputable def inputIso : reindex (family φ A T e) p ≅
    AmbientExtension.pulledCompatible φ A T e p :=
  (Functor.isoWhiskerLeft p.mapElements (familyIso φ A T e)) ≪≫ compatibleReindexIso φ A T e p

noncomputable def preliminaryCompatibleFill (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful)
    (ψ : Cofibration Δ) (b : OpenBox (reindex (family φ A T e) p) ψ) :=
  let b' := b.map (inputIso φ A T e p).hom
  let m := compatibleUnglue (φ.reindex p) (reindex A p) (reindex T (restrictSubstitution φ p))
    (Functor.whiskerLeft (restrictSubstitution φ p).mapElements e)
  AmbientExtension.extendSection φ A T e p E F hF G hG (boxPartial b') (G.fill p ψ (b'.map m))
    (boxPartial_image_filled m b' _ (hG.fills p ψ (b'.map m)))

theorem preliminaryCompatibleFill_fills (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful)
    (ψ : Cofibration Δ) (b : OpenBox (reindex (family φ A T e) p) ψ) :
    (b.map (inputIso φ A T e p).hom).Fills (preliminaryCompatibleFill φ A T e p E F hF G hG ψ b) := by
  apply fills_of_boxPartial
  intro x hx
  exact AmbientExtension.extendSection_boundary φ A T e p E F hF G hG _ _ _ x hx

/-- The preliminary whole filler is constructed from the two supplied lawful fillers and equivalence. -/
noncomputable def preliminaryFill (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful)
    (ψ : Cofibration Δ) (b : OpenBox (reindex (family φ A T e) p) ψ) :
    Term (reindex (family φ A T e) p) :=
  Term.map (inputIso φ A T e p).inv (preliminaryCompatibleFill φ A T e p E F hF G hG ψ b)

theorem preliminaryFill_fills (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful)
    (ψ : Cofibration Δ) (b : OpenBox (reindex (family φ A T e) p) ψ) :
    b.Fills (preliminaryFill φ A T e p E F hF G hG ψ b) := by
  let q := inputIso φ A T e p
  have h := preliminaryCompatibleFill_fills φ A T e p E F hF G hG ψ b
  constructor
  · apply Term.ext
    intro x
    exact (congrArg (q.inv.app ((endpointSub Δ false).mapElements.obj x))
      (congrArg (fun t => t.val x) h.1)).trans
        (congrArg (fun f => f.app ((endpointSub Δ false).mapElements.obj x) (b.base.val x)) q.hom_inv_id)
  · intro x hx
    exact (congrArg (q.inv.app x) (h.2 x hx)).trans
      (congrArg (fun f => f.app x (b.tube.val x hx)) q.hom_inv_id)

def inputComparison {Θ : Context.{u}} (σ : Θ ⟶ Δ) :=
  compatibleReindexMap (φ.reindex p) (reindex A p) (reindex T (restrictSubstitution φ p))
    (Functor.whiskerLeft (restrictSubstitution φ p).mapElements e) (liftSub (interval Δ) σ)

theorem inputIso_natural {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    (inputIso φ A T e (liftSub (interval Δ) σ ≫ p)).hom =
      Functor.whiskerLeft (liftSub (interval Δ) σ).mapElements (inputIso φ A T e p).hom ≫
        inputComparison φ A T e p σ := rfl

theorem inputBox_natural (ψ : Cofibration Δ) (b : OpenBox (reindex (family φ A T e) p) ψ)
    {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    (b.reindex σ).map (inputIso φ A T e (liftSub (interval Δ) σ ≫ p)).hom =
      ((b.map (inputIso φ A T e p).hom).reindex σ).map (inputComparison φ A T e p σ) := rfl

theorem inputPartial_natural (ψ : Cofibration Δ) (b : OpenBox (reindex (family φ A T e) p) ψ)
    {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    boxPartial ((b.reindex σ).map (inputIso φ A T e (liftSub (interval Δ) σ ≫ p)).hom) =
      AmbientExtension.substitutePartial φ A T e p (liftSub (interval Δ) σ)
        (boxPartial (b.map (inputIso φ A T e p).hom)) :=
  (boxPartial_map (inputComparison φ A T e p σ) ((b.map (inputIso φ A T e p).hom).reindex σ)).trans
    (congrArg (PartialSection.map (inputComparison φ A T e p σ))
      (boxPartial_reindex (b.map (inputIso φ A T e p).hom) σ))

theorem preliminaryCompatibleFill_reindex (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful)
    (ψ : Cofibration Δ) (b : OpenBox (reindex (family φ A T e) p) ψ)
    {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    preliminaryCompatibleFill φ A T e (liftSub (interval Δ) σ ≫ p) E F hF G hG (ψ.reindex σ) (b.reindex σ) =
      Term.map (inputComparison φ A T e p σ)
        ((preliminaryCompatibleFill φ A T e p E F hF G hG ψ b).reindex (liftSub (interval Δ) σ)) := by
  let τ := liftSub (interval Δ) σ
  let b₀ := b.map (inputIso φ A T e p).hom
  let b₁ := (b.reindex σ).map (inputIso φ A T e (τ ≫ p)).hom
  let m₀ := compatibleUnglue (φ.reindex p) (reindex A p) (reindex T (restrictSubstitution φ p))
    (Functor.whiskerLeft (restrictSubstitution φ p).mapElements e)
  let m₁ := compatibleUnglue (φ.reindex (τ ≫ p)) (reindex A (τ ≫ p))
    (reindex T (restrictSubstitution φ (τ ≫ p)))
    (Functor.whiskerLeft (restrictSubstitution φ (τ ≫ p)).mapElements e)
  let a₀ := G.fill p ψ (b₀.map m₀)
  let a₁ := G.fill (τ ≫ p) (ψ.reindex σ) (b₁.map m₁)
  have h₀ := boxPartial_image_filled m₀ b₀ a₀ (hG.fills p ψ (b₀.map m₀))
  have h₁ := boxPartial_image_filled m₁ b₁ a₁ (hG.fills (τ ≫ p) (ψ.reindex σ) (b₁.map m₁))
  have hs : boxPartial b₁ = AmbientExtension.substitutePartial φ A T e p τ (boxPartial b₀) :=
    inputPartial_natural φ A T e p ψ b σ
  have ha : a₁ = a₀.reindex τ := hG.uniform p ψ (b₀.map m₀) σ
  exact (AmbientExtension.extendSection_congr φ A T e (τ ≫ p) E F hF G hG
    (boxPartial b₁) a₁ h₁ (AmbientExtension.substitutePartial φ A T e p τ (boxPartial b₀))
      (a₀.reindex τ) (congrArg (fun s => s.reindex τ) h₀) hs ha).trans
    (AmbientExtension.extendSection_reindex φ A T e p E F hF G hG (boxPartial b₀) a₀ h₀ τ)

theorem inputIso_inverse_natural {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    inputComparison φ A T e p σ ≫ (inputIso φ A T e (liftSub (interval Δ) σ ≫ p)).inv =
      Functor.whiskerLeft (liftSub (interval Δ) σ).mapElements (inputIso φ A T e p).inv :=
  (Iso.comp_inv_eq (inputIso φ A T e (liftSub (interval Δ) σ ≫ p))).mpr
    ((Iso.eq_inv_comp (Functor.isoWhiskerLeft (liftSub (interval Δ) σ).mapElements
      (inputIso φ A T e p))).mpr (inputIso_natural φ A T e p σ).symm)

theorem preliminaryFill_reindex (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful)
    (ψ : Cofibration Δ) (b : OpenBox (reindex (family φ A T e) p) ψ)
    {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    preliminaryFill φ A T e (liftSub (interval Δ) σ ≫ p) E F hF G hG (ψ.reindex σ) (b.reindex σ) =
      (preliminaryFill φ A T e p E F hF G hG ψ b).reindex (liftSub (interval Δ) σ) :=
  (congrArg (Term.map (inputIso φ A T e (liftSub (interval Δ) σ ≫ p)).inv)
    (preliminaryCompatibleFill_reindex φ A T e p E F hF G hG ψ b σ)).trans
      (congrArg (fun η => Term.map η
        ((preliminaryCompatibleFill φ A T e p E F hF G hG ψ b).reindex (liftSub (interval Δ) σ)))
        (inputIso_inverse_natural φ A T e p σ))

/-- A lawful preliminary Glue filling, before repairing its selected full-face structure. -/
noncomputable def preliminaryFilling (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful) : Filling (family φ A T e) where
  fill q ψ b := preliminaryFill φ A T e q E F hF G hG ψ b

theorem preliminaryFilling_lawful (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful) :
    (preliminaryFilling φ A T e E F hF G hG).Lawful where
  fills q ψ b := preliminaryFill_fills φ A T e q E F hF G hG ψ b
  uniform q ψ b σ := preliminaryFill_reindex φ A T e q E F hF G hG ψ b σ

section FlexibleFace
variable (δ : Cofibration Δ)
  (hδ : ∀ (x : Δ.Elements), δ.full x → ∀ r : (interval Δ).obj x,
    (φ.reindex p).full (extendObj (interval Δ) x r))

/-- A supplied face whose lines stay inside the gluing face. -/
def wholeFaceLineOn : total (interval (restrictContext δ)) ⟶
    restrictContext φ where
  app I := TypeCat.ofHom (fun z => ⟨p.app I ⟨z.1.val,z.2⟩,
    hδ (Δ.elementsMk I z.1.val) z.1.property z.2⟩)
  naturality I J f := by
    apply ConcreteCategory.hom_ext
    intro z
    apply Subtype.ext
    exact p.naturality_apply f ⟨z.1.val,z.2⟩

theorem wholeFaceLine_inclusionOn :
    wholeFaceLineOn φ p δ hδ ≫ restrictInclusion φ =
      liftSub (interval Δ) (restrictInclusion δ) ≫ p := rfl

/-- The full-face equality transports the whole chosen filler, including its tube. -/
noncomputable def wholeFaceIsoOn :
    reindex (family φ A T e)
      (liftSub (interval Δ) (restrictInclusion δ) ≫ p) ≅
    reindex T (wholeFaceLineOn φ p δ hδ) :=
  eqToIso (congrArg (fun B => reindex B (wholeFaceLineOn φ p δ hδ)) (family_full φ A T e))

noncomputable def selectedFaceFillOn (F : Filling T) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) p) ψ) :
    Term (reindex (family φ A T e)
      (liftSub (interval Δ) (restrictInclusion δ) ≫ p)) :=
  Term.map (wholeFaceIsoOn φ A T e p δ hδ).inv
    (F.fill (wholeFaceLineOn φ p δ hδ) (ψ.reindex (restrictInclusion δ))
      ((b.reindex (restrictInclusion δ)).map
        (wholeFaceIsoOn φ A T e p δ hδ).hom))

noncomputable def selectedFaceTubeOn (F : Filling T) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) p) ψ) :
    PartialSection (reindex (family φ A T e) p)
      (δ.reindex (projection (interval Δ))) :=
  PartialSection.ofRestricted
    ((selectedFaceFillOn φ A T e p δ hδ F ψ b).reindex (restrictedInterval δ))

theorem selectedFaceFill_fillsOn (F : Filling T) (hF : F.Lawful) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) p) ψ) :
    (b.reindex (restrictInclusion δ)).Fills
      (selectedFaceFillOn φ A T e p δ hδ F ψ b) := by
  let i := restrictInclusion δ
  let q := wholeFaceIsoOn φ A T e p δ hδ
  have h := hF.fills (wholeFaceLineOn φ p δ hδ) (ψ.reindex i) ((b.reindex i).map q.hom)
  constructor
  · apply Term.ext
    intro x
    exact (congrArg (q.inv.app ((endpointSub _ false).mapElements.obj x))
      (congrArg (fun t => t.val x) h.1)).trans
        (congrArg (fun f => f.app ((endpointSub _ false).mapElements.obj x)
          ((b.reindex i).base.val x)) q.hom_inv_id)
  · intro x hx
    exact (congrArg (q.inv.app x) (h.2 x hx)).trans
      (congrArg (fun f => f.app x ((b.reindex i).tube.val x hx)) q.hom_inv_id)

theorem selectedFaceTube_compatibleOn (F : Filling T) (hF : F.Lawful) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) p) ψ) :
    b.tube.Compatible (selectedFaceTubeOn φ A T e p δ hδ F ψ b) := by
  intro x hp hq
  rcases x with @⟨I,⟨γ,r⟩⟩
  exact ((selectedFaceFill_fillsOn φ A T e p δ hδ F hF ψ b).2
    ((total (interval (restrictContext δ))).elementsMk I
      ⟨⟨γ,hq⟩,r⟩) hp).symm

theorem selectedFaceTube_zeroOn (F : Filling T) (hF : F.Lawful) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) p) ψ)
    (x : Δ.Elements) (hx : δ.full x) :
    (selectedFaceTubeOn φ A T e p δ hδ F ψ b).val ((endpointSub Δ false).mapElements.obj x) hx =
      b.base.val x := by
  exact congrArg (fun t => t.val
    ((restrictContext δ).elementsMk x.obj ⟨x.val,hx⟩))
    (selectedFaceFill_fillsOn φ A T e p δ hδ F hF ψ b).1

/-- A preliminary lawful filler can be repaired to retain the selected whole face filler. -/
noncomputable def preserveSelectedFaceOn (F : Filling T) (hF : F.Lawful)
    (H : Filling (family φ A T e)) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) p) ψ) : Term (reindex (family φ A T e) p) :=
  H.fill p (ψ.join δ)
    (addTube b (selectedFaceTubeOn φ A T e p δ hδ F ψ b)
      (selectedFaceTube_compatibleOn φ A T e p δ hδ F hF ψ b)
      (selectedFaceTube_zeroOn φ A T e p δ hδ F hF ψ b))

theorem preserveSelectedFace_fillsOn (F : Filling T) (hF : F.Lawful)
    (H : Filling (family φ A T e)) (hH : H.Lawful) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) p) ψ) :
    b.Fills (preserveSelectedFaceOn φ A T e p δ hδ F hF H ψ b) := by
  let t := selectedFaceTubeOn φ A T e p δ hδ F ψ b
  let h := selectedFaceTube_compatibleOn φ A T e p δ hδ F hF ψ b
  let h₀ := selectedFaceTube_zeroOn φ A T e p δ hδ F hF ψ b
  have hf := hH.fills p (ψ.join δ) (addTube b t h h₀)
  constructor
  · exact hf.1
  · intro x hx
    have hu : ((ψ.join δ).reindex (projection (interval Δ))).full x :=
      (Cofibration.full_join ψ δ
        ((projection (interval Δ)).mapElements.obj x)).mpr (Or.inl hx)
    exact (hf.2 x hu).trans (glueValue_left b.tube t x hu hx)

theorem preserveSelectedFace_wholeOn (F : Filling T) (hF : F.Lawful)
    (H : Filling (family φ A T e)) (hH : H.Lawful) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) p) ψ)
    (x : (total (interval Δ)).Elements)
    (hx : (δ.reindex (projection (interval Δ))).full x) :
    (preserveSelectedFaceOn φ A T e p δ hδ F hF H ψ b).val x =
      (selectedFaceTubeOn φ A T e p δ hδ F ψ b).val x hx :=
  addTube_preserves_whole H hH p b (selectedFaceTubeOn φ A T e p δ hδ F ψ b)
    (selectedFaceTube_compatibleOn φ A T e p δ hδ F hF ψ b)
    (selectedFaceTube_zeroOn φ A T e p δ hδ F hF ψ b) x hx


theorem reindexEqualityIso {Ξ Ω : Context.{u}} (B C : Family Ξ) (h : B = C) (σ : Ω ⟶ Ξ) :
    eqToIso (congrArg (fun D => reindex D σ) h) = Functor.isoWhiskerLeft σ.mapElements (eqToIso h) := by
  cases h
  rfl

theorem wholeFaceIsoOn_reindex {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    wholeFaceIsoOn φ A T e (liftSub (interval Δ) σ ≫ p) (δ.reindex σ)
      (fun x hx r => hδ (σ.mapElements.obj x) hx r) =
    Functor.isoWhiskerLeft (liftSub (interval (restrictContext δ)) (restrictSubstitution δ σ)).mapElements
      (wholeFaceIsoOn φ A T e p δ hδ) := by
  have ho := reindexEqualityIso _ _ (family_full φ A T e) (wholeFaceLineOn φ p δ hδ)
  have hn := reindexEqualityIso _ _ (family_full φ A T e)
    (wholeFaceLineOn φ (liftSub (interval Δ) σ ≫ p) (δ.reindex σ)
      (fun x hx r => hδ (σ.mapElements.obj x) hx r))
  exact hn.trans (congrArg
    (Functor.isoWhiskerLeft (liftSub (interval (restrictContext δ)) (restrictSubstitution δ σ)).mapElements) ho.symm)

theorem selectedFaceFillOn_reindex (F : Filling T) (hF : F.Lawful) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) p) ψ) {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    selectedFaceFillOn φ A T e (liftSub (interval Δ) σ ≫ p) (δ.reindex σ)
      (fun x hx r => hδ (σ.mapElements.obj x) hx r) F (ψ.reindex σ) (b.reindex σ) =
    (selectedFaceFillOn φ A T e p δ hδ F ψ b).reindex
      (liftSub (interval (restrictContext δ)) (restrictSubstitution δ σ)) := by
  let ρ := restrictSubstitution δ σ
  let q₀ := wholeFaceIsoOn φ A T e p δ hδ
  let q₁ := wholeFaceIsoOn φ A T e (liftSub (interval Δ) σ ≫ p) (δ.reindex σ)
    (fun x hx r => hδ (σ.mapElements.obj x) hx r)
  let b₀ := (b.reindex (restrictInclusion δ)).map q₀.hom
  let b₁ := ((b.reindex σ).reindex (restrictInclusion (δ.reindex σ))).map q₁.hom
  have hb : b₁ = b₀.reindex ρ :=
    congrArg (fun η => ((b.reindex σ).reindex (restrictInclusion (δ.reindex σ))).map η)
      (congrArg Iso.hom (wholeFaceIsoOn_reindex φ A T e p δ hδ σ))
  have hf := (congrArg (F.fill
    (wholeFaceLineOn φ (liftSub (interval Δ) σ ≫ p) (δ.reindex σ)
      (fun x hx r => hδ (σ.mapElements.obj x) hx r))
    ((ψ.reindex σ).reindex (restrictInclusion (δ.reindex σ)))) hb).trans
      (hF.uniform (wholeFaceLineOn φ p δ hδ) (ψ.reindex (restrictInclusion δ)) b₀ ρ)
  exact (congrArg (fun η => Term.map η (F.fill
    (wholeFaceLineOn φ (liftSub (interval Δ) σ ≫ p) (δ.reindex σ)
      (fun x hx r => hδ (σ.mapElements.obj x) hx r))
    ((ψ.reindex σ).reindex (restrictInclusion (δ.reindex σ))) b₁))
      (congrArg Iso.inv (wholeFaceIsoOn_reindex φ A T e p δ hδ σ))).trans
        (congrArg (Term.map (Functor.whiskerLeft
          (liftSub (interval (restrictContext δ)) ρ).mapElements q₀.inv)) hf)

theorem selectedFaceTubeOn_reindex (F : Filling T) (hF : F.Lawful) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) p) ψ) {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    selectedFaceTubeOn φ A T e (liftSub (interval Δ) σ ≫ p) (δ.reindex σ)
      (fun x hx r => hδ (σ.mapElements.obj x) hx r) F (ψ.reindex σ) (b.reindex σ) =
    (selectedFaceTubeOn φ A T e p δ hδ F ψ b).reindex (liftSub (interval Δ) σ) := by
  apply PartialSection.ext
  intro x hx
  exact congrArg (fun t => t.val
    ((total (interval (restrictContext (δ.reindex σ)))).elementsMk x.obj ⟨⟨x.val.1,hx⟩,x.val.2⟩))
    (selectedFaceFillOn_reindex φ A T e p δ hδ F hF ψ b σ)

theorem addTube_congr {Ω : Context.{u}} {B : Family (total (interval Ω))}
    {χ η : Cofibration Ω} (b : OpenBox B χ)
    (t t' : PartialSection B (η.reindex (projection (interval Ω)))) (ht : t = t')
    (h : b.tube.Compatible t) (h' : b.tube.Compatible t')
    (h₀ : ∀ x hx, t.val ((endpointSub Ω false).mapElements.obj x) hx = b.base.val x)
    (h₀' : ∀ x hx, t'.val ((endpointSub Ω false).mapElements.obj x) hx = b.base.val x) :
    addTube b t h h₀ = addTube b t' h' h₀' := by
  cases ht
  rfl

theorem preserveSelectedFaceOn_reindex (F : Filling T) (hF : F.Lawful)
    (H : Filling (family φ A T e)) (hH : H.Lawful) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) p) ψ) {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    preserveSelectedFaceOn φ A T e (liftSub (interval Δ) σ ≫ p) (δ.reindex σ)
      (fun x hx r => hδ (σ.mapElements.obj x) hx r) F hF H (ψ.reindex σ) (b.reindex σ) =
    (preserveSelectedFaceOn φ A T e p δ hδ F hF H ψ b).reindex (liftSub (interval Δ) σ) := by
  let t := selectedFaceTubeOn φ A T e p δ hδ F ψ b
  let hc := selectedFaceTube_compatibleOn φ A T e p δ hδ F hF ψ b
  let hz := selectedFaceTube_zeroOn φ A T e p δ hδ F hF ψ b
  let t' := selectedFaceTubeOn φ A T e (liftSub (interval Δ) σ ≫ p) (δ.reindex σ)
    (fun x hx r => hδ (σ.mapElements.obj x) hx r) F (ψ.reindex σ) (b.reindex σ)
  let hc' := selectedFaceTube_compatibleOn φ A T e (liftSub (interval Δ) σ ≫ p) (δ.reindex σ)
    (fun x hx r => hδ (σ.mapElements.obj x) hx r) F hF (ψ.reindex σ) (b.reindex σ)
  let hz' := selectedFaceTube_zeroOn φ A T e (liftSub (interval Δ) σ ≫ p) (δ.reindex σ)
    (fun x hx r => hδ (σ.mapElements.obj x) hx r) F hF (ψ.reindex σ) (b.reindex σ)
  have hb : addTube (b.reindex σ) t' hc' hz' = (addTube b t hc hz).reindex σ :=
    (addTube_congr (b.reindex σ) t' (t.reindex (liftSub (interval Δ) σ))
      (selectedFaceTubeOn_reindex φ A T e p δ hδ F hF ψ b σ)
      hc' (hc.reindex (liftSub (interval Δ) σ)) hz' (fun x hx => hz (σ.mapElements.obj x) hx)).trans
        (addTube_reindex b t hc hz σ).symm
  exact (congrArg (H.fill (liftSub (interval Δ) σ ≫ p) ((ψ.join δ).reindex σ)) hb).trans
    (hH.uniform p (ψ.join δ) (addTube b t hc hz) σ)

theorem preserveSelectedFaceOn_congr (δ' : Cofibration Δ)
    (hδ' : ∀ (x : Δ.Elements), δ'.full x → ∀ r : (interval Δ).obj x,
      (φ.reindex p).full (extendObj (interval Δ) x r)) (he : δ = δ')
    (F : Filling T) (hF : F.Lawful) (H : Filling (family φ A T e)) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) p) ψ) :
    preserveSelectedFaceOn φ A T e p δ hδ F hF H ψ b =
      preserveSelectedFaceOn φ A T e p δ' hδ' F hF H ψ b := by
  cases he
  rfl

end FlexibleFace

theorem preserveSelectedFace_reindex (F : Filling T) (hF : F.Lawful)
    (H : Filling (family φ A T e)) (hH : H.Lawful) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) p) ψ) {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    preserveSelectedFace φ A T e (liftSub (interval Δ) σ ≫ p) F hF H (ψ.reindex σ) (b.reindex σ) =
      (preserveSelectedFace φ A T e p F hF H ψ b).reindex (liftSub (interval Δ) σ) :=
  (preserveSelectedFaceOn_congr φ A T e (liftSub (interval Δ) σ ≫ p)
    (intervalAll (φ.reindex (liftSub (interval Δ) σ ≫ p)))
    (intervalAll_specialize (φ.reindex (liftSub (interval Δ) σ ≫ p)))
    ((intervalAll (φ.reindex p)).reindex σ)
    (fun x hx r => intervalAll_specialize (φ.reindex p) (σ.mapElements.obj x) hx r)
    (intervalAll_reindex (φ.reindex p) σ) F hF H (ψ.reindex σ) (b.reindex σ)).trans
      (preserveSelectedFaceOn_reindex φ A T e p (intervalAll (φ.reindex p))
        (intervalAll_specialize (φ.reindex p)) F hF H hH ψ b σ)

/-- The constructed Glue filler retains the specified whole face filler. -/
noncomputable def filling (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful) : Filling (family φ A T e) where
  fill q ψ b := preserveSelectedFace φ A T e q F hF (preliminaryFilling φ A T e E F hF G hG) ψ b

theorem filling_lawful (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful) :
    (filling φ A T e E F hF G hG).Lawful where
  fills q ψ b := preserveSelectedFace_fills φ A T e q F hF _
    (preliminaryFilling_lawful φ A T e E F hF G hG) ψ b
  uniform q ψ b σ := preserveSelectedFace_reindex φ A T e q F hF _
    (preliminaryFilling_lawful φ A T e E F hF G hG) ψ b σ

theorem filling_selected_whole (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful)
    (ψ : Cofibration Δ) (b : OpenBox (reindex (family φ A T e) p) ψ)
    (x : (total (interval Δ)).Elements)
    (hx : ((intervalAll (φ.reindex p)).reindex (projection (interval Δ))).full x) :
    ((filling φ A T e E F hF G hG).fill p ψ b).val x =
      (selectedFaceTube φ A T e p F ψ b).val x hx :=
  preserveSelectedFace_whole φ A T e p F hF _ (preliminaryFilling_lawful φ A T e E F hF G hG) ψ b x hx

theorem filling_restrict_line (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful)
    (ψ : Cofibration Δ) (b : OpenBox (reindex (family φ A T e) p) ψ) :
    ((filling φ A T e E F hF G hG).fill p ψ b).reindex
      (liftSub (interval Δ) (restrictInclusion (intervalAll (φ.reindex p)))) =
    selectedFaceFill φ A T e p F ψ b := by
  apply Term.ext
  intro x
  exact filling_selected_whole φ A T e p E F hF G hG ψ b
    ((liftSub (interval Δ) (restrictInclusion (intervalAll (φ.reindex p)))).mapElements.obj x)
    x.val.1.property

def fullLineSection (q : total (interval Δ) ⟶ restrictContext φ) :
    Δ ⟶ restrictContext (intervalAll (φ.reindex (q ≫ restrictInclusion φ))) where
  app I := TypeCat.ofHom (fun γ => ⟨γ,
    (intervalAll_full (φ.reindex (q ≫ restrictInclusion φ)) (Δ.elementsMk I γ)).mpr
      (q.mapElements.obj (freshExtension (Δ.elementsMk I γ))).val.property⟩)
  naturality _ _ _ := rfl

theorem fullLineSection_inclusion (q : total (interval Δ) ⟶ restrictContext φ) :
    fullLineSection φ q ≫ restrictInclusion (intervalAll (φ.reindex (q ≫ restrictInclusion φ))) = 𝟙 Δ := rfl

theorem fullLineSection_line (q : total (interval Δ) ⟶ restrictContext φ) :
    liftSub (interval (restrictContext (intervalAll (φ.reindex (q ≫ restrictInclusion φ)))))
      (fullLineSection φ q) ≫ wholeFaceLine φ (q ≫ restrictInclusion φ) = q := rfl

theorem fullLineSection_iso (q : total (interval Δ) ⟶ restrictContext φ) :
    Functor.isoWhiskerLeft
      (liftSub (interval (restrictContext (intervalAll (φ.reindex (q ≫ restrictInclusion φ)))))
        (fullLineSection φ q)).mapElements (wholeFaceIso φ A T e (q ≫ restrictInclusion φ)) =
      Functor.isoWhiskerLeft q.mapElements (eqToIso (family_full φ A T e)) :=
  congrArg (Functor.isoWhiskerLeft
    (liftSub (interval (restrictContext (intervalAll (φ.reindex (q ≫ restrictInclusion φ)))))
      (fullLineSection φ q)).mapElements)
      (reindexEqualityIso _ _ (family_full φ A T e) (wholeFaceLine φ (q ≫ restrictInclusion φ)))

theorem selectedFaceFill_full (F : Filling T) (hF : F.Lawful)
    (q : total (interval Δ) ⟶ restrictContext φ) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) (q ≫ restrictInclusion φ)) ψ) :
    (selectedFaceFill φ A T e (q ≫ restrictInclusion φ) F ψ b).reindex
      (liftSub (interval (restrictContext (intervalAll (φ.reindex (q ≫ restrictInclusion φ)))))
        (fullLineSection φ q)) =
    Term.map (Functor.whiskerLeft q.mapElements (eqToIso (family_full φ A T e)).inv)
      (F.fill q ψ (b.map (Functor.whiskerLeft q.mapElements (eqToIso (family_full φ A T e)).hom))) := by
  let δ := intervalAll (φ.reindex (q ≫ restrictInclusion φ))
  let τ := liftSub (interval (restrictContext δ)) (fullLineSection φ q)
  let q₀ := wholeFaceIso φ A T e (q ≫ restrictInclusion φ)
  let q₁ := Functor.isoWhiskerLeft q.mapElements (eqToIso (family_full φ A T e))
  let b₀ := (b.reindex (restrictInclusion δ)).map q₀.hom
  have hb : b₀.reindex (fullLineSection φ q) = b.map q₁.hom :=
    congrArg (fun η => b.map η) (congrArg Iso.hom (fullLineSection_iso φ A T e q))
  have hf := (hF.uniform (wholeFaceLine φ (q ≫ restrictInclusion φ))
    (ψ.reindex (restrictInclusion δ)) b₀ (fullLineSection φ q)).symm.trans
      (congrArg (F.fill q ψ) hb)
  exact (congrArg (fun η => Term.map η
    ((F.fill (wholeFaceLine φ (q ≫ restrictInclusion φ)) (ψ.reindex (restrictInclusion δ)) b₀).reindex τ))
      (congrArg Iso.inv (fullLineSection_iso φ A T e q))).trans
        (congrArg (Term.map q₁.inv) hf)

theorem filling_full_line (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful)
    (q : total (interval Δ) ⟶ restrictContext φ) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) (q ≫ restrictInclusion φ)) ψ) :
    (filling φ A T e E F hF G hG).fill (q ≫ restrictInclusion φ) ψ b =
    Term.map (Functor.whiskerLeft q.mapElements (eqToIso (family_full φ A T e)).inv)
      (F.fill q ψ (b.map (Functor.whiskerLeft q.mapElements (eqToIso (family_full φ A T e)).hom))) := by
  have h := congrArg (fun t => t.reindex
    (liftSub (interval (restrictContext (intervalAll (φ.reindex (q ≫ restrictInclusion φ)))))
      (fullLineSection φ q)))
    (filling_restrict_line φ A T e (q ≫ restrictInclusion φ) E F hF G hG ψ b)
  exact h.trans (selectedFaceFill_full φ A T e F hF q ψ b)

/-- Restriction recovers the supplied entire filling operation, not only endpoints. -/
theorem filling_full (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful) :
    ((filling φ A T e E F hF G hG).reindex (restrictInclusion φ)).transport
      (eqToIso (family_full φ A T e)) = F := by
  apply Filling.ext
  intro Ξ q ψ b
  let i := Functor.isoWhiskerLeft q.mapElements (eqToIso (family_full φ A T e))
  have h := filling_full_line φ A T e E F hF G hG q ψ (b.map i.inv)
  exact (congrArg (Term.map i.hom) h).trans
    ((Term.map_iso_roundtrip i.symm _).trans
      (congrArg (F.fill q ψ) (OpenBox.map_iso_roundtrip i b)))


section SourceSubstitution
variable {Γ' : Context.{u}} (σ : Γ' ⟶ Γ) (q : total (interval Δ) ⟶ Γ')

theorem inputIso_input_reindex :
    Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom ≫
      (inputIso (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
        (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q).hom =
    (inputIso φ A T e (q ≫ σ)).hom := by
  ext x z
  let i := familyIso (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
    (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e)
  let z' := (compatibleReindexIso φ A T e σ).hom.app (q.mapElements.obj x)
    ((familyIso φ A T e).hom.app ((q ≫ σ).mapElements.obj x) z)
  exact congrArg ((compatibleReindexMap (φ.reindex σ) (reindex A σ)
    (reindex T (restrictSubstitution φ σ))
    (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q).app x)
      (congrArg (fun m => m.app (q.mapElements.obj x) z') i.inv_hom_id)


theorem inputBox_input_reindex (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) (q ≫ σ)) ψ) :
    (b.map (Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom)).map
      (inputIso (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
        (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q).hom =
    b.map (inputIso φ A T e (q ≫ σ)).hom :=
  congrArg b.map (inputIso_input_reindex φ A T e σ q)

theorem preliminaryCompatibleFill_input_reindex (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful)
    (ψ : Cofibration Δ) (b : OpenBox (reindex (family φ A T e) (q ≫ σ)) ψ) :
    preliminaryCompatibleFill (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q
      (E.reindex (restrictSubstitution φ σ)) (F.reindex (restrictSubstitution φ σ))
      (hF.reindex _) (G.reindex σ) (hG.reindex _) ψ
      (b.map (Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom)) =
    preliminaryCompatibleFill φ A T e (q ≫ σ) E F hF G hG ψ b := by
  let m := compatibleUnglue (φ.reindex (q ≫ σ)) (reindex A (q ≫ σ))
    (reindex T (restrictSubstitution φ (q ≫ σ)))
    (Functor.whiskerLeft (restrictSubstitution φ (q ≫ σ)).mapElements e)
  let K (c : OpenBox (AmbientExtension.pulledCompatible φ A T e (q ≫ σ)) ψ) :=
    AmbientExtension.extendSection (φ.reindex σ) (reindex A σ)
      (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q
      (E.reindex (restrictSubstitution φ σ)) (F.reindex (restrictSubstitution φ σ))
      (hF.reindex _) (G.reindex σ) (hG.reindex _) (boxPartial c)
      (G.fill (q ≫ σ) ψ (c.map m))
      (boxPartial_image_filled m c _ (hG.fills (q ≫ σ) ψ (c.map m)))
  exact (congrArg K (inputBox_input_reindex φ A T e σ q ψ b)).trans
    (AmbientExtension.extendSection_input_reindex φ A T e σ q E F hF G hG _ _ _)


theorem inputIso_inverse_input_reindex :
    (inputIso (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q).inv =
    (inputIso φ A T e (q ≫ σ)).inv ≫
      Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom :=
  (Iso.eq_inv_comp (inputIso φ A T e (q ≫ σ))).mpr
    ((Iso.comp_inv_eq (inputIso (φ.reindex σ) (reindex A σ)
      (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q)).mpr
        (inputIso_input_reindex φ A T e σ q).symm)

theorem preliminaryFill_input_reindex (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful)
    (ψ : Cofibration Δ) (b : OpenBox (reindex (family φ A T e) (q ≫ σ)) ψ) :
    preliminaryFill (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q
      (E.reindex (restrictSubstitution φ σ)) (F.reindex (restrictSubstitution φ σ))
      (hF.reindex _) (G.reindex σ) (hG.reindex _) ψ
      (b.map (Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom)) =
    Term.map (Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom)
      (preliminaryFill φ A T e (q ≫ σ) E F hF G hG ψ b) :=
  (congrArg (Term.map (inputIso (φ.reindex σ) (reindex A σ)
    (reindex T (restrictSubstitution φ σ))
    (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q).inv)
      (preliminaryCompatibleFill_input_reindex φ A T e σ q E F hF G hG ψ b)).trans
    (congrArg (fun η => Term.map η (preliminaryCompatibleFill φ A T e (q ≫ σ) E F hF G hG ψ b))
      (inputIso_inverse_input_reindex φ A T e σ q))


theorem reindexIso_full :
    Functor.whiskerLeft (restrictInclusion (φ.reindex σ)).mapElements (reindexIso φ A T e σ).hom ≫
      (eqToIso (family_full (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
        (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e))).hom =
    Functor.whiskerLeft (restrictSubstitution φ σ).mapElements (eqToIso (family_full φ A T e)).hom := by
  ext x z
  have hc : ∀ {Ω : Context.{u}} {B C : Family Ω} (h : B = C) (y : Ω.Elements) (a : B.obj y),
      HEq ((eqToHom h).app y a) a := by
    intro Ω B C h y a
    cases h
    rfl
  let y := (restrictSubstitution φ σ).mapElements.obj x
  let t := (eqToHom (family_full φ A T e)).app y z
  have hf := fiberEquiv_full φ A T e
    (x := (restrictInclusion φ).mapElements.obj y) x.val.property z t (hc (family_full φ A T e) y z).symm
  let c := (compatibleReindexMap φ A T e σ).app
    ((restrictInclusion (φ.reindex σ)).mapElements.obj x) ((fiberEquiv φ A T e _) z)
  have hr : c.face (𝟙 _) x.val.property = t := by
    exact (congrArg (fun v : CompatibleElement φ A T e ((restrictInclusion φ).mapElements.obj y) =>
      v.face (𝟙 _) x.val.property) hf).trans (fromFace_read φ A T e (x := (restrictInclusion φ).mapElements.obj y) x.val.property t)
  exact eq_of_heq ((hc (family_full (φ.reindex σ) (reindex A σ)
    (reindex T (restrictSubstitution φ σ))
    (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e)) x _).trans
    ((fiberEquiv_symm_full (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) x.val.property c).trans
        (heq_of_eq hr)))


theorem wholeFaceIso_input_reindex :
    Functor.whiskerLeft
      (liftSub (interval Δ) (restrictInclusion (intervalAll (φ.reindex (q ≫ σ)) )) ≫ q).mapElements
      (reindexIso φ A T e σ).hom ≫
      (wholeFaceIso (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
        (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q).hom =
    (wholeFaceIso φ A T e (q ≫ σ)).hom := by
  let l := wholeFaceLine (φ.reindex σ) q
  let r := liftSub (interval Δ) (restrictInclusion (intervalAll (φ.reindex (q ≫ σ)))) ≫ q
  have hn := congrArg Iso.hom (reindexEqualityIso _ _
    (family_full (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e)) l)
  have ho := congrArg Iso.hom (reindexEqualityIso _ _
    (family_full φ A T e) (wholeFaceLine φ (q ≫ σ)))
  exact (congrArg (fun η => Functor.whiskerLeft r.mapElements (reindexIso φ A T e σ).hom ≫ η) hn).trans
    ((congrArg (Functor.whiskerLeft l.mapElements) (reindexIso_full φ A T e σ)).trans ho.symm)


theorem selectedFaceFill_input_reindex (F : Filling T) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) (q ≫ σ)) ψ) :
    selectedFaceFill (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q
      (F.reindex (restrictSubstitution φ σ)) ψ
      (b.map (Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom)) =
    Term.map (Functor.whiskerLeft
      (liftSub (interval Δ) (restrictInclusion (intervalAll (φ.reindex (q ≫ σ)))) ≫ q).mapElements
      (reindexIso φ A T e σ).hom) (selectedFaceFill φ A T e (q ≫ σ) F ψ b) := by
  let δ := intervalAll (φ.reindex (q ≫ σ))
  let r := Functor.whiskerLeft (liftSub (interval Δ) (restrictInclusion δ) ≫ q).mapElements
    (reindexIso φ A T e σ).hom
  let i₀ := wholeFaceIso φ A T e (q ≫ σ)
  let i₁ := wholeFaceIso (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
    (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q
  have hi : i₁.inv = i₀.inv ≫ r :=
    (Iso.eq_inv_comp i₀).mpr ((Iso.comp_inv_eq i₁).mpr (wholeFaceIso_input_reindex φ A T e σ q).symm)
  have hb := congrArg (fun η => (b.reindex (restrictInclusion δ)).map η)
    (wholeFaceIso_input_reindex φ A T e σ q)
  exact (congrArg (fun c => Term.map i₁.inv
    (F.fill (wholeFaceLine φ (q ≫ σ)) (ψ.reindex (restrictInclusion δ)) c)) hb).trans
      (congrArg (fun η => Term.map η (F.fill (wholeFaceLine φ (q ≫ σ))
        (ψ.reindex (restrictInclusion δ)) ((b.reindex (restrictInclusion δ)).map i₀.hom))) hi)


theorem selectedFaceTube_input_reindex (F : Filling T) (ψ : Cofibration Δ)
    (b : OpenBox (reindex (family φ A T e) (q ≫ σ)) ψ) :
    selectedFaceTube (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q
      (F.reindex (restrictSubstitution φ σ)) ψ
      (b.map (Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom)) =
    (selectedFaceTube φ A T e (q ≫ σ) F ψ b).map
      (Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom) := by
  apply PartialSection.ext
  intro x hx
  exact congrArg (fun t => t.val
    ((total (interval (restrictContext (intervalAll (φ.reindex (q ≫ σ)))))).elementsMk x.obj
      ⟨⟨x.val.1,hx⟩,x.val.2⟩)) (selectedFaceFill_input_reindex φ A T e σ q F ψ b)

theorem filling_input_reindex (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful)
    (ψ : Cofibration Δ) (b : OpenBox (reindex (family φ A T e) (q ≫ σ)) ψ) :
    (filling (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e)
      (E.reindex (restrictSubstitution φ σ)) (F.reindex (restrictSubstitution φ σ))
      (hF.reindex _) (G.reindex σ) (hG.reindex _)).fill q ψ
      (b.map (Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom)) =
    Term.map (Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom)
      ((filling φ A T e E F hF G hG).fill (q ≫ σ) ψ b) := by
  let r := Functor.whiskerLeft q.mapElements (reindexIso φ A T e σ).hom
  let t := selectedFaceTube φ A T e (q ≫ σ) F ψ b
  let hc := selectedFaceTube_compatible φ A T e (q ≫ σ) F hF ψ b
  let hz := selectedFaceTube_zero φ A T e (q ≫ σ) F hF ψ b
  let t' := selectedFaceTube (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
    (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q
    (F.reindex (restrictSubstitution φ σ)) ψ (b.map r)
  let hc' := selectedFaceTube_compatible (φ.reindex σ) (reindex A σ)
    (reindex T (restrictSubstitution φ σ))
    (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q
    (F.reindex (restrictSubstitution φ σ)) (hF.reindex _) ψ (b.map r)
  let hz' := selectedFaceTube_zero (φ.reindex σ) (reindex A σ)
    (reindex T (restrictSubstitution φ σ))
    (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q
    (F.reindex (restrictSubstitution φ σ)) (hF.reindex _) ψ (b.map r)
  have hb : addTube (b.map r) t' hc' hz' = (addTube b t hc hz).map r := by
    apply OpenBox.ext
    · exact (PartialSection.glue_congr rfl (selectedFaceTube_input_reindex φ A T e σ q F ψ b)
        hc' (fun x hp hq => congrArg (r.app x) (hc x hp hq))).trans
        (partialGlue_map r b.tube t hc).symm
    · rfl
  exact (congrArg (preliminaryFill (φ.reindex σ) (reindex A σ)
    (reindex T (restrictSubstitution φ σ))
    (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e) q
    (E.reindex (restrictSubstitution φ σ)) (F.reindex (restrictSubstitution φ σ))
    (hF.reindex _) (G.reindex σ) (hG.reindex _) (ψ.join (intervalAll (φ.reindex (q ≫ σ))))) hb).trans
      (preliminaryFill_input_reindex φ A T e σ q E F hF G hG _ (addTube b t hc hz))

theorem filling_reindex_iso (E : HomotopyEquivalence e)
    (F : Filling T) (hF : F.Lawful) (G : Filling A) (hG : G.Lawful) :
    ((filling φ A T e E F hF G hG).reindex σ).transport (reindexIso φ A T e σ) =
    filling (φ.reindex σ) (reindex A σ) (reindex T (restrictSubstitution φ σ))
      (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e)
      (E.reindex (restrictSubstitution φ σ)) (F.reindex (restrictSubstitution φ σ))
      (hF.reindex _) (G.reindex σ) (hG.reindex _) := by
  apply Filling.ext
  intro Ω p ψ b
  let i := Functor.isoWhiskerLeft p.mapElements (reindexIso φ A T e σ)
  have h := filling_input_reindex φ A T e σ p E F hF G hG ψ (b.map i.inv)
  exact h.symm.trans (congrArg (fun c => (filling (φ.reindex σ) (reindex A σ)
    (reindex T (restrictSubstitution φ σ))
    (Functor.whiskerLeft (restrictSubstitution φ σ).mapElements e)
    (E.reindex (restrictSubstitution φ σ)) (F.reindex (restrictSubstitution φ σ))
    (hF.reindex _) (G.reindex σ) (hG.reindex _)).fill p ψ c) (OpenBox.map_iso_roundtrip i b))

end SourceSubstitution

end SquareKit.Cubical.Presheaf.Glue
