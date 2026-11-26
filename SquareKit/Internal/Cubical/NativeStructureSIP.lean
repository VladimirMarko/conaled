import SquareKit.Internal.Cubical.NativeStructurePreservation
import SquareKit.Internal.Cubical.NativeStructureIdentity
import SquareKit.Internal.Cubical.NativeUnivalence

/-! Total structured identity uses native carrier equivalences and the
independent field-preservation family. Its identity fiber retains complete
native field paths. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.StructureIdentity.Native.SIP
open CategoryTheory SquareKit.StructureIdentity EquivalenceFamilies
universe u
namespace Exchange
variable {Γ : Context.{u}} {A : Family Γ} (E S : Family (total A))
def first (B : Family (total A)) : sigma A B ⟶ A where
  app _ := TypeCat.ofHom Sigma.fst
  naturality _ _ _ := rfl
abbrev leftBase : total (sigma A E) ⟶ total A := PiDomain.baseMap (first E)
abbrev rightBase : total (sigma A S) ⟶ total A := PiDomain.baseMap (first S)
abbrev fields : Family (total (sigma A E)) := reindex S (leftBase E)
abbrev witnesses : Family (total (sigma A S)) := reindex E (rightBase S)
def swap : total (witnesses E S) ⟶ total (fields E S) where
  app _ := TypeCat.ofHom (fun z => ⟨⟨z.1.1, ⟨z.1.2.1,z.2⟩⟩,z.1.2.2⟩)
  naturality _ _ _ := rfl
def totalIso (P : Family (total (fields E S))) :
    sigma (sigma A E) (sigma (fields E S) P) ≅
      sigma (sigma A S) (sigma (witnesses E S) (reindex P (swap E S))) where
  hom := {
    app _ := TypeCat.ofHom (fun z => ⟨⟨z.1.1,z.2.1⟩,⟨z.1.2,z.2.2⟩⟩)
    naturality _ _ _ := rfl }
  inv := {
    app _ := TypeCat.ofHom (fun z => ⟨⟨z.1.1,z.2.1⟩,⟨z.1.2,z.2.2⟩⟩)
    naturality _ _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl
end Exchange

private def reindexEquivalence {Γ Δ : Context.{u+1}} {A B : Family Γ}
    (e : Σ f : A ⟶ B, HomotopyEquivalence f) (σ : Δ ⟶ Γ) :
    Σ f : reindex A σ ⟶ reindex B σ, HomotopyEquivalence f :=
  ⟨Functor.whiskerLeft σ.mapElements e.1, e.2.reindex σ⟩

private theorem reindexEquivalence_comp {Γ Δ Θ : Context.{u+1}} {A B : Family Γ}
    (e : Σ f : A ⟶ B, HomotopyEquivalence f) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    reindexEquivalence (reindexEquivalence e σ) τ = reindexEquivalence e (τ ≫ σ) :=
  Sigma.ext rfl (heq_of_eq (e.2.reindex_comp σ τ))

variable {Γ : Context.{u+1}} (D : Description.{u}) (a : Γ ⟶ smallFamilyCodes.{u})

abbrev carrierBase : Family Γ :=
  sigma (SmallUniverse.family Γ) (SmallUniverse.NativeUnivalence.basedEquivalences a)

def unpackCarriers : total (carrierBase a) ⟶
    total (SmallUniverse.NativeUnivalence.basedEquivalences a) :=
  FiberwiseHomotopyRetracts.totalPoint

abbrev carrierProjection : total (carrierBase a) ⟶ total (SmallUniverse.family Γ) :=
  unpackCarriers a ≫ projection (SmallUniverse.NativeUnivalence.basedEquivalences a)

abbrev sourceCarrier : Family (total (carrierBase a)) :=
  reindex (SmallUniverse.liftedDecode a) (projection (carrierBase a))

abbrev targetCarrier : Family (total (carrierBase a)) :=
  reindex (SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ)))
    (carrierProjection a)

noncomputable def carrierEquivalence :
    Σ f : sourceCarrier a ⟶ targetCarrier a, HomotopyEquivalence f :=
  let A := SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingSource a)
  let B := SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ))
  (equivReindexSections A B (carrierProjection a)).symm
    ((generic (EquivalenceFamilies.equiv A B)).reindex (unpackCarriers a))

noncomputable def carrierPointOf
    (e : Σ f : SmallUniverse.liftedDecode a ⟶ SmallUniverse.liftedDecode a,
      HomotopyEquivalence f) : Term (carrierBase a) :=
  let σ := pair (A := SmallUniverse.family Γ) (𝟙 Γ) (SmallUniverse.term a)
  sigmaIntro (SmallUniverse.term a)
    (equivReindexSections
      (SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingSource a))
      (SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ))) σ
      e)

noncomputable def carrierPoint : Term (carrierBase a) :=
  carrierPointOf a ⟨𝟙 _, HomotopyEquivalence.ofIso (Iso.refl _)⟩

variable (s : Term (family D (SmallUniverse.liftedDecode a)))

abbrev targetData : Family (total (carrierBase a)) := family D (targetCarrier a)

abbrev sourceCode : total (targetData D a) ⟶ smallFamilyCodes.{u} :=
  projection (targetData D a) ≫ projection (carrierBase a) ≫ a

abbrev targetCode : total (targetData D a) ⟶ smallFamilyCodes.{u} :=
  projection (targetData D a) ≫ carrierProjection a ≫
    SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ)

noncomputable def sourceStructure :
    Term (family D (SmallUniverse.liftedDecode (sourceCode D a))) :=
  reindexTerm D (reindexTerm D s (projection (carrierBase a))) (projection (targetData D a))

noncomputable def targetStructure :
    Term (family D (SmallUniverse.liftedDecode (targetCode D a))) :=
  Term.map (reindexIso D (targetCarrier a) (projection (targetData D a))).hom
    (generic (targetData D a))

noncomputable def preservationWitnesses : Family (total (targetData D a)) :=
  preserves D (Functor.whiskerLeft (projection (targetData D a)).mapElements (carrierEquivalence a).1)
    (Functor.whiskerLeft (projection (targetData D a)).mapElements (carrierEquivalence a).2.selectedInverse)
    (sourceStructure D a s) (targetStructure D a)

noncomputable def sourceObject := objectOf D (sourceCode D a) (sourceStructure D a s)
noncomputable def targetObject := objectOf D (targetCode D a) (targetStructure D a)

noncomputable def uaPath : Term (SigmaPaths.base (sourceObject D a s) (targetObject D a)) :=
  Term.map (SmallUniverse.NativeUnivalence.equivToPath (sourceCode D a) (targetCode D a))
    (equivSections (SmallUniverse.liftedDecode (sourceCode D a))
      (SmallUniverse.liftedDecode (targetCode D a))
      ⟨Functor.whiskerLeft (projection (targetData D a)).mapElements (carrierEquivalence a).1,
        (carrierEquivalence a).2.reindex (projection (targetData D a))⟩)

noncomputable def uaFields : Family (total (targetData D a)) :=
  reindex (StructuredIdentity.StructuredPaths.fields (sourceObject D a s) (targetObject D a))
    (pair (𝟙 _) (uaPath D a s))

noncomputable def targetDataFilling : {F : Filling (targetData D a) // F.Lawful} :=
  filling D
    ((SmallUniverse.NativeDecode.filling (SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ))).reindex
      (carrierProjection a))
    ((SmallUniverse.NativeDecode.filling_lawful _).reindex _)

noncomputable def preservationWitnessesFilling :
    {F : Filling (preservationWitnesses D a s) // F.Lawful} :=
  preservesFilling D _ _ (sourceStructure D a s) (targetStructure D a)
    (SmallUniverse.NativeDecode.filling (sourceCode D a))
    (SmallUniverse.NativeDecode.filling_lawful _)
    (SmallUniverse.NativeDecode.filling (targetCode D a))
    (SmallUniverse.NativeDecode.filling_lawful _)

noncomputable def uaFieldsFilling : {F : Filling (uaFields D a s) // F.Lawful} :=
  let c := SmallUniverse.NativeUnivalence.movingTarget (Γ := total (targetData D a))
  let F := filling D (SmallUniverse.NativeDecode.filling c) (SmallUniverse.NativeDecode.filling_lawful c)
  ⟨(StructuredIdentity.StructuredPaths.fieldsFilling (sourceObject D a s) (targetObject D a) F.1 F.2).reindex _,
    (StructuredIdentity.StructuredPaths.fieldsFilling_lawful (sourceObject D a s) (targetObject D a) F.1 F.2).reindex _⟩

noncomputable def targetFields : Family (total (carrierBase a)) :=
  preservationTargets D (carrierEquivalence a).1 (carrierEquivalence a).2.selectedInverse
    (reindexTerm D s (projection (carrierBase a)))

noncomputable def totalFamily : Family Γ := sigma (carrierBase a) (targetFields D a s)

noncomputable def carrierBaseFilling : Filling (carrierBase a) :=
  sigmaFilling (SmallUniverse.filling Γ) (SmallUniverse.filling_lawful Γ)
    (SmallUniverse.NativeUnivalence.basedEquivalencesFilling a)

theorem carrierBaseFilling_lawful : (carrierBaseFilling a).Lawful :=
  sigmaFilling_lawful _ (SmallUniverse.filling_lawful Γ) _
    (SmallUniverse.NativeUnivalence.basedEquivalencesFilling_lawful a)

noncomputable def targetFieldsFilling : {F : Filling (targetFields D a s) // F.Lawful} :=
  preservationTargetsFilling D (carrierEquivalence a).1 (carrierEquivalence a).2.selectedInverse
    (reindexTerm D s (projection (carrierBase a)))
    ((SmallUniverse.NativeDecode.filling a).reindex (projection (carrierBase a)))
    ((SmallUniverse.NativeDecode.filling_lawful a).reindex _)
    ((SmallUniverse.NativeDecode.filling (SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ))).reindex
      (carrierProjection a))
    ((SmallUniverse.NativeDecode.filling_lawful _).reindex _)

theorem carrierEquivalence_at
    (e : Σ f : SmallUniverse.liftedDecode a ⟶ SmallUniverse.liftedDecode a,
      HomotopyEquivalence f) :
    let τ := pair (A := carrierBase a) (𝟙 Γ) (carrierPointOf a e)
    (⟨Functor.whiskerLeft τ.mapElements (carrierEquivalence a).1,
      (carrierEquivalence a).2.reindex τ⟩ :
      Σ f : SmallUniverse.liftedDecode a ⟶ SmallUniverse.liftedDecode a,
        HomotopyEquivalence f) =
      e := by
  let A := SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingSource a)
  let B := SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ))
  let E := EquivalenceFamilies.equiv A B
  let τ := pair (A := carrierBase a) (𝟙 Γ) (carrierPointOf a e)
  have h := equivReindexSections_symm_reindex A B (carrierProjection a) τ
    ((generic E).reindex (unpackCarriers a))
  refine h.symm.trans ?_
  let σ := pair (A := SmallUniverse.family Γ) (𝟙 Γ) (SmallUniverse.term a)
  have ht : ((generic E).reindex (unpackCarriers a)).reindex τ =
      (equivReindexSections A B σ) e := by
    apply Term.ext
    intro x
    rfl
  exact (congrArg (equivReindexSections A B σ).symm ht).trans (Equiv.symm_apply_apply _ _)


noncomputable def identityFiberIso :
    reindex (targetFields D a s) (pair (𝟙 Γ) (carrierPoint a)) ≅
      preservationTargets D (𝟙 (SmallUniverse.liftedDecode a))
        (𝟙 (SmallUniverse.liftedDecode a)) s := by
  let τ := pair (A := carrierBase a) (𝟙 Γ) (carrierPoint a)
  let e : Σ f : SmallUniverse.liftedDecode a ⟶ SmallUniverse.liftedDecode a,
      HomotopyEquivalence f :=
    ⟨Functor.whiskerLeft τ.mapElements (carrierEquivalence a).1,
      (carrierEquivalence a).2.reindex τ⟩
  have he : e = ⟨𝟙 _, HomotopyEquivalence.ofIso (Iso.refl _)⟩ := carrierEquivalence_at a _
  have hi : (e.2).selectedInverse =
      Functor.whiskerLeft τ.mapElements (carrierEquivalence a).2.selectedInverse := by
    ext x b
    rfl
  have hs : reindexTerm D (reindexTerm D s (projection (carrierBase a))) τ = s :=
    (reindexTerm_comp D s (projection (carrierBase a)) τ).trans (reindexTerm_id D s)
  refine preservationTargetsReindexIso D (carrierEquivalence a).1
    (carrierEquivalence a).2.selectedInverse
    (reindexTerm D s (projection (carrierBase a))) τ ≪≫ eqToIso ?_
  refine (congrArg (fun t => preservationTargets D
    (Functor.whiskerLeft τ.mapElements (carrierEquivalence a).1)
    (Functor.whiskerLeft τ.mapElements (carrierEquivalence a).2.selectedInverse) t) hs).trans ?_
  refine (congrArg (fun g => preservationTargets D e.1 g s) hi.symm).trans ?_
  refine (congrArg (fun e : Σ f : SmallUniverse.liftedDecode a ⟶ SmallUniverse.liftedDecode a,
      HomotopyEquivalence f => preservationTargets D e.1 e.2.selectedInverse s) he).trans ?_
  apply congrArg (fun g => preservationTargets D (𝟙 _) g s)
  ext x b
  rfl

noncomputable def totalContractible : HomotopyContractible (totalFamily D a s) :=
  StructuredIdentity.totalContractibleOfFiber (targetFields D a s)
    (SmallUniverse.NativeUnivalence.equivalenceTotal a) (carrierPoint a)
    ((identityTargetsContractible D s).transport (identityFiberIso D a s).symm)
    (carrierBaseFilling a) (carrierBaseFilling_lawful a)
    (targetFieldsFilling D a s).1 (targetFieldsFilling D a s).2

abbrev objectFields : Family (total (SmallUniverse.family Γ)) :=
  family D (SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ)))

noncomputable def targetDataIso :
    Exchange.fields (SmallUniverse.NativeUnivalence.basedEquivalences a) (objectFields D (Γ := Γ)) ≅
      targetData D a :=
  reindexIso D (SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ)))
    (carrierProjection a)

noncomputable def exchangedWitnesses :=
  reindex (preservationWitnesses D a s) (PiDomain.baseMap (targetDataIso D a).hom)

/-- An object equivalence retains the chosen carrier equivalence and the
independently defined native preservation witness. -/
noncomputable def relation : Family (total (objects D Γ)) :=
  sigma (Exchange.witnesses (SmallUniverse.NativeUnivalence.basedEquivalences a) (objectFields D))
    (reindex (exchangedWitnesses D a s)
      (Exchange.swap (SmallUniverse.NativeUnivalence.basedEquivalences a) (objectFields D)))

/-- Reorder carrier, equivalence, fields and preservation without discarding data. -/
noncomputable def totalRelationIso : totalFamily D a s ≅ sigma (objects D Γ) (relation D a s) :=
  sigmaSecondIso (carrierBase a)
    (PiDomain.sigmaCongr (targetDataIso D a) (preservationWitnesses D a s)).symm ≪≫
  Exchange.totalIso (SmallUniverse.NativeUnivalence.basedEquivalences a) (objectFields D)
    (exchangedWitnesses D a s)

theorem totalRelationIso_equivalence (x : Γ.Elements) (z : (totalFamily D a s).obj x) :
    ((totalRelationIso D a s).hom.app x z).2.1 = z.1.2 := rfl

noncomputable def relationFilling : {F : Filling (relation D a s) // F.Lawful} :=
  let E := SmallUniverse.NativeUnivalence.basedEquivalences a
  let S := objectFields D (Γ := Γ)
  let FE := (SmallUniverse.NativeUnivalence.basedEquivalencesFilling a).reindex (Exchange.rightBase S)
  have hFE := (SmallUniverse.NativeUnivalence.basedEquivalencesFilling_lawful a).reindex (Exchange.rightBase S)
  let FR := (preservationWitnessesFilling D a s).1.reindex
    (Exchange.swap E S ≫ PiDomain.baseMap (targetDataIso D a).hom)
  have hFR := (preservationWitnessesFilling D a s).2.reindex
    (Exchange.swap E S ≫ PiDomain.baseMap (targetDataIso D a).hom)
  ⟨sigmaFilling FE hFE FR, sigmaFilling_lawful FE hFE FR hFR⟩

noncomputable def relationTotalContractible :
    HomotopyContractible (sigma (objects D Γ) (relation D a s)) :=
  (totalContractible D a s).transport (totalRelationIso D a s)

theorem carrierEquivalence_map_at :
    Functor.whiskerLeft (pair (A := carrierBase a) (𝟙 Γ) (carrierPoint a)).mapElements
      (carrierEquivalence a).1 = 𝟙 (SmallUniverse.liftedDecode a) :=
  congrArg Sigma.fst (carrierEquivalence_at a _)

theorem carrierEquivalence_inverse_at :
    Functor.whiskerLeft (pair (A := carrierBase a) (𝟙 Γ) (carrierPoint a)).mapElements
      (carrierEquivalence a).2.selectedInverse = 𝟙 (SmallUniverse.liftedDecode a) := by
  have h := congrArg (fun e : Σ f : SmallUniverse.liftedDecode a ⟶ SmallUniverse.liftedDecode a,
      HomotopyEquivalence f => e.2.selectedInverse) (carrierEquivalence_at a
    ⟨𝟙 _, HomotopyEquivalence.ofIso (Iso.refl _)⟩)
  refine h.trans ?_
  ext x b
  rfl

noncomputable def identityFieldBase :=
  liftSub (targetData D a) (pair (A := carrierBase a) (𝟙 Γ) (carrierPoint a))

noncomputable def identityWitnessIso :
    reindex (preservationWitnesses D a s) (identityFieldBase D a) ≅
      homogeneousPath
        (family D (reindex (SmallUniverse.liftedDecode a)
          (projection (reindex (targetData D a) (pair (𝟙 Γ) (carrierPoint a))))))
        (reindexTerm D (sourceStructure D a s) (identityFieldBase D a))
        (reindexTerm D (targetStructure D a) (identityFieldBase D a)) := by
  let τ := pair (A := carrierBase a) (𝟙 Γ) (carrierPoint a)
  let π := projection (reindex (targetData D a) τ)
  let ρ := identityFieldBase D a
  let s₀ := reindexTerm D (sourceStructure D a s) ρ
  let t₀ := reindexTerm D (targetStructure D a) ρ
  have hf : Functor.whiskerLeft ρ.mapElements
      (Functor.whiskerLeft (projection (targetData D a)).mapElements (carrierEquivalence a).1) =
      𝟙 (reindex (SmallUniverse.liftedDecode a) π) :=
    congrArg (fun f => Functor.whiskerLeft π.mapElements f) (carrierEquivalence_map_at a)
  have hg : Functor.whiskerLeft ρ.mapElements
      (Functor.whiskerLeft (projection (targetData D a)).mapElements (carrierEquivalence a).2.selectedInverse) =
      𝟙 (reindex (SmallUniverse.liftedDecode a) π) :=
    congrArg (fun f => Functor.whiskerLeft π.mapElements f) (carrierEquivalence_inverse_at a)
  exact preservesReindexIso D _ _ (sourceStructure D a s) (targetStructure D a) ρ ≪≫
    eqToIso (congrArg₂ (fun f g => preserves D f g s₀ t₀) hf hg) ≪≫ identityPathIso D s₀ t₀

theorem uaPath_beta : uaPath D a s =
    SmallUniverse.NativeUnivalence.ua (sourceCode D a) (targetCode D a)
      (Functor.whiskerLeft (projection (targetData D a)).mapElements (carrierEquivalence a).1)
      ((carrierEquivalence a).2.reindex (projection (targetData D a))) :=
  SmallUniverse.NativeUnivalence.equivToPath_beta _ _

noncomputable def identityUa :=
  SmallUniverse.NativeUnivalence.ua a a (𝟙 _) (HomotopyEquivalence.ofIso (Iso.refl _))

theorem uaPath_at :
    SmallUniverse.NativeUnivalence.reindexPath (uaPath D a s) (identityFieldBase D a) =
      SmallUniverse.NativeUnivalence.reindexPath (identityUa a)
        (projection (reindex (targetData D a) (pair (𝟙 Γ) (carrierPoint a)))) := by
  let τ := pair (A := carrierBase a) (𝟙 Γ) (carrierPoint a)
  let π := projection (reindex (targetData D a) τ)
  let ρ := identityFieldBase D a
  let E := carrierEquivalence a
  let i : Σ f : SmallUniverse.liftedDecode a ⟶ SmallUniverse.liftedDecode a, HomotopyEquivalence f :=
    ⟨𝟙 _, HomotopyEquivalence.ofIso (Iso.refl _)⟩
  have h := congrArg (fun e : Σ f : SmallUniverse.liftedDecode a ⟶ SmallUniverse.liftedDecode a,
      HomotopyEquivalence f => reindexEquivalence e π) (carrierEquivalence_at a i)
  have he : reindexEquivalence (reindexEquivalence E (projection (targetData D a))) ρ =
      reindexEquivalence i π :=
    (reindexEquivalence_comp E (projection (targetData D a)) ρ).trans
      ((reindexEquivalence_comp E τ π).symm.trans h)
  have hu := congrArg (fun e : Σ f : reindex (SmallUniverse.liftedDecode a) π ⟶
      reindex (SmallUniverse.liftedDecode a) π, HomotopyEquivalence f =>
      SmallUniverse.NativeUnivalence.ua (π ≫ a) (π ≫ a) e.1 e.2) he
  exact (congrArg (fun p => SmallUniverse.NativeUnivalence.reindexPath p ρ) (uaPath_beta D a s)).trans
    ((SmallUniverse.NativeUnivalence.ua_reindex _ _ _ _ ρ).trans
      (hu.trans (SmallUniverse.NativeUnivalence.ua_reindex _ _ _ _ π).symm))

section EndpointComparison

private def preservationPairIso {Γ : Context.{u+1}} (D : Description.{u}) {A B : Family Γ}
    (e₀ e₁ : Σ f : A ⟶ B, HomotopyEquivalence f) (g₀ g₁ : B ⟶ A)
    (S₀ S₁ : Term (family D A)) (T₀ T₁ : Term (family D B))
    (he : e₀ = e₁) (hi₀ : e₀.2.selectedInverse = g₀) (hi₁ : e₁.2.selectedInverse = g₁)
    (hs : S₀ = S₁) (ht : T₀ = T₁) :
    preserves D e₀.1 g₀ S₀ T₀ ≅ preserves D e₁.1 g₁ S₁ T₁ :=
  eqToIso ((congrArg (fun g => preserves D e₀.1 g S₀ T₀) hi₀.symm).trans
    ((congrArg₂ (preserves D e₀.1 e₀.2.selectedInverse) hs ht).trans
      ((congrArg (fun e : Σ f : A ⟶ B, HomotopyEquivalence f =>
        preserves D e.1 e.2.selectedInverse S₁ T₁) he).trans
        (congrArg (fun g => preserves D e₁.1 g S₁ T₁) hi₁))))

variable {Γ : Context.{u+1}} (D : Description.{u})
  (a b : Γ ⟶ smallFamilyCodes.{u})
  (s : Term (family D (SmallUniverse.liftedDecode a)))
  (t : Term (family D (SmallUniverse.liftedDecode b)))
private theorem relation_target_at :
  let τ := pair (A := objects D Γ) (𝟙 Γ) (objectOf D b t)
  let E := Exchange.witnesses (SmallUniverse.NativeUnivalence.basedEquivalences a) (objectFields D)
  let ρ := liftSub E τ ≫
    Exchange.swap (SmallUniverse.NativeUnivalence.basedEquivalences a) (objectFields D) ≫
    PiDomain.baseMap (targetDataIso D a).hom
  reindexTerm D (targetStructure D a) ρ = reindexTerm D t (projection (reindex E τ)) := by
  let τ := pair (A := objects D Γ) (𝟙 Γ) (objectOf D b t)
  let E := Exchange.witnesses (SmallUniverse.NativeUnivalence.basedEquivalences a) (objectFields D)
  let B := SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ))
  let σ := pair (A := SmallUniverse.family Γ) (𝟙 Γ) (SmallUniverse.term b)
  let ρ := liftSub E τ ≫
    Exchange.swap (SmallUniverse.NativeUnivalence.basedEquivalences a) (objectFields D) ≫
    PiDomain.baseMap (targetDataIso D a).hom
  let π := projection (targetData D a)
  apply Term.ext
  intro x
  let π₀ := projection (reindex E τ)
  let v := (reindexIso D B σ).inv.app (π₀.mapElements.obj x) (t.val (π₀.mapElements.obj x))
  have h₁ := congrArg (fun m => m.app x ((generic (targetData D a)).val (ρ.mapElements.obj x)))
    (reindexIso_comp D (targetCarrier a) π ρ)
  have h₂ := congrArg (fun m => m.app x v)
    (reindexIso_comp D B (carrierProjection a) (ρ ≫ π))
  have h₃ := congrArg (fun m => m.app x v) (reindexIso_comp D B σ π₀)
  exact h₁.trans (h₂.trans (h₃.symm.trans
    (congrArg ((reindexIso D (SmallUniverse.liftedDecode b) π₀).hom.app x)
      ((reindexIso D B σ).inv_hom_id_app_apply (π₀.mapElements.obj x) (t.val (π₀.mapElements.obj x))))))

-- Full chosen-equivalence normalization exceeds the default heartbeat budget.
-- The separated proof checks at 400k with the default recursion depth.
set_option maxHeartbeats 400000 in
private theorem relation_equivalence_at :
  let τ := pair (A := objects D Γ) (𝟙 Γ) (objectOf D b t)
  let E := Exchange.witnesses (SmallUniverse.NativeUnivalence.basedEquivalences a) (objectFields D)
  let A := SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingSource a)
  let B := SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ))
  let σ := pair (A := SmallUniverse.family Γ) (𝟙 Γ) (SmallUniverse.term b)
  let i : reindex E τ ≅ EquivalenceFamilies.equiv (SmallUniverse.liftedDecode a) (SmallUniverse.liftedDecode b) :=
    EquivalenceFamilies.equivReindexIso A B σ
  let ρ := liftSub E τ ≫
    Exchange.swap (SmallUniverse.NativeUnivalence.basedEquivalences a) (objectFields D) ≫
    PiDomain.baseMap (targetDataIso D a).hom
  let π := projection (targetData D a)
  let e := carrierEquivalence a
  let π₀ := projection (reindex E τ)
  let κ := PiDomain.baseMap i.hom
  let e' := genericEquivalence (SmallUniverse.liftedDecode a) (SmallUniverse.liftedDecode b)
  let E₀ : Σ f : reindex (SmallUniverse.liftedDecode a) π₀ ⟶
      reindex (SmallUniverse.liftedDecode b) π₀, HomotopyEquivalence f :=
    ⟨Functor.whiskerLeft (ρ ≫ π).mapElements e.1, e.2.reindex (ρ ≫ π)⟩
  let E₁ : Σ f : reindex (SmallUniverse.liftedDecode a) π₀ ⟶
      reindex (SmallUniverse.liftedDecode b) π₀, HomotopyEquivalence f :=
    ⟨Functor.whiskerLeft κ.mapElements e'.1, e'.2.reindex κ⟩
  E₀ = E₁ := by
  let τ := pair (A := objects D Γ) (𝟙 Γ) (objectOf D b t)
  let E := Exchange.witnesses (SmallUniverse.NativeUnivalence.basedEquivalences a) (objectFields D)
  let A := SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingSource a)
  let B := SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ))
  let σ := pair (A := SmallUniverse.family Γ) (𝟙 Γ) (SmallUniverse.term b)
  let i : reindex E τ ≅ EquivalenceFamilies.equiv (SmallUniverse.liftedDecode a) (SmallUniverse.liftedDecode b) :=
    EquivalenceFamilies.equivReindexIso A B σ
  let ρ := liftSub E τ ≫
    Exchange.swap (SmallUniverse.NativeUnivalence.basedEquivalences a) (objectFields D) ≫
    PiDomain.baseMap (targetDataIso D a).hom
  let π := projection (targetData D a)
  let e := carrierEquivalence a
  let π₀ := projection (reindex E τ)
  let C' := EquivalenceFamilies.equiv (SmallUniverse.liftedDecode a) (SmallUniverse.liftedDecode b)
  let π' := projection C'
  let κ := PiDomain.baseMap i.hom
  let e' := genericEquivalence (SmallUniverse.liftedDecode a) (SmallUniverse.liftedDecode b)
  let E₀ : Σ f : reindex (SmallUniverse.liftedDecode a) π₀ ⟶
      reindex (SmallUniverse.liftedDecode b) π₀, HomotopyEquivalence f :=
    ⟨Functor.whiskerLeft (ρ ≫ π).mapElements e.1, e.2.reindex (ρ ≫ π)⟩
  let E₁ : Σ f : reindex (SmallUniverse.liftedDecode a) π₀ ⟶
      reindex (SmallUniverse.liftedDecode b) π₀, HomotopyEquivalence f :=
    ⟨Functor.whiskerLeft κ.mapElements e'.1, e'.2.reindex κ⟩
  have h₀ : (EquivalenceFamilies.equivReindexSections A B (π₀ ≫ σ)).symm
      (generic (reindex E τ)) = E₀ :=
    equivReindexSections_symm_reindex A B (carrierProjection a) (ρ ≫ π)
      (Term.reindex (generic (EquivalenceFamilies.equiv A B)) (unpackCarriers a))
  have h₁ : (EquivalenceFamilies.equivReindexSections (reindex A σ) (reindex B σ) π₀).symm
      (Term.map (Functor.whiskerLeft π₀.mapElements i.hom) (generic (reindex E τ))) = E₁ :=
    equivReindexSections_symm_reindex (reindex A σ) (reindex B σ) π' κ (generic C')
  have h := congrArg
    (EquivalenceFamilies.equivReindexSections (reindex A σ) (reindex B σ) π₀).symm
    (EquivalenceFamilies.equivReindexIso_hom_reindex_sections A B σ π₀ (generic (reindex E τ)))
  exact h₀.symm.trans ((h.trans (Equiv.symm_apply_apply _ _)).symm.trans h₁)


private noncomputable def relationFieldsAtIso :
    let τ := pair (A := objects D Γ) (𝟙 Γ) (objectOf D b t)
    let E := Exchange.witnesses (SmallUniverse.NativeUnivalence.basedEquivalences a) (objectFields D)
    let R := reindex (exchangedWitnesses D a s)
      (Exchange.swap (SmallUniverse.NativeUnivalence.basedEquivalences a) (objectFields D))
    let A := SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingSource a)
    let B := SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ))
    let σ := pair (A := SmallUniverse.family Γ) (𝟙 Γ) (SmallUniverse.term b)
    let i := EquivalenceFamilies.equivReindexIso A B σ
    reindex R (liftSub E τ) ≅ reindex (equivalenceFields D s t) (PiDomain.baseMap i.hom) := by
  let τ := pair (A := objects D Γ) (𝟙 Γ) (objectOf D b t)
  let E := Exchange.witnesses (SmallUniverse.NativeUnivalence.basedEquivalences a) (objectFields D)
  let R := reindex (exchangedWitnesses D a s)
    (Exchange.swap (SmallUniverse.NativeUnivalence.basedEquivalences a) (objectFields D))
  let A := SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingSource a)
  let B := SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ))
  let σ := pair (A := SmallUniverse.family Γ) (𝟙 Γ) (SmallUniverse.term b)
  let i : reindex E τ ≅ EquivalenceFamilies.equiv (SmallUniverse.liftedDecode a) (SmallUniverse.liftedDecode b) :=
    EquivalenceFamilies.equivReindexIso A B σ
  let ρ := liftSub E τ ≫
    Exchange.swap (SmallUniverse.NativeUnivalence.basedEquivalences a) (objectFields D) ≫
    PiDomain.baseMap (targetDataIso D a).hom
  let π := projection (targetData D a)
  let e := carrierEquivalence a
  have hs : reindexTerm D (sourceStructure D a s) ρ = reindexTerm D s (projection (reindex E τ)) :=
    (reindexTerm_comp D (reindexTerm D s (projection (carrierBase a))) π ρ).trans
      (reindexTerm_comp D s (projection (carrierBase a)) (ρ ≫ π))
  have ht := relation_target_at D a b t

  let π₀ := projection (reindex E τ)
  let C' := EquivalenceFamilies.equiv (SmallUniverse.liftedDecode a) (SmallUniverse.liftedDecode b)
  let π' := projection C'
  let κ := PiDomain.baseMap i.hom
  let e' := genericEquivalence (SmallUniverse.liftedDecode a) (SmallUniverse.liftedDecode b)
  let E₀ : Σ f : reindex (SmallUniverse.liftedDecode a) π₀ ⟶
      reindex (SmallUniverse.liftedDecode b) π₀, HomotopyEquivalence f :=
    ⟨Functor.whiskerLeft (ρ ≫ π).mapElements e.1, e.2.reindex (ρ ≫ π)⟩
  let E₁ : Σ f : reindex (SmallUniverse.liftedDecode a) π₀ ⟶
      reindex (SmallUniverse.liftedDecode b) π₀, HomotopyEquivalence f :=
    ⟨Functor.whiskerLeft κ.mapElements e'.1, e'.2.reindex κ⟩
  have he := relation_equivalence_at D a b t
  have hi₀ : E₀.2.selectedInverse = Functor.whiskerLeft ρ.mapElements
      (Functor.whiskerLeft π.mapElements e.2.selectedInverse) := by
    ext x y
    rfl
  have hi₁ : E₁.2.selectedInverse = Functor.whiskerLeft κ.mapElements e'.2.selectedInverse := by
    ext x y
    rfl
  let s' := reindexTerm D s π'
  let t' := reindexTerm D t π'
  have hs' : reindexTerm D (sourceStructure D a s) ρ = reindexTerm D s' κ :=
    hs.trans (reindexTerm_comp D s π' κ).symm
  have ht' : reindexTerm D (targetStructure D a) ρ = reindexTerm D t' κ :=
    ht.trans (reindexTerm_comp D t π' κ).symm
  let j₀ := preservesReindexIso D (Functor.whiskerLeft π.mapElements e.1)
    (Functor.whiskerLeft π.mapElements e.2.selectedInverse)
    (sourceStructure D a s) (targetStructure D a) ρ
  let j₁ := preservesReindexIso D e'.1 e'.2.selectedInverse s' t' κ
  exact j₀ ≪≫ preservationPairIso D E₀ E₁ _ _ _ _ _ _ he hi₀ hi₁ hs' ht' ≪≫ j₁.symm
/-- Fix both endpoints of the based preservation relation without discarding witnesses. -/
noncomputable def relationAtIso :
    reindex (relation D a s) (pair (𝟙 Γ) (objectOf D b t)) ≅ equivalences D s t := by
  let τ := pair (A := objects D Γ) (𝟙 Γ) (objectOf D b t)
  let E := Exchange.witnesses (SmallUniverse.NativeUnivalence.basedEquivalences a) (objectFields D)
  let R := reindex (exchangedWitnesses D a s)
    (Exchange.swap (SmallUniverse.NativeUnivalence.basedEquivalences a) (objectFields D))
  let A := SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingSource a)
  let B := SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ))
  let σ := pair (A := SmallUniverse.family Γ) (𝟙 Γ) (SmallUniverse.term b)
  let i : reindex E τ ≅ EquivalenceFamilies.equiv (SmallUniverse.liftedDecode a) (SmallUniverse.liftedDecode b) :=
    EquivalenceFamilies.equivReindexIso A B σ
  exact eqToIso (sigma_reindex E R τ) ≪≫
    sigmaSecondIso (reindex E τ) (relationFieldsAtIso D a b s t) ≪≫
    PiDomain.sigmaCongr i (equivalenceFields D s t)

/-- The endpoint comparison retains the complete witness in canonical carrier coordinates. -/
theorem relationAtIso_inv_equivalence_canonical (x : Γ.Elements) (w : (equivalences D s t).obj x) :
    let A := SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingSource a)
    let B := SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ))
    let σ := pair (A := SmallUniverse.family Γ) (𝟙 Γ) (SmallUniverse.term b)
    ((relationAtIso D a b s t).inv.app x w).1 =
      (EquivalenceFamilies.equivReindexIso A B σ).inv.app x w.1 := rfl

end EndpointComparison

end SquareKit.Cubical.Presheaf.StructureIdentity.Native.SIP
