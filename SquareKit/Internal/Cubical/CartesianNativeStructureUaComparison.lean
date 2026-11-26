import SquareKit.Internal.Cubical.CartesianNativeStructureIdentity
import SquareKit.Internal.Cubical.CartesianNativeStructurePreservation
import SquareKit.Internal.Cubical.CartesianNativeStructureSIP
import SquareKit.Internal.Cubical.CartesianNativeStructureLaws

/-! Independent field preservation compared with field paths along native ua. -/

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.StructuredIdentity.UaComparison
open CategoryTheory
universe u

private def pathIsoOfEq {Γ : Context.{u}} {F G : Family (total (interval Γ))}
    {a : Term (reindex F (endpointSub Γ false))} {b : Term (reindex F (endpointSub Γ true))}
    {a' : Term (reindex G (endpointSub Γ false))} {b' : Term (reindex G (endpointSub Γ true))}
    (h : F = G) (ha : ∀ x, HEq (a.val x) (a'.val x)) (hb : ∀ x, HEq (b.val x) (b'.val x)) :
    path F a b ≅ path G a' b' := by
  subst G
  have h₀ : a = a' := Term.ext (fun x => eq_of_heq (ha x))
  have h₁ : b = b' := Term.ext (fun x => eq_of_heq (hb x))
  subst a'
  subst b'
  exact Iso.refl _

private theorem fields_evaluation {Γ : Context.{u}} {A : Family Γ} {S : Family (total A)}
    (z₀ z₁ : Term (sigma A S)) (p : Term (SigmaPaths.base z₀ z₁)) :
    liftSub (interval (total (StructuredPaths.P z₀ z₁))) (pair (𝟙 Γ) p) ≫
      FieldsAlong.evaluation (StructuredPaths.liftedZero z₀ z₁)
        (StructuredPaths.liftedOne z₀ z₁) (StructuredPaths.genericBase z₀ z₁) ≫
      liftSub A (projection (StructuredPaths.P z₀ z₁)) = FieldsAlong.evaluation z₀ z₁ p := by
  ext I z
  apply congrArg (Sigma.mk _)
  exact congrArg (fun f => (p.val (Γ.elementsMk I z.1)).val.val f z.2)
    (Category.id_comp (𝟙 (Γ.elementsMk I z.1)))

/-- The generic field-path family specializes to the specified complete carrier path. -/
noncomputable def fieldsAtIso {Γ : Context.{u}} {A : Family Γ} {S : Family (total A)}
    (z₀ z₁ : Term (sigma A S)) (p : Term (SigmaPaths.base z₀ z₁)) :
    reindex (StructuredPaths.fields z₀ z₁) (pair (𝟙 Γ) p) ≅ FieldsAlong.family z₀ z₁ p := by
  let Z₀ := StructuredPaths.liftedZero z₀ z₁
  let Z₁ := StructuredPaths.liftedOne z₀ z₁
  let P := StructuredPaths.genericBase z₀ z₁
  let i := pathReindexIso (reindex (StructuredPaths.liftedB z₀ z₁)
    (FieldsAlong.evaluation Z₀ Z₁ P)) (FieldsAlong.zero Z₀ Z₁ P) (FieldsAlong.one Z₀ Z₁ P)
    (pair (𝟙 Γ) p)
  refine i ≪≫ pathIsoOfEq (congrArg (reindex S) (fields_evaluation z₀ z₁ p)) ?_ ?_
  · intro x
    exact (Term.sigmaSndOver_val Z₀ _ _ ((pair (A := SigmaPaths.base z₀ z₁) (𝟙 Γ) p).mapElements.obj x)).trans
      (Term.sigmaSndOver_val z₀ _ _ x).symm
  · intro x
    exact (Term.sigmaSndOver_val Z₁ _ _ ((pair (A := SigmaPaths.base z₀ z₁) (𝟙 Γ) p).mapElements.obj x)).trans
      (Term.sigmaSndOver_val z₁ _ _ x).symm

private def reindexStructuredTerm {Γ Δ : Context.{u}} {A : Family Γ}
    {S : Family (total A)} (z : Term (sigma A S)) (σ : Δ ⟶ Γ) :
    Term (sigma (reindex A σ) (reindex S (liftSub A σ))) := Term.reindex z σ

/-- Substitution retains every generalized value of a dependent field path. -/
noncomputable def fieldsAlongReindexIso {Γ Δ : Context.{u}} {A : Family Γ}
    {S : Family (total A)} (z₀ z₁ : Term (sigma A S))
    (p : Term (SigmaPaths.base z₀ z₁)) (σ : Δ ⟶ Γ) :
    reindex (FieldsAlong.family z₀ z₁ p) σ ≅
      FieldsAlong.family (reindexStructuredTerm z₀ σ) (reindexStructuredTerm z₁ σ) (homogeneousReindex p σ) := by
  let i := pathReindexIso (reindex S (FieldsAlong.evaluation z₀ z₁ p))
    (FieldsAlong.zero z₀ z₁ p) (FieldsAlong.one z₀ z₁ p) σ
  have he : FieldsAlong.evaluation (reindexStructuredTerm z₀ σ) (reindexStructuredTerm z₁ σ)
      (homogeneousReindex p σ) ≫ liftSub A σ =
      liftSub (interval Γ) σ ≫ FieldsAlong.evaluation z₀ z₁ p := by
    ext I z
    rfl
  refine i ≪≫ pathIsoOfEq (congrArg (reindex S) he.symm) ?_ ?_
  · intro x
    exact (Term.sigmaSndOver_val z₀ _ _ (σ.mapElements.obj x)).trans
      (Term.sigmaSndOver_val (reindexStructuredTerm z₀ σ) _ _ x).symm
  · intro x
    exact (Term.sigmaSndOver_val z₁ _ _ (σ.mapElements.obj x)).trans
      (Term.sigmaSndOver_val (reindexStructuredTerm z₁ σ) _ _ x).symm

/-- Specializing a field-path family commutes with substitution of its complete carrier path. -/
noncomputable def fieldsReindexIso {Γ Δ : Context.{u}} {A : Family Γ}
    {S : Family (total A)} (z₀ z₁ : Term (sigma A S))
    (p : Term (SigmaPaths.base z₀ z₁)) (σ : Δ ⟶ Γ) :
    reindex (reindex (StructuredPaths.fields z₀ z₁) (pair (𝟙 Γ) p)) σ ≅
      reindex (StructuredPaths.fields (reindexStructuredTerm z₀ σ) (reindexStructuredTerm z₁ σ))
        (pair (𝟙 Δ) (homogeneousReindex p σ)) :=
  Functor.isoWhiskerLeft σ.mapElements (fieldsAtIso z₀ z₁ p) ≪≫
    fieldsAlongReindexIso z₀ z₁ p σ ≪≫
    (fieldsAtIso (reindexStructuredTerm z₀ σ) (reindexStructuredTerm z₁ σ)
      (homogeneousReindex p σ)).symm

/-- At the constant carrier path, field paths are ordinary native field paths. -/
noncomputable def fieldsReflIso {Γ : Context.{u}} {A : Family Γ} {S : Family (total A)}
    (a : Term A) (s t : Term (reindex S (pair (𝟙 Γ) a))) :
    reindex (StructuredPaths.fields (sigmaIntro a s) (sigmaIntro a t))
      (pair (𝟙 Γ) (homogeneousRefl a)) ≅ homogeneousPath (reindex S (pair (𝟙 Γ) a)) s t :=
  fieldsAtIso (sigmaIntro a s) (sigmaIntro a t) (homogeneousRefl a)

/-- Change a dependent fiber along a supplied native base path by actual filling. -/
noncomputable def alongPath {Γ : Context.{u}} {A : Family Γ} (R : Family (total A))
    (p q : Term A) (h : Term (homogeneousPath A p q)) (F : Filling R) (hF : F.Lawful) :
    Σ f : reindex R (pair (𝟙 Γ) p) ⟶ reindex R (pair (𝟙 Γ) q), HomotopyEquivalence f := by
  let ev := pair (projection (interval Γ)) (pathApp h)
  have h₀ : endpointSub Γ false ≫ ev = pair (𝟙 Γ) p := by
    ext I z
    exact congrArg (Sigma.mk _) (congrArg (fun t => t.val (Γ.elementsMk I z)) (pathApp_zero h))
  have h₁ : endpointSub Γ true ≫ ev = pair (𝟙 Γ) q := by
    ext I z
    exact congrArg (Sigma.mk _) (congrArg (fun t => t.val (Γ.elementsMk I z)) (pathApp_one h))
  exact ⟨_, IntervalTransport.equivalenceTo (F.reindex ev) (hF.reindex ev) (endpoint Γ false) (endpoint Γ true)
    (reindex R (pair (𝟙 Γ) p)) (reindex R (pair (𝟙 Γ) q))
    (congrArg (reindex R) h₀) (congrArg (reindex R) h₁)⟩

/-- A native comparison to the constant carrier loop identifies the entire field-path family. -/
noncomputable def fieldsFromLoop {Γ : Context.{u}} {A : Family Γ} {S : Family (total A)}
    (a : Term A) (s t : Term (reindex S (pair (𝟙 Γ) a)))
    (p : Term (homogeneousPath A a a))
    (h : Term (homogeneousPath (homogeneousPath A a a) (homogeneousRefl a) p))
    (FS : Filling S) (hFS : FS.Lawful) :
    Σ f : homogeneousPath (reindex S (pair (𝟙 Γ) a)) s t ⟶
      reindex (StructuredPaths.fields (sigmaIntro a s) (sigmaIntro a t)) (pair (𝟙 Γ) p),
      HomotopyEquivalence f := by
  let z₀ := sigmaIntro a s
  let z₁ := sigmaIntro a t
  let E := alongPath (StructuredPaths.fields z₀ z₁) (homogeneousRefl a) p h
    (StructuredPaths.fieldsFilling z₀ z₁ FS hFS) (StructuredPaths.fieldsFilling_lawful z₀ z₁ FS hFS)
  exact ⟨_, E.2.conjugateIso (fieldsReflIso a s t).symm (Iso.refl _)⟩

/-- The selected native identity equivalence gives the complete field-path comparison. -/
noncomputable def fieldsAtIdentity {Γ : Context.{u+1}}
    (S : Family (total (SmallUniverse.family Γ)))
    (a : Γ ⟶ smallFamilyCodes.{u})
    (s t : Term (reindex S (pair (𝟙 Γ) (SmallUniverse.term a))))
    (FS : Filling S) (hFS : FS.Lawful) :
    Σ f : homogeneousPath (reindex S (pair (𝟙 Γ) (SmallUniverse.term a))) s t ⟶
      reindex (StructuredPaths.fields (sigmaIntro (SmallUniverse.term a) s)
        (sigmaIntro (SmallUniverse.term a) t))
        (pair (𝟙 Γ) (SmallUniverse.NativeUnivalence.ua a a (𝟙 _) (HomotopyEquivalence.ofIso (Iso.refl _) (SmallUniverse.NativeDecode.filling a) (SmallUniverse.NativeDecode.filling_lawful a)))),
      HomotopyEquivalence f :=
  fieldsFromLoop (SmallUniverse.term a) s t _
    (homogeneousReverse (SmallUniverse.NativeUnivalence.pathsFilling a a) (SmallUniverse.NativeUnivalence.pathsFilling_lawful a a) (SmallUniverse.NativeUnivalence.uaIdentity a)) FS hFS

/-- A witness over one point extends over a native contractible base by dependent filling. -/
noncomputable def extendSection {Γ : Context.{u}} {A : Family Γ}
    (c : Contractible A) (a : Term A) (Q : Family (total A))
    (q : Term (reindex Q (pair (𝟙 Γ) a)))
    (FA : Filling A) (hFA : FA.Lawful) (FQ : Filling Q) : Term Q :=
  let π := projection A
  let p := HomotopyLevels.pathOfContractible (c.reindex π) (FA.reindex π) (hFA.reindex π)
    (Term.reindex a π) (generic A)
  Term.map (IdentitySystem.map A a Q q FQ) p

/-- Compare dependent families over every target using a comparison at one base point.
The base and target indices are retained throughout. -/
noncomputable def equivalenceFromPoint {Γ : Context.{u}} {A : Family Γ}
    (c : Contractible A) (a : Term A) (T : Family (total A))
    (R Q : Family (total T))
    (f : reindex R (liftSub T (pair (𝟙 Γ) a)) ⟶
      reindex Q (liftSub T (pair (𝟙 Γ) a))) (E : HomotopyEquivalence f)
    (FA : Filling A) (hFA : FA.Lawful) (FT : Filling T) (hFT : FT.Lawful)
    (FR : Filling R) (hFR : FR.Lawful) (FQ : Filling Q) (hFQ : FQ.Lawful) :
    Σ g : R ⟶ Q, HomotopyEquivalence g := by
  let σ := pair (𝟙 Γ) a
  let K := EquivalenceFamilies.equiv R Q
  let p : Term (reindex (pi T K) σ) :=
    Term.map (piReindexIso T K σ).inv
      (lam (EquivalenceFamilies.equivReindexSections R Q (liftSub T σ) ⟨f, E⟩))
  let FK := EquivalenceFamilies.equivFilling FR hFR FQ hFQ
  let h := extendSection c a (pi T K) p FA hFA (piFilling FT hFT FK)
  exact (EquivalenceFamilies.equivSections R Q).symm (app h)

-- Check conjugation on abstract fibers before specializing the semantic families.
private noncomputable def equivalenceFromPointIso {Γ : Context.{u}} {A : Family Γ}
    (c : Contractible A) (a : Term A) (T : Family (total A))
    (R Q : Family (total T)) (I : Family (total (reindex T (pair (𝟙 Γ) a))))
    (i : reindex R (liftSub T (pair (𝟙 Γ) a)) ≅ I)
    (e : Σ f : I ⟶ reindex Q (liftSub T (pair (𝟙 Γ) a)), HomotopyEquivalence f)
    (FA : Filling A) (hFA : FA.Lawful) (FT : Filling T) (hFT : FT.Lawful)
    (FR : Filling R) (hFR : FR.Lawful) (FQ : Filling Q) (hFQ : FQ.Lawful) :
    Σ g : R ⟶ Q, HomotopyEquivalence g :=
  equivalenceFromPoint c a T R Q (i.hom ≫ e.1) (e.2.conjugateIso i (Iso.refl _))
    FA hFA FT hFT FR hFR FQ hFQ

/-- Include a selected dependent fiber without changing its base index. -/
noncomputable def includeFiber {Γ : Context.{u}} {A : Family Γ} (B : Family (total A)) (a : Term A) :
  reindex B (pair (𝟙 Γ) a) ⟶ sigma A B :=
  IntervalTransport.mapOfSection (sigmaIntro (B := reindex B (liftSub A (projection (reindex B (pair (𝟙 Γ) a)))))
    (Term.reindex a (projection (reindex B (pair (𝟙 Γ) a))))
    (generic (reindex B (pair (𝟙 Γ) a))))
noncomputable def fieldsToWhole {Γ : Context.{u}} {A : Family Γ} {S : Family (total A)}
  (z₀ z₁ : Term (sigma A S)) (p : Term (SigmaPaths.base z₀ z₁)) :
  reindex (StructuredPaths.fields z₀ z₁) (pair (𝟙 Γ) p) ⟶ SigmaPaths.whole z₀ z₁ :=
  includeFiber (StructuredPaths.fields z₀ z₁) p ≫ (StructuredPaths.wholeIso z₀ z₁).inv
/-- Reconstruction retains the entire supplied carrier path and field path. -/
theorem fieldsToWhole_components {Γ : Context.{u}} {A : Family Γ} {S : Family (total A)}
    (z₀ z₁ : Term (sigma A S)) (p : Term (SigmaPaths.base z₀ z₁))
    (x : Γ.Elements) (q : (reindex (StructuredPaths.fields z₀ z₁) (pair (𝟙 Γ) p)).obj x) :
    (StructuredPaths.wholeIso z₀ z₁).hom.app x ((fieldsToWhole z₀ z₁ p).app x q) = ⟨p.val x, q⟩ :=
  congrArg (fun f => f.app x ⟨p.val x, q⟩) (StructuredPaths.wholeIso z₀ z₁).inv_hom_id

/-- The reconstructed carrier is the prescribed whole native path. -/
theorem fieldsToWhole_carrier {Γ : Context.{u}} {A : Family Γ} {S : Family (total A)}
    (z₀ z₁ : Term (sigma A S)) (p : Term (SigmaPaths.base z₀ z₁))
    (x : Γ.Elements) (q : (reindex (StructuredPaths.fields z₀ z₁) (pair (𝟙 Γ) p)).obj x) :
    SigmaPaths.first z₀ z₁ ((fieldsToWhole z₀ z₁ p).app x q) = p.val x := rfl

theorem fieldsToWhole_fields {Γ : Context.{u}} {A : Family Γ} {S : Family (total A)}
    (z₀ z₁ : Term (sigma A S)) (p : Term (SigmaPaths.base z₀ z₁))
    (x : Γ.Elements) (q : (reindex (StructuredPaths.fields z₀ z₁) (pair (𝟙 Γ) p)).obj x) :
    SigmaPaths.second z₀ z₁ ((fieldsToWhole z₀ z₁ p).app x q) =
      StructuredPaths.fieldToDependent z₀ z₁ (p.val x) q :=
  StructuredPaths.wholeIso_inv_fields z₀ z₁ x ⟨p.val x, q⟩

private noncomputable def basedMapAt {Γ : Context.{u}} {A : Family Γ}
    (a : Term A) {R : Family (total A)} (f : R ⟶ IdentitySystem.paths A a) (z : Term A) :
    reindex R (pair (𝟙 Γ) z) ⟶ homogeneousPath A a z :=
  Functor.whiskerLeft (pair (𝟙 Γ) z).mapElements f ≫
    (EquivalenceFamilies.homogeneousReindexIso (reindex A (projection A))
      (Term.reindex a (projection A)) (generic A) (pair (𝟙 Γ) z)).hom

private noncomputable def basedMapAtEquivalence {Γ : Context.{u}} {A : Family Γ}
    (a : Term A) {R : Family (total A)} (f : R ⟶ IdentitySystem.paths A a)
    (e : HomotopyEquivalence f) (z : Term A) : HomotopyEquivalence (basedMapAt a f z) :=
  (e.reindex (pair (𝟙 Γ) z)).conjugateIso (Iso.refl _)
    (EquivalenceFamilies.homogeneousReindexIso (reindex A (projection A))
      (Term.reindex a (projection A)) (generic A) (pair (𝟙 Γ) z))

private noncomputable def recoveryRightAt {Γ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (E : HomotopyEquivalence f) (b : Term B) :
    Term (homogeneousPath B (Term.map f (Term.map (TotalRecovery.inverse f E) b)) b) :=
  Term.map (EquivalenceFamilies.homogeneousReindexIso (reindex B (projection B))
    (Term.map (Functor.whiskerLeft (projection B).mapElements f)
      (Term.map (Functor.whiskerLeft (projection B).mapElements (TotalRecovery.inverse f E)) (generic B)))
    (generic B) (pair (𝟙 Γ) b)).hom
    (Term.reindex (TotalRecovery.rightInverse f E) (pair (𝟙 Γ) b))

private noncomputable def recoveryLeftAt {Γ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (E : HomotopyEquivalence f) (F : Filling A) (hF : F.Lawful) (a : Term A) :
    Term (homogeneousPath A (Term.map (TotalRecovery.inverse f E) (Term.map f a)) a) :=
  Term.map (EquivalenceFamilies.homogeneousReindexIso (reindex A (projection A))
    (Term.map (Functor.whiskerLeft (projection A).mapElements (TotalRecovery.inverse f E))
      (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A)))
    (generic A) (pair (𝟙 Γ) a)).hom
    (Term.reindex (TotalRecovery.leftInverse f E F hF) (pair (𝟙 Γ) a))

section Description
open SquareKit.StructureIdentity StructureIdentity.Native SmallUniverse SmallUniverse.NativeUnivalence

noncomputable def identityLoopReindex {Γ Δ : Context.{u+1}}
    (a : Γ ⟶ smallFamilyCodes.{u}) (σ : Δ ⟶ Γ) :
    Term (homogeneousPath (paths (σ ≫ a) (σ ≫ a))
      (homogeneousRefl (term (σ ≫ a))) (reindexPath (StructureIdentity.Native.SIP.identityUa a) σ)) := by
  let q := homogeneousReindex (uaIdentity a) σ
  let f := (EquivalenceFamilies.homogeneousReindexIso (SmallUniverse.family Γ) (term a) (term a) σ).hom
  let h := Term.map (HomotopyLevels.pathMap f _ _) q
  exact homogeneousReverse (pathsFilling (σ ≫ a) (σ ≫ a))
    (pathsFilling_lawful (σ ≫ a) (σ ≫ a)) h

private theorem objectOf_field_reindex {Γ Δ : Context.{u+1}} (D : Description.{u})
    (a : Γ ⟶ smallFamilyCodes.{u})
    (s : Term (StructureIdentity.Native.family D (SmallUniverse.liftedDecode a)))
    (σ : Δ ⟶ Γ) :
    let A := SmallUniverse.liftedDecode (SmallUniverse.code (generic (SmallUniverse.family Γ)))
    let δ := pair (A := SmallUniverse.family Γ) (𝟙 Γ) (SmallUniverse.term a)
    Term.map (reindexIso D A (σ ≫ δ)).hom
      (Term.reindex (sigmaSnd (B := StructureIdentity.Native.family D A) (objectOf D a s)) σ) =
        reindexTerm D s σ := by
  let A := SmallUniverse.liftedDecode (SmallUniverse.code (generic (SmallUniverse.family Γ)))
  let δ := pair (A := SmallUniverse.family Γ) (𝟙 Γ) (SmallUniverse.term a)
  let t := sigmaSnd (B := StructureIdentity.Native.family D A) (objectOf D a s)
  have h : Term.map (reindexIso D A δ).hom t = s := by
    apply Term.ext
    intro x
    exact (reindexIso D A δ).inv_hom_id_app_apply x (s.val x)
  exact (reindexIso_comp_map D δ σ t).symm.trans (congrArg (fun t => reindexTerm D t σ) h)

variable {Γ : Context.{u+1}} (D : Description.{u}) (a : Γ ⟶ smallFamilyCodes.{u})
  (s : Term (StructureIdentity.Native.family D (SmallUniverse.liftedDecode a)))

noncomputable def identitySource : Term (sigma
    (SmallUniverse.family (total (reindex (SIP.targetData D a) (pair (𝟙 Γ) (SIP.carrierPoint a)))))
    (reindex (SIP.objectFields D (Γ := total (SIP.targetData D a)))
      (liftSub (SmallUniverse.family _) (SIP.identityFieldBase D a)))) :=
  Term.reindex (SIP.sourceObject D a s) (SIP.identityFieldBase D a)
noncomputable def identityTarget : Term (sigma
    (SmallUniverse.family (total (reindex (SIP.targetData D a) (pair (𝟙 Γ) (SIP.carrierPoint a)))))
    (reindex (SIP.objectFields D (Γ := total (SIP.targetData D a)))
      (liftSub (SmallUniverse.family _) (SIP.identityFieldBase D a)))) :=
  Term.reindex (SIP.targetObject D a) (SIP.identityFieldBase D a)
noncomputable def identityFieldPath :=
  homogeneousPath _ (sigmaSnd (identitySource D a s)) (sigmaSnd (identityTarget D a))
noncomputable def identityFieldEquivalence :
  Σ f : identityFieldPath D a s ⟶ reindex (SIP.uaFields D a s) (SIP.identityFieldBase D a),
    HomotopyEquivalence f := by
  let ρ := SIP.identityFieldBase D a
  let π := projection (reindex (SIP.targetData D a) (pair (𝟙 Γ) (SIP.carrierPoint a)))
  let z₀ := identitySource D a s
  let z₁ := identityTarget D a
  let p := homogeneousReindex (SIP.uaPath D a s) ρ
  have h : Term (homogeneousPath (homogeneousPath _ (sigmaFst z₀) (sigmaFst z₀))
      (homogeneousRefl (sigmaFst z₀)) p) := by
    change Term (homogeneousPath (paths (π ≫ a) (π ≫ a))
      (homogeneousRefl (term (π ≫ a))) (reindexPath (SIP.uaPath D a s) ρ))
    rw [SIP.uaPath_at]
    exact identityLoopReindex a π
  let c := movingTarget (Γ := total (SIP.targetData D a))
  let F := StructureIdentity.Native.filling D (NativeDecode.filling c) (NativeDecode.filling_lawful c)
  let E := fieldsFromLoop (sigmaFst z₀) (sigmaSnd z₀) (sigmaSnd z₁) p h
    (F.1.reindex (liftSub (SmallUniverse.family _) ρ))
    (F.2.reindex (liftSub (SmallUniverse.family _) ρ))
  exact ⟨_, E.2.conjugateIso (Iso.refl _)
    (fieldsReindexIso (SIP.sourceObject D a s) (SIP.targetObject D a) (SIP.uaPath D a s) ρ).symm⟩

noncomputable def identityFieldPathIso :
    identityFieldPath D a s ≅
      homogeneousPath
        (StructureIdentity.Native.family D (reindex (SmallUniverse.liftedDecode a)
          (projection (reindex (SIP.targetData D a) (pair (𝟙 Γ) (SIP.carrierPoint a))))))
        (reindexTerm D (SIP.sourceStructure D a s) (SIP.identityFieldBase D a))
        (reindexTerm D (SIP.targetStructure D a) (SIP.identityFieldBase D a)) := by
  let Γ₀ := total (SIP.targetData D a)
  let A := SmallUniverse.liftedDecode (SmallUniverse.code (generic (SmallUniverse.family Γ₀)))
  let ρ := SIP.identityFieldBase D a
  let δ := pair (A := SmallUniverse.family Γ₀) (𝟙 Γ₀) (SmallUniverse.term (SIP.sourceCode D a))
  let e := reindexIso D A (ρ ≫ δ)
  have hs : Term.map e.hom (sigmaSnd (identitySource D a s)) =
      reindexTerm D (SIP.sourceStructure D a s) ρ :=
    objectOf_field_reindex D (SIP.sourceCode D a) (SIP.sourceStructure D a s) ρ
  have ht : Term.map e.hom (sigmaSnd (identityTarget D a)) =
      reindexTerm D (SIP.targetStructure D a) ρ :=
    objectOf_field_reindex D (SIP.targetCode D a) (SIP.targetStructure D a) ρ
  exact HomotopyLevels.pathCongr e (sigmaSnd (identitySource D a s)) (sigmaSnd (identityTarget D a)) ≪≫
    eqToIso (congrArg₂ (fun l r => homogeneousPath _ l r) hs ht)

/-- Independent preservation determines fields along the exact selected native ua. -/
noncomputable def preservationFieldsEquivalence :
    Σ f : SIP.preservationWitnesses D a s ⟶ SIP.uaFields D a s, HomotopyEquivalence f := by
  let i := SIP.identityWitnessIso D a s ≪≫ (identityFieldPathIso D a s).symm
  let e := identityFieldEquivalence D a s
  let F := SIP.targetDataFilling D a
  let R := SIP.preservationWitnessesFilling D a s
  let Q := SIP.uaFieldsFilling D a s
  exact equivalenceFromPointIso (equivalenceTotal a) (SIP.carrierPoint a)
    (SIP.targetData D a) (SIP.preservationWitnesses D a s) (SIP.uaFields D a s)
    (identityFieldPath D a s) i e
    (SIP.carrierBaseFilling a) (SIP.carrierBaseFilling_lawful a)
    F.1 F.2 R.1 R.2 Q.1 Q.2

/-- Reconstruct the whole structured path, retaining the supplied carrier equivalence. -/
noncomputable def preservationToWhole : SIP.preservationWitnesses D a s ⟶
    SigmaPaths.whole (SIP.sourceObject D a s) (SIP.targetObject D a) :=
  (preservationFieldsEquivalence D a s).1 ≫
    fieldsToWhole (SIP.sourceObject D a s) (SIP.targetObject D a) (SIP.uaPath D a s)

theorem preservationToWhole_components (x : (total (SIP.targetData D a)).Elements)
    (q : (SIP.preservationWitnesses D a s).obj x) :
    (StructuredPaths.wholeIso (SIP.sourceObject D a s) (SIP.targetObject D a)).hom.app x
      ((preservationToWhole D a s).app x q) =
        ⟨(SIP.uaPath D a s).val x, (preservationFieldsEquivalence D a s).1.app x q⟩ :=
  fieldsToWhole_components _ _ _ x _

theorem preservationToWhole_carrier (x : (total (SIP.targetData D a)).Elements)
    (q : (SIP.preservationWitnesses D a s).obj x) :
    SigmaPaths.first (SIP.sourceObject D a s) (SIP.targetObject D a)
      ((preservationToWhole D a s).app x q) = (SIP.uaPath D a s).val x :=
  fieldsToWhole_carrier _ _ _ x _

theorem preservationToWhole_fields (x : (total (SIP.targetData D a)).Elements)
    (q : (SIP.preservationWitnesses D a s).obj x) :
    SigmaPaths.second (SIP.sourceObject D a s) (SIP.targetObject D a)
      ((preservationToWhole D a s).app x q) =
        StructuredPaths.fieldToDependent (SIP.sourceObject D a s) (SIP.targetObject D a)
          ((SIP.uaPath D a s).val x) ((preservationFieldsEquivalence D a s).1.app x q) :=
  fieldsToWhole_fields _ _ _ x _

private noncomputable def relationMapEquivalence
  (f : SIP.relation D a s ⟶ IdentitySystem.paths (objects D Γ) (objectOf D a s)) :
  HomotopyEquivalence f := by
  let A := objects D Γ
  let FA := objectsFilling D Γ
  let R := SIP.relationFilling D a s
  exact HomotopyEquivalence.ofContractibleTotals f FA.1 FA.2 R.1 R.2
    (pathFilling ((FA.1.reindex (projection A)).reindex (projection (interval (total A))))
      ((FA.2.reindex _).reindex _) _ _)
    (pathFilling_lawful ((FA.1.reindex (projection A)).reindex (projection (interval (total A))))
      ((FA.2.reindex _).reindex _) _ _)
    (SIP.relationTotalContractible D a s) (ForwardSingleton.contractible A (objectOf D a s) FA.1 FA.2)

section Endpoints
variable {Γ : Context.{u+1}} (D : Description.{u}) (z : Term (objects D Γ))
def endpointCode : Γ ⟶ smallFamilyCodes.{u} := SmallUniverse.code (sigmaFst z)
def endpointFields : Term (StructureIdentity.Native.family D (SmallUniverse.liftedDecode (endpointCode D z))) :=
  let A := SmallUniverse.liftedDecode (SmallUniverse.code (generic (SmallUniverse.family Γ)))
  Term.map (reindexIso D A (pair (𝟙 Γ) (sigmaFst z))).hom (sigmaSnd z)
theorem endpoint_eta : objectOf D (endpointCode D z) (endpointFields D z) = z := objectOf_eta D z

noncomputable def endpointPathIso (w : Term (objects D Γ)) :
    homogeneousPath (objects D Γ)
      (objectOf D (endpointCode D z) (endpointFields D z))
      (objectOf D (endpointCode D w) (endpointFields D w)) ≅
    homogeneousPath (objects D Γ) z w :=
  eqToIso (congrArg₂ (fun x y => homogeneousPath (objects D Γ) x y)
    (endpoint_eta D z) (endpoint_eta D w))

end Endpoints

end Description

section Models
open CategoryTheory SquareKit.StructureIdentity StructureIdentity.Native
variable {Γ : Context.{u+1}} (T : Specification.{u}) (z w : Term (modelObjects T Γ))
noncomputable def modelPathInverse :
    homogeneousPath (objects T.description Γ) (sigmaFst z) (sigmaFst w) ⟶
      homogeneousPath (modelObjects T Γ) z w :=
  let O := objectsFilling T.description Γ
  let C := objectConditionsFilling T Γ
  PropositionExtension.pathInverse (objectConditions T Γ) z w (objectConditionsIsProp T Γ)
    O.1 O.2 C.1 C.2
noncomputable def modelPathInverseEquivalence : HomotopyEquivalence (modelPathInverse T z w) :=
  let O := objectsFilling T.description Γ
  let C := objectConditionsFilling T Γ
  PropositionExtension.pathInverseEquivalence (objectConditions T Γ) z w (objectConditionsIsProp T Γ)
    O.1 O.2 C.1 C.2
noncomputable def modelPathInverseProjection
    (p : Term (homogeneousPath (objects T.description Γ) (sigmaFst z) (sigmaFst w))) :
    Term (homogeneousPath (homogeneousPath (objects T.description Γ) (sigmaFst z) (sigmaFst w))
      (Term.map (HomotopyLevels.pathMap (PropositionExtension.first (objectConditions T Γ)) z w)
        (Term.map (modelPathInverse T z w) p)) p) :=
  let O := objectsFilling T.description Γ
  let C := objectConditionsFilling T Γ
  PropositionExtension.pathInverseProjection (objectConditions T Γ) z w (objectConditionsIsProp T Γ)
    O.1 O.2 C.1 C.2 p

end Models

end SquareKit.Cubical.Cartesian.StructuredIdentity.UaComparison

namespace SquareKit.Cubical.Cartesian.StructuredIdentity.UaComparison.Reordered
open CategoryTheory SquareKit.StructureIdentity StructureIdentity.Native
universe u
noncomputable section
variable {Γ : Context.{u+1}} (D : Description.{u}) (a : Γ ⟶ smallFamilyCodes.{u})
  (s : Term (family D (SmallUniverse.liftedDecode a)))

abbrev R := SIP.relation D a s
abbrev Ω := total (R D a s)
abbrev base : Ω D a s ⟶ Γ := projection (R D a s) ≫ projection (objects D Γ)
abbrev E := SIP.Exchange.witnesses (SmallUniverse.NativeUnivalence.basedEquivalences a) (SIP.objectFields D)
abbrev P := reindex (SIP.exchangedWitnesses D a s)
  (SIP.Exchange.swap (SmallUniverse.NativeUnivalence.basedEquivalences a) (SIP.objectFields D))
noncomputable def equivalenceIndex : Ω D a s ⟶ total (E D a) :=
  PiDomain.baseMap (SIP.Exchange.first (P D a s))
noncomputable def dataIndex : Ω D a s ⟶ total (SIP.targetData D a) :=
  equivalenceIndex D a s ≫
    SIP.Exchange.swap (SmallUniverse.NativeUnivalence.basedEquivalences a) (SIP.objectFields D) ≫
    PiDomain.baseMap (SIP.targetDataIso D a).hom
noncomputable def witness : Term (reindex (SIP.preservationWitnesses D a s) (dataIndex D a s)) :=
  Term.reindex (generic (P D a s)) FiberwiseHomotopyRetracts.totalPoint

noncomputable def source : Term (objects D (Ω D a s)) :=
  Term.map (objectsReindexIso D (base D a s)).hom
    (Term.reindex (objectOf D a s) (base D a s))
noncomputable def target : Term (objects D (Ω D a s)) :=
  Term.map (objectsReindexIso D (base D a s)).hom
    (Term.reindex (generic (objects D Γ)) (projection (R D a s)))

theorem source_eq :
    Term.map (objectsReindexIso D (dataIndex D a s)).hom
      (Term.reindex (SIP.sourceObject D a s) (dataIndex D a s)) = source D a s := by
  change Term.map (objectsReindexIso D (dataIndex D a s)).hom
    (Term.reindex (objectOf D (SIP.sourceCode D a) (SIP.sourceStructure D a s)) (dataIndex D a s)) = _
  rw [objectOf_reindex]
  change _ = Term.map (objectsReindexIso D (base D a s)).hom (Term.reindex (objectOf D a s) _)
  rw [objectOf_reindex]
  apply congrArg (objectOf D (base D a s ≫ a))
  exact (reindexTerm_comp D (reindexTerm D s (projection (SIP.carrierBase a)))
    (projection (SIP.targetData D a)) (dataIndex D a s)).trans
    (reindexTerm_comp D s (projection (SIP.carrierBase a))
      (dataIndex D a s ≫ projection (SIP.targetData D a)))

theorem target_eq :
    Term.map (objectsReindexIso D (dataIndex D a s)).hom
      (Term.reindex (SIP.targetObject D a) (dataIndex D a s)) = target D a s := by
  change Term.map (objectsReindexIso D (dataIndex D a s)).hom
    (Term.reindex (objectOf D (SIP.targetCode D a) (SIP.targetStructure D a)) (dataIndex D a s)) = _
  rw [objectOf_reindex]
  let z := target D a s
  let U := SmallUniverse.family (Ω D a s)
  let A := SmallUniverse.liftedDecode (SmallUniverse.code (generic U))
  let σ := pair (A := U) (𝟙 _) (sigmaFst z)
  have hs : reindexTerm D (SIP.targetStructure D a) (dataIndex D a s) =
      Term.map (reindexIso D A σ).hom (sigmaSnd z) := by
    apply Term.ext
    intro x
    have h₀ := congrArg (fun m => m.app x
      ((SIP.targetDataIso D a).hom.app
        ((dataIndex D a s ≫ projection (SIP.targetData D a)).mapElements.obj x)
        (x.val.1.2.2)))
      (reindexIso_comp D (SIP.targetCarrier a) (projection (SIP.targetData D a)) (dataIndex D a s))
    let AΓ := SmallUniverse.liftedDecode (SmallUniverse.code (generic (SmallUniverse.family Γ)))
    have h₁ := congrArg (fun m => m.app x (x.val.1.2.2))
      (reindexIso_comp D AΓ (SIP.carrierProjection a)
        (dataIndex D a s ≫ projection (SIP.targetData D a)))
    have h₂ := congrArg (fun m => m.app x (x.val.1.2.2))
      (reindexIso_comp D AΓ (liftSub (SmallUniverse.family Γ) (base D a s)) σ)
    exact h₀.trans (h₁.trans h₂.symm)
  exact (congrArg (objectOf D (dataIndex D a s ≫ SIP.targetCode D a)) hs).trans (objectOf_eta D z)

variable (f : SIP.preservationWitnesses D a s ⟶
  homogeneousPath (objects D (total (SIP.targetData D a)))
    (SIP.sourceObject D a s) (SIP.targetObject D a))

noncomputable def rawPath : Term (homogeneousPath (objects D (Ω D a s))
    (Term.map (objectsReindexIso D (dataIndex D a s)).hom
      (Term.reindex (SIP.sourceObject D a s) (dataIndex D a s)))
    (Term.map (objectsReindexIso D (dataIndex D a s)).hom
      (Term.reindex (SIP.targetObject D a) (dataIndex D a s)))) :=
  Term.map (HomotopyLevels.pathMap (objectsReindexIso D (dataIndex D a s)).hom _ _)
    (Term.map (EquivalenceFamilies.homogeneousReindexIso
      (objects D (total (SIP.targetData D a))) (SIP.sourceObject D a s)
      (SIP.targetObject D a) (dataIndex D a s)).hom
      (Term.map (Functor.whiskerLeft (dataIndex D a s).mapElements f) (witness D a s)))

noncomputable def normalizedPath : Term (homogeneousPath (objects D (Ω D a s))
    (source D a s) (target D a s)) :=
  pathLam (pathApp (rawPath D a s f))
    ((pathApp_zero _).trans (source_eq D a s))
    ((pathApp_one _).trans (target_eq D a s))

noncomputable def basedPathIso :
    reindex (IdentitySystem.paths (objects D Γ) (objectOf D a s)) (projection (R D a s)) ≅
      homogeneousPath (objects D (Ω D a s)) (source D a s) (target D a s) :=
  EquivalenceFamilies.homogeneousReindexIso
    (reindex (objects D Γ) (projection (objects D Γ)))
    (Term.reindex (objectOf D a s) (projection (objects D Γ)))
    (generic (objects D Γ)) (projection (R D a s)) ≪≫
  HomotopyLevels.pathCongr (objectsReindexIso D (base D a s))
    (Term.reindex (objectOf D a s) (base D a s))
    (Term.reindex (generic (objects D Γ)) (projection (R D a s)))

noncomputable def map : R D a s ⟶ IdentitySystem.paths (objects D Γ) (objectOf D a s) :=
  IntervalTransport.mapOfSection
    (Term.map (basedPathIso D a s).inv (normalizedPath D a s f))

theorem map_body :
    pathApp (Term.map (basedPathIso D a s).hom
      (Term.map (Functor.whiskerLeft (projection (R D a s)).mapElements (map D a s f))
        (generic (R D a s)))) = pathApp (rawPath D a s f) := by
  change pathApp (Term.map (basedPathIso D a s).hom
    (Term.map (basedPathIso D a s).inv (normalizedPath D a s f))) = _
  exact congrArg pathApp
    (Term.map_iso_roundtrip (basedPathIso D a s).symm (normalizedPath D a s f))


theorem map_values {x y : (Ω D a s).Elements} (h : x ⟶ y) (r : (interval (Ω D a s)).obj y) :
    (objectsReindexIso D (base D a s)).hom.app y
      (((map D a s f).app ((projection (R D a s)).mapElements.obj x) x.val.2).val.val
        ((projection (R D a s)).mapElements.map h) r) =
    (objectsReindexIso D (dataIndex D a s)).hom.app y
      ((f.app ((dataIndex D a s).mapElements.obj x) ((witness D a s).val x)).val.val
        ((dataIndex D a s).mapElements.map h) r) := by
  let p := Term.map (basedPathIso D a s).hom
    (Term.map (Functor.whiskerLeft (projection (R D a s)).mapElements (map D a s f))
      (generic (R D a s)))
  have h₀ := congrArg (fun t => (t.val x).val.val h r) (pathLam_app p)
  have h₁ := congrArg (fun t => (t.val x).val.val h r) (pathLam_app (rawPath D a s f))
  have hb := congrArg (fun t => t.val (extendObj (interval (Ω D a s)) y r)) (map_body D a s f)
  exact h₀.symm.trans (hb.trans h₁)

theorem map_carrier_values {x y : (Ω D a s).Elements} (h : x ⟶ y)
    (r : (interval (Ω D a s)).obj y) :
    ((((map D a s f).app ((projection (R D a s)).mapElements.obj x) x.val.2).val.val
      ((projection (R D a s)).mapElements.map h) r)).1 =
    (((f.app ((dataIndex D a s).mapElements.obj x) ((witness D a s).val x)).val.val
      ((dataIndex D a s).mapElements.map h) r)).1 :=
  congrArg Sigma.fst (map_values D a s f h r)

end
end SquareKit.Cubical.Cartesian.StructuredIdentity.UaComparison.Reordered

namespace SquareKit.Cubical.Cartesian.StructuredIdentity.UaComparison
open CategoryTheory SquareKit.StructureIdentity StructureIdentity.Native
universe u
variable {Γ : Context.{u+1}} (D : Description.{u}) (a : Γ ⟶ smallFamilyCodes.{u})
  (s : Term (family D (SmallUniverse.liftedDecode a)))
  (f : SIP.preservationWitnesses D a s ⟶
    homogeneousPath (objects D (total (SIP.targetData D a)))
      (SIP.sourceObject D a s) (SIP.targetObject D a))
noncomputable def reorderToPaths :
    SIP.relation D a s ⟶ IdentitySystem.paths (objects D Γ) (objectOf D a s) :=
  Reordered.map D a s f


theorem reorderToPaths_values {x y : (total (objects D Γ)).Elements} (h : x ⟶ y)
    (q : (SIP.relation D a s).obj x) (r : (interval (total (objects D Γ))).obj y) :
    (objectsReindexIso D (Reordered.base D a s)).hom.app
      (extendObj (SIP.relation D a s) y ((SIP.relation D a s).map h q))
      (((reorderToPaths D a s f).app x q).val.val h r) =
    (objectsReindexIso D (Reordered.dataIndex D a s)).hom.app
      (extendObj (SIP.relation D a s) y ((SIP.relation D a s).map h q))
      ((f.app ((Reordered.dataIndex D a s).mapElements.obj (extendObj (SIP.relation D a s) x q))
        ((Reordered.witness D a s).val (extendObj (SIP.relation D a s) x q))).val.val
        ((Reordered.dataIndex D a s).mapElements.map (extendHom (SIP.relation D a s) h q)) r) :=
  Reordered.map_values D a s f (extendHom (SIP.relation D a s) h q) r

theorem reorderToPaths_carrier_values {x y : (total (objects D Γ)).Elements} (h : x ⟶ y)
    (q : (SIP.relation D a s).obj x) (r : (interval (total (objects D Γ))).obj y) :
    (((reorderToPaths D a s f).app x q).val.val h r).1 =
    ((f.app ((Reordered.dataIndex D a s).mapElements.obj (extendObj (SIP.relation D a s) x q))
      ((Reordered.witness D a s).val (extendObj (SIP.relation D a s) x q))).val.val
      ((Reordered.dataIndex D a s).mapElements.map (extendHom (SIP.relation D a s) h q)) r).1 :=
  Reordered.map_carrier_values D a s f (extendHom (SIP.relation D a s) h q) r

end SquareKit.Cubical.Cartesian.StructuredIdentity.UaComparison

namespace SquareKit.Cubical.Cartesian.StructuredIdentity.UaComparison
open CategoryTheory SquareKit.StructureIdentity StructureIdentity.Native SmallUniverse
universe u
variable {Γ : Context.{u+1}} (D : Description.{u}) (a : Γ ⟶ smallFamilyCodes.{u})
  (s : Term (StructureIdentity.Native.family D (SmallUniverse.liftedDecode a)))

/-- The actual whole-path reconstruction, before fixing the target object. -/
noncomputable def basedStructuredMap :=
  reorderToPaths D a s (preservationToWhole D a s)

noncomputable def basedStructuredEquivalence : HomotopyEquivalence (basedStructuredMap D a s) :=
  relationMapEquivalence D a s (basedStructuredMap D a s)

noncomputable def structuredMap (z : Term (objects D Γ)) :
    reindex (SIP.relation D a s) (pair (𝟙 Γ) z) ⟶
      homogeneousPath (objects D Γ) (objectOf D a s) z :=
  basedMapAt (objectOf D a s) (basedStructuredMap D a s) z

noncomputable def structuredEquivalence (z : Term (objects D Γ)) :
    HomotopyEquivalence (structuredMap D a s z) :=
  basedMapAtEquivalence (objectOf D a s) (basedStructuredMap D a s)
    (basedStructuredEquivalence D a s) z

noncomputable def structuredInverse (z : Term (objects D Γ)) :=
  TotalRecovery.inverse (structuredMap D a s z) (structuredEquivalence D a s z)
noncomputable def structuredRightInverse (z : Term (objects D Γ)) :=
  TotalRecovery.rightInverse (structuredMap D a s z) (structuredEquivalence D a s z)
noncomputable def structuredLeftInverse (z : Term (objects D Γ)) :=
  let R := SIP.relationFilling D a s
  TotalRecovery.leftInverse (structuredMap D a s z) (structuredEquivalence D a s z)
    (R.1.reindex (pair (𝟙 Γ) z)) (R.2.reindex (pair (𝟙 Γ) z))

noncomputable def explicitMap (b : Γ ⟶ smallFamilyCodes.{u})
    (t : Term (StructureIdentity.Native.family D (SmallUniverse.liftedDecode b))) :
    StructureIdentity.Native.equivalences D s t ⟶
      homogeneousPath (objects D Γ) (objectOf D a s) (objectOf D b t) :=
  (SIP.relationAtIso D a b s t).inv ≫ structuredMap D a s (objectOf D b t)
noncomputable def explicitEquivalence (b : Γ ⟶ smallFamilyCodes.{u})
    (t : Term (StructureIdentity.Native.family D (SmallUniverse.liftedDecode b))) :
    HomotopyEquivalence (explicitMap D a s b t) :=
  (structuredEquivalence D a s (objectOf D b t)).conjugateIso
    (SIP.relationAtIso D a b s t).symm (Iso.refl _)

section ExplicitRecovery
variable (b : Γ ⟶ smallFamilyCodes.{u})
  (t : Term (StructureIdentity.Native.family D (SmallUniverse.liftedDecode b)))
noncomputable def explicitInverse :=
  TotalRecovery.inverse (explicitMap D a s b t) (explicitEquivalence D a s b t)
noncomputable def explicitRightInverse :=
  TotalRecovery.rightInverse (explicitMap D a s b t) (explicitEquivalence D a s b t)
noncomputable def explicitLeftInverse :=
  let F := equivalencesFilling D s t (NativeDecode.filling a) (NativeDecode.filling_lawful a)
    (NativeDecode.filling b) (NativeDecode.filling_lawful b)
  TotalRecovery.leftInverse (explicitMap D a s b t) (explicitEquivalence D a s b t) F.1 F.2
noncomputable def explicitRightInverseAt
    (p : Term (homogeneousPath (objects D Γ) (objectOf D a s) (objectOf D b t))) :
    Term (homogeneousPath (homogeneousPath (objects D Γ) (objectOf D a s) (objectOf D b t))
      (Term.map (explicitMap D a s b t) (Term.map (explicitInverse D a s b t) p)) p) :=
  recoveryRightAt (explicitMap D a s b t) (explicitEquivalence D a s b t) p
noncomputable def explicitLeftInverseAt (q : Term (StructureIdentity.Native.equivalences D s t)) :
    Term (homogeneousPath (StructureIdentity.Native.equivalences D s t)
      (Term.map (explicitInverse D a s b t) (Term.map (explicitMap D a s b t) q)) q) :=
  let F := equivalencesFilling D s t (NativeDecode.filling a) (NativeDecode.filling_lawful a)
    (NativeDecode.filling b) (NativeDecode.filling_lawful b)
  recoveryLeftAt (explicitMap D a s b t) (explicitEquivalence D a s b t) F.1 F.2 q
end ExplicitRecovery

section Raw
variable {Γ : Context.{u+1}} (D : Description.{u}) (z w : Term (objects D Γ))
noncomputable def rawEquivalences : Family Γ :=
  StructureIdentity.Native.equivalences D (endpointFields D z) (endpointFields D w)
noncomputable def rawEquivalencesFilling : {F : Filling (rawEquivalences D z w) // F.Lawful} :=
  equivalencesFilling D (endpointFields D z) (endpointFields D w)
    (NativeDecode.filling (endpointCode D z)) (NativeDecode.filling_lawful (endpointCode D z))
    (NativeDecode.filling (endpointCode D w)) (NativeDecode.filling_lawful (endpointCode D w))
noncomputable def rawMap : rawEquivalences D z w ⟶ homogeneousPath (objects D Γ) z w :=
  explicitMap D (endpointCode D z) (endpointFields D z) (endpointCode D w) (endpointFields D w) ≫
    (endpointPathIso D z w).hom
noncomputable def rawEquivalence : HomotopyEquivalence (rawMap D z w) :=
  (explicitEquivalence D (endpointCode D z) (endpointFields D z)
    (endpointCode D w) (endpointFields D w)).conjugateIso (Iso.refl _) (endpointPathIso D z w)
noncomputable def rawInverse := TotalRecovery.inverse (rawMap D z w) (rawEquivalence D z w)
noncomputable def rawRightInverse := TotalRecovery.rightInverse (rawMap D z w) (rawEquivalence D z w)
noncomputable def rawLeftInverse :=
  let F := rawEquivalencesFilling D z w
  TotalRecovery.leftInverse (rawMap D z w) (rawEquivalence D z w) F.1 F.2
end Raw

private noncomputable def wholePathFilling {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) (a b : Term A) :
    {P : Filling (homogeneousPath A a b) // P.Lawful} :=
  ⟨pathFilling (F.reindex (projection (interval Γ))) (hF.reindex _) a b,
    pathFilling_lawful (F.reindex (projection (interval Γ))) (hF.reindex _) a b⟩

section FinalModels
variable {Γ : Context.{u+1}} (T : Specification.{u}) (z w : Term (modelObjects T Γ))
noncomputable def modelEquivalences : Family Γ := rawEquivalences T.description (sigmaFst z) (sigmaFst w)
noncomputable def modelMap : modelEquivalences T z w ⟶ homogeneousPath (modelObjects T Γ) z w :=
  rawMap T.description (sigmaFst z) (sigmaFst w) ≫ modelPathInverse T z w
noncomputable def modelEquivalence : HomotopyEquivalence (modelMap T z w) :=
  let R := rawEquivalencesFilling T.description (sigmaFst z) (sigmaFst w)
  let O := objectsFilling T.description Γ
  let M := modelObjectsFilling T Γ
  let P := wholePathFilling O.1 O.2 (sigmaFst z) (sigmaFst w)
  let Q := wholePathFilling M.1 M.2 z w
  (rawEquivalence T.description (sigmaFst z) (sigmaFst w)).comp
    (modelPathInverseEquivalence T z w) R.1 R.2 P.1 P.2 Q.1 Q.2
noncomputable def modelInverse := TotalRecovery.inverse (modelMap T z w) (modelEquivalence T z w)
noncomputable def modelRightInverse := TotalRecovery.rightInverse (modelMap T z w) (modelEquivalence T z w)
noncomputable def modelLeftInverse :=
  let R := rawEquivalencesFilling T.description (sigmaFst z) (sigmaFst w)
  TotalRecovery.leftInverse (modelMap T z w) (modelEquivalence T z w) R.1 R.2
noncomputable def modelRightInverseAt (p : Term (homogeneousPath (modelObjects T Γ) z w)) :
    Term (homogeneousPath (homogeneousPath (modelObjects T Γ) z w)
      (Term.map (modelMap T z w) (Term.map (modelInverse T z w) p)) p) :=
  recoveryRightAt (modelMap T z w) (modelEquivalence T z w) p
noncomputable def modelLeftInverseAt (q : Term (modelEquivalences T z w)) :
    Term (homogeneousPath (modelEquivalences T z w)
      (Term.map (modelInverse T z w) (Term.map (modelMap T z w) q)) q) :=
  let R := rawEquivalencesFilling T.description (sigmaFst z) (sigmaFst w)
  recoveryLeftAt (modelMap T z w) (modelEquivalence T z w) R.1 R.2 q
private noncomputable def modelCompositeProjection {R : Family Γ}
    (f : R ⟶ homogeneousPath (objects T.description Γ) (sigmaFst z) (sigmaFst w)) (q : Term R) :
    Term (homogeneousPath (homogeneousPath (objects T.description Γ) (sigmaFst z) (sigmaFst w))
      (Term.map (HomotopyLevels.pathMap (PropositionExtension.first (objectConditions T Γ)) z w)
        (Term.map (f ≫ modelPathInverse T z w) q)) (Term.map f q)) :=
  modelPathInverseProjection T z w (Term.map f q)
noncomputable def modelMapProjection (q : Term (modelEquivalences T z w)) :
    Term (homogeneousPath (homogeneousPath (objects T.description Γ) (sigmaFst z) (sigmaFst w))
      (Term.map (HomotopyLevels.pathMap (PropositionExtension.first (objectConditions T Γ)) z w)
        (Term.map (modelMap T z w) q))
      (Term.map (rawMap T.description (sigmaFst z) (sigmaFst w)) q)) :=
  modelCompositeProjection T z w (rawMap T.description (sigmaFst z) (sigmaFst w)) q
end FinalModels


section ValueObservations
open CategoryTheory SquareKit.StructureIdentity StructureIdentity.Native SmallUniverse
private theorem whiskered_path_values {Γ : Context.{u}} {A : Family Γ}
    (a : Term A) {R : Family (total A)} (f : R ⟶ IdentitySystem.paths A a) (z : Term A)
    {x y : Γ.Elements} (h : x ⟶ y) (q : (reindex R (pair (A := A) (𝟙 Γ) z)).obj x)
    (r : (interval Γ).obj y) :
    (((Functor.whiskerLeft (pair (A := A) (𝟙 Γ) z).mapElements f ≫
      (EquivalenceFamilies.homogeneousReindexIso (reindex A (projection A))
        (Term.reindex a (projection A)) (generic A) (pair (A := A) (𝟙 Γ) z)).hom).app x q).val.val h r) =
      ((f.app ((pair (A := A) (𝟙 Γ) z).mapElements.obj x) q).val.val
        ((pair (A := A) (𝟙 Γ) z).mapElements.map h) r) := rfl
private theorem compose_path_values {Γ : Context.{u}} {A R S : Family Γ}
    (a b : Term A) (f : R ⟶ S) (g : S ⟶ homogeneousPath A a b)
    {x y : Γ.Elements} (h : x ⟶ y) (q : R.obj x) (r : (interval Γ).obj y) :
    (((f ≫ g).app x q).val.val h r) = ((g.app x (f.app x q)).val.val h r) := rfl
variable {Γ : Context.{u+1}} (D : Description.{u}) (a : Γ ⟶ smallFamilyCodes.{u})
  (s : Term (StructureIdentity.Native.family D (SmallUniverse.liftedDecode a)))
theorem structuredMap_values (z : Term (objects D Γ)) {x y : Γ.Elements} (h : x ⟶ y)
    (q : (reindex (SIP.relation D a s) (pair (A := objects D Γ) (𝟙 Γ) z)).obj x) (r : (interval Γ).obj y) :
    (((structuredMap D a s z).app x q).val.val h r) =
      (((basedStructuredMap D a s).app ((pair (A := objects D Γ) (𝟙 Γ) z).mapElements.obj x) q).val.val
        ((pair (A := objects D Γ) (𝟙 Γ) z).mapElements.map h) r) := by
  let F := basedStructuredMap D a s
  let J := EquivalenceFamilies.homogeneousReindexIso
    (reindex (objects D Γ) (projection (objects D Γ)))
    (Term.reindex (objectOf D a s) (projection (objects D Γ))) (generic (objects D Γ))
    (pair (A := objects D Γ) (𝟙 Γ) z)
  have hm : structuredMap D a s z = Functor.whiskerLeft (pair (A := objects D Γ) (𝟙 Γ) z).mapElements F ≫ J.hom := rfl
  exact (congrArg (fun k : reindex (SIP.relation D a s) (pair (A := objects D Γ) (𝟙 Γ) z) ⟶
      homogeneousPath (objects D Γ) (objectOf D a s) z => (k.app x q).val.val h r) hm).trans
    (whiskered_path_values (objectOf D a s) F z h q r)

theorem explicitMap_values (b : Γ ⟶ smallFamilyCodes.{u})
    (t : Term (StructureIdentity.Native.family D (SmallUniverse.liftedDecode b)))
    {x y : Γ.Elements} (h : x ⟶ y) (q : (StructureIdentity.Native.equivalences D s t).obj x)
    (r : (interval Γ).obj y) :
    (((explicitMap D a s b t).app x q).val.val h r) =
      (((structuredMap D a s (objectOf D b t)).app x
        ((SIP.relationAtIso D a b s t).inv.app x q)).val.val h r) := by
  let f := (SIP.relationAtIso D a b s t).inv
  let g := structuredMap D a s (objectOf D b t)
  have hm : explicitMap D a s b t = f ≫ g := rfl
  exact (congrArg (fun k : StructureIdentity.Native.equivalences D s t ⟶
      homogeneousPath (objects D Γ) (objectOf D a s) (objectOf D b t) => (k.app x q).val.val h r) hm).trans
    (compose_path_values (objectOf D a s) (objectOf D b t) f g h q r)
end ValueObservations

section ExactCarrierObservations

open SquareKit.StructureIdentity StructureIdentity.Native EquivalenceFamilies

variable {Γ : Context.{u+1}} (D : Description.{u}) (a : Γ ⟶ smallFamilyCodes.{u})
  (s : Term (family D (SmallUniverse.liftedDecode a)))

private theorem reindexed_map_values {Γ Δ : Context.{u}} (A C : Family Γ)
    (a b : Term A) (σ : Δ ⟶ Γ) (f : C ⟶ homogeneousPath A a b)
    (q : Term (reindex C σ)) {x y : Δ.Elements} (h : x ⟶ y) (r : (interval Δ).obj y) :
    ((Term.map (EquivalenceFamilies.homogeneousReindexIso A a b σ).hom
      (Term.map (Functor.whiskerLeft σ.mapElements f) q)).val x).val.val h r =
      (f.app (σ.mapElements.obj x) (q.val x)).val.val (σ.mapElements.map h) r := rfl

private theorem conjugated_path_values {Γ Δ : Context.{u}} (A C : Family Γ)
    (a b : Term A) (σ : Δ ⟶ Γ) {E : Family Δ} (f : C ⟶ homogeneousPath A a b)
    (g : E ⟶ reindex C σ) {x y : Δ.Elements} (h : x ⟶ y) (e : E.obj x)
    (r : (interval Δ).obj y) :
    ((g ≫ Functor.whiskerLeft σ.mapElements f ≫
      (EquivalenceFamilies.homogeneousReindexIso A a b σ).hom).app x e).val.val h r =
      (f.app (σ.mapElements.obj x) (g.app x e)).val.val (σ.mapElements.map h) r := rfl

private theorem equivToPath_reindex_values {Γ Δ : Context.{u+1}}
    (a b : Γ ⟶ smallFamilyCodes.{u}) (σ : Δ ⟶ Γ)
    {x y : Δ.Elements} (h : x ⟶ y)
    (e : (EquivalenceFamilies.equiv (SmallUniverse.liftedDecode (σ ≫ a))
      (SmallUniverse.liftedDecode (σ ≫ b))).obj x) (r : (interval Δ).obj y) :
    ((SmallUniverse.NativeUnivalence.equivToPath a b).app (σ.mapElements.obj x)
      ((EquivalenceFamilies.equivReindexIso (SmallUniverse.liftedDecode a)
        (SmallUniverse.liftedDecode b) σ).inv.app x e)).val.val (σ.mapElements.map h) r =
      ((SmallUniverse.NativeUnivalence.equivToPath (σ ≫ a) (σ ≫ b)).app x e).val.val h r := by
  let J := EquivalenceFamilies.equivReindexIso (SmallUniverse.liftedDecode a) (SmallUniverse.liftedDecode b) σ
  have hm := SmallUniverse.NativeUnivalence.equivToPath_conjugate_reindex a b σ
  have hv := congrArg (fun k : EquivalenceFamilies.equiv (SmallUniverse.liftedDecode (σ ≫ a))
      (SmallUniverse.liftedDecode (σ ≫ b)) ⟶ SmallUniverse.NativeUnivalence.paths (σ ≫ a) (σ ≫ b) =>
      (k.app x e).val.val h r) hm
  exact (conjugated_path_values (SmallUniverse.family Γ)
    (EquivalenceFamilies.equiv (SmallUniverse.liftedDecode a) (SmallUniverse.liftedDecode b))
    (SmallUniverse.term a) (SmallUniverse.term b) σ (SmallUniverse.NativeUnivalence.equivToPath a b)
    J.inv h e r).symm.trans hv

private theorem uaPath_moving :
    let a₀ := SmallUniverse.NativeUnivalence.movingSource a
    let b₀ := SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ)
    let π := projection (SIP.targetData D a)
    let σ := π ≫ SIP.carrierProjection a
    let q := Term.reindex (generic (EquivalenceFamilies.equiv
      (SmallUniverse.liftedDecode a₀) (SmallUniverse.liftedDecode b₀))) (π ≫ SIP.unpackCarriers a)
    SIP.uaPath D a s =
      Term.map (pathReindex
        (reindex (SmallUniverse.family (total (SmallUniverse.family Γ)))
          (projection (interval (total (SmallUniverse.family Γ)))))
        (SmallUniverse.term a₀) (SmallUniverse.term b₀) σ)
        (Term.map (Functor.whiskerLeft σ.mapElements (SmallUniverse.NativeUnivalence.equivToPath a₀ b₀)) q) := by
  let a₀ := SmallUniverse.NativeUnivalence.movingSource a
  let b₀ := SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ)
  let A := SmallUniverse.liftedDecode a₀
  let B := SmallUniverse.liftedDecode b₀
  let π := projection (SIP.targetData D a)
  let σ := π ≫ SIP.carrierProjection a
  let q := Term.reindex (generic (EquivalenceFamilies.equiv A B)) (π ≫ SIP.unpackCarriers a)
  have hd := decodeEquivalence_reindex A B (SIP.carrierProjection a) π
    (Term.reindex (generic (EquivalenceFamilies.equiv A B)) (SIP.unpackCarriers a))
  have hb := SmallUniverse.NativeUnivalence.equivToPath_reindex_beta (a := a₀) (b := b₀) σ q
  have hu := congrArg (fun e : Σ f : reindex A σ ⟶ reindex B σ, HomotopyEquivalence f =>
    SmallUniverse.NativeUnivalence.ua (σ ≫ a₀) (σ ≫ b₀) e.1 e.2) hd
  exact (SIP.uaPath_beta D a s).trans (hu.symm.trans hb.symm)

private theorem uaPath_moving_values {x y : (total (SIP.targetData D a)).Elements}
    (h : x ⟶ y) (r : (interval (total (SIP.targetData D a))).obj y) :
    let σ := projection (SIP.targetData D a) ≫ SIP.carrierProjection a
    ((SIP.uaPath D a s).val x).val.val h r =
      ((SmallUniverse.NativeUnivalence.equivToPath (SmallUniverse.NativeUnivalence.movingSource a)
        (SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ))).app (σ.mapElements.obj x)
          x.val.1.2.2).val.val (σ.mapElements.map h) r := by
  let a₀ := SmallUniverse.NativeUnivalence.movingSource a
  let b₀ := SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ)
  let π := projection (SIP.targetData D a)
  let σ := π ≫ SIP.carrierProjection a
  let C := EquivalenceFamilies.equiv (SmallUniverse.liftedDecode a₀) (SmallUniverse.liftedDecode b₀)
  let q := Term.reindex (generic C) (π ≫ SIP.unpackCarriers a)
  have hu := congrArg (fun p : Term (SmallUniverse.NativeUnivalence.paths (SIP.sourceCode D a)
    (SIP.targetCode D a)) => (p.val x).val.val h r) (uaPath_moving D a s)
  exact hu.trans (reindexed_map_values (SmallUniverse.family (total (SmallUniverse.family Γ))) C
    (SmallUniverse.term a₀) (SmallUniverse.term b₀) σ
    (SmallUniverse.NativeUnivalence.equivToPath a₀ b₀) q h r)

private theorem first_value_of_eq {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (z₀ z₁ : Term (sigma A B)) {x y : Γ.Elements} (h : x ⟶ y) (r : (interval Γ).obj y)
    (p : (SigmaPaths.whole z₀ z₁).obj x) (q : (SigmaPaths.base z₀ z₁).obj x)
    (e : SigmaPaths.first z₀ z₁ p = q) :
    (p.val.val h r).1 = q.val.val h r := congrArg (fun p => p.val.val h r) e

private theorem reordered_carrier_values {x y : (total (objects D Γ)).Elements} (h : x ⟶ y)
    (q : (SIP.relation D a s).obj x) (r : (interval (total (objects D Γ))).obj y) :
    let R := SIP.relation D a s
    let κ := Reordered.dataIndex D a s
    (((reorderToPaths D a s (preservationToWhole D a s)).app x q).val.val h r).1 =
      ((SIP.uaPath D a s).val (κ.mapElements.obj (extendObj R x q))).val.val
        (κ.mapElements.map (extendHom R h q)) r := by
  let R := SIP.relation D a s
  let κ := Reordered.dataIndex D a s
  let x₀ := extendObj R x q
  let h₀ := extendHom R h q
  have hr := reorderToPaths_carrier_values D a s (preservationToWhole D a s) h q r
  have hp := first_value_of_eq (SIP.sourceObject D a s) (SIP.targetObject D a)
    (κ.mapElements.map h₀) r
    ((preservationToWhole D a s).app (κ.mapElements.obj x₀) ((Reordered.witness D a s).val x₀))
    ((SIP.uaPath D a s).val (κ.mapElements.obj x₀))
    (preservationToWhole_carrier D a s (κ.mapElements.obj x₀)
      ((Reordered.witness D a s).val x₀))
  exact hr.trans hp

private theorem reordered_moving_values {x y : (total (objects D Γ)).Elements} (h : x ⟶ y)
    (q : (SIP.relation D a s).obj x) (r : (interval (total (objects D Γ))).obj y) :
    let R := SIP.relation D a s
    let κ := Reordered.dataIndex D a s
    let σ := SIP.Exchange.rightBase (SIP.objectFields D)
    ((SIP.uaPath D a s).val (κ.mapElements.obj (extendObj R x q))).val.val
      (κ.mapElements.map (extendHom R h q)) r =
    ((SmallUniverse.NativeUnivalence.equivToPath
      (SmallUniverse.NativeUnivalence.movingSource a)
      (SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ))).app (σ.mapElements.obj x)
      q.1).val.val (σ.mapElements.map h) r := by
  exact uaPath_moving_values D a s
    ((Reordered.dataIndex D a s).mapElements.map (extendHom (SIP.relation D a s) h q)) r

private theorem endpoint_moving_coordinate_values (b : Γ ⟶ smallFamilyCodes.{u})
    (t : Term (family D (SmallUniverse.liftedDecode b)))
    {x y : Γ.Elements} (h : x ⟶ y)
    (q₀ : (reindex (SIP.relation D a s) (pair (A := objects D Γ) (𝟙 Γ) (objectOf D b t))).obj x)
    (r : (interval Γ).obj y) :
    let τ := pair (A := objects D Γ) (𝟙 Γ) (objectOf D b t)
    let R := SIP.relation D a s
    let κ := Reordered.dataIndex D a s
    let σ := pair (A := SmallUniverse.family Γ) (𝟙 Γ) (SmallUniverse.term b)
    ((SIP.uaPath D a s).val (κ.mapElements.obj (extendObj R (τ.mapElements.obj x) q₀))).val.val
      (κ.mapElements.map (extendHom R (τ.mapElements.map h) q₀)) r =
    ((SmallUniverse.NativeUnivalence.equivToPath
      (SmallUniverse.NativeUnivalence.movingSource a)
      (SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ))).app (σ.mapElements.obj x)
      q₀.1).val.val (σ.mapElements.map h) r := by
  exact reordered_moving_values D a s
    ((pair (A := objects D Γ) (𝟙 Γ) (objectOf D b t)).mapElements.map h) q₀ r

private theorem endpoint_selected_ua_canonical_values (b : Γ ⟶ smallFamilyCodes.{u})
    {x y : Γ.Elements} (h : x ⟶ y)
    (e : (EquivalenceFamilies.equiv (SmallUniverse.liftedDecode a) (SmallUniverse.liftedDecode b)).obj x)
    (r : (interval Γ).obj y) :
    let a₀ := SmallUniverse.NativeUnivalence.movingSource a
    let b₀ := SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ)
    let σ := pair (A := SmallUniverse.family Γ) (𝟙 Γ) (SmallUniverse.term b)
    ((SmallUniverse.NativeUnivalence.equivToPath a₀ b₀).app (σ.mapElements.obj x)
      ((EquivalenceFamilies.equivReindexIso (SmallUniverse.liftedDecode a₀)
        (SmallUniverse.liftedDecode b₀) σ).inv.app x e)).val.val (σ.mapElements.map h) r =
      ((SmallUniverse.NativeUnivalence.equivToPath a b).app x e).val.val h r := by
  exact equivToPath_reindex_values
    (SmallUniverse.NativeUnivalence.movingSource a)
    (SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ))
    (pair (A := SmallUniverse.family Γ) (𝟙 Γ) (SmallUniverse.term b)) h e r

private theorem structured_carrier_values (z : Term (objects D Γ)) {x y : Γ.Elements}
    (h : x ⟶ y) (q : (reindex (SIP.relation D a s) (pair (𝟙 Γ) z)).obj x)
    (r : (interval Γ).obj y) :
    let τ := pair (A := objects D Γ) (𝟙 Γ) z
    let R := SIP.relation D a s
    let κ := Reordered.dataIndex D a s
    (((structuredMap D a s z).app x q).val.val h r).1 =
      ((SIP.uaPath D a s).val (κ.mapElements.obj (extendObj R (τ.mapElements.obj x) q))).val.val
        (κ.mapElements.map (extendHom R (τ.mapElements.map h) q)) r := by
  let τ := pair (A := objects D Γ) (𝟙 Γ) z
  have hm : basedStructuredMap D a s = reorderToPaths D a s (preservationToWhole D a s) := rfl
  have hv := congrArg (fun k : SIP.relation D a s ⟶
      IdentitySystem.paths (objects D Γ) (objectOf D a s) =>
      ((k.app (τ.mapElements.obj x) q).val.val (τ.mapElements.map h) r).1) hm
  exact (congrArg Sigma.fst (structuredMap_values D a s z h q r)).trans
    (hv.trans (reordered_carrier_values D a s (τ.mapElements.map h) q r))

private theorem first_eq_of_values {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (z₀ z₁ : Term (sigma A B)) {x : Γ.Elements}
    (p : (SigmaPaths.whole z₀ z₁).obj x) (q : (SigmaPaths.base z₀ z₁).obj x)
    (e : ∀ {y : Γ.Elements} (h : x ⟶ y) (r : (interval Γ).obj y),
      (p.val.val h r).1 = q.val.val h r) : SigmaPaths.first z₀ z₁ p = q := by
  apply Subtype.ext
  apply PiElement.ext
  intro y h r
  exact e h r

private theorem pathMap_first_app {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (z₀ z₁ : Term (sigma A B)) (x : Γ.Elements) (p : (SigmaPaths.whole z₀ z₁).obj x) :
    (HomotopyLevels.pathMap (SIP.Exchange.first B) z₀ z₁).app x p =
      SigmaPaths.first z₀ z₁ p := rfl

private theorem carrier_of_values (b : Γ ⟶ smallFamilyCodes.{u})
    (t : Term (family D (SmallUniverse.liftedDecode b)))
    (f : equivalences D s t ⟶ homogeneousPath (objects D Γ) (objectOf D a s) (objectOf D b t))
    (hf : ∀ {x y : Γ.Elements} (h : x ⟶ y) (q : (equivalences D s t).obj x)
      (r : (interval Γ).obj y), ((f.app x q).val.val h r).1 =
        ((SmallUniverse.NativeUnivalence.equivToPath a b).app x q.1).val.val h r)
    (x : Γ.Elements) (q : (equivalences D s t).obj x) :
    SigmaPaths.first (objectOf D a s) (objectOf D b t) (f.app x q) =
      (SmallUniverse.NativeUnivalence.equivToPath a b).app x q.1 :=
  first_eq_of_values (objectOf D a s) (objectOf D b t) (f.app x q)
    ((SmallUniverse.NativeUnivalence.equivToPath a b).app x q.1) (fun h r => hf h q r)

private theorem carrier_ua_of_values (b : Γ ⟶ smallFamilyCodes.{u})
    (t : Term (family D (SmallUniverse.liftedDecode b)))
    (f : equivalences D s t ⟶ homogeneousPath (objects D Γ) (objectOf D a s) (objectOf D b t))
    (hf : ∀ {x y : Γ.Elements} (h : x ⟶ y) (q : (equivalences D s t).obj x)
      (r : (interval Γ).obj y), ((f.app x q).val.val h r).1 =
        ((SmallUniverse.NativeUnivalence.equivToPath a b).app x q.1).val.val h r)
    (q : Term (equivalences D s t)) :
    let E := (EquivalenceFamilies.equivSections (SmallUniverse.liftedDecode a)
      (SmallUniverse.liftedDecode b)).symm
        (sigmaFst (A := EquivalenceFamilies.equiv (SmallUniverse.liftedDecode a)
          (SmallUniverse.liftedDecode b)) q)
    Term.map (HomotopyLevels.pathMap (SIP.Exchange.first (SIP.objectFields D))
      (objectOf D a s) (objectOf D b t)) (Term.map f q) =
      SmallUniverse.NativeUnivalence.ua a b E.1 E.2 := by
  let c := sigmaFst (A := EquivalenceFamilies.equiv (SmallUniverse.liftedDecode a)
    (SmallUniverse.liftedDecode b)) q
  let K := EquivalenceFamilies.equivSections (SmallUniverse.liftedDecode a) (SmallUniverse.liftedDecode b)
  let E := K.symm c
  have hc : Term.map (HomotopyLevels.pathMap (SIP.Exchange.first (SIP.objectFields D))
      (objectOf D a s) (objectOf D b t)) (Term.map f q) =
        Term.map (SmallUniverse.NativeUnivalence.equivToPath a b) c := by
    apply Term.ext
    intro x
    exact (pathMap_first_app (objectOf D a s) (objectOf D b t) x (f.app x (q.val x))).trans
      (carrier_of_values D a s b t f hf x (q.val x))
  exact hc.trans ((congrArg (Term.map (SmallUniverse.NativeUnivalence.equivToPath a b))
    (K.apply_symm_apply c)).symm.trans
      (SmallUniverse.NativeUnivalence.equivToPath_beta E.1 E.2))

private theorem apply_heq {α : Sort*} {β : Sort*} (f : α → β)
    {e e' : α} (h : HEq e e') : HEq (f e) (f e') := by
  cases h
  rfl

private theorem endpoint_moving_canonical_values_of_equivalence
    (b : Γ ⟶ smallFamilyCodes.{u}) (t : Term (family D (SmallUniverse.liftedDecode b)))
    {x y : Γ.Elements} (h : x ⟶ y) (q : (equivalences D s t).obj x)
    (q₀ : (reindex (SIP.relation D a s) (pair (A := objects D Γ) (𝟙 Γ) (objectOf D b t))).obj x)
    (hq : HEq q₀.1 ((EquivalenceFamilies.equivReindexIso
      (SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingSource a))
      (SmallUniverse.liftedDecode (SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ)))
      (pair (A := SmallUniverse.family Γ) (𝟙 Γ) (SmallUniverse.term b))).inv.app x q.1))
    (r : (interval Γ).obj y) :
    let τ := pair (A := objects D Γ) (𝟙 Γ) (objectOf D b t)
    let R := SIP.relation D a s
    let κ := Reordered.dataIndex D a s
    ((SIP.uaPath D a s).val (κ.mapElements.obj (extendObj R (τ.mapElements.obj x) q₀))).val.val
      (κ.mapElements.map (extendHom R (τ.mapElements.map h) q₀)) r =
        ((SmallUniverse.NativeUnivalence.equivToPath a b).app x q.1).val.val h r := by
  let a₀ := SmallUniverse.NativeUnivalence.movingSource a
  let b₀ := SmallUniverse.NativeUnivalence.movingTarget (Γ := Γ)
  let σ := pair (A := SmallUniverse.family Γ) (𝟙 Γ) (SmallUniverse.term b)
  have hu := endpoint_moving_coordinate_values D a s b t h q₀ r
  have he := apply_heq (fun e : (EquivalenceFamilies.equiv (SmallUniverse.liftedDecode a₀)
      (SmallUniverse.liftedDecode b₀)).obj (σ.mapElements.obj x) =>
    ((SmallUniverse.NativeUnivalence.equivToPath a₀ b₀).app (σ.mapElements.obj x) e).val.val
      (σ.mapElements.map h) r) hq
  exact hu.trans ((eq_of_heq he).trans (endpoint_selected_ua_canonical_values a b h q.1 r))

variable (b : Γ ⟶ smallFamilyCodes.{u}) (t : Term (family D (SmallUniverse.liftedDecode b)))

/-- The reconstructed carrier is the selected native ua of the caller's complete equivalence,
    at every generalized interval evaluation. -/
theorem explicitMap_carrier_values {x y : Γ.Elements} (h : x ⟶ y)
    (q : (equivalences D s t).obj x) (r : (interval Γ).obj y) :
    (((explicitMap D a s b t).app x q).val.val h r).1 =
      ((SmallUniverse.NativeUnivalence.equivToPath a b).app x q.1).val.val h r := by
  let q₀ := (SIP.relationAtIso D a b s t).inv.app x q
  have hstart := congrArg Sigma.fst (explicitMap_values D a s b t h q r)
  have hs := structured_carrier_values D a s (objectOf D b t) h q₀ r
  have hm := endpoint_moving_canonical_values_of_equivalence D a s b t h q q₀
    (heq_of_eq (SIP.relationAtIso_inv_equivalence_canonical D a b s t x q)) r
  exact hstart.trans (hs.trans hm)

/-- The complete carrier path of reconstruction retains the supplied equivalence witness. -/
theorem explicitMap_carrier (x : Γ.Elements) (q : (equivalences D s t).obj x) :
    SigmaPaths.first (objectOf D a s) (objectOf D b t) ((explicitMap D a s b t).app x q) =
      (SmallUniverse.NativeUnivalence.equivToPath a b).app x q.1 :=
  carrier_of_values D a s b t (explicitMap D a s b t)
    (explicitMap_carrier_values D a s b t) x q

/-- On sections, the carrier is the actual selected ua of the decoded map and its
    retained homotopy-equivalence witness. -/
theorem explicitMap_carrier_ua (q : Term (equivalences D s t)) :
    let E := (EquivalenceFamilies.equivSections (SmallUniverse.liftedDecode a)
      (SmallUniverse.liftedDecode b)).symm
        (sigmaFst (A := EquivalenceFamilies.equiv (SmallUniverse.liftedDecode a)
          (SmallUniverse.liftedDecode b)) q)
    Term.map (HomotopyLevels.pathMap (SIP.Exchange.first (SIP.objectFields D))
      (objectOf D a s) (objectOf D b t)) (Term.map (explicitMap D a s b t) q) =
      SmallUniverse.NativeUnivalence.ua a b E.1 E.2 :=
  carrier_ua_of_values D a s b t (explicitMap D a s b t)
    (explicitMap_carrier_values D a s b t) q

end ExactCarrierObservations

end SquareKit.Cubical.Cartesian.StructuredIdentity.UaComparison
