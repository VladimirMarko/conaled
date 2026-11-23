import SquareKit.Internal.Cubical.ConstructorTransport
/-! Whole-section recomputation and comparisons between independently rebuilt
constructor transports. Exact equality of canonical comparison bodies remains
a separate selected-coherence obligation. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse.LargeConstructors
open CategoryTheory NativeUnivalence
universe u
variable {Ξ Ω : Context.{u+1}}
set_option maxHeartbeats 400000 in
theorem pairSection_reindex
    (a : total (interval Ξ) ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u})
    (z : Term (Presheaf.reindex (Presheaf.sigma (liftedDecode a) (liftedDecode b)) (endpointSub Ξ false)))
    (σ : Ω ⟶ Ξ) :
    pairSection (liftSub (interval Ξ) σ ≫ a)
      (liftSub (liftedDecode a) (liftSub (interval Ξ) σ) ≫ b) (z.reindex σ) =
      (pairSection a b z).reindex (liftSub (interval Ξ) σ) := by
  exact IntervalTransport.forward_reindex
    (sigmaFilling (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling b))
    (sigmaFilling_lawful (NativeDecode.filling a) (NativeDecode.filling_lawful a)
      (NativeDecode.filling b) (NativeDecode.filling_lawful b)) (𝟙 Ξ) z σ

def functionInitialReindex
    (a : total (interval Ξ) ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u})
    (z : Term (Presheaf.reindex (Presheaf.pi (liftedDecode a) (liftedDecode b)) (endpointSub Ξ false)))
    (σ : Ω ⟶ Ξ) :=
  Term.map (Functor.whiskerLeft (endpointSub Ω false).mapElements
    (piReindexIso (liftedDecode a) (liftedDecode b) (liftSub (interval Ξ) σ)).hom) (z.reindex σ)

theorem functionSection_reindex
    (a : total (interval Ξ) ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u})
    (z : Term (Presheaf.reindex (Presheaf.pi (liftedDecode a) (liftedDecode b)) (endpointSub Ξ false)))
    (σ : Ω ⟶ Ξ) :
    functionSection (liftSub (interval Ξ) σ ≫ a)
      (liftSub (liftedDecode a) (liftSub (interval Ξ) σ) ≫ b) (functionInitialReindex a b z σ) =
      Term.map (piReindexIso (liftedDecode a) (liftedDecode b) (liftSub (interval Ξ) σ)).hom
        ((functionSection a b z).reindex (liftSub (interval Ξ) σ)) := by
  let F := piFilling (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling b)
  let e := piReindexIso (liftedDecode a) (liftedDecode b) (liftSub (interval Ξ) σ)
  have hf : (F.reindex (liftSub (interval Ξ) σ)).transport e =
      piFilling (NativeDecode.filling (liftSub (interval Ξ) σ ≫ a))
        (NativeDecode.filling_lawful _)
        (NativeDecode.filling (liftSub (liftedDecode a) (liftSub (interval Ξ) σ) ≫ b)) :=
    Filling.transport_eq _ _ _ (piFilling_reindex
      (NativeDecode.filling a) (NativeDecode.filling_lawful a) (NativeDecode.filling b)
      (liftSub (interval Ξ) σ))
  have hn := IntervalTransport.forward_reindex F
    (piFilling_lawful (NativeDecode.filling a) (NativeDecode.filling_lawful a)
      (NativeDecode.filling b) (NativeDecode.filling_lawful b)) (𝟙 Ξ) z σ
  exact (congrArg (fun H => IntervalTransport.forward H (𝟙 Ω)
    (functionInitialReindex a b z σ)) hf.symm).trans
      ((IntervalTransport.forward_transport_map (F.reindex (liftSub (interval Ξ) σ)) e
        (z.reindex σ)).trans (congrArg (Term.map e.hom) hn))
/-- Relabeling the starting section in the public transport formula changes
only endpoint proofs, preserving the selected comparison body exactly. -/
theorem Result.transportFromSection_body {C : Family (total (interval Ξ))}
    (R : Result C) (z : Term C) (t : Term (Presheaf.reindex C (endpointSub Ξ false)))
    (hz : z.reindex (endpointSub Ξ false) = t) :
    pathApp (R.transportFromSection z t hz) = pathApp (R.transportComparison z) := by
  unfold Result.transportFromSection
  apply pathApp_lam

/-- The actual canonical decoder transport, expressed in the constructor family. -/
noncomputable def Result.transportInFamily {C : Family (total (interval Ξ))}
    (R : Result C) (z : Term C) : Term (Presheaf.reindex C (endpointSub Ξ true)) :=
  Term.map (Functor.whiskerLeft (endpointSub Ξ true).mapElements R.decoding.hom)
    (Term.map (IntervalTransport.map (NativeDecode.filling R.code))
      ((Term.map R.decoding.inv z).reindex (endpointSub Ξ false)))

/-- The whole chosen comparison body, mapped through the endpoint decoder. -/
noncomputable def Result.comparisonInFamily {C : Family (total (interval Ξ))}
    (R : Result C) (z : Term C) :
    Term (homogeneousPath (Presheaf.reindex C (endpointSub Ξ true))
      (R.transportInFamily z) (z.reindex (endpointSub Ξ true))) := by
  let q := homogeneousPathMap
    (Functor.whiskerLeft (endpointSub Ξ true).mapElements R.decoding.hom)
    (R.transportComparison z)
  exact pathLam (pathApp q) (pathApp_zero q)
    ((pathApp_one q).trans (congrArg (fun t => t.reindex (endpointSub Ξ true))
      (Term.map_iso_roundtrip R.decoding.symm z)))

/-- Decoder normalization keeps every point of the original chosen body. -/
theorem Result.comparisonInFamily_body {C : Family (total (interval Ξ))}
    (R : Result C) (z : Term C) :
    pathApp (R.comparisonInFamily z) =
      Term.map (Functor.whiskerLeft
        (projection (interval Ξ)).mapElements
        (Functor.whiskerLeft (endpointSub Ξ true).mapElements R.decoding.hom))
        (pathApp (R.transportComparison z)) := rfl

/-- Move the rebuilt comparison into the original family. Its full body is
retained even when its canonical filling is an independent selection. -/
noncomputable def Result.rebuiltComparison {C D : Family (total (interval Ξ))}
    (R : Result D) (e : C ≅ D) (z : Term C) (w : Term D)
    (hw : Term.map e.hom z = w) :
    Term (homogeneousPath (Presheaf.reindex C (endpointSub Ξ true))
      (Term.map (Functor.whiskerLeft (endpointSub Ξ true).mapElements e.inv)
        (R.transportInFamily w)) (z.reindex (endpointSub Ξ true))) := by
  let q := homogeneousPathMap
    (Functor.whiskerLeft (endpointSub Ξ true).mapElements e.inv) (R.comparisonInFamily w)
  have h : Term.map e.inv w = z := hw.symm ▸ Term.map_iso_roundtrip e z
  exact pathLam (pathApp q) (pathApp_zero q)
    ((pathApp_one q).trans (congrArg (fun t => t.reindex (endpointSub Ξ true)) h))

/-- Compare the two actual transports through their common reconstructed section.
No equality of the two canonical filling selections is assumed. -/
noncomputable def Result.compareRebuilt {C D : Family (total (interval Ξ))}
    (R : Result C) (S : Result D) (e : C ≅ D)
    (z : Term C) (w : Term D) (hw : Term.map e.hom z = w) :
    Term (homogeneousPath (Presheaf.reindex C (endpointSub Ξ true))
      (R.transportInFamily z)
      (Term.map (Functor.whiskerLeft (endpointSub Ξ true).mapElements e.inv)
        (S.transportInFamily w))) :=
  homogeneousConcat ((R.filling.transport R.decoding).reindex (endpointSub Ξ true))
    ((R.filling.transport_lawful R.decoding R.lawful).reindex (endpointSub Ξ true))
    (R.comparisonInFamily z) (homogeneousReverse (S.rebuiltComparison e z w hw))

/-- Compose two rebuilding comparisons, retaining each chosen constituent body.
The intermediate transport cancels as the common endpoint of the two paths. -/
noncomputable def Result.compareRebuiltTwice
    {C D E : Family (total (interval Ξ))}
    (R : Result C) (S : Result D) (T : Result E) (e : C ≅ D) (f : D ≅ E)
    (z : Term C) (w : Term D) (v : Term E)
    (hw : Term.map e.hom z = w) (hv : Term.map f.hom w = v) :
    Term (homogeneousPath (Presheaf.reindex C (endpointSub Ξ true))
      (R.transportInFamily z)
      (Term.map (Functor.whiskerLeft (endpointSub Ξ true).mapElements e.inv)
        (Term.map (Functor.whiskerLeft (endpointSub Ξ true).mapElements f.inv)
          (T.transportInFamily v)))) :=
  homogeneousConcat ((R.filling.transport R.decoding).reindex (endpointSub Ξ true))
    ((R.filling.transport_lawful R.decoding R.lawful).reindex (endpointSub Ξ true))
    (R.compareRebuilt S e z w hw)
    (homogeneousPathMap (Functor.whiskerLeft (endpointSub Ξ true).mapElements e.inv)
      (S.compareRebuilt T f w v hv))

/-- A necessary consequence of exact equality of normalized chosen bodies.
A decoder/filler comparison cannot be inferred merely from their common finish. -/
theorem Result.transport_eq_of_comparisonBody_eq {C D : Family (total (interval Ξ))}
    (R : Result C) (S : Result D) (e : C ≅ D)
    (z : Term C) (w : Term D) (hw : Term.map e.hom z = w)
    (h : pathApp (R.comparisonInFamily z) = pathApp (S.rebuiltComparison e z w hw)) :
    R.transportInFamily z =
      Term.map (Functor.whiskerLeft (endpointSub Ξ true).mapElements e.inv)
        (S.transportInFamily w) :=
  (pathApp_zero (R.comparisonInFamily z)).symm.trans
    ((congrArg (fun t => t.reindex (endpointSub Ξ false)) h).trans
      (pathApp_zero (S.rebuiltComparison e z w hw)))

/-- The adapter preserves the entire freshly selected comparison body. -/
theorem Result.rebuiltComparison_body {C D : Family (total (interval Ξ))}
    (S : Result D) (e : C ≅ D) (z : Term C) (w : Term D)
    (hw : Term.map e.hom z = w) :
    pathApp (S.rebuiltComparison e z w hw) =
      Term.map (Functor.whiskerLeft (projection (interval Ξ)).mapElements
        (Functor.whiskerLeft (endpointSub Ξ true).mapElements e.inv))
        (pathApp (S.comparisonInFamily w)) := rfl

/-- Exact recomputation is available when the same classified result is
restricted. This is a positive control, not a law for fresh classification. -/
theorem Result.comparisonInFamily_body_reindex {C : Family (total (interval Ξ))}
    (R : Result C) (z : Term C) (σ : Ω ⟶ Ξ) :
    pathApp ((R.reindex (liftSub (interval Ξ) σ)).comparisonInFamily
      (z.reindex (liftSub (interval Ξ) σ))) =
      (pathApp (R.comparisonInFamily z)).reindex (liftSub (interval Ξ) σ) := by
  exact congrArg
    (Term.map (Functor.whiskerLeft (projection (interval Ω)).mapElements
      (Functor.whiskerLeft (endpointSub Ω true).mapElements
        (Functor.whiskerLeft (liftSub (interval Ξ) σ).mapElements R.decoding.hom))))
    (R.transportComparison_body_reindex z σ)

/-- Rebuild the pair algorithm, retaining its original and rebuilt canonical
comparison paths through `Result.compareRebuilt`. -/
noncomputable def pairRecomputedComparison
    (a : total (interval Ξ) ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u})
    (z : Term (Presheaf.reindex (Presheaf.sigma (liftedDecode a) (liftedDecode b)) (endpointSub Ξ false)))
    (σ : Ω ⟶ Ξ) :=
  ((sigma a b).reindex (liftSub (interval Ξ) σ)).compareRebuilt
    (sigma (liftSub (interval Ξ) σ ≫ a)
      (liftSub (liftedDecode a) (liftSub (interval Ξ) σ) ≫ b))
    (Iso.refl _) ((pairSection a b z).reindex (liftSub (interval Ξ) σ))
    (pairSection (liftSub (interval Ξ) σ ≫ a)
      (liftSub (liftedDecode a) (liftSub (interval Ξ) σ) ≫ b) (z.reindex σ))
    (pairSection_reindex a b z σ).symm

/-- Rebuilt function transport compares through the complete backwards-argument
section, using the native Pi reindexing adapter at every dimension. -/
noncomputable def functionRecomputedComparison
    (a : total (interval Ξ) ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u})
    (z : Term (Presheaf.reindex (Presheaf.pi (liftedDecode a) (liftedDecode b)) (endpointSub Ξ false)))
    (σ : Ω ⟶ Ξ) :=
  ((pi a b).reindex (liftSub (interval Ξ) σ)).compareRebuilt
    (pi (liftSub (interval Ξ) σ ≫ a)
      (liftSub (liftedDecode a) (liftSub (interval Ξ) σ) ≫ b))
    (piReindexIso (liftedDecode a) (liftedDecode b) (liftSub (interval Ξ) σ))
    ((functionSection a b z).reindex (liftSub (interval Ξ) σ))
    (functionSection (liftSub (interval Ξ) σ ≫ a)
      (liftSub (liftedDecode a) (liftSub (interval Ξ) σ) ≫ b) (functionInitialReindex a b z σ))
    (functionSection_reindex a b z σ).symm

/-- Compose two independently rebuilt pair comparisons. All three chosen
canonical transports and both complete constituent comparison paths remain. -/
noncomputable def pairRecomputedComparisonTwice {Θ : Context.{u+1}}
    (a : total (interval Ξ) ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u})
    (z : Term (Presheaf.reindex (Presheaf.sigma (liftedDecode a) (liftedDecode b))
      (endpointSub Ξ false))) (σ : Ω ⟶ Ξ) (τ : Θ ⟶ Ω) := by
  let L := liftSub (interval Ξ) σ
  let M := liftSub (interval Ω) τ
  let a₁ := L ≫ a
  let b₁ := liftSub (liftedDecode a) L ≫ b
  let a₂ := M ≫ a₁
  let b₂ := liftSub (liftedDecode a₁) M ≫ b₁
  let R := ((sigma a b).reindex L).reindex M
  let S := (sigma a₁ b₁).reindex M
  let T := sigma a₂ b₂
  let z₀ := ((pairSection a b z).reindex L).reindex M
  let z₁ := (pairSection a₁ b₁ (z.reindex σ)).reindex M
  let z₂ := pairSection a₂ b₂ ((z.reindex σ).reindex τ)
  have h₁ : z₀ = z₁ := congrArg (fun t => t.reindex M)
    (pairSection_reindex a b z σ).symm
  have h₂ : z₁ = z₂ :=
    (pairSection_reindex a₁ b₁ (z.reindex σ) τ).symm
  exact R.compareRebuiltTwice S T (Iso.refl _) (Iso.refl _) z₀ z₁ z₂ h₁ h₂

/-- The function case also composes two actual rebuilding comparisons; each
step retains the native Pi adapter and the backwards-argument section. -/
noncomputable def functionRecomputedComparisonTwice {Θ : Context.{u+1}}
    (a : total (interval Ξ) ⟶ smallFamilyCodes.{u})
    (b : total (liftedDecode a) ⟶ smallFamilyCodes.{u})
    (z : Term (Presheaf.reindex (Presheaf.pi (liftedDecode a) (liftedDecode b))
      (endpointSub Ξ false))) (σ : Ω ⟶ Ξ) (τ : Θ ⟶ Ω) := by
  let L := liftSub (interval Ξ) σ
  let M := liftSub (interval Ω) τ
  let a₁ := L ≫ a
  let b₁ := liftSub (liftedDecode a) L ≫ b
  let a₂ := M ≫ a₁
  let b₂ := liftSub (liftedDecode a₁) M ≫ b₁
  let t₁ := functionInitialReindex a b z σ
  let t₂ := functionInitialReindex a₁ b₁ t₁ τ
  let R := ((pi a b).reindex L).reindex M
  let S := (pi a₁ b₁).reindex M
  let T := pi a₂ b₂
  let e := Functor.isoWhiskerLeft M.mapElements
    (piReindexIso (liftedDecode a) (liftedDecode b) L)
  let f := piReindexIso (liftedDecode a₁) (liftedDecode b₁) M
  let z₀ := ((functionSection a b z).reindex L).reindex M
  let z₁ := (functionSection a₁ b₁ t₁).reindex M
  let z₂ := functionSection a₂ b₂ t₂
  have h₁ : Term.map e.hom z₀ = z₁ := congrArg (fun t => t.reindex M)
    (functionSection_reindex a b z σ).symm
  have h₂ : Term.map f.hom z₁ = z₂ :=
    (functionSection_reindex a₁ b₁ t₁ τ).symm
  exact R.compareRebuiltTwice S T e f z₀ z₁ z₂ h₁ h₂

end SquareKit.Cubical.Presheaf.SmallUniverse.LargeConstructors
