import SquareKit.Internal.Cubical.CartesianUniverse
import SquareKit.Internal.Cubical.CartesianEquivalenceIsoTransport

/-! A native Glue code path with exact chosen-family endpoints. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u
noncomputable section
namespace CodeSystem.Equivalences
open CategoryTheory EquivalenceFamilies
noncomputable section
variable {Γ : Context.{u}} {φ ψ : Subcontext Γ}
  {A B : Family (restrictContext (φ.join ψ))} (f : A ⟶ B)
  (a : HomotopyEquivalence (Functor.whiskerLeft (includeLeft φ ψ).mapElements f))
  (b : HomotopyEquivalence (Functor.whiskerLeft (includeRight φ ψ).mapElements f))
  (d : ∀ x, φ.Holds x → ψ.Holds x → False)

def disjointGlue : HomotopyEquivalence f := decodeIsEquiv
  (Sections.glue (isEquivReindexSections f (includeLeft φ ψ) a)
    (isEquivReindexSections f (includeRight φ ψ) b)
    (fun x h k => (d (Maps.original x) h k).elim))

theorem disjointGlue_left : (disjointGlue f a b d).reindex (includeLeft φ ψ) = a := by
  apply (isEquivReindexSections f (includeLeft φ ψ)).injective
  rw [isEquivReindexSections_reindex, disjointGlue, encode_decodeIsEquiv]
  exact Sections.glue_left _ _ _

theorem disjointGlue_right : (disjointGlue f a b d).reindex (includeRight φ ψ) = b := by
  apply (isEquivReindexSections f (includeRight φ ψ)).injective
  rw [isEquivReindexSections_reindex, disjointGlue, encode_decodeIsEquiv]
  exact Sections.glue_right _ _ _

theorem ext_cover (E F : HomotopyEquivalence f)
    (hL : E.reindex (includeLeft φ ψ) = F.reindex (includeLeft φ ψ))
    (hR : E.reindex (includeRight φ ψ) = F.reindex (includeRight φ ψ)) : E = F := by
  have hL' := congrArg (isEquivReindexSections f (includeLeft φ ψ)) hL
  have hR' := congrArg (isEquivReindexSections f (includeRight φ ψ)) hR
  rw [isEquivReindexSections_reindex, isEquivReindexSections_reindex] at hL' hR'
  apply (isEquivSections f).injective
  apply Term.ext
  intro x
  rcases x.val.property with h | k
  · exact congrArg (fun s => s.val (Maps.left x h)) hL'
  · exact congrArg (fun s => s.val (Maps.right x k)) hR'

theorem disjointGlue_reindex {Δ : Context.{u}} (σ : Δ ⟶ Γ) :
    (disjointGlue f a b d).reindex (restrictSubstitution (φ.join ψ) σ) =
      disjointGlue (φ := φ.reindex σ) (ψ := ψ.reindex σ)
        (Functor.whiskerLeft (restrictSubstitution (φ.join ψ) σ).mapElements f)
        (a.reindex (restrictSubstitution φ σ)) (b.reindex (restrictSubstitution ψ σ))
        (fun x h k => d (σ.mapElements.obj x) h k) := by
  let e := disjointGlue f a b d
  let ρ := restrictSubstitution (φ.join ψ) σ
  let f' := Functor.whiskerLeft ρ.mapElements f
  let a' := a.reindex (restrictSubstitution φ σ)
  let b' := b.reindex (restrictSubstitution ψ σ)
  let d' := fun x h k => d (σ.mapElements.obj x) h k
  apply ext_cover (φ := φ.reindex σ) (ψ := ψ.reindex σ) f'
  · have hc : (e.reindex ρ).reindex (includeLeft (φ.reindex σ) (ψ.reindex σ)) =
        (e.reindex (includeLeft φ ψ)).reindex (restrictSubstitution φ σ) :=
      (e.reindex_comp ρ (includeLeft (φ.reindex σ) (ψ.reindex σ))).trans
        (e.reindex_comp (includeLeft φ ψ) (restrictSubstitution φ σ)).symm
    exact hc.trans ((congrArg (fun q => q.reindex (restrictSubstitution φ σ))
      (disjointGlue_left f a b d)).trans (disjointGlue_left (φ := φ.reindex σ) (ψ := ψ.reindex σ) f' a' b' d').symm)
  · have hc : (e.reindex ρ).reindex (includeRight (φ.reindex σ) (ψ.reindex σ)) =
        (e.reindex (includeRight φ ψ)).reindex (restrictSubstitution ψ σ) :=
      (e.reindex_comp ρ (includeRight (φ.reindex σ) (ψ.reindex σ))).trans
        (e.reindex_comp (includeRight φ ψ) (restrictSubstitution ψ σ)).symm
    exact hc.trans ((congrArg (fun q => q.reindex (restrictSubstitution ψ σ))
      (disjointGlue_right f a b d)).trans (disjointGlue_right (φ := φ.reindex σ) (ψ := ψ.reindex σ) f' a' b' d').symm)
end
end CodeSystem.Equivalences

namespace NativeUa
variable {Γ : Context.{u}} (A B : LocalFamily Γ)
abbrev face := (intervalFace Γ false).join (intervalFace Γ true)
abbrev boundary := decodedLocalFamily (CodeSystem.boundary A.code B.code)
abbrev ambient := B.reindex (projection (interval Γ))
abbrev faceProjection (b : Bool) := restrictInclusion (intervalFace Γ b) ≫ projection (interval Γ)

theorem boundary_left : (boundary A B).reindex (CodeSystem.includeLeft _ _) =
    A.reindex (faceProjection (Γ := Γ) false) :=
  (CodeSystem.decoded_glue_left _ _ (CodeSystem.endpoints_compatible A.code B.code)).trans
    ((decodedLocalFamily_reindex A.code _).trans
      (congrArg (fun C : LocalFamily Γ => C.reindex (faceProjection (Γ := Γ) false)) A.decodedLocalFamily_code))

theorem boundary_right : (boundary A B).reindex (CodeSystem.includeRight _ _) =
    B.reindex (faceProjection (Γ := Γ) true) :=
  (CodeSystem.decoded_glue_right _ _ (CodeSystem.endpoints_compatible A.code B.code)).trans
    ((decodedLocalFamily_reindex B.code _).trans
      (congrArg (fun C : LocalFamily Γ => C.reindex (faceProjection (Γ := Γ) true)) B.decodedLocalFamily_code))

variable (f : A.family ⟶ B.family)
def leftMap : reindex (boundary A B).family (CodeSystem.includeLeft _ _) ⟶
    reindex (reindex (ambient B).family (restrictInclusion (face (Γ := Γ)))) (CodeSystem.includeLeft _ _) :=
  eqToHom (congrArg LocalFamily.family (boundary_left A B)) ≫
    Functor.whiskerLeft (faceProjection (Γ := Γ) false).mapElements f

def rightMap : reindex (boundary A B).family (CodeSystem.includeRight _ _) ⟶
    reindex (reindex (ambient B).family (restrictInclusion (face (Γ := Γ)))) (CodeSystem.includeRight _ _) :=
  eqToHom (congrArg LocalFamily.family (boundary_right A B))

theorem maps_compatible : CodeSystem.Maps.Compatible (leftMap A B f) (rightMap A B) :=
  fun x h k _ => (intervalFace_disjoint (CodeSystem.Maps.original x) h k).elim

def boundaryMap : (boundary A B).family ⟶ reindex (ambient B).family (restrictInclusion (face (Γ := Γ))) :=
  CodeSystem.Maps.glue (leftMap A B f) (rightMap A B) (maps_compatible A B f)

noncomputable def leftEquivalence (E : HomotopyEquivalence f) : HomotopyEquivalence (leftMap A B f) :=
  (E.reindex (faceProjection (Γ := Γ) false)).castFamilies _ _
    (congrArg LocalFamily.family (boundary_left A B)).symm rfl
noncomputable def rightEquivalence : HomotopyEquivalence (rightMap A B) :=
  (HomotopyEquivalence.identity B.toFilling B.toFilling_lawful).reindex
    (faceProjection (Γ := Γ) true) |>.castFamilies _ _
      (congrArg LocalFamily.family (boundary_right A B)).symm rfl
def mapCast {Ξ : Context.{u}} {C D : Family Ξ} {f g : C ⟶ D}
    (h : f = g) (E : HomotopyEquivalence f) : HomotopyEquivalence g := h ▸ E

noncomputable def boundaryEquivalence (E : HomotopyEquivalence f) : HomotopyEquivalence (boundaryMap A B f) :=
  CodeSystem.Equivalences.disjointGlue (boundaryMap A B f)
    (mapCast (CodeSystem.Maps.glue_left (leftMap A B f) (rightMap A B) (maps_compatible A B f)).symm
      (leftEquivalence A B f E))
    (mapCast (CodeSystem.Maps.glue_right (leftMap A B f) (rightMap A B) (maps_compatible A B f)).symm
      (rightEquivalence A B)) intervalFace_disjoint

noncomputable def line (E : HomotopyEquivalence f) : LocalFamily (total (interval Γ)) :=
  LocalFamily.normalizedGlue (face (Γ := Γ)) (ambient B) (boundary A B)
    (boundaryMap A B f) (boundaryEquivalence A B f E)

theorem line_face (E : HomotopyEquivalence f) :
    (line A B f E).reindex (restrictInclusion (face (Γ := Γ))) = boundary A B :=
  LocalFamily.normalizedGlue_full _ _ _ _ _

theorem line_zero (E : HomotopyEquivalence f) : (line A B f E).reindex (endpointSub Γ false) = A := by
  have h := congrArg (fun C : LocalFamily (restrictContext (face (Γ := Γ))) =>
    C.reindex (CodeSystem.boundaryZero Γ)) (line_face A B f E)
  exact h.trans ((decodedLocalFamily_reindex _ _).symm.trans
    ((congrArg decodedLocalFamily (CodeSystem.boundary_zero A.code B.code)).trans A.decodedLocalFamily_code))

theorem line_one (E : HomotopyEquivalence f) : (line A B f E).reindex (endpointSub Γ true) = B := by
  have h := congrArg (fun C : LocalFamily (restrictContext (face (Γ := Γ))) =>
    C.reindex (CodeSystem.boundaryOne Γ)) (line_face A B f E)
  exact h.trans ((decodedLocalFamily_reindex _ _).symm.trans
    ((congrArg decodedLocalFamily (CodeSystem.boundary_one A.code B.code)).trans B.decodedLocalFamily_code))

noncomputable def codeLine (E : HomotopyEquivalence f) : total (interval (raisedContext Γ)) ⟶ smallFamilyCodes.{u} :=
  (SmallUniverse.raisedIntervalIso Γ).inv ≫ (line A B f E).code

theorem codeLine_zero (E : HomotopyEquivalence f) :
    endpointSub (raisedContext Γ) false ≫ codeLine A B f E = A.code :=
  (LocalFamily.code_reindex (line A B f E) (endpointSub Γ false)).symm.trans
    (congrArg LocalFamily.code (line_zero A B f E))

theorem codeLine_one (E : HomotopyEquivalence f) :
    endpointSub (raisedContext Γ) true ≫ codeLine A B f E = B.code :=
  (LocalFamily.code_reindex (line A B f E) (endpointSub Γ true)).symm.trans
    (congrArg LocalFamily.code (line_one A B f E))

noncomputable def path (E : HomotopyEquivalence f) : Term (homogeneousPath (SmallUniverse.family (raisedContext Γ))
    (SmallUniverse.term A.code) (SmallUniverse.term B.code)) :=
  SmallUniverse.pathOfCode A.code B.code (codeLine A B f E) (codeLine_zero A B f E) (codeLine_one A B f E)

end NativeUa
namespace SmallUniverse.NativeUnivalence
variable {Γ : Context.{u+1}} (a b : Γ ⟶ smallFamilyCodes.{u})
abbrev paths := homogeneousPath (family Γ) (term a) (term b)
abbrev equivalences := EquivalenceFamilies.equiv (liftedDecode a) (liftedDecode b)
variable {a b} (p : Term (paths a b))
noncomputable def pathToMap : liftedDecode a ⟶ liftedDecode b :=
  HomotopyEquivalence.castMap
    (UniversalTransport.selectedMap (codeOfPath p) (endpoint Γ false) (endpoint Γ true))
    _ _ (congrArg liftedDecode (codeOfPath_zero p)) (congrArg liftedDecode (codeOfPath_one p))
noncomputable def pathToEquivalence : HomotopyEquivalence (pathToMap p) :=
  (UniversalTransport.normalizedEquivalence (codeOfPath p) (endpoint Γ false) (endpoint Γ true)).castFamilies
    _ _ (congrArg liftedDecode (codeOfPath_zero p)) (congrArg liftedDecode (codeOfPath_one p))
variable (a b)
def genericPath : Term (paths (projection (paths a b) ≫ a) (projection (paths a b) ≫ b)) :=
  Term.map (pathReindex (reindex (family Γ) (projection (interval Γ)))
    (term a) (term b) (projection (paths a b))) (generic (paths a b))
noncomputable def pathEquivalenceSection : Term (reindex (equivalences a b) (projection (paths a b))) :=
  EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) (projection (paths a b))
    ⟨pathToMap (genericPath a b),pathToEquivalence (genericPath a b)⟩
noncomputable def pathToEquiv : paths a b ⟶ equivalences a b :=
  EquivalenceFamilies.decodeMap (lam (pathEquivalenceSection a b))
end SmallUniverse.NativeUnivalence
end
end SquareKit.Cubical.Cartesian

namespace SquareKit.Cubical.Cartesian.NativeUa
open CategoryTheory
universe u
variable {Γ Δ : Context.{u}} (A B : LocalFamily Γ) (σ : Δ ⟶ Γ)
theorem code_boundary_reindex :
    raisedSub (restrictSubstitution (face (Γ := Γ)) (intervalSub σ)) ≫ CodeSystem.boundary A.code B.code =
      CodeSystem.boundary (A.reindex σ).code (B.reindex σ).code := by
  rw [LocalFamily.code_reindex, LocalFamily.code_reindex]
  exact CodeSystem.glue_reindex _ _ _ (intervalSub σ)

theorem boundary_reindex :
    (boundary A B).reindex (restrictSubstitution (face (Γ := Γ)) (intervalSub σ)) =
      boundary (A.reindex σ) (B.reindex σ) :=
  (decodedLocalFamily_reindex _ _).symm.trans
    (congrArg decodedLocalFamily (code_boundary_reindex A B σ))

theorem whisker_eqToHom {Ξ Ω : Context.{u}} {C D : Family Ξ} (h : C = D) (τ : Ω ⟶ Ξ) :
    Functor.whiskerLeft τ.mapElements (eqToHom h) =
      eqToHom (congrArg (fun Z => reindex Z τ) h) := by
  cases h; rfl

theorem whisker_cast_source {Ξ Ω : Context.{u}} {C D E : Family Ξ}
    (f : D ⟶ E) (h : C = D) (τ : Ω ⟶ Ξ) {C' : Family Ω} (k : C' = reindex C τ) :
    eqToHom k ≫ Functor.whiskerLeft τ.mapElements (eqToHom h ≫ f) =
      eqToHom (k.trans (congrArg (fun Z => reindex Z τ) h)) ≫ Functor.whiskerLeft τ.mapElements f := by
  subst D; subst C'; rfl

theorem leftMap_reindex (f : A.family ⟶ B.family) :
    eqToHom (congrArg (fun T : LocalFamily _ => reindex T.family
      (CodeSystem.includeLeft (intervalFace Δ false) (intervalFace Δ true)))
        (boundary_reindex A B σ)).symm ≫
      Functor.whiskerLeft (restrictSubstitution (intervalFace Γ false) (intervalSub σ)).mapElements
        (leftMap A B f) =
      leftMap (A.reindex σ) (B.reindex σ) (Functor.whiskerLeft σ.mapElements f) := by
  exact whisker_cast_source _ _ _ _

theorem rightMap_reindex :
    eqToHom (congrArg (fun T : LocalFamily _ => reindex T.family
      (CodeSystem.includeRight (intervalFace Δ false) (intervalFace Δ true)))
        (boundary_reindex A B σ)).symm ≫
      Functor.whiskerLeft (restrictSubstitution (intervalFace Γ true) (intervalSub σ)).mapElements
        (rightMap A B) = rightMap (A.reindex σ) (B.reindex σ) := by
  exact (congrArg (fun z => eqToHom (congrArg (fun T : LocalFamily _ => reindex T.family
    (CodeSystem.includeRight (intervalFace Δ false) (intervalFace Δ true)))
      (boundary_reindex A B σ)).symm ≫ z)
    (whisker_eqToHom (congrArg LocalFamily.family (boundary_right A B))
      (restrictSubstitution (intervalFace Γ true) (intervalSub σ)))).trans (eqToHom_trans _ _)


theorem glue_source_congr {Ξ : Context.{u}} {φ ψ : Subcontext Ξ}
    {C D C' : Family (restrictContext (φ.join ψ))} (h : C' = C)
    (a : reindex C (CodeSystem.includeLeft φ ψ) ⟶ reindex D (CodeSystem.includeLeft φ ψ))
    (b : reindex C (CodeSystem.includeRight φ ψ) ⟶ reindex D (CodeSystem.includeRight φ ψ))
    (c : CodeSystem.Maps.Compatible a b)
    (a' : reindex C' (CodeSystem.includeLeft φ ψ) ⟶ reindex D (CodeSystem.includeLeft φ ψ))
    (b' : reindex C' (CodeSystem.includeRight φ ψ) ⟶ reindex D (CodeSystem.includeRight φ ψ))
    (c' : CodeSystem.Maps.Compatible a' b')
    (hL : eqToHom (congrArg (fun Z => reindex Z (CodeSystem.includeLeft φ ψ)) h) ≫ a = a')
    (hR : eqToHom (congrArg (fun Z => reindex Z (CodeSystem.includeRight φ ψ)) h) ≫ b = b') :
    eqToHom h ≫ CodeSystem.Maps.glue a b c = CodeSystem.Maps.glue a' b' c' := by
  subst C'
  have ha : a = a' := hL
  have hb : b = b' := hR
  subst a'; subst b'; rfl

theorem boundaryMap_reindex (f : A.family ⟶ B.family) :
    eqToHom (congrArg LocalFamily.family (boundary_reindex A B σ)).symm ≫
      Functor.whiskerLeft (restrictSubstitution (face (Γ := Γ)) (intervalSub σ)).mapElements
        (boundaryMap A B f) =
      boundaryMap (A.reindex σ) (B.reindex σ) (Functor.whiskerLeft σ.mapElements f) := by
  have h := CodeSystem.Maps.glue_reindex (leftMap A B f) (rightMap A B)
    (maps_compatible A B f) (intervalSub σ)
  refine (congrArg (fun m => eqToHom (congrArg LocalFamily.family (boundary_reindex A B σ)).symm ≫ m) h).trans ?_
  exact glue_source_congr _ _ _ _ _ _ _ (leftMap_reindex A B σ f) (rightMap_reindex A B σ)


theorem cast_reindex_twice {Ξ Ω Λ : Context.{u}} {C D : Family Ξ} {f : C ⟶ D}
    (E : HomotopyEquivalence f) (ρ : Ω ⟶ Ξ) (τ : Λ ⟶ Ω) (κ : Λ ⟶ Ξ) (h : τ ≫ ρ = κ)
    (C' D' : Family Ω) (hC : reindex C ρ = C') (hD : reindex D ρ = D')
    (C'' D'' : Family Λ) (hC' : reindex C' τ = C'') (hD' : reindex D' τ = D'')
    (hC'' : reindex C κ = C'') (hD'' : reindex D κ = D'') :
    HEq ((((E.reindex ρ).castFamilies C' D' hC hD).reindex τ).castFamilies C'' D'' hC' hD')
      ((E.reindex κ).castFamilies C'' D'' hC'' hD'') := by
  subst κ
  subst C'; subst D'; subst C''; subst D''
  exact heq_of_eq (E.reindex_comp ρ τ)


theorem cast_reindex_associate {Ξ Ω Λ : Context.{u}} {C D : Family Ξ} {f : C ⟶ D}
    (E : HomotopyEquivalence f) (ρ : Ω ⟶ Ξ) (τ : Λ ⟶ Ω)
    (C' D' : Family Λ) (hC : reindex C (τ ≫ ρ) = C') (hD : reindex D (τ ≫ ρ) = D') :
    HEq (((E.reindex ρ).reindex τ).castFamilies C' D' hC hD)
      ((E.reindex (τ ≫ ρ)).castFamilies C' D' hC hD) :=
  heq_of_eq (congrArg (fun e => e.castFamilies C' D' hC hD) (E.reindex_comp ρ τ))

theorem leftEquivalence_reindex (f : A.family ⟶ B.family) (E : HomotopyEquivalence f) :
    HEq (((leftEquivalence A B f E).reindex
      (restrictSubstitution (intervalFace Γ false) (intervalSub σ))).castFamilies
        (reindex (boundary (A.reindex σ) (B.reindex σ)).family
          (CodeSystem.includeLeft (intervalFace Δ false) (intervalFace Δ true))) _
        (congrArg (fun T : LocalFamily _ => reindex T.family
          (CodeSystem.includeLeft (intervalFace Δ false) (intervalFace Δ true)))
            (boundary_reindex A B σ)) rfl)
      (leftEquivalence (A.reindex σ) (B.reindex σ) (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)) := by
  exact (cast_reindex_twice E (faceProjection (Γ := Γ) false)
    (restrictSubstitution (intervalFace Γ false) (intervalSub σ))
    (faceProjection (Γ := Δ) false ≫ σ) rfl _ _ _ _ _ _ _ _ _ _).trans
      (cast_reindex_associate E σ (faceProjection (Γ := Δ) false) _ _ _ _).symm


theorem rightEquivalence_reindex :
    HEq (((rightEquivalence A B).reindex
      (restrictSubstitution (intervalFace Γ true) (intervalSub σ))).castFamilies
        (reindex (boundary (A.reindex σ) (B.reindex σ)).family
          (CodeSystem.includeRight (intervalFace Δ false) (intervalFace Δ true))) _
        (congrArg (fun T : LocalFamily _ => reindex T.family
          (CodeSystem.includeRight (intervalFace Δ false) (intervalFace Δ true)))
            (boundary_reindex A B σ)) rfl)
      (rightEquivalence (A.reindex σ) (B.reindex σ)) := by
  let I := HomotopyEquivalence.identity B.toFilling B.toFilling_lawful
  have hi : I.reindex σ = HomotopyEquivalence.identity
      (B.reindex σ).toFilling (B.reindex σ).toFilling_lawful :=
    HomotopyEquivalence.ofIso_reindex (Iso.refl B.family) B.toFilling B.toFilling_lawful σ
  refine (cast_reindex_twice I (faceProjection (Γ := Γ) true)
    (restrictSubstitution (intervalFace Γ true) (intervalSub σ))
    (faceProjection (Γ := Δ) true ≫ σ) rfl _ _ _ _ _ _ _ _
      (congrArg LocalFamily.family (boundary_right (A.reindex σ) (B.reindex σ))).symm rfl).trans ?_
  refine (cast_reindex_associate I σ (faceProjection (Γ := Δ) true) _ _
    (congrArg LocalFamily.family (boundary_right (A.reindex σ) (B.reindex σ))).symm rfl).symm.trans ?_
  exact heq_of_eq (congrArg (fun e => (e.reindex (faceProjection (Γ := Δ) true)).castFamilies _ _
    (congrArg LocalFamily.family (boundary_right (A.reindex σ) (B.reindex σ))).symm rfl) hi)


theorem disjointGlue_cast {Ξ : Context.{u}} {φ ψ : Subcontext Ξ}
    {C D C' : Family (restrictContext (φ.join ψ))} (h : C = C')
    (f : C ⟶ D) (f' : C' ⟶ D)
    (hf : HomotopyEquivalence.castMap f C' D h rfl = f')
    (a : HomotopyEquivalence (Functor.whiskerLeft (CodeSystem.includeLeft φ ψ).mapElements f))
    (b : HomotopyEquivalence (Functor.whiskerLeft (CodeSystem.includeRight φ ψ).mapElements f))
    (a' : HomotopyEquivalence (Functor.whiskerLeft (CodeSystem.includeLeft φ ψ).mapElements f'))
    (b' : HomotopyEquivalence (Functor.whiskerLeft (CodeSystem.includeRight φ ψ).mapElements f'))
    (d : ∀ x, φ.Holds x → ψ.Holds x → False)
    (ha : HEq (a.castFamilies (reindex C' (CodeSystem.includeLeft φ ψ)) _
      (congrArg (fun Z => reindex Z (CodeSystem.includeLeft φ ψ)) h) rfl) a')
    (hb : HEq (b.castFamilies (reindex C' (CodeSystem.includeRight φ ψ)) _
      (congrArg (fun Z => reindex Z (CodeSystem.includeRight φ ψ)) h) rfl) b') :
    HEq ((CodeSystem.Equivalences.disjointGlue f a b d).castFamilies C' D h rfl)
      (CodeSystem.Equivalences.disjointGlue f' a' b' d) := by
  subst C'
  have hf' : f = f' := hf
  subst f'
  have ha' : a = a' := eq_of_heq ha
  have hb' : b = b' := eq_of_heq hb
  subst a'; subst b'; rfl

theorem cast_map_reindex {Ξ Ω : Context.{u}} {C D : Family Ξ} {f g : C ⟶ D}
    (h : f = g) (E : HomotopyEquivalence f) (τ : Ω ⟶ Ξ)
    (C' D' : Family Ω) (hC : reindex C τ = C') (hD : reindex D τ = D') :
    HEq (((h ▸ E).reindex τ).castFamilies C' D' hC hD)
      ((E.reindex τ).castFamilies C' D' hC hD) := by
  cases h; rfl

theorem cast_map_heq {Ξ : Context.{u}} {C D : Family Ξ} {f g : C ⟶ D}
    (h : f = g) (E : HomotopyEquivalence f) : HEq (h ▸ E) E := by
  cases h; rfl


attribute [local irreducible] boundaryEquivalence in
theorem boundaryEquivalence_reindex (f : A.family ⟶ B.family) (E : HomotopyEquivalence f) :
    HEq (((boundaryEquivalence A B f E).reindex
      (restrictSubstitution (face (Γ := Γ)) (intervalSub σ))).castFamilies
        (boundary (A.reindex σ) (B.reindex σ)).family
        (reindex (ambient (B.reindex σ)).family (restrictInclusion (face (Γ := Δ))))
        (congrArg LocalFamily.family (boundary_reindex A B σ)) rfl)
      (boundaryEquivalence (A.reindex σ) (B.reindex σ) (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)) := by
  unfold boundaryEquivalence
  let ρ := restrictSubstitution (face (Γ := Γ)) (intervalSub σ)
  let f' := Functor.whiskerLeft σ.mapElements f
  let hL := (CodeSystem.Maps.glue_left (leftMap A B f) (rightMap A B) (maps_compatible A B f)).symm
  let hR := (CodeSystem.Maps.glue_right (leftMap A B f) (rightMap A B) (maps_compatible A B f)).symm
  let a := hL ▸ leftEquivalence A B f E
  let b := hR ▸ rightEquivalence A B
  let hL' := (CodeSystem.Maps.glue_left (leftMap (A.reindex σ) (B.reindex σ) f')
    (rightMap (A.reindex σ) (B.reindex σ)) (maps_compatible (A.reindex σ) (B.reindex σ) f')).symm
  let hR' := (CodeSystem.Maps.glue_right (leftMap (A.reindex σ) (B.reindex σ) f')
    (rightMap (A.reindex σ) (B.reindex σ)) (maps_compatible (A.reindex σ) (B.reindex σ) f')).symm
  let a' := hL' ▸ leftEquivalence (A.reindex σ) (B.reindex σ) f' (E.reindex σ)
  let b' := hR' ▸ rightEquivalence (A.reindex σ) (B.reindex σ)
  have hg := CodeSystem.Equivalences.disjointGlue_reindex (boundaryMap A B f) a b
    intervalFace_disjoint (intervalSub σ)
  refine (heq_of_eq (congrArg (fun e => e.castFamilies
    (boundary (A.reindex σ) (B.reindex σ)).family
        (reindex (ambient (B.reindex σ)).family (restrictInclusion (face (Γ := Δ))))
    (congrArg LocalFamily.family (boundary_reindex A B σ)) rfl) hg)).trans ?_
  refine disjointGlue_cast (φ := intervalFace Δ false) (ψ := intervalFace Δ true) (congrArg LocalFamily.family (boundary_reindex A B σ))
    (Functor.whiskerLeft ρ.mapElements (boundaryMap A B f))
    (boundaryMap (A.reindex σ) (B.reindex σ) f') (boundaryMap_reindex A B σ f)
    (a.reindex (restrictSubstitution (intervalFace Γ false) (intervalSub σ)))
    (b.reindex (restrictSubstitution (intervalFace Γ true) (intervalSub σ))) a' b'
    intervalFace_disjoint ?_ ?_
  · exact (cast_map_reindex hL (leftEquivalence A B f E)
      (restrictSubstitution (intervalFace Γ false) (intervalSub σ)) _ _ _ _).trans
        ((leftEquivalence_reindex A B σ f E).trans
          (cast_map_heq hL' (leftEquivalence (A.reindex σ) (B.reindex σ) f' (E.reindex σ))).symm)
  · exact (cast_map_reindex hR (rightEquivalence A B)
      (restrictSubstitution (intervalFace Γ true) (intervalSub σ)) _ _ _ _).trans
        ((rightEquivalence_reindex A B σ).trans
          (cast_map_heq hR' (rightEquivalence (A.reindex σ) (B.reindex σ))).symm)


theorem normalizedGlue_source_congr {Ξ : Context.{u}} (φ : Subcontext Ξ)
    (C : LocalFamily Ξ) (T T' : LocalFamily (restrictContext φ)) (h : T = T')
    (f : T.family ⟶ reindex C.family (restrictInclusion φ))
    (f' : T'.family ⟶ reindex C.family (restrictInclusion φ))
    (E : HomotopyEquivalence f) (E' : HomotopyEquivalence f')
    (hf : HomotopyEquivalence.castMap f T'.family _ (congrArg LocalFamily.family h) rfl = f')
    (hE : HEq (E.castFamilies T'.family _ (congrArg LocalFamily.family h) rfl) E') :
    LocalFamily.normalizedGlue φ C T f E = LocalFamily.normalizedGlue φ C T' f' E' := by
  subst T'
  have hf' : f = f' := hf
  subst f'
  have he : E = E' := eq_of_heq hE
  subst E'; rfl

theorem line_reindex (f : A.family ⟶ B.family) (E : HomotopyEquivalence f) :
    (line A B f E).reindex (intervalSub σ) =
      line (A.reindex σ) (B.reindex σ) (Functor.whiskerLeft σ.mapElements f) (E.reindex σ) := by
  refine (LocalFamily.normalizedGlue_substitution (face (Γ := Γ)) (ambient B) (boundary A B)
    (boundaryMap A B f) (boundaryEquivalence A B f E) (intervalSub σ)).trans ?_
  exact normalizedGlue_source_congr (face (Γ := Δ)) (ambient (B.reindex σ)) _ _
    (boundary_reindex A B σ) _ _ _ _ (boundaryMap_reindex A B σ f) (boundaryEquivalence_reindex A B σ f E)


theorem line_code_reindex (f : A.family ⟶ B.family) (E : HomotopyEquivalence f) :
    raisedSub (intervalSub σ) ≫ (line A B f E).code =
      (line (A.reindex σ) (B.reindex σ) (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)).code :=
  (LocalFamily.code_reindex (line A B f E) (intervalSub σ)).symm.trans
    (congrArg LocalFamily.code (line_reindex A B σ f E))

theorem line_congr {Ξ : Context.{u}} (C D C' D' : LocalFamily Ξ)
    (hC : C = C') (hD : D = D') (f : C.family ⟶ D.family) (f' : C'.family ⟶ D'.family)
    (hf : HEq f f') (E : HomotopyEquivalence f) (E' : HomotopyEquivalence f') (hE : HEq E E') :
    line C D f E = line C' D' f' E' := by
  subst C'; subst D'
  have hf' := eq_of_heq hf
  subst f'
  have he := eq_of_heq hE
  subst E'; rfl

end SquareKit.Cubical.Cartesian.NativeUa

namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u
namespace HomotopyEquivalence
 theorem castFamilies_substitute {Γ Δ : Context.{u}} {A B : Family Γ}
    {f : A ⟶ B} (E : HomotopyEquivalence f) (σ : Δ ⟶ Γ)
    (g : Cartesian.reindex A σ ⟶ Cartesian.reindex B σ) (H : HomotopyEquivalence g)
    (hg : Functor.whiskerLeft σ.mapElements f = g) (hH : HEq (E.reindex σ) H)
    (A' B' : Family Γ) (hA : A = A') (hB : B = B') :
    HEq ((E.castFamilies A' B' hA hB).reindex σ)
      (H.castFamilies (Cartesian.reindex A' σ) (Cartesian.reindex B' σ)
        (congrArg (fun C => Cartesian.reindex C σ) hA) (congrArg (fun C => Cartesian.reindex C σ) hB)) := by
  subst g
  have h := eq_of_heq hH
  subst H
  subst A'; subst B'; rfl
 theorem castMap_substitute {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ Γ) (g : Cartesian.reindex A σ ⟶ Cartesian.reindex B σ)
    (hg : Functor.whiskerLeft σ.mapElements f = g)
    (A' B' : Family Γ) (hA : A = A') (hB : B = B') :
    Functor.whiskerLeft σ.mapElements (castMap f A' B' hA hB) =
      castMap g (Cartesian.reindex A' σ) (Cartesian.reindex B' σ)
        (congrArg (fun C => Cartesian.reindex C σ) hA) (congrArg (fun C => Cartesian.reindex C σ) hB) := by
  subst g; subst A'; subst B'; rfl
end HomotopyEquivalence
namespace EquivalenceFamilies
theorem decodeMap_lam_reindex_apply {Γ Δ : Context.{u}} {A B : Family Γ}
    (s : Term (Cartesian.reindex B (projection A))) (σ : Δ ⟶ Γ)
    (a : Term (Cartesian.reindex A σ)) :
    Term.map (Functor.whiskerLeft σ.mapElements (decodeMap (lam s))) a =
      Term.reindex s (pair σ a) := by
  apply Term.ext
  intro x
  rfl

end EquivalenceFamilies
namespace SmallUniverse.NativeUnivalence
variable {Γ Δ : Context.{u+1}} {a b : Γ ⟶ smallFamilyCodes.{u}}
def reindexPath (p : Term (paths a b)) (σ : Δ ⟶ Γ) : Term (paths (σ ≫ a) (σ ≫ b)) :=
  homogeneousReindex p σ
theorem codeOfPath_reindexPath (p : Term (paths a b)) (σ : Δ ⟶ Γ) :
    codeOfPath (reindexPath p σ) = intervalSub σ ≫ codeOfPath p := rfl

theorem pathToMap_reindex (p : Term (paths a b)) (σ : Δ ⟶ Γ) :
    Functor.whiskerLeft σ.mapElements (pathToMap p) = pathToMap (reindexPath p σ) := by
  exact HomotopyEquivalence.castMap_substitute
    (UniversalTransport.selectedMap (codeOfPath p) (endpoint Γ false) (endpoint Γ true)) σ
    (UniversalTransport.selectedMap (codeOfPath (reindexPath p σ)) (endpoint Δ false) (endpoint Δ true))
    (UniversalTransport.selectedMap_reindex (codeOfPath p) (endpoint Γ false) (endpoint Γ true) σ).symm
    _ _ (congrArg liftedDecode (codeOfPath_zero p)) (congrArg liftedDecode (codeOfPath_one p))

theorem pathToEquivalence_reindex (p : Term (paths a b)) (σ : Δ ⟶ Γ) :
    HEq ((pathToEquivalence p).reindex σ) (pathToEquivalence (reindexPath p σ)) := by
  exact HomotopyEquivalence.castFamilies_substitute
    (UniversalTransport.normalizedEquivalence (codeOfPath p) (endpoint Γ false) (endpoint Γ true)) σ
    (UniversalTransport.selectedMap (codeOfPath (reindexPath p σ)) (endpoint Δ false) (endpoint Δ true))
    (UniversalTransport.normalizedEquivalence (codeOfPath (reindexPath p σ)) (endpoint Δ false) (endpoint Δ true))
    (UniversalTransport.selectedMap_reindex (codeOfPath p) (endpoint Γ false) (endpoint Γ true) σ).symm
    (UniversalTransport.normalizedEquivalence_reindex (codeOfPath p) (endpoint Γ false) (endpoint Γ true) σ)
    _ _ (congrArg liftedDecode (codeOfPath_zero p)) (congrArg liftedDecode (codeOfPath_one p))
theorem genericPath_pair (σ : Δ ⟶ Γ) (p : Term (Cartesian.reindex (paths a b) σ)) :
    reindexPath (genericPath a b) (pair (A := paths a b) σ p) =
      Term.map (pathReindex (Cartesian.reindex (family Γ) (projection (interval Γ)))
        (term a) (term b) σ) p := by
  apply pathApp_injective
  rfl

private theorem pathToEquivalence_congr {p q : Term (paths a b)} (h : p = q) :
    HEq (pathToEquivalence p) (pathToEquivalence q) := by
  cases h
  rfl

/-- Evaluation after any substitution recovers all selected equivalence data. -/
theorem pathToEquivalence_record_pair (σ : Δ ⟶ Γ) (p : Term (Cartesian.reindex (paths a b) σ)) :
    let q : Term (paths (σ ≫ a) (σ ≫ b)) := Term.map (pathReindex (Cartesian.reindex (family Γ) (projection (interval Γ)))
      (term a) (term b) σ) p
    (⟨Functor.whiskerLeft (pair (A := paths a b) σ p).mapElements
        (pathToMap (genericPath a b)),
      (pathToEquivalence (genericPath a b)).reindex (pair (A := paths a b) σ p)⟩ :
      Σ f : liftedDecode (σ ≫ a) ⟶ liftedDecode (σ ≫ b), HomotopyEquivalence f) =
      ⟨pathToMap q, pathToEquivalence q⟩ := by
  dsimp only
  have hm := (pathToMap_reindex (genericPath a b) (pair (A := paths a b) σ p)).trans
    (congrArg (@pathToMap Δ (σ ≫ a) (σ ≫ b)) (genericPath_pair σ p))
  have hE := (pathToEquivalence_reindex (genericPath a b) (pair (A := paths a b) σ p)).trans
    (pathToEquivalence_congr (genericPath_pair σ p))
  exact Sigma.ext hm hE

/-- The native forward map evaluates to the full selected transport equivalence
in every substituted context. -/
theorem pathToEquiv_reindex_beta (σ : Δ ⟶ Γ) (p : Term (Cartesian.reindex (paths a b) σ)) :
    Term.map (Functor.whiskerLeft σ.mapElements (pathToEquiv a b)) p =
      EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) σ
        ⟨pathToMap (a := σ ≫ a) (b := σ ≫ b) (Term.map (pathReindex (Cartesian.reindex (family Γ) (projection (interval Γ)))
          (term a) (term b) σ) p),
         pathToEquivalence (a := σ ≫ a) (b := σ ≫ b) (Term.map (pathReindex (Cartesian.reindex (family Γ) (projection (interval Γ)))
          (term a) (term b) σ) p)⟩ := by
  let q := pair (A := paths a b) σ p
  have h := EquivalenceFamilies.equivReindexSections_comp (liftedDecode a) (liftedDecode b)
    (projection (paths a b)) q (pathToMap (genericPath a b)) (pathToEquivalence (genericPath a b))
  exact (EquivalenceFamilies.decodeMap_lam_reindex_apply (pathEquivalenceSection a b) σ p).trans
    (h.trans (congrArg
      (EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) σ)
      (pathToEquivalence_record_pair σ p)))


end SmallUniverse.NativeUnivalence
end SquareKit.Cubical.Cartesian

namespace SquareKit.Cubical.Cartesian.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u
variable {Ξ : Context.{u+1}}

def chartPoint (x : (total (interval Ξ)).Elements) :
    (raisedContext (total (interval (representable.{u} x.obj.unop)))).obj x.obj :=
  ⟨⟨⟨𝟙 x.obj.unop⟩,⟨x.val.2.down⟩⟩⟩

theorem chartInterval_generic (x : (total (interval Ξ)).Elements) :
    (chartInterval (chart (intervalBase x))).app x.obj (chartPoint x) = x.val := by
  apply Sigma.ext
  · exact chart_generic (intervalBase x)
  · rfl

theorem chartPoint_natural {x y : (total (interval Ξ)).Elements} (f : x ⟶ y) :
    (raisedContext (total (interval (representable.{u} x.obj.unop)))).map f.hom (chartPoint x) =
      (raisedSub (intervalSub (representableMap f.hom.unop))).app y.obj (chartPoint y) := by
  apply ULift.ext
  apply Sigma.ext
  · exact congrArg ULift.up ((Category.comp_id f.hom.unop).trans (Category.id_comp f.hom.unop).symm)
  · exact heq_of_eq (congrArg (fun z : (total (interval Ξ)).obj y.obj =>
      (ULift.up z.2.down : ULift.{u} (Cube.Hom y.obj.unop ⟨1⟩))) f.map_val)



variable (a b : Ξ ⟶ smallFamilyCodes.{u})
  (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
noncomputable def chartCode {Γ : Context.{u}} (σ : raisedContext Γ ⟶ Ξ) :
    raisedContext (total (interval Γ)) ⟶ smallFamilyCodes.{u} :=
  (NativeUa.line (decodedLocalFamily (σ ≫ a)) (decodedLocalFamily (σ ≫ b))
    (lowerChartMap a b σ f) (lowerChartEquivalence a b σ f E)).code

theorem chartCode_reindex {Γ Δ : Context.{u}} (σ : raisedContext Γ ⟶ Ξ) (τ : Δ ⟶ Γ) :
    raisedSub (intervalSub τ) ≫ chartCode a b f E σ =
      chartCode a b f E (raisedSub τ ≫ σ) := by
  apply (NativeUa.line_code_reindex (decodedLocalFamily (σ ≫ a))
    (decodedLocalFamily (σ ≫ b)) τ (lowerChartMap a b σ f)
    (lowerChartEquivalence a b σ f E)).trans
  apply congrArg LocalFamily.code
  apply NativeUa.line_congr
  · exact (decodedLocalFamily_reindex (σ ≫ a) τ).symm
  · exact (decodedLocalFamily_reindex (σ ≫ b) τ).symm
  · rfl
  · exact heq_of_eq (lowerChartEquivalence_reindex a b σ f E τ).symm

theorem chartCode_zero {Γ : Context.{u}} (σ : raisedContext Γ ⟶ Ξ) :
    raisedSub (endpointSub Γ false) ≫ chartCode a b f E σ = σ ≫ a := by
  exact (LocalFamily.code_reindex _ _).symm.trans
    ((congrArg LocalFamily.code (NativeUa.line_zero (decodedLocalFamily (σ ≫ a))
      (decodedLocalFamily (σ ≫ b)) (lowerChartMap a b σ f)
      (lowerChartEquivalence a b σ f E))).trans (code_decode (σ ≫ a)))
theorem chartCode_one {Γ : Context.{u}} (σ : raisedContext Γ ⟶ Ξ) :
    raisedSub (endpointSub Γ true) ≫ chartCode a b f E σ = σ ≫ b := by
  exact (LocalFamily.code_reindex _ _).symm.trans
    ((congrArg LocalFamily.code (NativeUa.line_one (decodedLocalFamily (σ ≫ a))
      (decodedLocalFamily (σ ≫ b)) (lowerChartMap a b σ f)
      (lowerChartEquivalence a b σ f E))).trans (code_decode (σ ≫ b)))
noncomputable def uaValue (x : (total (interval Ξ)).Elements) : SmallFamilyCode.{u} x.obj.unop :=
  (chartCode a b f E (chart (intervalBase x))).app x.obj (chartPoint x)

theorem uaValue_natural {x y : (total (interval Ξ)).Elements} (g : x ⟶ y) :
    smallFamilyCodes.map g.hom (uaValue a b f E x) = uaValue a b f E y := by
  let σ := chart (intervalBase x)
  have hn := ((chartCode a b f E σ).naturality_apply g.hom (chartPoint x)).symm
  have hr := congrArg (fun c : raisedContext (total (interval (representable.{u} y.obj.unop))) ⟶
    smallFamilyCodes.{u} => c.app y.obj (chartPoint y))
    (chartCode_reindex a b f E σ (representableMap g.hom.unop))
  have hc := congrArg (fun c : raisedContext (representable.{u} y.obj.unop) ⟶ Ξ =>
    (chartCode a b f E c).app y.obj (chartPoint y))
    (chart_restrict ((projection (interval Ξ)).mapElements.map g))
  exact hn.trans ((congrArg ((chartCode a b f E σ).app y.obj) (chartPoint_natural g)).trans
    (hr.trans hc))

noncomputable def coherentLine : Term (family (total (interval Ξ))) where
  val := uaValue a b f E
  property g := uaValue_natural a b f E g

theorem coherentLine_zero : Term.reindex (coherentLine a b f E) (endpointSub Ξ false) = term a := by
  apply Term.ext
  intro x
  have h := congrArg (fun c => c.app x.obj ⟨⟨𝟙 x.obj.unop⟩⟩)
    (chartCode_zero a b f E (chart x))
  exact h.trans (congrArg (a.app x.obj) (chart_generic x))

theorem coherentLine_one : Term.reindex (coherentLine a b f E) (endpointSub Ξ true) = term b := by
  apply Term.ext
  intro x
  have h := congrArg (fun c => c.app x.obj ⟨⟨𝟙 x.obj.unop⟩⟩)
    (chartCode_one a b f E (chart x))
  exact h.trans (congrArg (b.app x.obj) (chart_generic x))

noncomputable def ua : Term (paths a b) :=
  pathLam (coherentLine a b f E) (coherentLine_zero a b f E) (coherentLine_one a b f E)


noncomputable def genericEquivalence :
    Σ g : Cartesian.reindex (liftedDecode a) (projection (equivalences a b)) ⟶
      Cartesian.reindex (liftedDecode b) (projection (equivalences a b)), HomotopyEquivalence g :=
  (EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b)
    (projection (equivalences a b))).symm (generic (equivalences a b))

noncomputable def equivalencePathSection :
    Term (Cartesian.reindex (paths a b) (projection (equivalences a b))) :=
  Term.map (pathReindexIso (Cartesian.reindex (family Ξ) (projection (interval Ξ)))
    (term a) (term b) (projection (equivalences a b))).inv
    (ua (projection (equivalences a b) ≫ a) (projection (equivalences a b) ≫ b)
      (genericEquivalence a b).1 (genericEquivalence a b).2)

/-- The reverse operation is a native map out of the full internal equivalence family. -/
noncomputable def equivToPath : equivalences a b ⟶ paths a b :=
  EquivalenceFamilies.decodeMap (lam (equivalencePathSection a b))


end SquareKit.Cubical.Cartesian.SmallUniverse.NativeUnivalence

namespace SquareKit.Cubical.Cartesian.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u
variable {Γ Δ : Context.{u+1}} {a b : Γ ⟶ smallFamilyCodes.{u}}
theorem lowerChartEquivalence_comp {Θ : Context.{u}}
    (a b : Γ ⟶ smallFamilyCodes.{u}) (f : liftedDecode a ⟶ liftedDecode b)
    (E : HomotopyEquivalence f) (σ : Δ ⟶ Γ) (ρ : raisedContext Θ ⟶ Δ) :
    lowerChartEquivalence a b (ρ ≫ σ) f E =
      lowerChartEquivalence (σ ≫ a) (σ ≫ b) ρ
        (Functor.whiskerLeft σ.mapElements f) (E.reindex σ) := by
  exact congrArg
    (fun H : HomotopyEquivalence (Functor.whiskerLeft (ρ ≫ σ).mapElements f) =>
      Raising.lowerEquivalence (A := Cartesian.decode (ρ ≫ σ ≫ a))
        (B := Cartesian.decode (ρ ≫ σ ≫ b))
        (f := lowerChartMap a b (ρ ≫ σ) f) H)
    (E.reindex_comp σ ρ).symm

theorem chartCode_comp {Θ : Context.{u}}
    (a b : Γ ⟶ smallFamilyCodes.{u}) (f : liftedDecode a ⟶ liftedDecode b)
    (E : HomotopyEquivalence f) (σ : Δ ⟶ Γ) (ρ : raisedContext Θ ⟶ Δ) :
    chartCode a b f E (ρ ≫ σ) =
      chartCode (σ ≫ a) (σ ≫ b) (Functor.whiskerLeft σ.mapElements f) (E.reindex σ) ρ :=
  congrArg (fun H => (NativeUa.line (decodedLocalFamily (ρ ≫ σ ≫ a))
    (decodedLocalFamily (ρ ≫ σ ≫ b)) (lowerChartMap a b (ρ ≫ σ) f) H).code) (lowerChartEquivalence_comp a b f E σ ρ)

theorem coherentLine_reindex (a b : Γ ⟶ smallFamilyCodes.{u})
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f) (σ : Δ ⟶ Γ) :
    Term.reindex (coherentLine a b f E) (intervalSub σ) =
      coherentLine (σ ≫ a) (σ ≫ b) (Functor.whiskerLeft σ.mapElements f) (E.reindex σ) := by
  apply Term.ext
  intro x
  have h := congrArg (fun ρ : raisedContext (representable.{u} x.obj.unop) ⟶ Γ =>
    (chartCode a b f E ρ).app x.obj (chartPoint x))
    (chart_substitution σ (intervalBase x))
  exact h.trans (congrArg (fun c => c.app x.obj (chartPoint x))
    (chartCode_comp a b f E σ (chart (intervalBase x))))

theorem ua_reindex (a b : Γ ⟶ smallFamilyCodes.{u})
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f) (σ : Δ ⟶ Γ) :
    reindexPath (ua a b f E) σ =
      ua (σ ≫ a) (σ ≫ b) (Functor.whiskerLeft σ.mapElements f) (E.reindex σ) := by
  apply eq_of_heq
  apply heq_of_pathApp_eq
  exact coherentLine_reindex a b f E σ


theorem reindexPath_section_reindex_pair {C : Family Γ}
    (s : Term (Cartesian.reindex (paths a b) (projection C))) (σ : Δ ⟶ Γ)
    (c : Term (reindex C σ)) :
    reindexPath (a := projection C ≫ a) (b := projection C ≫ b)
      (Term.map (pathReindex (Cartesian.reindex (family Γ) (projection (interval Γ)))
        (term a) (term b) (projection C)) s) (pair (A := C) σ c) =
      Term.map (pathReindex (Cartesian.reindex (family Γ) (projection (interval Γ)))
        (term a) (term b) σ) (Term.reindex s (pair (A := C) σ c)) := by
  apply eq_of_heq
  apply heq_of_pathApp_eq
  rfl

theorem equivalencePathSection_reindex_pair (σ : Δ ⟶ Γ)
    (c : Term (Cartesian.reindex (equivalences a b) σ)) :
    Term.map (pathReindex (Cartesian.reindex (family Γ) (projection (interval Γ)))
      (term a) (term b) σ)
      (Term.reindex (equivalencePathSection a b) (pair (A := equivalences a b) σ c)) =
      ua (σ ≫ a) (σ ≫ b)
        (Functor.whiskerLeft (pair (A := equivalences a b) σ c).mapElements (genericEquivalence a b).1)
        ((genericEquivalence a b).2.reindex (pair (A := equivalences a b) σ c)) := by
  have h := Term.map_iso_roundtrip
    (pathReindexIso (Cartesian.reindex (family Γ) (projection (interval Γ)))
      (term a) (term b) (projection (equivalences a b))).symm
    (ua (projection (equivalences a b) ≫ a) (projection (equivalences a b) ≫ b)
      (genericEquivalence a b).1 (genericEquivalence a b).2)
  exact (reindexPath_section_reindex_pair (equivalencePathSection a b) σ c).symm.trans
    ((congrArg (fun p => reindexPath p (pair (A := equivalences a b) σ c)) h).trans
      (ua_reindex _ _ _ _ (pair (A := equivalences a b) σ c)))

/-- Generic evaluation recovers the supplied internal section's full decoded data. -/
theorem genericEquivalence_reindex_pair (σ : Δ ⟶ Γ)
    (s : Term (Cartesian.reindex (equivalences a b) σ)) :
    (⟨Functor.whiskerLeft (pair (A := equivalences a b) σ s).mapElements
        (genericEquivalence a b).1,
      (genericEquivalence a b).2.reindex (pair (A := equivalences a b) σ s)⟩ :
      Σ f : liftedDecode (σ ≫ a) ⟶ liftedDecode (σ ≫ b), HomotopyEquivalence f) =
      (EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) σ).symm s := by
  let q := pair (A := equivalences a b) σ s
  let S := EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) σ
  apply S.injective
  have h := EquivalenceFamilies.equivReindexSections_comp (liftedDecode a) (liftedDecode b)
    (projection (equivalences a b)) q (genericEquivalence a b).1 (genericEquivalence a b).2
  have hr := (EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b)
    (projection (equivalences a b))).apply_symm_apply (generic (equivalences a b))
  exact (h.symm.trans (congrArg (fun t => Term.reindex t q) hr)).trans (S.apply_symm_apply s).symm

private theorem ua_congr_data (a b : Γ ⟶ smallFamilyCodes.{u})
    (f g : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (F : HomotopyEquivalence g)
    (h : (⟨f,E⟩ : Σ k : liftedDecode a ⟶ liftedDecode b, HomotopyEquivalence k) = ⟨g,F⟩) :
    ua a b f E = ua a b g F :=
  @congrArg (Σ k : liftedDecode a ⟶ liftedDecode b, HomotopyEquivalence k)
    (Term (paths a b)) ⟨f,E⟩ ⟨g,F⟩ (fun z => ua a b z.1 z.2) h

/-- The native reverse map evaluates to the actual chosen Glue path in every
substituted context, retaining the section's selected equivalence witness. -/
theorem equivToPath_reindex_beta (σ : Δ ⟶ Γ)
    (s : Term (Cartesian.reindex (equivalences a b) σ)) :
    Term.map (pathReindex (Cartesian.reindex (family Γ) (projection (interval Γ)))
      (term a) (term b) σ)
      (Term.map (Functor.whiskerLeft σ.mapElements (equivToPath a b)) s) =
      ua (σ ≫ a) (σ ≫ b)
        ((EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) σ).symm s).1
        ((EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) σ).symm s).2 := by
  have h := EquivalenceFamilies.decodeMap_lam_reindex_apply (equivalencePathSection a b) σ s
  let q := pair (A := equivalences a b) σ s
  let d := (EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) σ).symm s
  have hu : ua (σ ≫ a) (σ ≫ b)
      (Functor.whiskerLeft q.mapElements (genericEquivalence a b).1)
      ((genericEquivalence a b).2.reindex q) = ua (σ ≫ a) (σ ≫ b) d.1 d.2 :=
    ua_congr_data (σ ≫ a) (σ ≫ b)
      (Functor.whiskerLeft q.mapElements (genericEquivalence a b).1) d.1
      ((genericEquivalence a b).2.reindex q) d.2 (genericEquivalence_reindex_pair σ s)
  exact (congrArg (Term.map (pathReindex (Cartesian.reindex (family Γ) (projection (interval Γ)))
    (term a) (term b) σ)) h).trans
    ((equivalencePathSection_reindex_pair σ s).trans hu)

/-- Global sections of the reverse native map recover the actual chosen Glue path. -/
theorem equivToPath_beta (f : liftedDecode a ⟶ liftedDecode b)
    (E : HomotopyEquivalence f) :
    Term.map (equivToPath a b)
      (EquivalenceFamilies.equivSections (liftedDecode a) (liftedDecode b) ⟨f,E⟩) =
      ua a b f E := by
  let S := EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) (𝟙 Γ)
  have hd : S.symm (EquivalenceFamilies.equivSections (liftedDecode a) (liftedDecode b) ⟨f,E⟩) =
      ⟨f,E⟩ :=
    (congrArg S.symm (EquivalenceFamilies.equivReindexSections_id
      (liftedDecode a) (liftedDecode b) f E).symm).trans (S.symm_apply_apply ⟨f,E⟩)
  exact (equivToPath_reindex_beta (𝟙 Γ)
    (EquivalenceFamilies.equivSections (liftedDecode a) (liftedDecode b) ⟨f,E⟩)).trans
    (ua_congr_data a b _ f _ E hd)

end SquareKit.Cubical.Cartesian.SmallUniverse.NativeUnivalence

namespace SquareKit.Cubical.Cartesian.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u
variable {Γ : Context.{u+1}} {a b : Γ ⟶ smallFamilyCodes.{u}}
/-- Global sections of the forward native map retain the chosen contractions. -/
theorem pathToEquiv_beta (p : Term (paths a b)) :
    EquivalenceFamilies.equivSections (liftedDecode a) (liftedDecode b)
      ⟨pathToMap p, pathToEquivalence p⟩ = Term.map (pathToEquiv a b) p := by
  exact (EquivalenceFamilies.equivReindexSections_id (liftedDecode a) (liftedDecode b)
    (pathToMap p) (pathToEquivalence p)).symm.trans
    (pathToEquiv_reindex_beta (𝟙 Γ) p).symm


end SquareKit.Cubical.Cartesian.SmallUniverse.NativeUnivalence

namespace SquareKit.Cubical.Cartesian.IntervalTransport
open CategoryTheory
universe u
variable {Γ : Context.{u}} {A : Family (total (interval Γ))} {B : Family Γ}
def mapLineComparison (F : Filling A) (hF : F.Lawful)
    (f : A ⟶ reindex B (projection (interval Γ)))
    (a : Term (reindex A (endpointSub Γ false))) :
    Term (homogeneousPath B
      (Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements f) a)
      (Term.map (Functor.whiskerLeft (endpointSub Γ true).mapElements f)
        (Term.map (map F (endpoint Γ false) (endpoint Γ true)) a))) :=
  pathLam (Term.map f (line F (endpoint Γ false) (𝟙 Γ) a))
    (congrArg (Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements f))
      (line_source F hF (endpoint Γ false) (𝟙 Γ) a))
    (congrArg (Term.map (Functor.whiskerLeft (endpointSub Γ true).mapElements f))
      (map_section F hF (endpoint Γ false) (endpoint Γ true) a).symm)
def mapLineComparisonTo {C : Family Γ} (F : Filling A) (hF : F.Lawful)
    (h₀ : reindex A (endpointSub Γ false) = C)
    (h₁ : reindex A (endpointSub Γ true) = B)
    (g : A ⟶ reindex B (projection (interval Γ))) (f : C ⟶ B)
    (g₀ : Functor.whiskerLeft (endpointSub Γ false).mapElements g = eqToHom h₀ ≫ f)
    (g₁ : Functor.whiskerLeft (endpointSub Γ true).mapElements g = eqToHom h₁)
    (x : Term C) :
    Term (homogeneousPath B (Term.map f x)
      (Term.map (mapTo F (endpoint Γ false) (endpoint Γ true) C B h₀ h₁) x)) := by
  let z := Term.map (eqToHom h₀.symm) x
  let q := mapLineComparison F hF g z
  refine pathLam (pathApp q) ((pathApp_zero q).trans ?_) ((pathApp_one q).trans ?_)
  · change Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements g) z = Term.map f x
    rw [g₀]
    exact congrArg (Term.map f) (Term.map_iso_roundtrip (eqToIso h₀).symm x)
  · change Term.map (Functor.whiskerLeft (endpointSub Γ true).mapElements g)
      (Term.map (map F (endpoint Γ false) (endpoint Γ true)) z) = _
    rw [g₁]
    rfl
end SquareKit.Cubical.Cartesian.IntervalTransport

namespace SquareKit.Cubical.Cartesian.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u
variable {Γ : Context.{u+1}} {a b : Γ ⟶ smallFamilyCodes.{u}}
theorem decode_zero (p : Term (paths a b)) :
    reindex (liftedDecode (codeOfPath p)) (endpointSub Γ false) = liftedDecode a :=
  congrArg liftedDecode (codeOfPath_zero p)
theorem decode_one (p : Term (paths a b)) :
    reindex (liftedDecode (codeOfPath p)) (endpointSub Γ true) = liftedDecode b :=
  congrArg liftedDecode (codeOfPath_one p)
theorem pathToMap_eq (p : Term (paths a b)) :
    pathToMap p = IntervalTransport.mapTo (NativeDecode.filling (codeOfPath p))
      (endpoint Γ false) (endpoint Γ true) (liftedDecode a) (liftedDecode b)
      (decode_zero p) (decode_one p) := by
  unfold pathToMap
  rw [UniversalTransport.selectedMap_eq]
  generalize h₀ : decode_zero p = hzero
  generalize h₁ : decode_one p = hone
  unfold HomotopyEquivalence.castMap IntervalTransport.mapTo
  rfl
end SquareKit.Cubical.Cartesian.SmallUniverse.NativeUnivalence

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
open EquivalenceFamilies
universe u

namespace EquivalencePaths

namespace PiContractibility
variable {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
  (c : Contractible B) (F : Filling B) (hF : F.Lawful)
  {Δ : Context.{u}} (σ : Δ ⟶ Γ) (φ : Subcontext Δ)
  (s : PartialSection (reindex (pi A B) σ) φ)

noncomputable def body : Term (reindex B (liftSub A σ)) :=
  (c.reindex (liftSub A σ)).extend (F.reindex (liftSub A σ))
    ((s.map (piReindex A B σ)).app)

noncomputable def extend : Term (reindex (pi A B) σ) :=
  Term.map (piReindexIso A B σ).inv (lam (body c F σ φ s))

include hF in
theorem boundary (x : Δ.Elements) (hx : φ.Holds x) :
    (extend c F σ φ s).val x = s.val x hx := by
  let i := piReindexIso A B σ
  let p := s.map i.hom
  have h : (lam (body c F σ φ s)).val x = p.val x hx := by
    apply PiElement.ext
    intro y g v
    have hb := (c.reindex (liftSub A σ)).extend_boundary (F.reindex (liftSub A σ))
      (hF.reindex _) p.app (extendObj (reindex A σ) y v) (φ.natural g hx)
    have hp := congrArg (fun k => k.val (𝟙 y) v) (p.natural g hx)
    refine hb.trans ?_
    change (p.val x hx).val (g ≫ 𝟙 y) v =
      (p.val y (φ.natural g hx)).val (𝟙 y) v at hp
    change (p.val y (φ.natural g hx)).val (𝟙 y) v = (p.val x hx).val g v
    simpa only [Category.comp_id] using hp.symm
  exact (congrArg (i.inv.app x) h).trans
    (congrArg (fun m => m.app x (s.val x hx)) i.hom_inv_id)

end PiContractibility

private noncomputable def piContractible {Γ : Context.{u}} {A : Family Γ}
    {B : Family (total A)} (c : Contractible B) (F : Filling B) (hF : F.Lawful) :
    Contractible (pi A B) :=
  Contractible.ofExtensions (PiContractibility.extend c F)
    (PiContractibility.boundary c F hF)

/-- An inhabited substituted equivalence-witness family is contractible with
its full native contraction data, even when the original map is not invertible globally. -/
noncomputable def substitutedWitnessContractible {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (σ : Δ ⟶ Γ) (w : Term (reindex (isEquiv f) σ)) :
    Contractible (reindex (isEquiv f) σ) := by
  let C := Homotopy.fiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)
  let τ := liftSub B σ
  let i := genericFiberReindexIso f σ
  let c := ((isEquivReindexSections f σ).symm w).fibers.map i.symm
  let K := (genericFiberFilling f F hF G hG).reindex τ
  have hK : K.Lawful := (genericFiberFilling_lawful f F hF G hG).reindex τ
  let q := contrReindexIso C τ
  let d := (contrContractible c K hK).map q.symm
  let L := (contrFilling (genericFiberFilling f F hF G hG)
    (genericFiberFilling_lawful f F hF G hG)).reindex τ
  have hL : L.Lawful := (contrFilling_lawful _ (genericFiberFilling_lawful f F hF G hG)).reindex τ
  exact (piContractible d L hL).map (piReindexIso B (contr C) σ).symm

variable {Γ : Context.{u}} {A B : Family Γ} (f g : A ⟶ B)
  (H : Term (homogeneousPath (reindex B (projection A))
    (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
    (Term.map (Functor.whiskerLeft (projection A).mapElements g) (generic A))))

/-- Abstract the supplied pointwise native homotopy over all generalized arguments. -/
def mapLine : Term (reindex (maps A B) (projection (interval Γ))) where
  val x := {
    val := fun {y} k a => (pathApp H).val
      (extendObj (interval (total A)) (extendObj A y a) ((interval Γ).map k x.val.2))
    naturality := by
      intro y z k l a
      let q := extendHom A l a
      have hr : (interval (total A)).map q ((interval Γ).map k x.val.2) =
          (interval Γ).map (k ≫ l) x.val.2 :=
        (congrArg (fun m => m x.val.2) ((interval Γ).map_comp k l)).symm
      exact (pathApp H).property (extendAlong (interval (total A)) q hr) }
  property {x y} h := by
    apply PiElement.ext
    intro z k a
    let l := (projection (interval Γ)).mapElements.map h
    have hr : (interval Γ).map (l ≫ k) x.val.2 = (interval Γ).map k y.val.2 :=
      (congrArg (fun m => m x.val.2) ((interval Γ).map_comp l k)).trans
        (congrArg ((interval Γ).map k) ((generic (interval Γ)).property h))
    exact congrArg (fun r : (interval Γ).obj z =>
      (show B.obj z from (pathApp H).val
        (extendObj (interval (total A)) (extendObj A z a) r))) hr

theorem mapLine_zero : Term.reindex (mapLine f g H) (endpointSub Γ false) = encodeMap f := by
  apply Term.ext
  intro x
  apply PiElement.ext
  intro y k a
  have hr := (endpoint Γ false).property k
  exact (congrArg (fun r : (interval Γ).obj y =>
    (show B.obj y from (pathApp H).val
      (extendObj (interval (total A)) (extendObj A y a) r))) hr).trans
    (congrArg (fun t => t.val (extendObj A y a)) (pathApp_zero H))

theorem mapLine_one : Term.reindex (mapLine f g H) (endpointSub Γ true) = encodeMap g := by
  apply Term.ext
  intro x
  apply PiElement.ext
  intro y k a
  have hr := (endpoint Γ true).property k
  exact (congrArg (fun r : (interval Γ).obj y =>
    (show B.obj y from (pathApp H).val
      (extendObj (interval (total A)) (extendObj A y a) r))) hr).trans
    (congrArg (fun t => t.val (extendObj A y a)) (pathApp_one H))

/-- Function extensionality here is a construction from the supplied native homotopy. -/
def mapPath : Term (homogeneousPath (maps A B) (encodeMap f) (encodeMap g)) :=
  pathLam (mapLine f g H) (mapLine_zero f g H) (mapLine_one f g H)


abbrev witnessFamily := isEquiv (universalMap A B)
def witnessSub : total (interval Γ) ⟶ total (maps A B) :=
  pair (projection (interval Γ)) (mapLine f g H)
abbrev witnessLine := reindex (witnessFamily (A := A) (B := B)) (witnessSub f g H)

theorem witnessSub_zero : endpointSub Γ false ≫ witnessSub f g H = pair (A := maps A B) (𝟙 Γ) (encodeMap f) := by
  ext I γ
  exact congrArg (fun a => (⟨γ,a⟩ : (total (maps A B)).obj I))
    (congrArg (fun t => t.val (Γ.elementsMk I γ)) (mapLine_zero f g H))

theorem witnessSub_one : endpointSub Γ true ≫ witnessSub f g H = pair (A := maps A B) (𝟙 Γ) (encodeMap g) := by
  ext I γ
  exact congrArg (fun a => (⟨γ,a⟩ : (total (maps A B)).obj I))
    (congrArg (fun t => t.val (Γ.elementsMk I γ)) (mapLine_one f g H))

def startIso : reindex (witnessLine f g H) (endpointSub Γ false) ≅
    reindex (witnessFamily (A := A) (B := B)) (pair (𝟙 Γ) (encodeMap f)) :=
  eqToIso (congrArg (reindex (witnessFamily (A := A) (B := B))) (witnessSub_zero f g H))

def finishIso : reindex (witnessLine f g H) (endpointSub Γ true) ≅
    reindex (witnessFamily (A := A) (B := B)) (pair (𝟙 Γ) (encodeMap g)) :=
  eqToIso (congrArg (reindex (witnessFamily (A := A) (B := B))) (witnessSub_one f g H))

noncomputable def chosenWitness (e : HomotopyEquivalence f) :
    Term (reindex (witnessFamily (A := A) (B := B)) (pair (𝟙 Γ) (encodeMap f))) :=
  sigmaSnd (B := witnessFamily (A := A) (B := B)) ((equivSections A B) ⟨f,e⟩)

variable (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
  (Ef : HomotopyEquivalence f) (Eg : HomotopyEquivalence g)

noncomputable def universalFilling : Filling (witnessFamily (A := A) (B := B)) :=
  isEquivFilling (universalMap A B) (F.reindex (projection (maps A B))) (hF.reindex _)
    (G.reindex (projection (maps A B))) (hG.reindex _)

theorem universalFilling_lawful : (universalFilling F hF G hG).Lawful :=
  isEquivFilling_lawful _ _ (hF.reindex _) _ (hG.reindex _)

noncomputable def lineFilling : Filling (witnessLine f g H) :=
  (universalFilling F hF G hG).reindex (witnessSub f g H)

theorem lineFilling_lawful : (lineFilling f g H F hF G hG).Lawful :=
  (universalFilling_lawful F hF G hG).reindex _

noncomputable def initialWitness : Term (reindex (witnessLine f g H) (endpointSub Γ false)) :=
  Term.map (startIso f g H).inv (chosenWitness f Ef)

noncomputable def finalWitness : Term (reindex (witnessLine f g H) (endpointSub Γ true)) :=
  Term.map (finishIso f g H).inv (chosenWitness g Eg)

noncomputable def witnessContraction : Contractible (witnessLine f g H) := by
  let L := lineFilling f g H F hF G hG
  let w : Term (witnessLine f g H) :=
    IntervalTransport.line L (endpoint Γ false) (𝟙 Γ) (initialWitness f g H Ef)
  exact substitutedWitnessContractible (universalMap A B)
    (F.reindex (projection (maps A B))) (hF.reindex _)
    (G.reindex (projection (maps A B))) (hG.reindex _)
    (witnessSub f g H) w

noncomputable def witnessSection : Term (witnessLine f g H) :=
  (witnessContraction f g H F hF G hG Ef).extend (lineFilling f g H F hF G hG)
    (endpointBoundary (witnessLine f g H) (initialWitness f g H Ef) (finalWitness f g H Eg))

theorem witnessSection_zero :
    Term.reindex (witnessSection f g H F hF G hG Ef Eg) (endpointSub Γ false) = initialWitness f g H Ef := by
  apply Term.ext
  intro x
  let y := (endpointSub Γ false).mapElements.obj x
  let p := endpointBoundary (witnessLine f g H) (initialWitness f g H Ef) (finalWitness f g H Eg)
  have hb := (witnessContraction f g H F hF G hG Ef).extend_boundary
    (lineFilling f g H F hF G hG) (lineFilling_lawful f g H F hF G hG) p y (Or.inl rfl)
  exact hb.trans (eq_of_heq ((heq_of_eq (endpointBoundary_zero _ _ _ y _ rfl)).trans
    (endpointSection_val _ false _ y rfl)))

theorem witnessSection_one :
    Term.reindex (witnessSection f g H F hF G hG Ef Eg) (endpointSub Γ true) = finalWitness f g H Eg := by
  apply Term.ext
  intro x
  let y := (endpointSub Γ true).mapElements.obj x
  let p := endpointBoundary (witnessLine f g H) (initialWitness f g H Ef) (finalWitness f g H Eg)
  have hb := (witnessContraction f g H F hF G hG Ef).extend_boundary
    (lineFilling f g H F hF G hG) (lineFilling_lawful f g H F hF G hG) p y (Or.inr rfl)
  exact hb.trans (eq_of_heq ((heq_of_eq (endpointBoundary_one _ _ _ y _ rfl)).trans
    (endpointSection_val _ true _ y rfl)))

noncomputable def equivalenceLine : Term (reindex (equiv A B) (projection (interval Γ))) :=
  sigmaIntro (B := reindex (witnessFamily (A := A) (B := B)) (liftSub (maps A B) (projection (interval Γ))))
    (mapLine f g H) (witnessSection f g H F hF G hG Ef Eg)

private theorem eqToIso_inv_value_heq {Ξ : Context.{u}} {C D : Family Ξ}
    (h : C = D) (t : Term D) (x : Ξ.Elements) :
    HEq ((Term.map (eqToIso h).inv t).val x) (t.val x) := by
  cases h
  rfl

theorem equivalenceLine_zero :
    Term.reindex (equivalenceLine f g H F hF G hG Ef Eg) (endpointSub Γ false) =
      (equivSections A B) ⟨f,Ef⟩ := by
  apply Term.ext
  intro x
  apply Sigma.ext (congrArg (fun t => t.val x) (mapLine_zero f g H))
  exact (heq_of_eq (congrArg (fun t => t.val x)
    (witnessSection_zero f g H F hF G hG Ef Eg))).trans
    (eqToIso_inv_value_heq _ (chosenWitness f Ef) x)

theorem equivalenceLine_one :
    Term.reindex (equivalenceLine f g H F hF G hG Ef Eg) (endpointSub Γ true) =
      (equivSections A B) ⟨g,Eg⟩ := by
  apply Term.ext
  intro x
  apply Sigma.ext (congrArg (fun t => t.val x) (mapLine_one f g H))
  exact (heq_of_eq (congrArg (fun t => t.val x)
    (witnessSection_one f g H F hF G hG Ef Eg))).trans
    (eqToIso_inv_value_heq _ (chosenWitness g Eg) x)

/-- A native map homotopy yields a path between the full supplied equivalences,
including their selected generic-fiber contractions. -/
noncomputable def ofHomotopy : Term (homogeneousPath (equiv A B)
    ((equivSections A B) ⟨f,Ef⟩) ((equivSections A B) ⟨g,Eg⟩)) :=
  pathLam (equivalenceLine f g H F hF G hG Ef Eg)
    (equivalenceLine_zero f g H F hF G hG Ef Eg)
    (equivalenceLine_one f g H F hF G hG Ef Eg)


/-- Changing only the chosen equivalence witness gives a native path, without
identifying the two witnesses by equality. -/
noncomputable def sameMapWitnessPath (Eg : HomotopyEquivalence f) : Term (homogeneousPath (equiv A B)
    ((equivSections A B) ⟨f,Ef⟩) ((equivSections A B) ⟨f,Eg⟩)) :=
  ofHomotopy f f (homogeneousRefl
    (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A)))
    F hF G hG Ef Eg


end EquivalencePaths
end SquareKit.Cubical.Cartesian

namespace SquareKit.Cubical.Cartesian.NativeUa
open CategoryTheory
universe u
variable {Γ : Context.{u}} (A B : LocalFamily Γ) (f : A.family ⟶ B.family) (E : HomotopyEquivalence f)
noncomputable def unglueLine : (line A B f E).family ⟶ (ambient B).family :=
  (Glue.Datum.mk (face (Γ := Γ)) (ambient B).family (boundary A B).family (boundaryMap A B f)).smallUnglue

theorem unglueLine_zero :
    Functor.whiskerLeft (endpointSub Γ false).mapElements (unglueLine A B f E) =
      eqToHom (congrArg LocalFamily.family (line_zero A B f E)) ≫ f := by
  let D := Glue.Datum.mk (face (Γ := Γ)) (ambient B).family (boundary A B).family (boundaryMap A B f)
  have h := congrArg (Functor.whiskerLeft (CodeSystem.boundaryZero Γ).mapElements) D.smallUnglue_full
  have hb := congrArg (Functor.whiskerLeft (CodeSystem.endpointFace Γ false).mapElements)
    (CodeSystem.Maps.glue_left (leftMap A B f) (rightMap A B) (maps_compatible A B f))
  change Functor.whiskerLeft (endpointSub Γ false).mapElements (unglueLine A B f E) =
    Functor.whiskerLeft (CodeSystem.boundaryZero Γ).mapElements (eqToHom D.smallFamily_full) ≫
      Functor.whiskerLeft (CodeSystem.boundaryZero Γ).mapElements (boundaryMap A B f) at h
  rw [h]
  erw [hb]
  change _ ≫ (Functor.whiskerLeft (CodeSystem.endpointFace Γ false).mapElements
    (eqToHom (congrArg LocalFamily.family (boundary_left A B))) ≫ f) = _
  rw [whisker_eqToHom, whisker_eqToHom]
  erw [← Category.assoc, eqToHom_trans]
  rfl

theorem unglueLine_one :
    Functor.whiskerLeft (endpointSub Γ true).mapElements (unglueLine A B f E) =
      eqToHom (congrArg LocalFamily.family (line_one A B f E)) := by
  let D := Glue.Datum.mk (face (Γ := Γ)) (ambient B).family (boundary A B).family (boundaryMap A B f)
  have h := congrArg (Functor.whiskerLeft (CodeSystem.boundaryOne Γ).mapElements) D.smallUnglue_full
  have hb := congrArg (Functor.whiskerLeft (CodeSystem.endpointFace Γ true).mapElements)
    (CodeSystem.Maps.glue_right (leftMap A B f) (rightMap A B) (maps_compatible A B f))
  change Functor.whiskerLeft (endpointSub Γ true).mapElements (unglueLine A B f E) =
    Functor.whiskerLeft (CodeSystem.boundaryOne Γ).mapElements (eqToHom D.smallFamily_full) ≫
      Functor.whiskerLeft (CodeSystem.boundaryOne Γ).mapElements (boundaryMap A B f) at h
  rw [h]
  erw [hb]
  change _ ≫ Functor.whiskerLeft (CodeSystem.endpointFace Γ true).mapElements
    (eqToHom (congrArg LocalFamily.family (boundary_right A B))) = _
  rw [whisker_eqToHom, whisker_eqToHom]
  erw [eqToHom_trans]
  rfl

theorem smallUnglue_source_congr {Ξ : Context.{u}} (φ : Subcontext Ξ)
    (C : Family Ξ) (T T' : Family (restrictContext φ)) (h : T = T')
    (f : T ⟶ reindex C (restrictInclusion φ))
    (f' : T' ⟶ reindex C (restrictInclusion φ))
    (hf : eqToHom h.symm ≫ f = f') :
    HEq (Glue.Datum.mk φ C T f).smallUnglue (Glue.Datum.mk φ C T' f').smallUnglue := by
  subst T'
  simp only [eqToHom_refl, Category.id_comp] at hf
  subst f'; rfl

theorem family_eqToHom_comp_heq {Ξ : Context.{u}} {X Y Z : Family Ξ} (h : X = Y) (f : Y ⟶ Z) :
    HEq (eqToHom h ≫ f) f := by
  subst Y
  rfl

theorem unglueLine_reindex {Δ : Context.{u}} (σ : Δ ⟶ Γ)
    (f : A.family ⟶ B.family) (E : HomotopyEquivalence f) :
    HEq (Functor.whiskerLeft (intervalSub σ).mapElements (unglueLine A B f E))
      (unglueLine (A.reindex σ) (B.reindex σ)
        (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)) := by
  let D := Glue.Datum.mk (face (Γ := Γ)) (ambient B).family (boundary A B).family (boundaryMap A B f)
  have h := D.smallUnglue_substitution (intervalSub σ)
  have hh : HEq (Functor.whiskerLeft (intervalSub σ).mapElements D.smallUnglue)
      (D.reindex (intervalSub σ)).smallUnglue := by
    rw [h]
    exact family_eqToHom_comp_heq _ _
  exact hh.trans (smallUnglue_source_congr (face (Γ := Δ)) (ambient (B.reindex σ)).family _ _
    (congrArg LocalFamily.family (boundary_reindex A B σ)) _ _ (boundaryMap_reindex A B σ f))
end SquareKit.Cubical.Cartesian.NativeUa

namespace SquareKit.Cubical.Cartesian.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u
variable {Ξ : Context.{u+1}} (a b : Ξ ⟶ smallFamilyCodes.{u})
  (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)

noncomputable def chartUnglue {Γ : Context.{u}} (σ : raisedContext Γ ⟶ Ξ) :
    Cartesian.decode (chartCode a b f E σ) ⟶
      reindex (Cartesian.decode (σ ≫ b)) (projection (interval Γ)) :=
  eqToHom (LocalFamily.decode_code_eq _) ≫
    NativeUa.unglueLine (decodedLocalFamily (σ ≫ a)) (decodedLocalFamily (σ ≫ b))
      (lowerChartMap a b σ f) (lowerChartEquivalence a b σ f E)


private theorem unglueLine_congr {Γ : Context.{u}} (A B A' B' : LocalFamily Γ)
    (hA : A = A') (hB : B = B') (g : A.family ⟶ B.family) (g' : A'.family ⟶ B'.family)
    (hg : HEq g g') (H : HomotopyEquivalence g) (H' : HomotopyEquivalence g') (hH : HEq H H') :
    HEq (NativeUa.unglueLine A B g H) (NativeUa.unglueLine A' B' g' H') := by
  subst A'; subst B'
  have hg' := eq_of_heq hg; subst g'
  have hH' := eq_of_heq hH; subst H'; rfl

private theorem whiskerLeft_eqToHom_comp_heq {Γ Δ : Context.{u}} {A A' B : Family Γ}
    (h : A = A') (g : A' ⟶ B) (σ : Δ ⟶ Γ) :
    HEq (Functor.whiskerLeft σ.mapElements (eqToHom h ≫ g))
      (Functor.whiskerLeft σ.mapElements g) := by
  cases h; rfl
private theorem family_eqToHom_comp_heq {Γ : Context.{u}} {A A' B : Family Γ}
    (h : A = A') (g : A' ⟶ B) : HEq (eqToHom h ≫ g) g := by
  cases h; rfl

theorem chartUnglue_reindex {Γ Δ : Context.{u}} (σ : raisedContext Γ ⟶ Ξ) (τ : Δ ⟶ Γ) :
    HEq (Functor.whiskerLeft (intervalSub τ).mapElements (chartUnglue a b f E σ))
      (chartUnglue a b f E (raisedSub τ ≫ σ)) := by
  have hn := NativeUa.unglueLine_reindex (decodedLocalFamily (σ ≫ a))
    (decodedLocalFamily (σ ≫ b)) τ (lowerChartMap a b σ f)
    (lowerChartEquivalence a b σ f E)
  have hc := unglueLine_congr _ _ _ _
    (decodedLocalFamily_reindex (σ ≫ a) τ).symm
    (decodedLocalFamily_reindex (σ ≫ b) τ).symm
    (Functor.whiskerLeft τ.mapElements (lowerChartMap a b σ f))
    (lowerChartMap a b (raisedSub τ ≫ σ) f) HEq.rfl
    ((lowerChartEquivalence a b σ f E).reindex τ)
    (lowerChartEquivalence a b (raisedSub τ ≫ σ) f E)
    (heq_of_eq (lowerChartEquivalence_reindex a b σ f E τ).symm)
  exact (whiskerLeft_eqToHom_comp_heq _ _ _).trans (hn.trans (hc.trans (family_eqToHom_comp_heq _ _).symm))

theorem chartUnglue_zero {Γ : Context.{u}} (σ : raisedContext Γ ⟶ Ξ) :
    Functor.whiskerLeft (endpointSub Γ false).mapElements (chartUnglue a b f E σ) =
      eqToHom (congrArg Cartesian.decode (chartCode_zero a b f E σ)) ≫ lowerChartMap a b σ f := by
  change Functor.whiskerLeft (endpointSub Γ false).mapElements (eqToHom _ ≫ _) = _
  change Functor.whiskerLeft (endpointSub Γ false).mapElements (eqToHom _) ≫
    Functor.whiskerLeft (endpointSub Γ false).mapElements (NativeUa.unglueLine _ _ _ _) = _
  erw [NativeUa.whisker_eqToHom, NativeUa.unglueLine_zero, ← Category.assoc, eqToHom_trans]
  rfl

theorem chartUnglue_one {Γ : Context.{u}} (σ : raisedContext Γ ⟶ Ξ) :
    Functor.whiskerLeft (endpointSub Γ true).mapElements (chartUnglue a b f E σ) =
      eqToHom (congrArg Cartesian.decode (chartCode_one a b f E σ)) := by
  change Functor.whiskerLeft (endpointSub Γ true).mapElements (eqToHom _) ≫
    Functor.whiskerLeft (endpointSub Γ true).mapElements (NativeUa.unglueLine _ _ _ _) = _
  erw [NativeUa.whisker_eqToHom, NativeUa.unglueLine_one, eqToHom_trans]
  rfl

def smallPoint (x : (total (interval Ξ)).Elements) :
    (total (interval (representable.{u} x.obj.unop))).Elements :=
  (total (interval (representable.{u} x.obj.unop))).elementsMk x.obj (chartPoint x).down

def chartBasePoint (x : (total (interval Ξ)).Elements) : Ξ.Elements :=
  (chart (intervalBase x)).mapElements.obj
    ((raisedElements (representable.{u} x.obj.unop)).obj
      ((projection (interval (representable.{u} x.obj.unop))).mapElements.obj (smallPoint x)))

theorem chartBasePoint_eq (x : (total (interval Ξ)).Elements) :
    chartBasePoint x = intervalBase x := by
  change Ξ.elementsMk x.obj _ = Ξ.elementsMk x.obj _
  exact congrArg (Ξ.elementsMk x.obj) (chart_generic (intervalBase x))

noncomputable def unglueValue (x : (total (interval Ξ)).Elements)
    (z : (liftedDecode (code (coherentLine a b f E))).obj x) :
    (liftedDecode b).obj (intervalBase x) :=
  cast (congrArg (liftedDecode b).obj (chartBasePoint_eq x))
    ⟨(chartUnglue a b f E (chart (intervalBase x))).app (smallPoint x) z.down⟩

private theorem map_input_heq {Γ : Context.{u}} (A : Family Γ)
    {x x' y y' : Γ.Elements} (hx : x = x') (hy : y = y')
    (g : x ⟶ y) (g' : x' ⟶ y') (hg : HEq g.hom g'.hom)
    (z : A.obj x) (z' : A.obj x') (hz : HEq z z') :
    HEq (A.map g z) (A.map g' z') := by
  cases hx
  cases hy
  have h : g = g' := Functor.Elements.Hom.ext (eq_of_heq hg)
  cases h
  cases hz
  rfl

private theorem nat_app_heq {Γ : Context.{u}} {A A' B B' : Family Γ}
    (hA : A = A') (hB : B = B') (g : A ⟶ B) (g' : A' ⟶ B')
    (hg : HEq g g') (x : Γ.Elements) (z : A.obj x) (z' : A'.obj x)
    (hz : HEq z z') : HEq (g.app x z) (g'.app x z') := by
  cases hA
  cases hB
  cases hg
  cases hz
  rfl

def smallSub {x y : (total (interval Ξ)).Elements} (g : x ⟶ y) :=
  intervalSub (representableMap.{u} g.hom.unop)

def smallArrow {x y : (total (interval Ξ)).Elements} (g : x ⟶ y) :
    smallPoint x ⟶ (smallSub g).mapElements.obj (smallPoint y) :=
  Functor.Elements.homMk g.hom (congrArg ULift.down (chartPoint_natural g))

private theorem input_restrict_heq {x y : (total (interval Ξ)).Elements} (g : x ⟶ y)
    (z : (liftedDecode (code (coherentLine a b f E))).obj x) :
    HEq ((Cartesian.decode (chartCode a b f E (chart (intervalBase x)))).map (smallArrow g) z.down)
      (((liftedDecode (code (coherentLine a b f E))).map g z).down) :=
  (cast_heq _ _).trans (cast_heq _ _).symm


private theorem chartUnglue_congr {Γ : Context.{u}} (σ τ : raisedContext Γ ⟶ Ξ)
    (h : σ = τ) : HEq (chartUnglue a b f E σ) (chartUnglue a b f E τ) := by
  cases h
  rfl

private theorem output_restrict_heq {x y : (total (interval Ξ)).Elements} (g : x ⟶ y)
    (z : (liftedDecode (code (coherentLine a b f E))).obj x) :
    HEq ((reindex (Cartesian.decode (chart (intervalBase x) ≫ b))
      (projection (interval (representable.{u} x.obj.unop)))).map (smallArrow g)
        ((chartUnglue a b f E (chart (intervalBase x))).app (smallPoint x) z.down))
      ((chartUnglue a b f E (chart (intervalBase y))).app (smallPoint y)
        (((liftedDecode (code (coherentLine a b f E))).map g z).down)) := by
  let σ := chart (intervalBase x)
  let τ := representableMap.{u} g.hom.unop
  have hs : raisedSub τ ≫ σ = chart (intervalBase y) :=
    chart_restrict ((projection (interval Ξ)).mapElements.map g)
  have hA := congrArg Cartesian.decode
    ((chartCode_reindex a b f E σ τ).trans (congrArg (chartCode a b f E) hs))
  have hB := congrArg (fun t : raisedContext (representable.{u} y.obj.unop) ⟶ Ξ =>
    reindex (Cartesian.decode (t ≫ b)) (projection (interval (representable.{u} y.obj.unop)))) hs
  have hG := (chartUnglue_reindex a b f E σ τ).trans
    (chartUnglue_congr a b f E _ _ hs)
  have hn := ConcreteCategory.congr_hom
    ((chartUnglue a b f E σ).naturality (smallArrow g)) z.down
  exact (heq_of_eq hn.symm).trans
    (nat_app_heq hA hB _ _ hG (smallPoint y) _ _ (input_restrict_heq a b f E g z))

def chartBaseArrow {x y : (total (interval Ξ)).Elements} (g : x ⟶ y) :=
  (chart (intervalBase x)).mapElements.map
    ((raisedElements (representable.{u} x.obj.unop)).map
      ((projection (interval (representable.{u} x.obj.unop))).mapElements.map (smallArrow g)))

theorem chartBaseArrow_target {x y : (total (interval Ξ)).Elements} (g : x ⟶ y) :
    (chart (intervalBase x)).mapElements.obj
      ((raisedElements (representable.{u} x.obj.unop)).obj
        ((projection (interval (representable.{u} x.obj.unop))).mapElements.obj
          ((smallSub g).mapElements.obj (smallPoint y)))) = intervalBase y := by
  change Ξ.elementsMk y.obj _ = Ξ.elementsMk y.obj _
  apply congrArg (Ξ.elementsMk y.obj)
  exact (chartBaseArrow g).map_val.symm.trans
    ((congrArg (Ξ.map g.hom) (chart_generic (intervalBase x))).trans
      ((projection (interval Ξ)).mapElements.map g).map_val)

private theorem ulift_heq {A B : Type u} {z : A} {w : B} (h : HEq z w) :
    HEq (ULift.up.{u+1} z) (ULift.up.{u+1} w) := by
  cases h
  rfl

theorem unglueValue_natural {x y : (total (interval Ξ)).Elements} (g : x ⟶ y)
    (z : (liftedDecode (code (coherentLine a b f E))).obj x) :
    (liftedDecode b).map ((projection (interval Ξ)).mapElements.map g)
      (unglueValue a b f E x z) =
    unglueValue a b f E y ((liftedDecode (code (coherentLine a b f E))).map g z) := by
  apply eq_of_heq
  have hm := map_input_heq (liftedDecode b) (chartBasePoint_eq x)
    (chartBaseArrow_target g) (chartBaseArrow g)
    ((projection (interval Ξ)).mapElements.map g) HEq.rfl
    (show (liftedDecode b).obj (chartBasePoint x) from
      ⟨(chartUnglue a b f E (chart (intervalBase x))).app (smallPoint x) z.down⟩)
    (unglueValue a b f E x z) (cast_heq _ _).symm
  exact hm.symm.trans ((ulift_heq (output_restrict_heq a b f E g z)).trans
    (cast_heq _ _).symm)

noncomputable def unglue : liftedDecode (code (coherentLine a b f E)) ⟶
    reindex (liftedDecode b) (projection (interval Ξ)) where
  app x := TypeCat.ofHom (unglueValue a b f E x)
  naturality x y g := by
    apply ConcreteCategory.hom_ext
    intro z
    exact (unglueValue_natural a b f E g z).symm


private theorem point_app_heq {Γ : Context.{u}} {A B : Family Γ} (g : A ⟶ B)
    {x y : Γ.Elements} (h : x = y) (z : A.obj x) (w : A.obj y) (hz : HEq z w) :
    HEq (g.app x z) (g.app y w) := by
  cases h
  cases hz
  rfl


theorem unglue_zero :
    Functor.whiskerLeft (endpointSub Ξ false).mapElements (unglue a b f E) =
      eqToHom (decode_zero (ua a b f E)) ≫ f := by
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro z
  apply eq_of_heq
  let sx := (representable.{u} x.obj.unop).elementsMk x.obj ⟨𝟙 x.obj.unop⟩
  let σ := chart x
  let h₀ := congrArg Cartesian.decode
    (chartCode_zero a b f E σ)
  let w := (eqToHom h₀).app sx z.down
  have h := congrArg (fun k => k.app sx z.down)
    (chartUnglue_zero a b f E σ)
  have hw : HEq (ULift.up.{u+1} w) ((eqToHom (decode_zero (ua a b f E))).app x z) :=
    (ulift_heq (family_eqToIso_hom_heq h₀ sx z.down)).trans
      (family_eqToIso_hom_heq (decode_zero (ua a b f E)) x z).symm
  exact (cast_heq _ _).trans ((heq_of_eq (congrArg ULift.up h)).trans
    (point_app_heq f (chartBasePoint_eq ((endpointSub Ξ false).mapElements.obj x)) _ _ hw))

theorem unglue_one :
    Functor.whiskerLeft (endpointSub Ξ true).mapElements (unglue a b f E) =
      eqToHom (decode_one (ua a b f E)) := by
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro z
  apply eq_of_heq
  let sx := (representable.{u} x.obj.unop).elementsMk x.obj ⟨𝟙 x.obj.unop⟩
  let σ := chart x
  let h₁ := congrArg Cartesian.decode
    (chartCode_one a b f E σ)
  have h := congrArg (fun k => k.app sx z.down)
    (chartUnglue_one a b f E σ)
  exact (cast_heq _ _).trans ((heq_of_eq (congrArg ULift.up h)).trans
    ((ulift_heq (family_eqToIso_hom_heq h₁ sx z.down)).trans
      (family_eqToIso_hom_heq (decode_one (ua a b f E)) x z).symm))

/-- Comparison uses the actual universal decoding filler, retaining its chosen transport. -/
noncomputable def uaComparison (x : Term (liftedDecode a)) :
    Term (homogeneousPath (liftedDecode b) (Term.map f x)
      (Term.map (pathToMap (ua a b f E)) x)) := by
  let q := IntervalTransport.mapLineComparisonTo
    (NativeDecode.filling (codeOfPath (ua a b f E)))
    (NativeDecode.filling_lawful (codeOfPath (ua a b f E)))
    (decode_zero (ua a b f E)) (decode_one (ua a b f E))
    (unglue a b f E) f (unglue_zero a b f E) (unglue_one a b f E) x
  exact pathLam (pathApp q) (pathApp_zero q)
    ((pathApp_one q).trans (congrArg (fun g => Term.map g x) (pathToMap_eq (ua a b f E)).symm))

/-- Pointwise native comparison at the generic source element. -/
noncomputable def uaMapHomotopy : Term (homogeneousPath
    (reindex (liftedDecode b) (projection (liftedDecode a)))
    (Term.map (Functor.whiskerLeft (projection (liftedDecode a)).mapElements f)
      (generic (liftedDecode a)))
    (Term.map (Functor.whiskerLeft (projection (liftedDecode a)).mapElements
      (pathToMap (ua a b f E))) (generic (liftedDecode a)))) := by
  let σ := projection (liftedDecode a)
  let q := uaComparison (σ ≫ a) (σ ≫ b)
    (Functor.whiskerLeft σ.mapElements f) (E.reindex σ) (generic (liftedDecode a))
  have hm := (pathToMap_reindex (ua a b f E) σ).trans
    (congrArg pathToMap (ua_reindex a b f E σ))
  exact pathLam (pathApp q) (pathApp_zero q)
    ((pathApp_one q).trans (congrArg (fun k => Term.map k (generic (liftedDecode a))) hm.symm))

/-- The native comparison retains both complete chosen endpoint equivalences. -/
noncomputable def uaEquivalenceComparison : Term (homogeneousPath (equivalences a b)
    ((EquivalenceFamilies.equivSections (liftedDecode a) (liftedDecode b)) ⟨f,E⟩)
    ((EquivalenceFamilies.equivSections (liftedDecode a) (liftedDecode b))
      ⟨pathToMap (ua a b f E),pathToEquivalence (ua a b f E)⟩)) :=
  EquivalencePaths.ofHomotopy f (pathToMap (ua a b f E)) (uaMapHomotopy a b f E)
    (NativeDecode.filling a) (NativeDecode.filling_lawful a)
    (NativeDecode.filling b) (NativeDecode.filling_lawful b)
    E (pathToEquivalence (ua a b f E))


end SquareKit.Cubical.Cartesian.SmallUniverse.NativeUnivalence

namespace SquareKit.Cubical.Cartesian.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u
variable {Γ Δ : Context.{u+1}} (a b : Γ ⟶ smallFamilyCodes.{u})
private theorem pathToEquivalence_record_congr {a b : Δ ⟶ smallFamilyCodes.{u}}
    {p q : Term (paths a b)} (h : p = q) :
    (⟨pathToMap p,pathToEquivalence p⟩ : Σ f, HomotopyEquivalence f) =
      ⟨pathToMap q,pathToEquivalence q⟩ := by
  cases h
  rfl

/-- The supplied equivalence comparison, transported back through the faithful
native family isomorphism, retains the complete original section. -/
noncomputable def encodedRoundtripAt (σ : Δ ⟶ Γ)
    (s : Term (reindex (equivalences a b) σ)) :
    let S := EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) σ
    let e := S.symm s
    let q := ua (σ ≫ a) (σ ≫ b) e.1 e.2
    Term (homogeneousPath (reindex (equivalences a b) σ)
      (S ⟨pathToMap q,pathToEquivalence q⟩) s) := by
  let S := EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) σ
  let J := EquivalenceFamilies.equivReindexIso (liftedDecode a) (liftedDecode b) σ
  let e := S.symm s
  let q := ua (σ ≫ a) (σ ≫ b) e.1 e.2
  let c := homogeneousReverse
    (EquivalenceFamilies.equivFilling (NativeDecode.filling (σ ≫ a))
      (NativeDecode.filling_lawful _) (NativeDecode.filling (σ ≫ b))
      (NativeDecode.filling_lawful _))
    (EquivalenceFamilies.equivFilling_lawful _ (NativeDecode.filling_lawful _) _
      (NativeDecode.filling_lawful _))
    (uaEquivalenceComparison (σ ≫ a) (σ ≫ b) e.1 e.2)
  let r := homogeneousPathMap J.inv c
  exact pathLam (pathApp r)
    ((pathApp_zero r).trans
      (EquivalenceFamilies.equivReindexIso_inv_encode (liftedDecode a) (liftedDecode b) σ
        (pathToMap q) (pathToEquivalence q)))
    ((pathApp_one r).trans
      ((EquivalenceFamilies.equivReindexIso_inv_encode (liftedDecode a) (liftedDecode b) σ
        e.1 e.2).trans (S.apply_symm_apply s)))

/-- The actual native reverse map is a right inverse through a path retaining the
complete selected internal equivalence, in every substituted context. -/
noncomputable def rightInverseAt (σ : Δ ⟶ Γ)
    (s : Term (reindex (equivalences a b) σ)) :
    Term (homogeneousPath (reindex (equivalences a b) σ)
      (Term.map (Functor.whiskerLeft σ.mapElements (pathToEquiv a b))
        (Term.map (Functor.whiskerLeft σ.mapElements (equivToPath a b)) s)) s) := by
  let S := EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) σ
  let e := S.symm s
  let p := Term.map (Functor.whiskerLeft σ.mapElements (equivToPath a b)) s
  let t := Term.map (Functor.whiskerLeft σ.mapElements (pathToEquiv a b)) p
  let q := ua (σ ≫ a) (σ ≫ b) e.1 e.2
  have hp := equivToPath_reindex_beta (a := a) (b := b) σ s
  have ht : t = S ⟨pathToMap q,pathToEquivalence q⟩ :=
    (pathToEquiv_reindex_beta (a := a) (b := b) σ p).trans
      (congrArg S (pathToEquivalence_record_congr hp))
  let r := encodedRoundtripAt a b σ s
  exact pathLam (pathApp r) ((pathApp_zero r).trans ht.symm) (pathApp_one r)

noncomputable def rightInverseHomotopy :=
  rightInverseAt a b (projection (equivalences a b)) (generic (equivalences a b))

end SquareKit.Cubical.Cartesian.SmallUniverse.NativeUnivalence
