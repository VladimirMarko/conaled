import SquareKit.Internal.Cubical.UnivalenceTransport
import SquareKit.Internal.Cubical.EquivalenceIsoTransport

/-! A Glue line between arbitrary native families, without universe codes. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.NativeEquivalenceLine
open CategoryTheory
universe u
variable {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B)

abbrev face := intervalFace Γ false
abbrev faceProjection := restrictInclusion (face (Γ := Γ)) ≫ projection (interval Γ)
abbrev ambient := reindex B (projection (interval Γ))
abbrev boundary := reindex A (faceProjection (Γ := Γ))
def boundaryMap : boundary (A := A) ⟶ reindex (ambient (B := B)) (restrictInclusion face) :=
  Functor.whiskerLeft (faceProjection (Γ := Γ)).mapElements f
abbrev line := Glue.family face (ambient (B := B)) (boundary (A := A)) (boundaryMap f)

def start : reindex (line f) (endpointSub Γ false) ≅ A :=
  Functor.isoWhiskerLeft (CodeSystem.endpointFace Γ false).mapElements
    (Glue.fullFaceIso face (ambient (B := B)) (boundary (A := A)) (boundaryMap f))

def unglue : line f ⟶ ambient (B := B) :=
  Glue.unglue face (ambient (B := B)) (boundary (A := A)) (boundaryMap f)

private theorem absent {x y : (total (interval Γ)).Elements}
    (hx : (intervalFace Γ true).full x) (k : x ⟶ y) (hy : (face (Γ := Γ)).full y) : False :=
  intervalFace_disjoint y hy ((intervalFace Γ true).full_natural k hx)

private def finishCompatibleInv : B ⟶
    reindex (Glue.compatibleFamily face (ambient (B := B)) (boundary (A := A)) (boundaryMap f))
      (endpointSub Γ true) where
  app x := TypeCat.ofHom (fun b =>
    { ambient := b
      face := fun k hy => (absent ((Cofibration.full_endpoint _ true _).mpr rfl) k hy).elim
      naturality := by
        intro y z k l hy
        exact (absent ((Cofibration.full_endpoint _ true _).mpr rfl) k hy).elim
      compatible := by
        intro y k hy
        exact (absent ((Cofibration.full_endpoint _ true _).mpr rfl) k hy).elim })
  naturality x y k := by
    apply ConcreteCategory.hom_ext
    intro b
    apply Glue.CompatibleElement.ext
    · rfl
    · intro z h hz
      exact (absent ((Cofibration.full_endpoint _ true _).mpr rfl) h hz).elim

def finishCompatible :
    reindex (Glue.compatibleFamily face (ambient (B := B)) (boundary (A := A)) (boundaryMap f))
      (endpointSub Γ true) ≅ B where
  hom := Functor.whiskerLeft (endpointSub Γ true).mapElements
    (Glue.compatibleUnglue face (ambient (B := B)) (boundary (A := A)) (boundaryMap f))
  inv := finishCompatibleInv f
  hom_inv_id := by
    ext x z
    apply Glue.CompatibleElement.ext
    · rfl
    · intro y k hy
      exact (absent ((Cofibration.full_endpoint _ true _).mpr rfl) k hy).elim
  inv_hom_id := rfl

def finish : reindex (line f) (endpointSub Γ true) ≅ B :=
  Functor.isoWhiskerLeft (endpointSub Γ true).mapElements
    (Glue.familyIso face (ambient (B := B)) (boundary (A := A)) (boundaryMap f)) ≪≫ finishCompatible f

theorem unglue_start : Functor.whiskerLeft (endpointSub Γ false).mapElements (unglue f) =
    (start f).hom ≫ f := by
  ext x z
  have h := ((Glue.fiberEquiv face (ambient (B := B)) (boundary (A := A)) (boundaryMap f)
    ((endpointSub Γ false).mapElements.obj x)) z).compatible (𝟙 _) ((Cofibration.full_endpoint _ false _).mpr rfl) |>.symm
  change B.map (𝟙 x) _ = _ at h
  rw [B.map_id] at h
  exact h

theorem unglue_finish : Functor.whiskerLeft (endpointSub Γ true).mapElements (unglue f) =
    (finish f).hom := rfl

abbrev reverseLine := reindex (line f) (reverseInterval Γ)
def reverseStart : reindex (reverseLine f) (endpointSub Γ false) ≅ B :=
  eqToIso (congrArg (reindex (line f)) (reverseInterval_endpoint Γ false)) ≪≫ finish f
def reverseFinish : reindex (reverseLine f) (endpointSub Γ true) ≅ A :=
  eqToIso (congrArg (reindex (line f)) (reverseInterval_endpoint Γ true)) ≪≫ start f

private theorem whisker_eq {Δ Ξ : Context.{u}} {C D : Family Ξ}
    {σ τ : Δ ⟶ Ξ} (h : σ = τ) (g : C ⟶ D) :
    Functor.whiskerLeft σ.mapElements g =
      eqToHom (congrArg (reindex C) h) ≫ Functor.whiskerLeft τ.mapElements g ≫
        eqToHom (congrArg (reindex D) h.symm) := by
  cases h
  rfl

def reverseUnglue : reverseLine f ⟶ reindex B (projection (interval Γ)) :=
  Functor.whiskerLeft (reverseInterval Γ).mapElements (unglue f)

theorem reverseUnglue_start :
    Functor.whiskerLeft (endpointSub Γ false).mapElements (reverseUnglue f) =
      (reverseStart f).hom := by
  have h := whisker_eq (reverseInterval_endpoint Γ false) (unglue f)
  change _ = eqToHom _ ≫ (Functor.whiskerLeft (endpointSub Γ true).mapElements (unglue f)) ≫ eqToHom _ at h
  rw [unglue_finish] at h
  change _ = (reverseStart f).hom ≫ eqToHom (show B = B from rfl) at h
  simp only [eqToHom_refl, Category.comp_id] at h
  exact h

theorem reverseUnglue_finish :
    Functor.whiskerLeft (endpointSub Γ true).mapElements (reverseUnglue f) =
      (reverseFinish f).hom ≫ f := by
  have h := whisker_eq (reverseInterval_endpoint Γ true) (unglue f)
  change _ = eqToHom _ ≫ (Functor.whiskerLeft (endpointSub Γ false).mapElements (unglue f)) ≫ eqToHom _ at h
  rw [unglue_start] at h
  change _ = ((reverseFinish f).hom ≫ f) ≫ eqToHom (show B = B from rfl) at h
  simp only [eqToHom_refl, Category.comp_id] at h
  exact h

variable (E : HomotopyEquivalence f) (FA : Filling A) (hFA : FA.Lawful)
  (FB : Filling B) (hFB : FB.Lawful)
noncomputable def filling : Filling (line f) :=
  Glue.filling face (ambient (B := B)) (boundary (A := A)) (boundaryMap f)
    (E.reindex faceProjection) (FA.reindex faceProjection) (hFA.reindex _)
    (FB.reindex (projection (interval Γ))) (hFB.reindex _)
theorem filling_lawful : (filling f E FA hFA FB hFB).Lawful :=
  Glue.filling_lawful _ _ _ _ _ _ _ _ _

noncomputable def reverseFilling : Filling (reverseLine f) :=
  (filling f E FA hFA FB hFB).reindex (reverseInterval Γ)
theorem reverseFilling_lawful : (reverseFilling f E FA hFA FB hFB).Lawful :=
  (filling_lawful f E FA hFA FB hFB).reindex _

noncomputable def auxiliary : B ⟶ A :=
  (reverseStart f).inv ≫ IntervalTransport.map (reverseFilling f E FA hFA FB hFB) ≫
    (reverseFinish f).hom

noncomputable def auxiliaryEquivalence : HomotopyEquivalence (auxiliary f E FA hFA FB hFB) :=
  (IntervalTransport.equivalence (reverseFilling f E FA hFA FB hFB)
    (reverseFilling_lawful f E FA hFA FB hFB)).conjugateIso
      (reverseStart f).symm (reverseFinish f)

noncomputable def auxiliaryRight : Term (homogeneousPath (reindex B (projection B))
    (Term.map (Functor.whiskerLeft (projection B).mapElements f)
      (Term.map (Functor.whiskerLeft (projection B).mapElements
        (auxiliary f E FA hFA FB hFB)) (generic B)))
    (generic B)) := by
  let F := reverseFilling f E FA hFA FB hFB
  have hF := reverseFilling_lawful f E FA hFA FB hFB
  let σ := projection B
  let a := Term.map (Functor.whiskerLeft σ.mapElements (reverseStart f).inv) (generic B)
  let q := IntervalTransport.mapLineComparison (B := reindex B σ)
    (F.reindex (liftSub (interval Γ) σ)) (hF.reindex _)
    (Functor.whiskerLeft (liftSub (interval Γ) σ).mapElements (reverseUnglue f)) a
  apply homogeneousReverse
  refine pathLam (pathApp q) ((pathApp_zero q).trans ?_) ((pathApp_one q).trans ?_)
  · change Term.map (Functor.whiskerLeft σ.mapElements
      (Functor.whiskerLeft (endpointSub Γ false).mapElements (reverseUnglue f))) a = _
    rw [reverseUnglue_start]
    exact Term.map_iso_roundtrip (Functor.isoWhiskerLeft σ.mapElements (reverseStart f)).symm (generic B)
  · change Term.map (Functor.whiskerLeft σ.mapElements
      (Functor.whiskerLeft (endpointSub Γ true).mapElements (reverseUnglue f)))
        (Term.map (IntervalTransport.map (F.reindex (liftSub (interval Γ) σ))) a) = _
    rw [reverseUnglue_finish, IntervalTransport.map_reindex F hF σ]
    rfl

end SquareKit.Cubical.Presheaf.NativeEquivalenceLine
