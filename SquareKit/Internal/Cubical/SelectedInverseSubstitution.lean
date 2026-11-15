import SquareKit.Internal.Cubical.SelectedInverse
import SquareKit.Internal.Cubical.SelectedEquivalenceIsoSubstitution
import SquareKit.Internal.Cubical.SelectedIntervalTransportSubstitution
import SquareKit.Internal.Cubical.SelectedMapHomotopySubstitution

/-! Substitution of the selected inverse, native recovery paths, and complete
chosen equivalence witness. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.HomotopyEquivalence
open CategoryTheory
universe u
variable {Γ Δ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}

private def firstMap {Ω : Context.{u}} (C : Family Ω) (D : Family (total C)) : sigma C D ⟶ C where
  app _ := TypeCat.ofHom Sigma.fst
  naturality _ _ _ := rfl

/-- The map after substitution selects exactly the original fiber center. -/
theorem selectedInverse_reindex (E : HomotopyEquivalence f) (σ : Δ ⟶ Γ) :
    (E.reindex σ).selectedInverse = Functor.whiskerLeft σ.mapElements E.selectedInverse := by
  ext x b
  rfl

/-- Comparison is of the entire native path, through the standard path
presentation isomorphism, rather than just of its endpoints. -/
theorem selectedRight_reindex (E : HomotopyEquivalence f) (σ : Δ ⟶ Γ) :
    HEq (E.reindex σ).selectedRight
      (homogeneousReindex E.selectedRight (liftSub B σ)) := by
  apply pathTerm_hext
  apply Term.ext
  intro x
  rfl

private theorem pathTo_transport_reindex {Ω Ξ : Context.{u}} {C D : Family Ω}
    (c : HomotopyContractible C) (i : C ≅ D) (τ : Ξ ⟶ Ω) (z : Term (Presheaf.reindex D τ)) :
    pathApp (((c.transport i).reindex τ).pathTo z) =
      Term.map (Functor.whiskerLeft (projection (interval Ξ) ≫ τ).mapElements i.hom)
        (pathApp ((c.reindex τ).pathTo
          (Term.map (Functor.whiskerLeft τ.mapElements i.inv) z))) := by
  apply Term.ext
  intro x
  rfl

/-- The projected contraction giving left recovery is stable under substitution. -/
theorem selectedLeft_reindex (E : HomotopyEquivalence f) (σ : Δ ⟶ Γ) :
    HEq (E.reindex σ).selectedLeft
      (homogeneousReindex E.selectedLeft (liftSub A σ)) := by
  let τ := pair (projection (Presheaf.reindex A σ))
    (Term.map (Functor.whiskerLeft (projection (Presheaf.reindex A σ)).mapElements
      (Functor.whiskerLeft σ.mapElements f)) (generic (Presheaf.reindex A σ)))
  let z := genericFiberIntro f (τ ≫ liftSub B σ) (generic (Presheaf.reindex A σ))
    (homogeneousRefl (Term.map (Functor.whiskerLeft (projection (Presheaf.reindex A σ)).mapElements
      (Functor.whiskerLeft σ.mapElements f)) (generic (Presheaf.reindex A σ))))
  let i := Functor.isoWhiskerLeft τ.mapElements (genericFiberReindexIso f σ)
  have hz := genericFiberIntro_input_reindex f σ τ (generic (Presheaf.reindex A σ))
    (homogeneousRefl (Term.map (Functor.whiskerLeft (projection (Presheaf.reindex A σ)).mapElements
      (Functor.whiskerLeft σ.mapElements f)) (generic (Presheaf.reindex A σ))))
  have hi : Term.map i.inv (genericFiberIntro (Functor.whiskerLeft σ.mapElements f) τ
      (generic (Presheaf.reindex A σ))
      (homogeneousRefl (Term.map (Functor.whiskerLeft (projection (Presheaf.reindex A σ)).mapElements
        (Functor.whiskerLeft σ.mapElements f)) (generic (Presheaf.reindex A σ))))) = z :=
    (congrArg (Term.map i.inv) hz.symm).trans (Term.map_iso_roundtrip i z)
  let z' := genericFiberIntro (Functor.whiskerLeft σ.mapElements f) τ
    (generic (Presheaf.reindex A σ))
    (homogeneousRefl (Term.map (Functor.whiskerLeft (projection (Presheaf.reindex A σ)).mapElements
      (Functor.whiskerLeft σ.mapElements f)) (generic (Presheaf.reindex A σ))))
  let m := Functor.whiskerLeft (projection (interval (total (Presheaf.reindex A σ)))).mapElements
    (firstMap (Presheaf.reindex (Presheaf.reindex A σ) (τ ≫ projection (Presheaf.reindex B σ)))
      (Presheaf.reindex (genericFiberPathFamily (Functor.whiskerLeft σ.mapElements f))
        (liftSub (Presheaf.reindex (Presheaf.reindex A σ) (projection (Presheaf.reindex B σ))) τ)))
  have hp := congrArg (Term.map m) (pathTo_transport_reindex
    (E.fibers.reindex (liftSub B σ)) (genericFiberReindexIso f σ) τ z')
  have hq := congrArg (fun t => Term.map m
    (Term.map (Functor.whiskerLeft (projection (interval (total (Presheaf.reindex A σ))) ≫ τ).mapElements
      (genericFiberReindexIso f σ).hom) (pathApp (((E.fibers.reindex (liftSub B σ)).reindex τ).pathTo t)))) hi
  let τ₀ := pair (projection A)
    (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
  have hz₀ := genericFiberIntro_reindex f τ₀ (generic A)
    (homogeneousRefl (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A)))
    (liftSub A σ)
  have hr := congrArg (fun t => Term.map m
    (Term.map (Functor.whiskerLeft (projection (interval (total (Presheaf.reindex A σ))) ≫ τ).mapElements
      (genericFiberReindexIso f σ).hom) (pathApp (((E.fibers.reindex (liftSub B σ)).reindex τ).pathTo t)))) hz₀
  apply pathTerm_hext
  exact hp.trans (hq.trans (hr.trans (by apply Term.ext; intro x; rfl)))

private theorem comparisonPoint_reindex (g : B ⟶ A)
    (h : Term (homogeneousPath (Presheaf.reindex B (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements f)
        (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B))) (generic B)))
    (σ : Δ ⟶ Γ) :
    Term.map (genericFiberReindexIso f σ).inv
      (genericFiberIntro (Functor.whiskerLeft σ.mapElements f) (𝟙 (total (Presheaf.reindex B σ)))
        (Term.map (Functor.whiskerLeft (projection (Presheaf.reindex B σ)).mapElements
          (Functor.whiskerLeft σ.mapElements g)) (generic (Presheaf.reindex B σ)))
        (homogeneousReindex h (liftSub B σ))) =
    (genericFiberIntro f (𝟙 (total B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B)) h).reindex (liftSub B σ) := by
  let τ := liftSub B σ
  let a := Term.map (Functor.whiskerLeft (projection (Presheaf.reindex B σ)).mapElements
    (Functor.whiskerLeft σ.mapElements g)) (generic (Presheaf.reindex B σ))
  let q := homogeneousReindex h τ
  let z := genericFiberIntro f τ a q
  let z' := genericFiberIntro (Functor.whiskerLeft σ.mapElements f) (𝟙 _) a q
  let i := genericFiberReindexIso f σ
  have hz := genericFiberIntro_input_reindex f σ (𝟙 _) a q
  have hi : Term.map i.inv z' = z :=
    (congrArg (Term.map i.inv) hz.symm).trans (Term.map_iso_roundtrip i z)
  have hz₀ := genericFiberIntro_reindex f (𝟙 (total B))
    (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B)) h τ
  exact hi.trans hz₀

private theorem projected_pathTo_transport {Ω : Context.{u}} {C D X : Family Ω}
    (c : HomotopyContractible C) (i : C ≅ D) (m : D ⟶ X) (n : C ⟶ X)
    (hm : i.hom ≫ m = n) (z : Term C) :
    pathApp (homogeneousPathMap m ((c.transport i).pathTo (Term.map i.hom z))) =
    pathApp (homogeneousPathMap n (c.pathTo z)) := by
  subst n
  have hp := congrArg (Term.map (Functor.whiskerLeft (projection (interval Ω)).mapElements m))
    (pathTo_transport_reindex c i (𝟙 Ω) (Term.map i.hom z))
  have hz := Term.map_iso_roundtrip i z
  have hq := congrArg (fun t => Term.map
    (Functor.whiskerLeft (projection (interval Ω)).mapElements (i.hom ≫ m))
    (pathApp (c.pathTo t))) hz
  exact hp.trans hq

theorem selectedComparison_reindex (E : HomotopyEquivalence f) (g : B ⟶ A)
    (h : Term (homogeneousPath (Presheaf.reindex B (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements f)
        (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B))) (generic B)))
    (σ : Δ ⟶ Γ) :
    HEq ((E.reindex σ).selectedComparison (Functor.whiskerLeft σ.mapElements g)
      (homogeneousReindex h (liftSub B σ)))
      (homogeneousReindex (E.selectedComparison g h) (liftSub B σ)) := by
  let τ := liftSub B σ
  let i := genericFiberReindexIso f σ
  let z := (genericFiberIntro f (𝟙 (total B))
    (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B)) h).reindex τ
  let z' := genericFiberIntro (Functor.whiskerLeft σ.mapElements f) (𝟙 (total (Presheaf.reindex B σ)))
    (Term.map (Functor.whiskerLeft (projection (Presheaf.reindex B σ)).mapElements
      (Functor.whiskerLeft σ.mapElements g)) (generic (Presheaf.reindex B σ)))
    (homogeneousReindex h τ)
  let m := firstMap (Presheaf.reindex (Presheaf.reindex A σ) (projection (Presheaf.reindex B σ)))
    (genericFiberPathFamily (Functor.whiskerLeft σ.mapElements f))
  let n := Functor.whiskerLeft τ.mapElements
    (firstMap (Presheaf.reindex A (projection B)) (genericFiberPathFamily f))
  have hz : z' = Term.map i.hom z := (Term.map_iso_roundtrip i.symm z').symm.trans
    (congrArg (Term.map i.hom) (comparisonPoint_reindex g h σ))
  have hp := congrArg (fun t => pathApp (homogeneousPathMap m ((E.reindex σ).fibers.pathTo t))) hz
  have hq := projected_pathTo_transport (E.fibers.reindex τ) i m n rfl z
  have hr : pathApp (homogeneousPathMap m ((E.reindex σ).fibers.pathTo z')) =
      (pathApp (homogeneousPathMap
        (firstMap (Presheaf.reindex A (projection B)) (genericFiberPathFamily f))
        (E.fibers.pathTo (genericFiberIntro f (𝟙 (total B))
          (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B)) h)))).reindex
            (liftSub (interval (total B)) τ) :=
    hp.trans (hq.trans (by apply Term.ext; intro x; rfl))
  apply pathTerm_hext
  exact congrArg (fun t => t.reindex (reverseInterval (total (Presheaf.reindex B σ)))) hr

end SquareKit.Cubical.Presheaf.HomotopyEquivalence

namespace SquareKit.Cubical.Presheaf.NativeEquivalenceLine
open CategoryTheory
universe u
variable {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (σ : Δ ⟶ Γ)

/-- The native Glue line uses the standard Glue substitution presentation. -/
noncomputable def lineReindexIso : reindex (line f) (liftSub (interval Γ) σ) ≅
    line (Functor.whiskerLeft σ.mapElements f) :=
  Glue.reindexIso face (ambient (B := B)) (boundary (A := A)) (boundaryMap f)
    (liftSub (interval Γ) σ)

theorem filling_reindex (E : HomotopyEquivalence f)
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    ((filling f E FA hFA FB hFB).reindex (liftSub (interval Γ) σ)).transport
      (lineReindexIso f σ) =
    filling (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)
      (FA.reindex σ) (hFA.reindex _) (FB.reindex σ) (hFB.reindex _) := by
  have h := Glue.filling_reindex_iso face (ambient (B := B)) (boundary (A := A)) (boundaryMap f)
    (liftSub (interval Γ) σ) (E.reindex faceProjection) (FA.reindex faceProjection) (hFA.reindex _)
    (FB.reindex (projection (interval Γ))) (hFB.reindex _)
  have hE : (E.reindex faceProjection).reindex (restrictSubstitution face (liftSub (interval Γ) σ)) =
      (E.reindex σ).reindex faceProjection :=
    (E.reindex_comp faceProjection (restrictSubstitution face (liftSub (interval Γ) σ))).trans
      (E.reindex_comp σ faceProjection).symm
  have hk := congrArg (fun e => Glue.filling (face (Γ := Δ)) (ambient (B := reindex B σ))
    (boundary (A := reindex A σ)) (boundaryMap (Functor.whiskerLeft σ.mapElements f)) e
    ((FA.reindex σ).reindex faceProjection) ((hFA.reindex σ).reindex _)
    ((FB.reindex σ).reindex (projection (interval Δ))) ((hFB.reindex σ).reindex _)) hE
  exact h.trans hk

theorem lineReindexIso_start :
    Functor.whiskerLeft (endpointSub Δ false).mapElements (lineReindexIso f σ).hom ≫
      (start (Functor.whiskerLeft σ.mapElements f)).hom =
    Functor.whiskerLeft σ.mapElements (start f).hom := by
  ext x z
  let y := (endpointSub Δ false).mapElements.obj x
  let c := (Glue.compatibleReindexIso face (ambient (B := B)) (boundary (A := A))
    (boundaryMap f) (liftSub (interval Γ) σ)).hom.app y
    ((Glue.familyIso face (ambient (B := B)) (boundary (A := A)) (boundaryMap f)).hom.app
      ((liftSub (interval Γ) σ).mapElements.obj y) z)
  exact congrArg (fun w => w.face (𝟙 y) ((Cofibration.full_endpoint _ false _).mpr rfl))
    ((Glue.fiberEquiv face (ambient (B := reindex B σ)) (boundary (A := reindex A σ))
      (boundaryMap (Functor.whiskerLeft σ.mapElements f)) y).apply_symm_apply c)

theorem lineReindexIso_finish :
    Functor.whiskerLeft (endpointSub Δ true).mapElements (lineReindexIso f σ).hom ≫
      (finish (Functor.whiskerLeft σ.mapElements f)).hom =
    Functor.whiskerLeft σ.mapElements (finish f).hom := by
  ext x z
  let y := (endpointSub Δ true).mapElements.obj x
  let c := (Glue.compatibleReindexIso face (ambient (B := B)) (boundary (A := A))
    (boundaryMap f) (liftSub (interval Γ) σ)).hom.app y
    ((Glue.familyIso face (ambient (B := B)) (boundary (A := A)) (boundaryMap f)).hom.app
      ((liftSub (interval Γ) σ).mapElements.obj y) z)
  exact congrArg Glue.CompatibleElement.ambient
    ((Glue.fiberEquiv face (ambient (B := reindex B σ)) (boundary (A := reindex A σ))
      (boundaryMap (Functor.whiskerLeft σ.mapElements f)) y).apply_symm_apply c)

end SquareKit.Cubical.Presheaf.NativeEquivalenceLine

namespace SquareKit.Cubical.Presheaf.NativeEquivalenceLine
open CategoryTheory
universe u
variable {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (σ : Δ ⟶ Γ)

noncomputable def reverseLineReindexIso : reindex (reverseLine f) (liftSub (interval Γ) σ) ≅
    reverseLine (Functor.whiskerLeft σ.mapElements f) :=
  Functor.isoWhiskerLeft (reverseInterval Δ).mapElements (lineReindexIso f σ)

theorem reverseFilling_reindex (E : HomotopyEquivalence f)
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    ((reverseFilling f E FA hFA FB hFB).reindex (liftSub (interval Γ) σ)).transport
      (reverseLineReindexIso f σ) =
    reverseFilling (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)
      (FA.reindex σ) (hFA.reindex _) (FB.reindex σ) (hFB.reindex _) :=
  congrArg (fun G => G.reindex (reverseInterval Δ)) (filling_reindex f σ E FA hFA FB hFB)

private theorem whisker_eq_square {Ω Ξ : Context.{u}} {C D : Family Ξ}
    {τ ν : Ω ⟶ Ξ} (h : τ = ν) (g : C ⟶ D) :
    Functor.whiskerLeft τ.mapElements g ≫ eqToHom (congrArg (reindex D) h) =
      eqToHom (congrArg (reindex C) h) ≫ Functor.whiskerLeft ν.mapElements g := by
  cases h
  rfl

private theorem whisker_eqToHom {Ω Ξ : Context.{u}} {C D : Family Ξ}
    (h : C = D) (τ : Ω ⟶ Ξ) :
    Functor.whiskerLeft τ.mapElements (eqToHom h) = eqToHom (congrArg (fun K => reindex K τ) h) := by
  cases h
  rfl

private theorem reverse_endpoint_square
    (C : Family (total (interval Γ))) (D : Family (total (interval Δ)))
    (g : reindex C (liftSub (interval Γ) σ) ⟶ D) (v : Bool) :
    Functor.whiskerLeft (endpointSub Δ v ≫ reverseInterval Δ).mapElements g ≫
      eqToHom (congrArg (reindex D) (reverseInterval_endpoint Δ v)) =
    Functor.whiskerLeft σ.mapElements (eqToHom (congrArg (reindex C) (reverseInterval_endpoint Γ v))) ≫
      Functor.whiskerLeft (endpointSub Δ (!v)).mapElements g := by
  have h := whisker_eq_square (reverseInterval_endpoint Δ v) g
  have he := whisker_eqToHom (congrArg (reindex C) (reverseInterval_endpoint Γ v)) σ
  exact h.trans (congrArg (fun k => k ≫ Functor.whiskerLeft (endpointSub Δ (!v)).mapElements g) he.symm)

theorem reverseLineReindexIso_start :
    Functor.whiskerLeft (endpointSub Δ false).mapElements (reverseLineReindexIso f σ).hom ≫
      (reverseStart (Functor.whiskerLeft σ.mapElements f)).hom =
    Functor.whiskerLeft σ.mapElements (reverseStart f).hom := by
  have h := reverse_endpoint_square σ (line f) (line (Functor.whiskerLeft σ.mapElements f))
    (lineReindexIso f σ).hom false
  have hc := congrArg (fun k => k ≫ (finish (Functor.whiskerLeft σ.mapElements f)).hom) h
  exact hc.trans (congrArg (fun k =>
    Functor.whiskerLeft σ.mapElements
      (eqToHom (congrArg (reindex (line f)) (reverseInterval_endpoint Γ false))) ≫ k)
    (lineReindexIso_finish f σ))

theorem reverseLineReindexIso_finish :
    Functor.whiskerLeft (endpointSub Δ true).mapElements (reverseLineReindexIso f σ).hom ≫
      (reverseFinish (Functor.whiskerLeft σ.mapElements f)).hom =
    Functor.whiskerLeft σ.mapElements (reverseFinish f).hom := by
  have h := reverse_endpoint_square σ (line f) (line (Functor.whiskerLeft σ.mapElements f))
    (lineReindexIso f σ).hom true
  have hc := congrArg (fun k => k ≫ (start (Functor.whiskerLeft σ.mapElements f)).hom) h
  exact hc.trans (congrArg (fun k =>
    Functor.whiskerLeft σ.mapElements
      (eqToHom (congrArg (reindex (line f)) (reverseInterval_endpoint Γ true))) ≫ k)
    (lineReindexIso_start f σ))

end SquareKit.Cubical.Presheaf.NativeEquivalenceLine

namespace SquareKit.Cubical.Presheaf.SelectedMapHomotopySubstitution
open CategoryTheory
universe u
private theorem interval_fixed_presentations_reindex {Γ Δ : Context.{u}}
    {A : Family (total (interval Γ))} {B : Family (total (interval Δ))}
    {X Y : Family Γ}
    (F : Filling A) (hF : F.Lawful) (K : Filling B) (hK : K.Lawful) (σ : Δ ⟶ Γ)
    (S : Presheaf.reindex A (endpointSub Γ false) ≅ X)
    (T : Presheaf.reindex A (endpointSub Γ true) ≅ Y)
    (S' : Presheaf.reindex B (endpointSub Δ false) ≅ Presheaf.reindex X σ)
    (T' : Presheaf.reindex B (endpointSub Δ true) ≅ Presheaf.reindex Y σ)
    (e : Presheaf.reindex A (liftSub (interval Γ) σ) ≅ B)
    (hf : (F.reindex (liftSub (interval Γ) σ)).transport e = K)
    (hs : SelectedIntervalTransport.atEndpoint e false ≪≫ S' = Functor.isoWhiskerLeft σ.mapElements S)
    (ht : SelectedIntervalTransport.atEndpoint e true ≪≫ T' = Functor.isoWhiskerLeft σ.mapElements T) :
    HEq (((IntervalTransport.equivalence F hF).conjugateIso S.symm T).reindex σ)
      ((IntervalTransport.equivalence K hK).conjugateIso S'.symm T') := by
  let e₀ := SelectedIntervalTransport.atEndpoint e false
  let e₁ := SelectedIntervalTransport.atEndpoint e true
  let D := IntervalTransport.equivalence F hF
  have hsi : Functor.isoWhiskerLeft σ.mapElements S.symm = S'.symm ≪≫ e₀.symm :=
    congrArg Iso.symm hs.symm
  have he := (interval_equivalence_reindex_transport F hF σ e).trans
    (interval_equivalence_congr hf (Filling.transport_lawful e _ (hF.reindex _)) hK)
  have hm : e₀.inv ≫ Functor.whiskerLeft σ.mapElements (IntervalTransport.map F) ≫ e₁.hom =
      IntervalTransport.map K :=
    (congrArg (fun k => e₀.inv ≫ k ≫ e₁.hom) (IntervalTransport.map_reindex F hF σ).symm).trans
      ((SelectedIntervalTransport.conjugate_map e _ (hF.reindex _)).trans
        (congrArg IntervalTransport.map hf))
  exact (heq_of_eq (D.conjugateIso_reindex S.symm T σ)).trans
    ((conjugate_presentations_heq (D.reindex σ) hsi ht.symm).trans
      ((heq_of_eq ((D.reindex σ).conjugateIso_trans e₀.symm e₁ S'.symm T')).symm.trans
        (conjugate_heq hm he S'.symm T')))

end SquareKit.Cubical.Presheaf.SelectedMapHomotopySubstitution

namespace SquareKit.Cubical.Presheaf.NativeEquivalenceLine
open CategoryTheory
open SelectedMapHomotopySubstitution
universe u
variable {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (σ : Δ ⟶ Γ)
  (E : HomotopyEquivalence f) (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful)

theorem auxiliaryEquivalence_reindex :
    HEq ((auxiliaryEquivalence f E FA hFA FB hFB).reindex σ)
      (auxiliaryEquivalence (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)
        (FA.reindex σ) (hFA.reindex _) (FB.reindex σ) (hFB.reindex _)) := by
  let F := reverseFilling f E FA hFA FB hFB
  let hF := reverseFilling_lawful f E FA hFA FB hFB
  let K := reverseFilling (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)
    (FA.reindex σ) (hFA.reindex _) (FB.reindex σ) (hFB.reindex _)
  let hK := reverseFilling_lawful (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)
    (FA.reindex σ) (hFA.reindex _) (FB.reindex σ) (hFB.reindex _)
  let e := reverseLineReindexIso f σ
  exact interval_fixed_presentations_reindex F hF K hK σ
    (reverseStart f) (reverseFinish f)
    (reverseStart (Functor.whiskerLeft σ.mapElements f))
    (reverseFinish (Functor.whiskerLeft σ.mapElements f)) e
    (reverseFilling_reindex f σ E FA hFA FB hFB)
    (Iso.ext (reverseLineReindexIso_start f σ))
    (Iso.ext (reverseLineReindexIso_finish f σ))

set_option backward.isDefEq.respectTransparency false in
theorem auxiliary_reindex :
    Functor.whiskerLeft σ.mapElements (auxiliary f E FA hFA FB hFB) =
      auxiliary (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)
        (FA.reindex σ) (hFA.reindex _) (FB.reindex σ) (hFB.reindex _) := by
  have hs : SelectedIntervalTransport.atEndpoint (reverseLineReindexIso f σ) false ≪≫
      reverseStart (Functor.whiskerLeft σ.mapElements f) =
      Functor.isoWhiskerLeft σ.mapElements (reverseStart f) :=
    Iso.ext (reverseLineReindexIso_start f σ)
  have ht : SelectedIntervalTransport.atEndpoint (reverseLineReindexIso f σ) true ≪≫
      reverseFinish (Functor.whiskerLeft σ.mapElements f) =
      Functor.isoWhiskerLeft σ.mapElements (reverseFinish f) :=
    Iso.ext (reverseLineReindexIso_finish f σ)
  have h := interval_presentations_map_reindex
    (reverseFilling f E FA hFA FB hFB) (reverseFilling_lawful f E FA hFA FB hFB)
    (reverseFilling (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)
      (FA.reindex σ) (hFA.reindex _) (FB.reindex σ) (hFB.reindex _)) σ
    (reverseStart f) (reverseFinish f)
    (reverseStart (Functor.whiskerLeft σ.mapElements f))
    (reverseFinish (Functor.whiskerLeft σ.mapElements f))
    (Iso.refl _) (Iso.refl _) (reverseLineReindexIso f σ)
    (reverseFilling_reindex f σ E FA hFA FB hFB)
    (by exact (Iso.trans_refl _).trans hs.symm)
    (by exact (Iso.trans_refl _).trans ht.symm)
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm.trans h

end SquareKit.Cubical.Presheaf.NativeEquivalenceLine

namespace SquareKit.Cubical.Presheaf.SelectedIntervalTransport
open CategoryTheory
universe u
variable {Γ : Context.{u}} {A B : Family (total (interval Γ))} {C : Family Γ}

theorem mapped_forward_transport (e : A ≅ B) (F : Filling A) (K : Filling B)
    (hf : F.transport e = K)
    (g : A ⟶ reindex C (projection (interval Γ)))
    (h : B ⟶ reindex C (projection (interval Γ)))
    (hm : e.hom ≫ h = g)
    (a : Term (reindex A (endpointSub Γ false)))
    (b : Term (reindex B (endpointSub Γ false)))
    (ha : Term.map (atEndpoint e false).hom a = b) :
    Term.map h (IntervalTransport.forward K (𝟙 Γ) b) =
      Term.map g (IntervalTransport.forward F (𝟙 Γ) a) := by
  subst K
  subst b
  have hh := congrArg (Term.map h) (forward_map e F (𝟙 Γ) a)
  exact hh.trans (congrArg (fun k => Term.map k (IntervalTransport.forward F (𝟙 Γ) a)) hm)

theorem mapped_forward_reindex {Δ : Context.{u}}
    {D : Family (total (interval Δ))} (σ : Δ ⟶ Γ)
    (e : reindex A (liftSub (interval Γ) σ) ≅ D)
    (F : Filling A) (hF : F.Lawful) (K : Filling D)
    (hf : (F.reindex (liftSub (interval Γ) σ)).transport e = K)
    (g : A ⟶ reindex C (projection (interval Γ)))
    (h : D ⟶ reindex (reindex C σ) (projection (interval Δ)))
    (hm : e.hom ≫ h = Functor.whiskerLeft (liftSub (interval Γ) σ).mapElements g)
    (a : Term (reindex A (endpointSub Γ false)))
    (b : Term (reindex D (endpointSub Δ false)))
    (ha : Term.map (atEndpoint e false).hom (a.reindex σ) = b) :
    Term.map h (IntervalTransport.forward K (𝟙 Δ) b) =
      (Term.map g (IntervalTransport.forward F (𝟙 Γ) a)).reindex (liftSub (interval Γ) σ) := by
  have hh := mapped_forward_transport (C := reindex C σ) e (F.reindex (liftSub (interval Γ) σ)) K hf
    (Functor.whiskerLeft (liftSub (interval Γ) σ).mapElements g) h hm (a.reindex σ) b ha
  exact hh.trans (congrArg (Term.map (Functor.whiskerLeft (liftSub (interval Γ) σ).mapElements g))
    (IntervalTransport.forward_reindex F hF (𝟙 Γ) a σ))

end SquareKit.Cubical.Presheaf.SelectedIntervalTransport

namespace SquareKit.Cubical.Presheaf.NativeEquivalenceLine
open CategoryTheory
open SelectedIntervalTransport
universe u
variable {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (σ : Δ ⟶ Γ)

theorem lineReindexIso_unglue :
    (lineReindexIso f σ).hom ≫ unglue (Functor.whiskerLeft σ.mapElements f) =
      Functor.whiskerLeft (liftSub (interval Γ) σ).mapElements (unglue f) := by
  ext x z
  let c := (Glue.compatibleReindexIso face (ambient (B := B)) (boundary (A := A))
    (boundaryMap f) (liftSub (interval Γ) σ)).hom.app x
    ((Glue.familyIso face (ambient (B := B)) (boundary (A := A)) (boundaryMap f)).hom.app
      ((liftSub (interval Γ) σ).mapElements.obj x) z)
  exact congrArg Glue.CompatibleElement.ambient
    ((Glue.fiberEquiv face (ambient (B := reindex B σ)) (boundary (A := reindex A σ))
      (boundaryMap (Functor.whiskerLeft σ.mapElements f)) x).apply_symm_apply c)

theorem reverseLineReindexIso_unglue :
    (reverseLineReindexIso f σ).hom ≫ reverseUnglue (Functor.whiskerLeft σ.mapElements f) =
      Functor.whiskerLeft (liftSub (interval Γ) σ).mapElements (reverseUnglue f) :=
  congrArg (Functor.whiskerLeft (reverseInterval Δ).mapElements) (lineReindexIso_unglue f σ)

private theorem initial_inverse {Ω : Context.{u}} {X Y Z : Family Ω}
    (i : X ≅ Z) (j : Y ≅ Z) (e : X ⟶ Y) (h : e ≫ j.hom = i.hom) :
    i.inv ≫ e = j.inv := by
  have hh := congrArg (fun k => i.inv ≫ k ≫ j.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, Category.comp_id] using hh

theorem reverseLineReindexIso_initial :
    Functor.whiskerLeft σ.mapElements (reverseStart f).inv ≫
      (atEndpoint (reverseLineReindexIso f σ) false).hom =
        (reverseStart (Functor.whiskerLeft σ.mapElements f)).inv :=
  initial_inverse (Functor.isoWhiskerLeft σ.mapElements (reverseStart f))
    (reverseStart (Functor.whiskerLeft σ.mapElements f))
    (atEndpoint (reverseLineReindexIso f σ) false).hom (reverseLineReindexIso_start f σ)

end SquareKit.Cubical.Presheaf.NativeEquivalenceLine

namespace SquareKit.Cubical.Presheaf.NativeEquivalenceLine
open CategoryTheory
open SelectedIntervalTransport
universe u
variable {Γ Δ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (σ : Δ ⟶ Γ)
  (E : HomotopyEquivalence f) (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful)

theorem auxiliaryRight_reindex :
    HEq (homogeneousReindex (auxiliaryRight f E FA hFA FB hFB) (liftSub B σ))
      (auxiliaryRight (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)
        (FA.reindex σ) (hFA.reindex _) (FB.reindex σ) (hFB.reindex _)) := by
  let F := reverseFilling f E FA hFA FB hFB
  let hF := reverseFilling_lawful f E FA hFA FB hFB
  let K := reverseFilling (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)
    (FA.reindex σ) (hFA.reindex _) (FB.reindex σ) (hFB.reindex _)
  let τ := liftSub B σ
  let ρ := liftSub (interval Δ) (projection (reindex B σ))
  let e := Functor.isoWhiskerLeft ρ.mapElements (reverseLineReindexIso f σ)
  let g := Functor.whiskerLeft (liftSub (interval Γ) (projection B)).mapElements (reverseUnglue f)
  let k := Functor.whiskerLeft ρ.mapElements (reverseUnglue (Functor.whiskerLeft σ.mapElements f))
  let a := Term.map (Functor.whiskerLeft (projection B).mapElements (reverseStart f).inv) (generic B)
  let b := Term.map (Functor.whiskerLeft (projection (reindex B σ)).mapElements
    (reverseStart (Functor.whiskerLeft σ.mapElements f)).inv) (generic (reindex B σ))
  have hf : ((F.reindex (liftSub (interval Γ) (projection B))).reindex
      (liftSub (interval (total B)) τ)).transport e = K.reindex ρ :=
    congrArg (fun H => H.reindex ρ) (reverseFilling_reindex f σ E FA hFA FB hFB)
  have hm : e.hom ≫ k = Functor.whiskerLeft (liftSub (interval (total B)) τ).mapElements g :=
    congrArg (Functor.whiskerLeft ρ.mapElements) (reverseLineReindexIso_unglue f σ)
  have ha : Term.map (atEndpoint e false).hom (a.reindex τ) = b := by
    have h := congrArg (fun m => Term.map
      (Functor.whiskerLeft (projection (reindex B σ)).mapElements m) (generic (reindex B σ)))
      (reverseLineReindexIso_initial f σ)
    exact h
  have hh := mapped_forward_reindex
    (A := reindex (reverseLine f) (liftSub (interval Γ) (projection B)))
    (C := reindex B (projection B)) τ e
    (F.reindex (liftSub (interval Γ) (projection B))) (hF.reindex _) (K.reindex ρ)
    hf g k hm a b ha
  apply pathTerm_hext
  exact (congrArg (fun t => t.reindex (reverseInterval (total (reindex B σ)))) hh).symm

end SquareKit.Cubical.Presheaf.NativeEquivalenceLine

namespace SquareKit.Cubical.Presheaf.HomotopyEquivalence
open CategoryTheory
universe u
variable {Γ Δ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
private theorem selectedComparison_heq (E : HomotopyEquivalence f) {g g' : B ⟶ A}
    (hg : g = g')
    {h : Term (homogeneousPath (Presheaf.reindex B (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements f)
        (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B))) (generic B))}
    {h' : Term (homogeneousPath (Presheaf.reindex B (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements f)
        (Term.map (Functor.whiskerLeft (projection B).mapElements g') (generic B))) (generic B))}
    (hh : HEq h h') : HEq (E.selectedComparison g h) (E.selectedComparison g' h') := by
  subst g'
  cases eq_of_heq hh
  rfl

private theorem ofMapHomotopy_heq {f' : A ⟶ B} {g g' : A ⟶ B}
    (hf : f = f') (hg : g = g')
    {E : HomotopyEquivalence f} {E' : HomotopyEquivalence f'} (hE : HEq E E')
    {H : Term (homogeneousPath (Presheaf.reindex B (projection A))
      (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
      (Term.map (Functor.whiskerLeft (projection A).mapElements g) (generic A)))}
    {H' : Term (homogeneousPath (Presheaf.reindex B (projection A))
      (Term.map (Functor.whiskerLeft (projection A).mapElements f') (generic A))
      (Term.map (Functor.whiskerLeft (projection A).mapElements g') (generic A)))}
    (hH : HEq H H') (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    HEq (E.ofMapHomotopy g H FA hFA FB hFB) (E'.ofMapHomotopy g' H' FA hFA FB hFB) := by
  subst f'
  subst g'
  cases eq_of_heq hE
  cases eq_of_heq hH
  rfl

open NativeEquivalenceLine in
/-- Recompute the complete selected inverse equivalence after substitution. -/
theorem selectedInverseEquivalence_reindex (E : HomotopyEquivalence f)
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) (σ : Δ ⟶ Γ) :
    HEq ((E.selectedInverseEquivalence FA hFA FB hFB).reindex σ)
      ((E.reindex σ).selectedInverseEquivalence (FA.reindex σ) (hFA.reindex _)
        (FB.reindex σ) (hFB.reindex _)) := by
  have hr := auxiliaryRight_reindex f σ E FA hFA FB hFB
  let D := auxiliaryEquivalence f E FA hFA FB hFB
  let g := auxiliary f E FA hFA FB hFB
  let r := auxiliaryRight f E FA hFA FB hFB
  have hc := (selectedComparison_reindex E g r σ).symm.trans
    (selectedComparison_heq (E.reindex σ) (auxiliary_reindex f σ E FA hFA FB hFB) hr)
  exact (heq_of_eq (ofMapHomotopy_reindex D E.selectedInverse (E.selectedComparison g r)
    FB hFB FA hFA σ)).trans
    (ofMapHomotopy_heq (auxiliary_reindex f σ E FA hFA FB hFB)
      (selectedInverse_reindex E σ).symm (auxiliaryEquivalence_reindex f σ E FA hFA FB hFB)
      hc (FB.reindex σ) (hFB.reindex _) (FA.reindex σ) (hFA.reindex _))
end SquareKit.Cubical.Presheaf.HomotopyEquivalence
