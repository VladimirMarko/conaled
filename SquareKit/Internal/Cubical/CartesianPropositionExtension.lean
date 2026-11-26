import SquareKit.Internal.Cubical.CartesianEquivalenceIsoTransport
import SquareKit.Internal.Cubical.CartesianNativeStructureIdentity
import SquareKit.Internal.Cubical.CartesianPiDomainIso

/-! Proposition-valued fields preserve the native identity correspondence. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.PropositionExtension
open CategoryTheory
universe u
variable {Γ : Context.{u}} {A : Family Γ} (B : Family (total A))

def first : sigma A B ⟶ A where
  app _ := TypeCat.ofHom Sigma.fst
  naturality _ _ _ := rfl

/-- Exchange independent fields over their shared carrier, retaining both values. -/
def exchange (R : Family (total A)) :
    sigma (sigma A B) (reindex R (PiDomain.baseMap (first B))) ≅
      sigma (sigma A R) (reindex B (PiDomain.baseMap (first R))) where
  hom := {
    app _ := TypeCat.ofHom (fun z => ⟨⟨z.1.1, z.2⟩, z.1.2⟩)
    naturality _ _ _ := rfl }
  inv := {
    app _ := TypeCat.ofHom (fun z => ⟨⟨z.1.1, z.2⟩, z.1.2⟩)
    naturality _ _ _ := rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- An inhabited proposition field preserves contractibility of the total relation. -/
noncomputable def relationTotalContractible
    (pB : Term (HomotopyLevels.isProp B))
    (R : Family (total A)) (cR : Contractible (sigma A R))
    (a : Term A) (b : Term (reindex B (pair (𝟙 Γ) a)))
    (r : Term (reindex R (pair (𝟙 Γ) a)))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful)
    (FR : Filling R) (hFR : FR.Lawful) :
    Contractible (sigma (sigma A B) (reindex R (PiDomain.baseMap (first B)))) := by
  let n : Term (sigma A R) := sigmaIntro a r
  let q := PiDomain.baseMap (first R)
  let C := reindex B q
  let τ : Γ ⟶ total (sigma A R) := pair (𝟙 Γ) n
  let cC : Contractible (reindex C (pair (𝟙 Γ) n)) :=
    HomotopyLevels.contractible
      (HomotopyLevels.reindexProp pB (τ ≫ q)) b
  let c := StructuredIdentity.totalContractibleOfFiber C cR n cC
    (sigmaFilling FA hFA FR) (sigmaFilling_lawful FA hFA FR hFR)
    (FB.reindex q) (hFB.reindex q)
  exact Contractible.map (exchange B R).symm c

namespace BasedPaths
variable (z : Term (sigma A B))
abbrev paths := StructuredIdentity.IdentitySystem.paths A (sigmaFst z)
abbrev relation := reindex (paths B z) (PiDomain.baseMap (first B))

def project : StructuredIdentity.IdentitySystem.paths (sigma A B) z ⟶ relation B z :=
  HomotopyLevels.pathMap (Functor.whiskerLeft (projection (sigma A B)).mapElements (first B))
    (Term.reindex z (projection (sigma A B))) (generic (sigma A B)) ≫
  (EquivalenceFamilies.homogeneousReindexIso (reindex A (projection A))
    (Term.reindex (sigmaFst z) (projection A)) (generic A) (PiDomain.baseMap (first B))).inv

private noncomputable def relationContractible (pB : Term (HomotopyLevels.isProp B))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    Contractible (sigma (sigma A B) (relation B z)) := by
  let FR := pathFilling ((FA.reindex (projection A)).reindex (projection (interval (total A))))
    ((hFA.reindex _).reindex _) (Term.reindex (sigmaFst z) (projection A)) (generic A)
  have hFR := pathFilling_lawful ((FA.reindex (projection A)).reindex (projection (interval (total A))))
    ((hFA.reindex _).reindex _) (Term.reindex (sigmaFst z) (projection A)) (generic A)
  let r : Term (reindex (paths B z) (pair (𝟙 Γ) (sigmaFst z))) :=
    Term.map (EquivalenceFamilies.homogeneousReindexIso (reindex A (projection A))
      (Term.reindex (sigmaFst z) (projection A)) (generic A) (pair (𝟙 Γ) (sigmaFst z))).inv
      (homogeneousRefl (sigmaFst z))
  exact relationTotalContractible B pB (paths B z)
    (ForwardSingleton.contractible A (sigmaFst z) FA hFA) (sigmaFst z) (sigmaSnd z) r
    FA hFA FB hFB FR hFR

noncomputable def equivalence (pB : Term (HomotopyLevels.isProp B))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    HomotopyEquivalence (project B z) := by
  let M := sigma A B
  let FM := sigmaFilling FA hFA FB
  have hFM := sigmaFilling_lawful FA hFA FB hFB
  let FR := pathFilling ((FA.reindex (projection A)).reindex (projection (interval (total A))))
    ((hFA.reindex _).reindex _) (Term.reindex (sigmaFst z) (projection A)) (generic A)
  have hFR := pathFilling_lawful ((FA.reindex (projection A)).reindex (projection (interval (total A))))
    ((hFA.reindex _).reindex _) (Term.reindex (sigmaFst z) (projection A)) (generic A)
  let c := relationContractible B z pB FA hFA FB hFB
  exact HomotopyEquivalence.ofContractibleTotals (project B z) FM hFM
    (pathFilling ((FM.reindex (projection M)).reindex (projection (interval (total M))))
      ((hFM.reindex _).reindex _) _ _)
    (pathFilling_lawful ((FM.reindex (projection M)).reindex (projection (interval (total M))))
      ((hFM.reindex _).reindex _) _ _)
    (FR.reindex (PiDomain.baseMap (first B))) (hFR.reindex _)
    (ForwardSingleton.contractible M z FM hFM) c

/-- The inverse selected by the based projection also has contractible fibers. -/
noncomputable def inverseEquivalence (pB : Term (HomotopyLevels.isProp B))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    HomotopyEquivalence (StructuredIdentity.TotalRecovery.inverse (project B z)
      (equivalence B z pB FA hFA FB hFB)) := by
  let M := sigma A B
  let FM := sigmaFilling FA hFA FB
  have hFM := sigmaFilling_lawful FA hFA FB hFB
  let FR := pathFilling ((FA.reindex (projection A)).reindex (projection (interval (total A))))
    ((hFA.reindex _).reindex _) (Term.reindex (sigmaFst z) (projection A)) (generic A)
  have hFR := pathFilling_lawful ((FA.reindex (projection A)).reindex (projection (interval (total A))))
    ((hFA.reindex _).reindex _) (Term.reindex (sigmaFst z) (projection A)) (generic A)
  let c := relationContractible B z pB FA hFA FB hFB
  exact HomotopyEquivalence.ofContractibleTotals
    (StructuredIdentity.TotalRecovery.inverse (project B z) (equivalence B z pB FA hFA FB hFB))
    FM hFM
    (FR.reindex (PiDomain.baseMap (first B))) (hFR.reindex _)
    (pathFilling ((FM.reindex (projection M)).reindex (projection (interval (total M))))
      ((hFM.reindex _).reindex _) _ _)
    (pathFilling_lawful ((FM.reindex (projection M)).reindex (projection (interval (total M))))
      ((hFM.reindex _).reindex _) _ _)
    c (ForwardSingleton.contractible M z FM hFM)

end BasedPaths

private theorem path_project_conjugate (z w : Term (sigma A B)) :
    let M := sigma A B
    let τ : Γ ⟶ total M := pair (𝟙 Γ) w
    let σ := PiDomain.baseMap (first B)
    let JM := EquivalenceFamilies.homogeneousReindexIso (reindex M (projection M))
      (Term.reindex z (projection M)) (generic M) τ
    let JA := EquivalenceFamilies.homogeneousReindexIso (reindex A (projection A))
      (Term.reindex (sigmaFst z) (projection A)) (generic A) (τ ≫ σ)
    JM.inv ≫ Functor.whiskerLeft τ.mapElements (BasedPaths.project B z) ≫ JA.hom =
      HomotopyLevels.pathMap (first B) z w := by
  let M := sigma A B
  let τ : Γ ⟶ total M := pair (𝟙 Γ) w
  let σ := PiDomain.baseMap (first B)
  let JM := EquivalenceFamilies.homogeneousReindexIso (reindex M (projection M))
    (Term.reindex z (projection M)) (generic M) τ
  let JA := EquivalenceFamilies.homogeneousReindexIso (reindex A (projection A))
    (Term.reindex (sigmaFst z) (projection A)) (generic A) (τ ≫ σ)
  ext x p
  apply Subtype.ext
  apply PiElement.ext
  intro y f r
  let q := (HomotopyLevels.pathMap
    (Functor.whiskerLeft (projection (sigma A B)).mapElements (first B))
    (Term.reindex z (projection (sigma A B))) (generic (sigma A B))).app
    (τ.mapElements.obj x) (JM.inv.app x p)
  have hq := piInverseValue_map (A := interval (total A))
    (B := reindex (reindex A (projection A)) (projection (interval (total A))))
    σ q.val (τ.mapElements.map f) r
  refine hq.trans ?_
  change (piInverseValue (A := interval (total M))
    (B := reindex (reindex M (projection M)) (projection (interval (total M))))
    τ p.val (τ.mapElements.map f) r).1 = (p.val.val f r).1
  exact congrArg Sigma.fst (piInverseValue_map (A := interval (total M))
    (B := reindex (reindex M (projection M)) (projection (interval (total M)))) τ p.val f r)

/-- Forgetting a proposition field induces a native equivalence on whole paths. -/
noncomputable def pathEquivalence (z w : Term (sigma A B))
    (pB : Term (HomotopyLevels.isProp B))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    HomotopyEquivalence (HomotopyLevels.pathMap (first B) z w) := by
  let M := sigma A B
  let τ : Γ ⟶ total M := pair (𝟙 Γ) w
  let σ := PiDomain.baseMap (first B)
  let JM := EquivalenceFamilies.homogeneousReindexIso (reindex M (projection M))
    (Term.reindex z (projection M)) (generic M) τ
  let JA := EquivalenceFamilies.homogeneousReindexIso (reindex A (projection A))
    (Term.reindex (sigmaFst z) (projection A)) (generic A) (τ ≫ σ)
  have E := ((BasedPaths.equivalence B z pB FA hFA FB hFB).reindex τ).conjugateIso JM.symm JA
  exact (path_project_conjugate B z w) ▸ E

/-- Reconstruct a whole path from its projection through a proposition field. -/
noncomputable def pathInverse (z w : Term (sigma A B))
    (pB : Term (HomotopyLevels.isProp B))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    homogeneousPath A (sigmaFst z) (sigmaFst w) ⟶ homogeneousPath (sigma A B) z w :=
  let M := sigma A B
  let τ : Γ ⟶ total M := pair (𝟙 Γ) w
  let σ := PiDomain.baseMap (first B)
  let JM := EquivalenceFamilies.homogeneousReindexIso (reindex M (projection M))
    (Term.reindex z (projection M)) (generic M) τ
  let JA := EquivalenceFamilies.homogeneousReindexIso (reindex A (projection A))
    (Term.reindex (sigmaFst z) (projection A)) (generic A) (τ ≫ σ)
  JA.inv ≫ Functor.whiskerLeft τ.mapElements
    (StructuredIdentity.TotalRecovery.inverse (BasedPaths.project B z)
      (BasedPaths.equivalence B z pB FA hFA FB hFB)) ≫ JM.hom

/-- The selected reconstruction is a native homotopy equivalence at arbitrary endpoints. -/
noncomputable def pathInverseEquivalence (z w : Term (sigma A B))
    (pB : Term (HomotopyLevels.isProp B))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) :
    HomotopyEquivalence (pathInverse B z w pB FA hFA FB hFB) := by
  let M := sigma A B
  let τ : Γ ⟶ total M := pair (𝟙 Γ) w
  let σ := PiDomain.baseMap (first B)
  let JM := EquivalenceFamilies.homogeneousReindexIso (reindex M (projection M))
    (Term.reindex z (projection M)) (generic M) τ
  let JA := EquivalenceFamilies.homogeneousReindexIso (reindex A (projection A))
    (Term.reindex (sigmaFst z) (projection A)) (generic A) (τ ≫ σ)
  exact ((BasedPaths.inverseEquivalence B z pB FA hFA FB hFB).reindex τ).conjugateIso JA.symm JM

private noncomputable def rightInverseAt {Γ : Context.{u}} {C D : Family Γ}
    (f : C ⟶ D) (E : HomotopyEquivalence f) (b : Term D) :
    Term (homogeneousPath D
      (Term.map f (Term.map (StructuredIdentity.TotalRecovery.inverse f E) b)) b) :=
  Term.map (EquivalenceFamilies.homogeneousReindexIso (reindex D (projection D))
    (Term.map (Functor.whiskerLeft (projection D).mapElements f)
      (Term.map (Functor.whiskerLeft (projection D).mapElements
        (StructuredIdentity.TotalRecovery.inverse f E)) (generic D)))
    (generic D) (pair (𝟙 Γ) b)).hom
    (Term.reindex (StructuredIdentity.TotalRecovery.rightInverse f E) (pair (𝟙 Γ) b))


private theorem conjugate_composition {C : Type*} [Category C]
    {W X Y Z : C} (i : W ≅ X) (j : Y ≅ Z) (f : W ⟶ Y) (g : Y ⟶ W) :
    (j.inv ≫ g ≫ i.hom) ≫ (i.inv ≫ f ≫ j.hom) = j.inv ≫ g ≫ f ≫ j.hom := by
  simp only [Category.assoc, Iso.hom_inv_id_assoc]

/-- Projection of the reconstruction recovers the complete supplied path natively. -/
noncomputable def pathInverseProjection (z w : Term (sigma A B))
    (pB : Term (HomotopyLevels.isProp B))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful)
    (p : Term (homogeneousPath A (sigmaFst z) (sigmaFst w))) :
    Term (homogeneousPath (homogeneousPath A (sigmaFst z) (sigmaFst w))
      (Term.map (HomotopyLevels.pathMap (first B) z w)
        (Term.map (pathInverse B z w pB FA hFA FB hFB) p)) p) := by
  let M := sigma A B
  let τ : Γ ⟶ total M := pair (𝟙 Γ) w
  let σ := PiDomain.baseMap (first B)
  let JM := EquivalenceFamilies.homogeneousReindexIso (reindex M (projection M))
    (Term.reindex z (projection M)) (generic M) τ
  let JA := EquivalenceFamilies.homogeneousReindexIso (reindex A (projection A))
    (Term.reindex (sigmaFst z) (projection A)) (generic A) (τ ≫ σ)
  let F := BasedPaths.project B z
  let E := BasedPaths.equivalence B z pB FA hFA FB hFB
  let f := Functor.whiskerLeft τ.mapElements F
  let g := StructuredIdentity.TotalRecovery.inverse f (E.reindex τ)
  let p₀ := Term.map JA.inv p
  let h := Term.map (HomotopyLevels.pathMap JA.hom _ _) (rightInverseAt f (E.reindex τ) p₀)
  have hg : g = Functor.whiskerLeft τ.mapElements (StructuredIdentity.TotalRecovery.inverse F E) := by
    ext x q
    rfl
  have hc : pathInverse B z w pB FA hFA FB hFB ≫ HomotopyLevels.pathMap (first B) z w =
      JA.inv ≫ g ≫ f ≫ JA.hom := by
    change (JA.inv ≫ Functor.whiskerLeft τ.mapElements
      (StructuredIdentity.TotalRecovery.inverse F E) ≫ JM.hom) ≫ _ = _
    rw [← path_project_conjugate B z w, ← hg]
    change (JA.inv ≫ g ≫ JM.hom) ≫ (JM.inv ≫ f ≫ JA.hom) = JA.inv ≫ g ≫ f ≫ JA.hom
    exact conjugate_composition JM JA f g
  have hl : Term.map (HomotopyLevels.pathMap (first B) z w)
      (Term.map (pathInverse B z w pB FA hFA FB hFB) p) =
      Term.map JA.hom (Term.map f (Term.map g p₀)) :=
    congrArg (fun m => Term.map m p) hc
  have hr : Term.map JA.hom p₀ = p := Term.map_iso_roundtrip JA.symm p
  exact pathLam (pathApp h) ((pathApp_zero h).trans hl.symm) ((pathApp_one h).trans hr)

end SquareKit.Cubical.Cartesian.PropositionExtension
