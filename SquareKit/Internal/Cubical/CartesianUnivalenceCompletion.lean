import SquareKit.Internal.Cubical.CartesianUnivalence
import SquareKit.Internal.Cubical.CartesianContractibleTotals

/-! The actual path-to-equivalence map has contractible fibers. Its constructed
Glue inverse retains both native inverse homotopies and complete chosen witnesses. -/

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u

private def nativePathIso {Γ Δ : Context.{u+1}} (a b : Γ ⟶ smallFamilyCodes.{u})
    (σ : Δ ⟶ Γ) : reindex (paths a b) σ ≅ paths (σ ≫ a) (σ ≫ b) :=
  pathReindexIso (reindex (family Γ) (projection (interval Γ))) (term a) (term b) σ

private noncomputable def pathData {Γ : Context.{u+1}} {a b : Γ ⟶ smallFamilyCodes.{u}}
    (p : Term (paths a b)) : Σ f : liftedDecode a ⟶ liftedDecode b, HomotopyEquivalence f :=
  ⟨pathToMap p, pathToEquivalence p⟩

set_option maxHeartbeats 1600000 in
private theorem conjugate_sections {Γ Δ Θ : Context.{u+1}}
    (a b : Γ ⟶ smallFamilyCodes.{u}) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (p : Term (reindex (paths (σ ≫ a) (σ ≫ b)) τ)) :
    Term.map
      (Functor.whiskerLeft τ.mapElements (nativePathIso a b σ).inv ≫
        Functor.whiskerLeft (τ ≫ σ).mapElements (pathToEquiv a b) ≫
        Functor.whiskerLeft τ.mapElements
          (EquivalenceFamilies.equivReindexIso (liftedDecode a) (liftedDecode b) σ).hom) p =
      Term.map (Functor.whiskerLeft τ.mapElements (pathToEquiv (σ ≫ a) (σ ≫ b))) p := by
  let Jp := nativePathIso a b σ
  let q := Term.map (Functor.whiskerLeft τ.mapElements Jp.inv) p
  let r : Term (paths ((τ ≫ σ) ≫ a) ((τ ≫ σ) ≫ b)) :=
    Term.map (nativePathIso a b (τ ≫ σ)).hom q
  let r' : Term (paths (τ ≫ σ ≫ a) (τ ≫ σ ≫ b)) :=
    Term.map (nativePathIso (σ ≫ a) (σ ≫ b) τ).hom p
  have hp : r = r' :=
    congrArg (Term.map (nativePathIso (σ ≫ a) (σ ≫ b) τ).hom)
      (Term.map_iso_roundtrip (Functor.isoWhiskerLeft τ.mapElements Jp).symm p)
  let old := Term.map (Functor.whiskerLeft (τ ≫ σ).mapElements (pathToEquiv a b)) q
  let S := EquivalenceFamilies.equivReindexSections (liftedDecode a) (liftedDecode b) (τ ≫ σ)
  let T := EquivalenceFamilies.equivReindexSections
    (liftedDecode (σ ≫ a)) (liftedDecode (σ ≫ b)) τ
  have hβ : old = S (pathData r) := pathToEquiv_reindex_beta (τ ≫ σ) q
  have hdata : S.symm old = pathData r :=
    (congrArg S.symm hβ).trans (S.symm_apply_apply (pathData r))
  have hJ := EquivalenceFamilies.equivReindexIso_hom_reindex_sections
    (liftedDecode a) (liftedDecode b) σ τ old
  have hpath : pathData r = pathData r' :=
    @congrArg (Term (paths (τ ≫ σ ≫ a) (τ ≫ σ ≫ b)))
      (Σ f : liftedDecode (τ ≫ σ ≫ a) ⟶ liftedDecode (τ ≫ σ ≫ b), HomotopyEquivalence f)
      r r' pathData hp
  have hnew : Term.map (Functor.whiskerLeft τ.mapElements
      (pathToEquiv (σ ≫ a) (σ ≫ b))) p = T (pathData r') :=
    pathToEquiv_reindex_beta τ p
  exact hJ.trans ((congrArg T hdata).trans ((congrArg T hpath).trans hnew.symm))

/-- The forward native univalence map commutes with substitution through the
actual path and complete-equivalence presentation isomorphisms. -/
theorem pathToEquiv_conjugate_reindex {Γ Δ : Context.{u+1}}
    (a b : Γ ⟶ smallFamilyCodes.{u}) (σ : Δ ⟶ Γ) :
    (pathReindexIso (reindex (family Γ) (projection (interval Γ)))
      (term a) (term b) σ).inv ≫
      Functor.whiskerLeft σ.mapElements (pathToEquiv a b) ≫
      (EquivalenceFamilies.equivReindexIso (liftedDecode a) (liftedDecode b) σ).hom =
      pathToEquiv (σ ≫ a) (σ ≫ b) := by
  let C := paths (σ ≫ a) (σ ≫ b)
  have h := conjugate_sections a b σ (projection C) (generic C)
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro p
  exact congrArg (fun t => t.val (extendObj C x p)) h

end SquareKit.Cubical.Cartesian.SmallUniverse.NativeUnivalence

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u
variable {Γ : Context.{u+1}} (a : Γ ⟶ smallFamilyCodes.{u})

def movingSource : total (family Γ) ⟶ smallFamilyCodes.{u} := projection (family Γ) ≫ a

def movingTarget : total (family Γ) ⟶ smallFamilyCodes.{u} := code (generic (family Γ))

abbrev basedPaths := paths (movingSource a) (movingTarget (Γ := Γ))
abbrev basedEquivalences := equivalences (movingSource a) (movingTarget (Γ := Γ))

noncomputable def basedPathsFilling : Filling (basedPaths a) :=
  pathFilling (filling (total (interval (total (family Γ)))))
    (filling_lawful _) (term (movingSource a)) (term (movingTarget (Γ := Γ)))

theorem basedPathsFilling_lawful : (basedPathsFilling a).Lawful :=
  pathFilling_lawful (filling (total (interval (total (family Γ)))))
    (filling_lawful _) (term (movingSource a)) (term (movingTarget (Γ := Γ)))

noncomputable def basedEquivalencesFilling : Filling (basedEquivalences a) :=
  EquivalenceFamilies.equivFilling (NativeDecode.filling (movingSource a))
    (NativeDecode.filling_lawful _) (NativeDecode.filling (movingTarget (Γ := Γ)))
    (NativeDecode.filling_lawful _)

theorem basedEquivalencesFilling_lawful : (basedEquivalencesFilling a).Lawful :=
  EquivalenceFamilies.equivFilling_lawful (NativeDecode.filling (movingSource a))
    (NativeDecode.filling_lawful _) (NativeDecode.filling (movingTarget (Γ := Γ)))
    (NativeDecode.filling_lawful _)

noncomputable def basedPathTotalContractible : Contractible (sigma (family Γ) (basedPaths a)) :=
  ForwardSingleton.contractible (family Γ) (term a) (filling Γ) (filling_lawful Γ)

variable (h : Term (homogeneousPath (reindex (basedEquivalences a) (projection (basedEquivalences a)))
  (Term.map (Functor.whiskerLeft (projection (basedEquivalences a)).mapElements
    (pathToEquiv (movingSource a) (movingTarget (Γ := Γ))))
    (Term.map (Functor.whiskerLeft (projection (basedEquivalences a)).mapElements
      (equivToPath (movingSource a) (movingTarget (Γ := Γ)))) (generic (basedEquivalences a))))
  (generic (basedEquivalences a))))

/-- The total contraction uses the supplied native right-inverse homotopy, not an assumed contraction. -/
noncomputable def equivalenceTotalOfHomotopy :
    Contractible (sigma (family Γ) (basedEquivalences a)) :=
  (basedPathTotalContractible a).fiberwiseRetract (filling Γ) (filling_lawful Γ)
    (basedEquivalencesFilling a) (basedEquivalencesFilling_lawful a)
    (pathToEquiv (movingSource a) (movingTarget (Γ := Γ)))
    (equivToPath (movingSource a) (movingTarget (Γ := Γ))) h

noncomputable def univalenceOfHomotopy :
    HomotopyEquivalence (pathToEquiv (movingSource a) (movingTarget (Γ := Γ))) :=
  HomotopyEquivalence.ofContractibleTotals
    (pathToEquiv (movingSource a) (movingTarget (Γ := Γ)))
    (filling Γ) (filling_lawful Γ)
    (basedPathsFilling a) (basedPathsFilling_lawful a)
    (basedEquivalencesFilling a) (basedEquivalencesFilling_lawful a)
    (basedPathTotalContractible a) (equivalenceTotalOfHomotopy a h)

end SquareKit.Cubical.Cartesian.SmallUniverse.NativeUnivalence

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u

private def sigmaFirstMap {Γ : Context.{u}} (A : Family Γ) (B : Family (total A)) :
    sigma A B ⟶ A where
  app _ := TypeCat.ofHom Sigma.fst
  naturality _ _ _ := rfl

/-- A supplied right inverse of a genuine native equivalence also has a native
left-inverse homotopy. The supplied inverse and its right-inverse path are retained. -/
noncomputable def HomotopyEquivalence.chosenLeftInverse
    {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B} (E : HomotopyEquivalence f)
    (F : Filling A) (hF : F.Lawful) (g : B ⟶ A)
    (h : Term (homogeneousPath (Cartesian.reindex B (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements f)
        (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B)))
      (generic B))) :
    Term (homogeneousPath (Cartesian.reindex A (projection A))
      (Term.map (Functor.whiskerLeft (projection A).mapElements g)
        (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A)))
      (generic A)) := by
  let σ := projection A
  let a := generic A
  let f' := Functor.whiskerLeft σ.mapElements f
  let g' := Functor.whiskerLeft σ.mapElements g
  let b := Term.map f' a
  let τ := pair σ b
  let q := Term.map (pathReindexIso
    (Cartesian.reindex (Cartesian.reindex B (projection B)) (projection (interval (total B))))
    (Term.map (Functor.whiskerLeft (projection B).mapElements f)
      (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B)))
    (generic B) τ).hom (Term.reindex h τ)
  let c := (E.reindex σ).fiberAt b
  let z₀ := Homotopy.fiberIntro f' b (Term.map g' b) q
  let z₁ := Homotopy.fiberIntro f' b a (homogeneousRefl b)
  let π := sigmaFirstMap (Cartesian.reindex A σ)
    (homogeneousPath (Cartesian.reindex (Cartesian.reindex B σ) (projection (Cartesian.reindex A σ)))
      (Term.map (Functor.whiskerLeft (projection (Cartesian.reindex A σ)).mapElements f')
        (generic (Cartesian.reindex A σ))) (Term.reindex b (projection (Cartesian.reindex A σ))))
  let p₀ := homogeneousPathMap π (c.pathTo z₀)
  let p₁ := homogeneousPathMap π (c.pathTo z₁)
  exact homogeneousConcat (F.reindex σ) (hF.reindex σ)
    (homogeneousReverse (F.reindex σ) (hF.reindex σ) p₀) p₁

end SquareKit.Cubical.Cartesian

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u
variable {Γ : Context.{u+1}} (a b : Γ ⟶ smallFamilyCodes.{u})

noncomputable def equivalenceTotal : Contractible (sigma (family Γ) (basedEquivalences a)) :=
  equivalenceTotalOfHomotopy a (rightInverseHomotopy (movingSource a) (movingTarget (Γ := Γ)))

noncomputable def movingUnivalence :
    HomotopyEquivalence (pathToEquiv (movingSource a) (movingTarget (Γ := Γ))) :=
  univalenceOfHomotopy a (rightInverseHomotopy (movingSource a) (movingTarget (Γ := Γ)))

/-- Native univalence for the actual universal-El path-to-equivalence map. -/
noncomputable def univalence : HomotopyEquivalence (pathToEquiv a b) := by
  let τ := pair (A := family Γ) (𝟙 Γ) (term b)
  let Jp := pathReindexIso
    (reindex (family (total (family Γ))) (projection (interval (total (family Γ)))))
    (term (movingSource a)) (term (movingTarget (Γ := Γ))) τ
  let Je := EquivalenceFamilies.equivReindexIso
    (liftedDecode (movingSource a)) (liftedDecode (movingTarget (Γ := Γ))) τ
  have E := ((movingUnivalence a).reindex τ).conjugateIso Jp.symm Je
  -- The naturality law identifies the transported map itself, not only its observations.
  exact (pathToEquiv_conjugate_reindex (movingSource a) (movingTarget (Γ := Γ)) τ) ▸ E

noncomputable def pathsFilling : Filling (paths a b) :=
  pathFilling (filling (total (interval Γ))) (filling_lawful _)
    (term a) (term b)

theorem pathsFilling_lawful : (pathsFilling a b).Lawful :=
  pathFilling_lawful (filling (total (interval Γ))) (filling_lawful _)
    (term a) (term b)

/-- The same constructed ua map is also a left inverse, through a native path. -/
noncomputable def leftInverseHomotopy :=
  (univalence a b).chosenLeftInverse (pathsFilling a b) (pathsFilling_lawful a b)
    (equivToPath a b) (rightInverseHomotopy a b)

/-- Pointwise form of the left inverse, for an arbitrary native universe path. -/
noncomputable def leftInverseAt (p : Term (paths a b)) :
    Term (homogeneousPath (paths a b)
      (Term.map (equivToPath a b) (Term.map (pathToEquiv a b) p)) p) :=
  homogeneousReindex (leftInverseHomotopy a b) (pair (A := paths a b) (𝟙 Γ) p)

end SquareKit.Cubical.Cartesian.SmallUniverse.NativeUnivalence
