import SquareKit.Internal.Cubical.CompositionalUnivalence
import SquareKit.Internal.Cubical.NativeUniverseSquares
import SquareKit.Internal.Cubical.UnivalenceLawParameters
import SquareKit.Internal.Cubical.HomotopyIsoSubstitution
import SquareKit.Internal.Cubical.HomotopyEquivalenceCompositionSubstitution

/-! Chosen univalence comparisons obtained from full-data parameter contexts.
The chosen witnesses commute with substitution because classification does. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse.NaturalUnivalenceLaws
open CategoryTheory NativeUnivalence
universe u

private def restrictSquare {Γ Δ : Context.{u+1}}
    (z : Term (family (total (interval (total (interval Γ)))))) (σ : Δ ⟶ Γ) :
    Term (family (total (interval (total (interval Δ))))) :=
  z.reindex (liftSub (interval (total (interval Γ))) (liftSub (interval Γ) σ))

private theorem restrictSquare_comp {Γ Δ Θ : Context.{u+1}}
    (z : Term (family (total (interval (total (interval Γ)))))) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    restrictSquare (restrictSquare z σ) τ = restrictSquare z (τ ≫ σ) := rfl

private theorem identity_start {Γ : Context.{u+1}} (a : Γ ⟶ smallFamilyCodes.{u}) :
    reindexPath (ua (𝟙 smallFamilyCodes) (𝟙 smallFamilyCodes) (𝟙 _)
      (HomotopyEquivalence.ofIso (Iso.refl _))) a =
      ua a a (𝟙 _) (HomotopyEquivalence.ofIso (Iso.refl _)) := by
  rw [ua_reindex, HomotopyEquivalence.ofIso_reindex]
  rfl

/-- The chosen identity comparison is the restriction of one universal choice. -/
noncomputable def identity {Γ : Context.{u+1}} (a : Γ ⟶ smallFamilyCodes.{u}) :
    Term (homogeneousPath (paths a a)
      (ua a a (𝟙 _) (HomotopyEquivalence.ofIso (Iso.refl _)))
      (homogeneousRefl (term a))) := by
  let p := reindexComparison (uaIdentity (𝟙 smallFamilyCodes.{u})) a
  exact relabelComparison p (identity_start a) rfl

private theorem uaData_congr {Γ : Context.{u+1}} (a b : Γ ⟶ smallFamilyCodes.{u})
    (v w : Σ k : liftedDecode a ⟶ liftedDecode b, HomotopyEquivalence k) (h : v = w) :
    ua a b v.1 v.2 = ua a b w.1 w.2 := by
  cases h
  rfl

private theorem inverseUaData_congr {Γ : Context.{u+1}} (a b : Γ ⟶ smallFamilyCodes.{u})
    (v w : Σ k : liftedDecode a ⟶ liftedDecode b, HomotopyEquivalence k) (h : v = w) :
    ua b a (inverseMap a b v.1 v.2) (inverseEquivalence a b v.1 v.2) =
      ua b a (inverseMap a b w.1 w.2) (inverseEquivalence a b w.1 w.2) := by
  cases h
  rfl

private theorem inverseUa_reindex {Γ Δ : Context.{u+1}} (a b : Γ ⟶ smallFamilyCodes.{u})
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f) (σ : Δ ⟶ Γ) :
    reindexPath (ua b a (inverseMap a b f E) (inverseEquivalence a b f E)) σ =
      ua (σ ≫ b) (σ ≫ a)
        (inverseMap (σ ≫ a) (σ ≫ b) (Functor.whiskerLeft σ.mapElements f) (E.reindex σ))
        (inverseEquivalence (σ ≫ a) (σ ≫ b) (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)) := by
  have hd : (⟨Functor.whiskerLeft σ.mapElements (inverseMap a b f E),
      (inverseEquivalence a b f E).reindex σ⟩ :
      Σ k : liftedDecode (σ ≫ b) ⟶ liftedDecode (σ ≫ a), HomotopyEquivalence k) =
    ⟨inverseMap (σ ≫ a) (σ ≫ b) (Functor.whiskerLeft σ.mapElements f) (E.reindex σ),
      inverseEquivalence (σ ≫ a) (σ ≫ b) (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)⟩ :=
    Sigma.ext (inverseMap_reindex a b f E σ) (inverseEquivalence_reindex a b f E σ)
  exact (ua_reindex b a (inverseMap a b f E) (inverseEquivalence a b f E) σ).trans
    (uaData_congr (σ ≫ b) (σ ≫ a)
      ⟨Functor.whiskerLeft σ.mapElements (inverseMap a b f E), (inverseEquivalence a b f E).reindex σ⟩
      ⟨inverseMap (σ ≫ a) (σ ≫ b) (Functor.whiskerLeft σ.mapElements f) (E.reindex σ),
        inverseEquivalence (σ ≫ a) (σ ≫ b) (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)⟩ hd)

open UnivalenceLawParameters

private theorem inverse_start {Γ : Context.{u+1}} (a b : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f) :
    reindexPath (ua targetCode sourceCode
      (inverseMap sourceCode targetCode universalEquivalence.1 universalEquivalence.2)
      (inverseEquivalence sourceCode targetCode universalEquivalence.1 universalEquivalence.2))
      (classifyEquivalence a b f E) =
      ua b a (inverseMap a b f E) (inverseEquivalence a b f E) :=
  (inverseUa_reindex sourceCode targetCode universalEquivalence.1 universalEquivalence.2
    (classifyEquivalence a b f E)).trans
    (inverseUaData_congr a b
      ⟨Functor.whiskerLeft (classifyEquivalence a b f E).mapElements universalEquivalence.1,
        universalEquivalence.2.reindex (classifyEquivalence a b f E)⟩ ⟨f,E⟩
      (universalEquivalence_beta a b f E))

private theorem inverse_finish {Γ : Context.{u+1}} (a b : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f) :
    reindexPath (homogeneousReverse (ua sourceCode targetCode universalEquivalence.1 universalEquivalence.2))
      (classifyEquivalence a b f E) = homogeneousReverse (ua a b f E) :=
  (homogeneousReindex_reverse (ua sourceCode targetCode universalEquivalence.1 universalEquivalence.2)
    (classifyEquivalence a b f E)).trans
    (congrArg homogeneousReverse ((ua_reindex sourceCode targetCode universalEquivalence.1
      universalEquivalence.2 (classifyEquivalence a b f E)).trans
      (uaData_congr a b
        ⟨Functor.whiskerLeft (classifyEquivalence a b f E).mapElements universalEquivalence.1,
          universalEquivalence.2.reindex (classifyEquivalence a b f E)⟩ ⟨f,E⟩
        (universalEquivalence_beta a b f E))))

/-- A chosen inverse comparison retaining the entire classified equivalence. -/
noncomputable def inverse {Γ : Context.{u+1}} (a b : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f) :
    Term (homogeneousPath (paths b a)
      (ua b a (inverseMap a b f E) (inverseEquivalence a b f E))
      (homogeneousReverse (ua a b f E))) := by
  let p := reindexComparison
    (uaInverse sourceCode targetCode universalEquivalence.1 universalEquivalence.2)
    (classifyEquivalence a b f E)
  exact relabelComparison p (inverse_start a b f E) (inverse_finish a b f E)

private theorem compositeEquivalence_reindex {Γ Δ : Context.{u+1}} (a b c : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (g : liftedDecode b ⟶ liftedDecode c) (D : HomotopyEquivalence g) (σ : Δ ⟶ Γ) :
    (compositeEquivalence a b c f E g D).reindex σ =
      compositeEquivalence (σ ≫ a) (σ ≫ b) (σ ≫ c)
        (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)
        (Functor.whiskerLeft σ.mapElements g) (D.reindex σ) :=
  E.comp_reindex D (NativeDecode.filling a) (NativeDecode.filling_lawful a)
    (NativeDecode.filling b) (NativeDecode.filling_lawful b)
    (NativeDecode.filling c) (NativeDecode.filling_lawful c) σ

private theorem compositeUaData_congr {Γ : Context.{u+1}} (a b c : Γ ⟶ codes)
    (v v' : Σ k : liftedDecode a ⟶ liftedDecode b, HomotopyEquivalence k)
    (w w' : Σ k : liftedDecode b ⟶ liftedDecode c, HomotopyEquivalence k)
    (hv : v = v') (hw : w = w') :
    ua a c (v.1 ≫ w.1) (compositeEquivalence a b c v.1 v.2 w.1 w.2) =
      ua a c (v'.1 ≫ w'.1) (compositeEquivalence a b c v'.1 v'.2 w'.1 w'.2) := by
  cases hv
  cases hw
  rfl

private theorem compositeUa_reindex {Γ Δ : Context.{u+1}} (a b c : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (g : liftedDecode b ⟶ liftedDecode c) (D : HomotopyEquivalence g) (σ : Δ ⟶ Γ) :
    reindexPath (ua a c (f ≫ g) (compositeEquivalence a b c f E g D)) σ =
      ua (σ ≫ a) (σ ≫ c)
        (Functor.whiskerLeft σ.mapElements f ≫ Functor.whiskerLeft σ.mapElements g)
        (compositeEquivalence (σ ≫ a) (σ ≫ b) (σ ≫ c)
          (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)
          (Functor.whiskerLeft σ.mapElements g) (D.reindex σ)) :=
  (ua_reindex a c (f ≫ g) (compositeEquivalence a b c f E g D) σ).trans
    (congrArg (fun (C : HomotopyEquivalence (Functor.whiskerLeft σ.mapElements f ≫ Functor.whiskerLeft σ.mapElements g)) => ua (σ ≫ a) (σ ≫ c)
      (Functor.whiskerLeft σ.mapElements f ≫ Functor.whiskerLeft σ.mapElements g) C)
      (compositeEquivalence_reindex a b c f E g D σ))

private theorem composition_start {Γ : Context.{u+1}} (a b c : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (g : liftedDecode b ⟶ liftedDecode c) (D : HomotopyEquivalence g) :
    reindexPath (ua compositionSource compositionTarget (firstEquivalence.1 ≫ secondEquivalence.1)
      (compositeEquivalence compositionSource compositionMiddle compositionTarget
        firstEquivalence.1 firstEquivalence.2 secondEquivalence.1 secondEquivalence.2))
      (classifyComposition a b c f E g D) =
      ua a c (f ≫ g) (compositeEquivalence a b c f E g D) :=
  (compositeUa_reindex compositionSource compositionMiddle compositionTarget
    firstEquivalence.1 firstEquivalence.2 secondEquivalence.1 secondEquivalence.2
    (classifyComposition a b c f E g D)).trans
    (compositeUaData_congr a b c
      ⟨Functor.whiskerLeft (classifyComposition a b c f E g D).mapElements firstEquivalence.1,
        firstEquivalence.2.reindex (classifyComposition a b c f E g D)⟩ ⟨f,E⟩
      ⟨Functor.whiskerLeft (classifyComposition a b c f E g D).mapElements secondEquivalence.1,
        secondEquivalence.2.reindex (classifyComposition a b c f E g D)⟩ ⟨g,D⟩
      (firstEquivalence_beta a b c f E g D) (secondEquivalence_beta a b c f E g D))

private theorem composition_finish {Γ : Context.{u+1}} (a b c : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (g : liftedDecode b ⟶ liftedDecode c) (D : HomotopyEquivalence g) :
    reindexPath (homogeneousConcat (filling compositionContext) (filling_lawful compositionContext)
      (ua compositionSource compositionMiddle firstEquivalence.1 firstEquivalence.2)
      (ua compositionMiddle compositionTarget secondEquivalence.1 secondEquivalence.2))
      (classifyComposition a b c f E g D) =
      homogeneousConcat (filling Γ) (filling_lawful Γ) (ua a b f E) (ua b c g D) :=
  (uaConcat_reindex compositionSource compositionMiddle compositionTarget
    firstEquivalence.1 firstEquivalence.2 secondEquivalence.1 secondEquivalence.2
    (classifyComposition a b c f E g D)).trans
    (congrArg₂ (homogeneousConcat (filling Γ) (filling_lawful Γ))
      (uaData_congr a b
        ⟨Functor.whiskerLeft (classifyComposition a b c f E g D).mapElements firstEquivalence.1,
          firstEquivalence.2.reindex (classifyComposition a b c f E g D)⟩ ⟨f,E⟩
        (firstEquivalence_beta a b c f E g D))
      (uaData_congr b c
        ⟨Functor.whiskerLeft (classifyComposition a b c f E g D).mapElements secondEquivalence.1,
          secondEquivalence.2.reindex (classifyComposition a b c f E g D)⟩ ⟨g,D⟩
        (secondEquivalence_beta a b c f E g D)))

/-- A naturally chosen comparison for the actual composite map and contraction. -/
noncomputable def composition {Γ : Context.{u+1}} (a b c : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (g : liftedDecode b ⟶ liftedDecode c) (D : HomotopyEquivalence g) :
    Term (homogeneousPath (paths a c)
      (ua a c (f ≫ g) (compositeEquivalence a b c f E g D))
      (homogeneousConcat (filling Γ) (filling_lawful Γ) (ua a b f E) (ua b c g D))) := by
  let p := reindexComparison
    (uaComposition compositionSource compositionMiddle compositionTarget
      firstEquivalence.1 firstEquivalence.2 secondEquivalence.1 secondEquivalence.2)
    (classifyComposition a b c f E g D)
  exact relabelComparison p (composition_start a b c f E g D) (composition_finish a b c f E g D)

private theorem identity_square {Γ : Context.{u+1}} (a : Γ ⟶ codes) :
    comparisonSquare (identity a) = restrictSquare (comparisonSquare (uaIdentity (𝟙 codes))) a :=
  (comparisonSquare_relabel (reindexComparison (uaIdentity (𝟙 codes)) a) (identity_start a) rfl).trans
    (comparisonSquare_reindex (uaIdentity (𝟙 codes)) a)

private theorem inverse_square {Γ : Context.{u+1}} (a b : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f) :
    comparisonSquare (inverse a b f E) =
      restrictSquare (comparisonSquare (uaInverse sourceCode targetCode universalEquivalence.1 universalEquivalence.2))
        (classifyEquivalence a b f E) :=
  (comparisonSquare_relabel (reindexComparison
    (uaInverse sourceCode targetCode universalEquivalence.1 universalEquivalence.2)
    (classifyEquivalence a b f E)) (inverse_start a b f E) (inverse_finish a b f E)).trans
    (comparisonSquare_reindex (uaInverse sourceCode targetCode universalEquivalence.1 universalEquivalence.2)
      (classifyEquivalence a b f E))

private theorem composition_square {Γ : Context.{u+1}} (a b c : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (g : liftedDecode b ⟶ liftedDecode c) (D : HomotopyEquivalence g) :
    comparisonSquare (composition a b c f E g D) =
      restrictSquare (comparisonSquare (uaComposition compositionSource compositionMiddle compositionTarget
        firstEquivalence.1 firstEquivalence.2 secondEquivalence.1 secondEquivalence.2))
        (classifyComposition a b c f E g D) :=
  (comparisonSquare_relabel (reindexComparison
    (uaComposition compositionSource compositionMiddle compositionTarget
      firstEquivalence.1 firstEquivalence.2 secondEquivalence.1 secondEquivalence.2)
    (classifyComposition a b c f E g D)) (composition_start a b c f E g D) (composition_finish a b c f E g D)).trans
    (comparisonSquare_reindex (uaComposition compositionSource compositionMiddle compositionTarget
      firstEquivalence.1 firstEquivalence.2 secondEquivalence.1 secondEquivalence.2)
      (classifyComposition a b c f E g D))

/-- Exact recomputation law for the entire chosen identity square. -/
theorem identity_body_reindex {Γ Δ : Context.{u+1}} (a : Γ ⟶ codes) (σ : Δ ⟶ Γ) :
    comparisonSquare (identity (σ ≫ a)) =
      (comparisonSquare (identity a)).reindex
        (liftSub (interval (total (interval Γ))) (liftSub (interval Γ) σ)) :=
  (identity_square (σ ≫ a)).trans
    ((restrictSquare_comp (comparisonSquare (uaIdentity (𝟙 codes))) a σ).symm.trans
      (congrArg (fun z => restrictSquare z σ) (identity_square a).symm))

/-- Exact recomputation retains the whole inverse comparison square. -/
theorem inverse_body_reindex {Γ Δ : Context.{u+1}} (a b : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f) (σ : Δ ⟶ Γ) :
    comparisonSquare (inverse (σ ≫ a) (σ ≫ b) (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)) =
      (comparisonSquare (inverse a b f E)).reindex
        (liftSub (interval (total (interval Γ))) (liftSub (interval Γ) σ)) :=
  (inverse_square (σ ≫ a) (σ ≫ b) (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)).trans
    ((congrArg (restrictSquare (comparisonSquare
      (uaInverse sourceCode targetCode universalEquivalence.1 universalEquivalence.2)))
      (classifyEquivalence_comp a b f E σ).symm).trans
      ((restrictSquare_comp (comparisonSquare
        (uaInverse sourceCode targetCode universalEquivalence.1 universalEquivalence.2))
        (classifyEquivalence a b f E) σ).symm.trans
        (congrArg (fun z => restrictSquare z σ) (inverse_square a b f E).symm)))

/-- Exact recomputation retains the whole binary composition square. -/
theorem composition_body_reindex {Γ Δ : Context.{u+1}} (a b c : Γ ⟶ codes)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (g : liftedDecode b ⟶ liftedDecode c) (D : HomotopyEquivalence g) (σ : Δ ⟶ Γ) :
    comparisonSquare (composition (σ ≫ a) (σ ≫ b) (σ ≫ c)
      (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)
      (Functor.whiskerLeft σ.mapElements g) (D.reindex σ)) =
      (comparisonSquare (composition a b c f E g D)).reindex
        (liftSub (interval (total (interval Γ))) (liftSub (interval Γ) σ)) :=
  (composition_square (σ ≫ a) (σ ≫ b) (σ ≫ c)
    (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)
    (Functor.whiskerLeft σ.mapElements g) (D.reindex σ)).trans
    ((congrArg (restrictSquare (comparisonSquare
      (uaComposition compositionSource compositionMiddle compositionTarget
        firstEquivalence.1 firstEquivalence.2 secondEquivalence.1 secondEquivalence.2)))
      (classifyComposition_comp a b c f E g D σ).symm).trans
      ((restrictSquare_comp (comparisonSquare
        (uaComposition compositionSource compositionMiddle compositionTarget
          firstEquivalence.1 firstEquivalence.2 secondEquivalence.1 secondEquivalence.2))
        (classifyComposition a b c f E g D) σ).symm.trans
        (congrArg (fun z => restrictSquare z σ) (composition_square a b c f E g D).symm)))

end SquareKit.Cubical.Presheaf.SmallUniverse.NaturalUnivalenceLaws
