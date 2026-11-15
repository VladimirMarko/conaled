import SquareKit.Internal.Cubical.NativeUnivalence
import SquareKit.Internal.Cubical.NativeUniverseSquares
import SquareKit.Internal.Cubical.HomotopyEquivalenceComposition
import SquareKit.Internal.Cubical.NativePathComposition
import SquareKit.Internal.Cubical.DependentTransportComposition

/-! Native comparisons between `ua` and paths with the same transport action. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
open CategoryTheory
universe u
variable {Γ : Context.{u+1}} (a b : Γ ⟶ smallFamilyCodes.{u})

/-- Turn an actual transport comparison into a comparison of universe paths.
Both supplied equivalence records are retained before applying univalence. -/
noncomputable def uaOfTransportHomotopy
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (p : Term (paths a b))
    (H : Term (homogeneousPath
      (reindex (liftedDecode b) (projection (liftedDecode a)))
      (Term.map (Functor.whiskerLeft (projection (liftedDecode a)).mapElements f)
        (generic (liftedDecode a)))
      (Term.map (Functor.whiskerLeft (projection (liftedDecode a)).mapElements (pathToMap p))
        (generic (liftedDecode a))))) :
    Term (homogeneousPath (paths a b) (ua a b f E) p) := by
  let c := EquivalencePaths.ofHomotopy f (pathToMap p) H
    (NativeDecode.filling a) (NativeDecode.filling_lawful a)
    (NativeDecode.filling b) (NativeDecode.filling_lawful b) E (pathToEquivalence p)
  let q := homogeneousPathMap (equivToPath a b) c
  have h₀ := equivToPath_beta f E
  have h₁ := pathToEquiv_beta p
  let q' := pathLam (pathApp q)
    ((pathApp_zero q).trans h₀)
    ((pathApp_one q).trans (congrArg (Term.map (equivToPath a b)) h₁))
  exact homogeneousConcat (pathsFilling a b) (pathsFilling_lawful a b) q' (leftInverseAt a b p)

/-- The generic dependent transport specializes to the actual universal El map. -/
theorem pathToMap_along (p : Term (paths a b)) :
    NativeTransportComposition.along (liftedDecode (movingTarget (Γ := Γ))) p
      (NativeDecode.filling (movingTarget (Γ := Γ))) = pathToMap p := rfl

/-- Transport along the constant universe path need not be strictly regular. -/
noncomputable def reflexiveTransportComparison (x : Term (liftedDecode a)) :
    Term (homogeneousPath (liftedDecode a)
      (Term.map (pathToMap (homogeneousRefl (term a))) x) x) :=
  NativeTransportComposition.alongIdentityComparison
    (liftedDecode (movingTarget (Γ := Γ)))
    (NativeDecode.filling (movingTarget (Γ := Γ)))
    (NativeDecode.filling_lawful _) (term a) x

noncomputable def uaIdentity : Term (homogeneousPath (paths a a)
    (ua a a (𝟙 _) (HomotopyEquivalence.ofIso (Iso.refl _)))
    (homogeneousRefl (term a))) := by
  let σ := projection (liftedDecode a)
  let p := homogeneousRefl (term a)
  let h := reflexiveTransportComparison (σ ≫ a) (generic (liftedDecode a))
  have hm := pathToMap_reindex p σ
  let q := pathLam (pathApp h)
    ((pathApp_zero h).trans (congrArg (fun k => Term.map k (generic (liftedDecode a))) hm.symm))
    (pathApp_one h)
  exact uaOfTransportHomotopy a a (𝟙 _) (HomotopyEquivalence.ofIso (Iso.refl _)) p
    (homogeneousReverse q)

section Composition
variable (c : Γ ⟶ smallFamilyCodes.{u})

/-- The selected universal transport respects concatenation through a native path. -/
noncomputable def concatTransportComparison (p : Term (paths a b)) (q : Term (paths b c))
    (x : Term (liftedDecode a)) : Term (homogeneousPath (liftedDecode c)
      (Term.map (pathToMap (homogeneousConcat (filling Γ) (filling_lawful Γ) p q)) x)
      (Term.map (pathToMap q) (Term.map (pathToMap p) x))) :=
  by
  let h := NativeTransportComposition.concatComparison (filling Γ) (filling_lawful Γ)
    (liftedDecode (movingTarget (Γ := Γ)))
    (NativeDecode.filling (movingTarget (Γ := Γ))) (NativeDecode.filling_lawful _)
    p q x
  have h₀ := congrArg (fun k => Term.map k x)
    (pathToMap_along a c (homogeneousConcat (filling Γ) (filling_lawful Γ) p q))
  let tp := NativeTransportComposition.along (liftedDecode (movingTarget (Γ := Γ))) p
    (NativeDecode.filling (movingTarget (Γ := Γ)))
  have h₁ := congrArg (fun k => Term.map k (Term.map tp x)) (pathToMap_along b c q)
  have h₂ := congrArg (fun k => Term.map (pathToMap q) (Term.map k x)) (pathToMap_along a b p)
  exact pathLam (pathApp h) ((pathApp_zero h).trans h₀)
    ((pathApp_one h).trans (h₁.trans h₂))

noncomputable def sequentialTransportComparison
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (g : liftedDecode b ⟶ liftedDecode c) (D : HomotopyEquivalence g)
    (x : Term (liftedDecode a)) : Term (homogeneousPath (liftedDecode c)
      (Term.map (f ≫ g) x)
      (Term.map (pathToMap (ua b c g D)) (Term.map (pathToMap (ua a b f E)) x))) :=
  homogeneousConcat (NativeDecode.filling c) (NativeDecode.filling_lawful c)
    (homogeneousPathMap g (uaComparison a b f E x))
    (uaComparison b c g D (Term.map (pathToMap (ua a b f E)) x))

/-- For two arbitrary genuine equivalences, the composed map agrees with
transport along the concatenation of their constructed universe paths. -/
noncomputable def compositeTransportComparison
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (g : liftedDecode b ⟶ liftedDecode c) (D : HomotopyEquivalence g)
    (x : Term (liftedDecode a)) : Term (homogeneousPath (liftedDecode c)
      (Term.map (f ≫ g) x)
      (Term.map (pathToMap (homogeneousConcat (filling Γ) (filling_lawful Γ)
        (ua a b f E) (ua b c g D))) x)) := by
  exact homogeneousConcat (NativeDecode.filling c) (NativeDecode.filling_lawful c)
    (sequentialTransportComparison a b c f E g D x)
    (homogeneousReverse (concatTransportComparison a b c (ua a b f E) (ua b c g D) x))

theorem uaConcat_reindex {Δ : Context.{u+1}}
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (g : liftedDecode b ⟶ liftedDecode c) (D : HomotopyEquivalence g) (σ : Δ ⟶ Γ) :
    homogeneousReindex (homogeneousConcat (filling Γ) (filling_lawful Γ)
      (ua a b f E) (ua b c g D)) σ =
    homogeneousConcat (filling Δ) (filling_lawful Δ)
      (ua (σ ≫ a) (σ ≫ b) (Functor.whiskerLeft σ.mapElements f) (E.reindex σ))
      (ua (σ ≫ b) (σ ≫ c) (Functor.whiskerLeft σ.mapElements g) (D.reindex σ)) :=
  (homogeneousConcat_reindex (filling Γ) (filling_lawful Γ) (ua a b f E) (ua b c g D) σ).trans
    (congrArg₂ (homogeneousConcat (filling Δ) (filling_lawful Δ))
      (ua_reindex a b f E σ) (ua_reindex b c g D σ))

noncomputable def compositeMapHomotopy
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (g : liftedDecode b ⟶ liftedDecode c) (D : HomotopyEquivalence g) :
    Term (homogeneousPath (reindex (liftedDecode c) (projection (liftedDecode a)))
      (Term.map (Functor.whiskerLeft (projection (liftedDecode a)).mapElements (f ≫ g))
        (generic (liftedDecode a)))
      (Term.map (Functor.whiskerLeft (projection (liftedDecode a)).mapElements
        (pathToMap (homogeneousConcat (filling Γ) (filling_lawful Γ)
          (ua a b f E) (ua b c g D)))) (generic (liftedDecode a)))) := by
  let σ := projection (liftedDecode a)
  let p := homogeneousConcat (filling Γ) (filling_lawful Γ) (ua a b f E) (ua b c g D)
  let h := compositeTransportComparison (σ ≫ a) (σ ≫ b) (σ ≫ c)
    (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)
    (Functor.whiskerLeft σ.mapElements g) (D.reindex σ) (generic (liftedDecode a))
  have hm := (pathToMap_reindex p σ).trans
    (congrArg pathToMap (uaConcat_reindex a b c f E g D σ))
  exact pathLam (pathApp h) (pathApp_zero h)
    ((pathApp_one h).trans (congrArg (fun k => Term.map k (generic (liftedDecode a))) hm.symm))

/-- The result retains any supplied genuine composite witness, including its
chosen contractions. The canonical composite supplies this argument below. -/
noncomputable def uaCompositeOfWitness
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (g : liftedDecode b ⟶ liftedDecode c) (D : HomotopyEquivalence g)
    (C : HomotopyEquivalence (f ≫ g)) :
    Term (homogeneousPath (paths a c) (ua a c (f ≫ g) C)
      (homogeneousConcat (filling Γ) (filling_lawful Γ) (ua a b f E) (ua b c g D))) :=
  uaOfTransportHomotopy a c (f ≫ g) C _ (compositeMapHomotopy a b c f E g D)

noncomputable def compositeEquivalence
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (g : liftedDecode b ⟶ liftedDecode c) (D : HomotopyEquivalence g) :
    HomotopyEquivalence (f ≫ g) :=
  E.comp D (NativeDecode.filling a) (NativeDecode.filling_lawful a)
    (NativeDecode.filling b) (NativeDecode.filling_lawful b)
    (NativeDecode.filling c) (NativeDecode.filling_lawful c)

noncomputable def uaComposition
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
    (g : liftedDecode b ⟶ liftedDecode c) (D : HomotopyEquivalence g) :
    Term (homogeneousPath (paths a c)
      (ua a c (f ≫ g) (compositeEquivalence a b c f E g D))
      (homogeneousConcat (filling Γ) (filling_lawful Γ) (ua a b f E) (ua b c g D))) :=
  uaCompositeOfWitness a b c f E g D (compositeEquivalence a b c f E g D)

end Composition

noncomputable def reverseTransportLeft (p : Term (paths a b)) (x : Term (liftedDecode a)) :
    Term (homogeneousPath (liftedDecode a)
      (Term.map (pathToMap (homogeneousReverse p)) (Term.map (pathToMap p) x)) x) := by
  let h := NativeTransportComposition.reverseLeftComparison
    (liftedDecode (movingTarget (Γ := Γ))) p
    (NativeDecode.filling (movingTarget (Γ := Γ))) (NativeDecode.filling_lawful _) x
  let tp := NativeTransportComposition.along (liftedDecode (movingTarget (Γ := Γ))) p
    (NativeDecode.filling (movingTarget (Γ := Γ)))
  have h₀ := congrArg (fun k => Term.map k (Term.map tp x))
    (pathToMap_along b a (homogeneousReverse p))
  have h₁ := congrArg (fun k => Term.map (pathToMap (homogeneousReverse p)) (Term.map k x))
    (pathToMap_along a b p)
  exact pathLam (pathApp h) ((pathApp_zero h).trans (h₀.trans h₁)) (pathApp_one h)

noncomputable def reverseTransportRight (p : Term (paths a b)) (x : Term (liftedDecode b)) :
    Term (homogeneousPath (liftedDecode b)
      (Term.map (pathToMap p) (Term.map (pathToMap (homogeneousReverse p)) x)) x) := by
  let h := NativeTransportComposition.reverseRightComparison
    (liftedDecode (movingTarget (Γ := Γ))) p
    (NativeDecode.filling (movingTarget (Γ := Γ))) (NativeDecode.filling_lawful _) x
  let tp := NativeTransportComposition.along (liftedDecode (movingTarget (Γ := Γ)))
    (homogeneousReverse p) (NativeDecode.filling (movingTarget (Γ := Γ)))
  have h₀ := congrArg (fun k => Term.map k (Term.map tp x)) (pathToMap_along a b p)
  have h₁ := congrArg (fun k => Term.map (pathToMap p) (Term.map k x))
    (pathToMap_along b a (homogeneousReverse p))
  exact pathLam (pathApp h) ((pathApp_zero h).trans (h₀.trans h₁)) (pathApp_one h)

theorem reverseMap_reindex {Δ : Context.{u+1}} (p : Term (paths a b)) (σ : Δ ⟶ Γ) :
    Functor.whiskerLeft σ.mapElements (pathToMap (homogeneousReverse p)) =
      pathToMap (homogeneousReverse (reindexPath p σ)) :=
  (pathToMap_reindex (homogeneousReverse p) σ).trans
    (congrArg pathToMap (homogeneousReindex_reverse p σ))

section Inverse
variable (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)

/-- An inverse selected by actual universal transport along the reversed Glue path. -/
noncomputable def inverseMap : liftedDecode b ⟶ liftedDecode a :=
  pathToMap (homogeneousReverse (ua a b f E))

noncomputable def inverseEquivalence : HomotopyEquivalence (inverseMap a b f E) :=
  pathToEquivalence (homogeneousReverse (ua a b f E))

noncomputable def uaInverse : Term (homogeneousPath (paths b a)
    (ua b a (inverseMap a b f E) (inverseEquivalence a b f E))
    (homogeneousReverse (ua a b f E))) :=
  uaOfTransportHomotopy b a _ (inverseEquivalence a b f E) _ (homogeneousRefl _)

/-- The chosen inverse is a left inverse of the original arbitrary map. -/
noncomputable def inverseLeft (x : Term (liftedDecode a)) :
    Term (homogeneousPath (liftedDecode a)
      (Term.map (inverseMap a b f E) (Term.map f x)) x) :=
  homogeneousConcat (NativeDecode.filling a) (NativeDecode.filling_lawful a)
    (homogeneousPathMap (inverseMap a b f E) (uaComparison a b f E x))
    (reverseTransportLeft a b (ua a b f E) x)

/-- The same chosen inverse is a right inverse, with a native witness. -/
noncomputable def inverseRight (x : Term (liftedDecode b)) :
    Term (homogeneousPath (liftedDecode b)
      (Term.map f (Term.map (inverseMap a b f E) x)) x) :=
  homogeneousConcat (NativeDecode.filling b) (NativeDecode.filling_lawful b)
    (uaComparison a b f E (Term.map (inverseMap a b f E) x))
    (reverseTransportRight a b (ua a b f E) x)

theorem inverseMap_reindex {Δ : Context.{u+1}} (σ : Δ ⟶ Γ) :
    Functor.whiskerLeft σ.mapElements (inverseMap a b f E) =
      inverseMap (σ ≫ a) (σ ≫ b) (Functor.whiskerLeft σ.mapElements f) (E.reindex σ) :=
  (reverseMap_reindex a b (ua a b f E) σ).trans
    (congrArg (fun p => pathToMap (homogeneousReverse p)) (ua_reindex a b f E σ))

theorem inverseEquivalence_reindex {Δ : Context.{u+1}} (σ : Δ ⟶ Γ) :
    HEq ((inverseEquivalence a b f E).reindex σ)
      (inverseEquivalence (σ ≫ a) (σ ≫ b) (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)) := by
  have hp := congrArg homogeneousReverse (ua_reindex a b f E σ)
  have hE : ∀ (p q : Term (paths (σ ≫ b) (σ ≫ a))), p = q →
      HEq (pathToEquivalence p) (pathToEquivalence q) := by
    intro p q h
    cases h
    rfl
  exact (pathToEquivalence_reindex (homogeneousReverse (ua a b f E)) σ).trans (hE _ _ hp)

end Inverse

section ThreeChanges
variable (c d : Γ ⟶ smallFamilyCodes.{u})
variable (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f)
variable (g : liftedDecode b ⟶ liftedDecode c) (D : HomotopyEquivalence g)
variable (h : liftedDecode c ⟶ liftedDecode d) (K : HomotopyEquivalence h)

noncomputable def leftTriplePath : Term (paths a d) :=
  homogeneousConcat (filling Γ) (filling_lawful Γ)
    (homogeneousConcat (filling Γ) (filling_lawful Γ) (ua a b f E) (ua b c g D))
    (ua c d h K)

noncomputable def rightTriplePath : Term (paths a d) :=
  homogeneousConcat (filling Γ) (filling_lawful Γ) (ua a b f E)
    (homogeneousConcat (filling Γ) (filling_lawful Γ) (ua b c g D) (ua c d h K))

noncomputable def leftTripleSequential (x : Term (liftedDecode a)) :
    Term (homogeneousPath (liftedDecode d) (Term.map ((f ≫ g) ≫ h) x)
      (Term.map (pathToMap (ua c d h K))
        (Term.map (pathToMap (homogeneousConcat (filling Γ) (filling_lawful Γ)
          (ua a b f E) (ua b c g D))) x))) :=
  homogeneousConcat (NativeDecode.filling d) (NativeDecode.filling_lawful d)
    (homogeneousPathMap h (compositeTransportComparison a b c f E g D x))
    (uaComparison c d h K (Term.map (pathToMap
      (homogeneousConcat (filling Γ) (filling_lawful Γ) (ua a b f E) (ua b c g D))) x))

noncomputable def leftTripleTransport (x : Term (liftedDecode a)) :
    Term (homogeneousPath (liftedDecode d) (Term.map ((f ≫ g) ≫ h) x)
      (Term.map (pathToMap (leftTriplePath a b c d f E g D h K)) x)) := by
  unfold leftTriplePath
  exact homogeneousConcat (NativeDecode.filling d) (NativeDecode.filling_lawful d)
    (leftTripleSequential a b c d f E g D h K x)
    (homogeneousReverse (concatTransportComparison a c d
      (homogeneousConcat (filling Γ) (filling_lawful Γ) (ua a b f E) (ua b c g D))
      (ua c d h K) x))

noncomputable def rightTripleSequential (x : Term (liftedDecode a)) :
    Term (homogeneousPath (liftedDecode d) (Term.map ((f ≫ g) ≫ h) x)
      (Term.map (pathToMap (homogeneousConcat (filling Γ) (filling_lawful Γ)
        (ua b c g D) (ua c d h K))) (Term.map (pathToMap (ua a b f E)) x))) :=
  homogeneousConcat (NativeDecode.filling d) (NativeDecode.filling_lawful d)
    (homogeneousPathMap (g ≫ h) (uaComparison a b f E x))
    (compositeTransportComparison b c d g D h K (Term.map (pathToMap (ua a b f E)) x))

noncomputable def rightTripleTransport (x : Term (liftedDecode a)) :
    Term (homogeneousPath (liftedDecode d) (Term.map ((f ≫ g) ≫ h) x)
      (Term.map (pathToMap (rightTriplePath a b c d f E g D h K)) x)) := by
  unfold rightTriplePath
  exact homogeneousConcat (NativeDecode.filling d) (NativeDecode.filling_lawful d)
    (rightTripleSequential a b c d f E g D h K x)
    (homogeneousReverse (concatTransportComparison a b d (ua a b f E)
      (homogeneousConcat (filling Γ) (filling_lawful Γ) (ua b c g D) (ua c d h K)) x))

theorem leftTriplePath_reindex {Δ : Context.{u+1}} (σ : Δ ⟶ Γ) :
    homogeneousReindex (leftTriplePath a b c d f E g D h K) σ =
      leftTriplePath (σ ≫ a) (σ ≫ b) (σ ≫ c) (σ ≫ d)
        (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)
        (Functor.whiskerLeft σ.mapElements g) (D.reindex σ)
        (Functor.whiskerLeft σ.mapElements h) (K.reindex σ) :=
  (homogeneousConcat_reindex (filling Γ) (filling_lawful Γ)
    (homogeneousConcat (filling Γ) (filling_lawful Γ) (ua a b f E) (ua b c g D))
    (ua c d h K) σ).trans
    (congrArg₂ (homogeneousConcat (filling Δ) (filling_lawful Δ))
      (uaConcat_reindex a b c f E g D σ) (ua_reindex c d h K σ))

theorem rightTriplePath_reindex {Δ : Context.{u+1}} (σ : Δ ⟶ Γ) :
    homogeneousReindex (rightTriplePath a b c d f E g D h K) σ =
      rightTriplePath (σ ≫ a) (σ ≫ b) (σ ≫ c) (σ ≫ d)
        (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)
        (Functor.whiskerLeft σ.mapElements g) (D.reindex σ)
        (Functor.whiskerLeft σ.mapElements h) (K.reindex σ) :=
  (homogeneousConcat_reindex (filling Γ) (filling_lawful Γ) (ua a b f E)
    (homogeneousConcat (filling Γ) (filling_lawful Γ) (ua b c g D) (ua c d h K)) σ).trans
    (congrArg₂ (homogeneousConcat (filling Δ) (filling_lawful Δ))
      (ua_reindex a b f E σ) (uaConcat_reindex b c d g D h K σ))

noncomputable def leftTripleMapHomotopy :
    Term (homogeneousPath (reindex (liftedDecode d) (projection (liftedDecode a)))
      (Term.map (Functor.whiskerLeft (projection (liftedDecode a)).mapElements ((f ≫ g) ≫ h))
        (generic (liftedDecode a)))
      (Term.map (Functor.whiskerLeft (projection (liftedDecode a)).mapElements
        (pathToMap (leftTriplePath a b c d f E g D h K))) (generic (liftedDecode a)))) := by
  let σ := projection (liftedDecode a)
  let p := leftTriplePath a b c d f E g D h K
  let q := leftTripleTransport (σ ≫ a) (σ ≫ b) (σ ≫ c) (σ ≫ d)
    (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)
    (Functor.whiskerLeft σ.mapElements g) (D.reindex σ)
    (Functor.whiskerLeft σ.mapElements h) (K.reindex σ) (generic (liftedDecode a))
  have hm := (pathToMap_reindex p σ).trans
    (congrArg pathToMap (leftTriplePath_reindex a b c d f E g D h K σ))
  exact pathLam (pathApp q) (pathApp_zero q)
    ((pathApp_one q).trans (congrArg (fun k => Term.map k (generic (liftedDecode a))) hm.symm))

noncomputable def rightTripleMapHomotopy :
    Term (homogeneousPath (reindex (liftedDecode d) (projection (liftedDecode a)))
      (Term.map (Functor.whiskerLeft (projection (liftedDecode a)).mapElements ((f ≫ g) ≫ h))
        (generic (liftedDecode a)))
      (Term.map (Functor.whiskerLeft (projection (liftedDecode a)).mapElements
        (pathToMap (rightTriplePath a b c d f E g D h K))) (generic (liftedDecode a)))) := by
  let σ := projection (liftedDecode a)
  let p := rightTriplePath a b c d f E g D h K
  let q := rightTripleTransport (σ ≫ a) (σ ≫ b) (σ ≫ c) (σ ≫ d)
    (Functor.whiskerLeft σ.mapElements f) (E.reindex σ)
    (Functor.whiskerLeft σ.mapElements g) (D.reindex σ)
    (Functor.whiskerLeft σ.mapElements h) (K.reindex σ) (generic (liftedDecode a))
  have hm := (pathToMap_reindex p σ).trans
    (congrArg pathToMap (rightTriplePath_reindex a b c d f E g D h K σ))
  exact pathLam (pathApp q) (pathApp_zero q)
    ((pathApp_one q).trans (congrArg (fun k => Term.map k (generic (liftedDecode a))) hm.symm))

noncomputable def tripleEquivalence : HomotopyEquivalence ((f ≫ g) ≫ h) :=
  compositeEquivalence a c d (f ≫ g) (compositeEquivalence a b c f E g D) h K

noncomputable def tripleLeftComparison : Term (homogeneousPath (paths a d)
    (ua a d ((f ≫ g) ≫ h) (tripleEquivalence a b c d f E g D h K))
    (leftTriplePath a b c d f E g D h K)) :=
  uaOfTransportHomotopy a d _ (tripleEquivalence a b c d f E g D h K) _
    (leftTripleMapHomotopy a b c d f E g D h K)

noncomputable def tripleRightComparison : Term (homogeneousPath (paths a d)
    (ua a d ((f ≫ g) ≫ h) (tripleEquivalence a b c d f E g D h K))
    (rightTriplePath a b c d f E g D h K)) :=
  uaOfTransportHomotopy a d _ (tripleEquivalence a b c d f E g D h K) _
    (rightTripleMapHomotopy a b c d f E g D h K)

/-- A two-dimensional comparison of the two triple bracketings. This does not
assert equality of independently chosen two-paths or a pentagon law. -/
noncomputable def tripleComparison : Term (homogeneousPath (paths a d)
    (leftTriplePath a b c d f E g D h K) (rightTriplePath a b c d f E g D h K)) :=
  homogeneousConcat (pathsFilling a d) (pathsFilling_lawful a d)
    (homogeneousReverse (tripleLeftComparison a b c d f E g D h K))
    (tripleRightComparison a b c d f E g D h K)

/-- The actual code-valued square of the triple two-path. -/
noncomputable def tripleSquare : Term (family (total (interval (total (interval Γ))))) :=
  comparisonSquare (tripleComparison a b c d f E g D h K)

theorem tripleSquare_left :
    (tripleSquare a b c d f E g D h K).reindex (endpointSub (total (interval Γ)) false) =
      term (projection (interval Γ) ≫ a) :=
  comparisonSquare_left (tripleComparison a b c d f E g D h K)

theorem tripleSquare_right :
    (tripleSquare a b c d f E g D h K).reindex (endpointSub (total (interval Γ)) true) =
      term (projection (interval Γ) ≫ d) :=
  comparisonSquare_right (tripleComparison a b c d f E g D h K)

theorem tripleSquare_bottom :
    (tripleSquare a b c d f E g D h K).reindex
      (liftSub (interval (total (interval Γ))) (endpointSub Γ false)) =
      pathApp (leftTriplePath a b c d f E g D h K) :=
  comparisonSquare_zero (tripleComparison a b c d f E g D h K)

theorem tripleSquare_top :
    (tripleSquare a b c d f E g D h K).reindex
      (liftSub (interval (total (interval Γ))) (endpointSub Γ true)) =
      pathApp (rightTriplePath a b c d f E g D h K) :=
  comparisonSquare_one (tripleComparison a b c d f E g D h K)

end ThreeChanges

end SquareKit.Cubical.Presheaf.SmallUniverse.NativeUnivalence
