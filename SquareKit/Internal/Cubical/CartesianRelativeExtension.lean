import SquareKit.Internal.Cubical.CartesianEquivalenceExtension

/-!
Cartesian square filling contracts the forward based-path singleton and constructs
a weak connection with prescribed edges. Complete equivalence records transport
sections and loops, with exact evaluation and substitution laws.
-/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory
universe u
namespace ForwardSingleton
variable {Γ : Context.{u}} (A : Family Γ) (a : Term A)

def paths : Family (total A) :=
  homogeneousPath (reindex A (projection A)) (Term.reindex a (projection A)) (generic A)

def family : Family Γ := sigma A (paths A a)

variable {Δ Θ : Context.{u}}

def fstOver (σ : Δ ⟶ Γ) (z : Term (reindex (family A a) σ)) : Term (reindex A σ) :=
  sigmaFst (B := reindex (paths A a) (liftSub A σ)) z

def introOver (σ : Δ ⟶ Γ) (b : Term (reindex A σ))
    (p : Term (homogeneousPath (reindex A σ) (Term.reindex a σ) b)) :
    Term (reindex (family A a) σ) :=
  sigmaIntro (B := reindex (paths A a) (liftSub A σ)) b
    (Term.map (pathReindexIso (intervalCoefficient (reindex A (projection A)))
      (Term.reindex a (projection A)) (generic A) (pair σ b)).inv p)

def pathOver (σ : Δ ⟶ Γ) (z : Term (reindex (family A a) σ)) :
    Term (homogeneousPath (reindex A σ) (Term.reindex a σ) (fstOver A a σ z)) :=
  Term.map (pathReindexIso (intervalCoefficient (reindex A (projection A)))
    (Term.reindex a (projection A)) (generic A) (pair σ (fstOver A a σ z))).hom
      (sigmaSnd (B := reindex (paths A a) (liftSub A σ)) z)

theorem introOver_eta (σ : Δ ⟶ Γ) (z : Term (reindex (family A a) σ)) :
    introOver A a σ (fstOver A a σ z) (pathOver A a σ z) = z := by
  let e := pathReindexIso (intervalCoefficient (reindex A (projection A)))
    (Term.reindex a (projection A)) (generic A) (pair σ (fstOver A a σ z))
  exact congrArg (sigmaIntro (B := reindex (paths A a) (liftSub A σ)) (fstOver A a σ z))
    (Term.map_iso_roundtrip e (sigmaSnd (B := reindex (paths A a) (liftSub A σ)) z))

theorem introOver_reindex (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (b : Term (reindex A σ))
    (p : Term (homogeneousPath (reindex A σ) (Term.reindex a σ) b)) :
    Term.reindex (introOver A a σ b p) τ =
      introOver A a (τ ≫ σ) (Term.reindex b τ) (homogeneousReindex p τ) := by
  exact congrArg (sigmaIntro (B := reindex (paths A a) (liftSub A (τ ≫ σ))) (Term.reindex b τ))
    (Homotopy.pathInverse_reindex (intervalCoefficient (reindex A (projection A)))
      (Term.reindex a (projection A)) (generic A) (pair σ b) τ p)

theorem introOver_congr (σ : Δ ⟶ Γ) (b b' : Term (reindex A σ))
    (p : Term (homogeneousPath (reindex A σ) (Term.reindex a σ) b))
    (p' : Term (homogeneousPath (reindex A σ) (Term.reindex a σ) b'))
    (hb : b = b') (hp : HEq (pathApp p) (pathApp p')) :
    introOver A a σ b p = introOver A a σ b' p' := by
  subst b'
  have h := pathApp_injective (eq_of_heq hp)
  subst p'
  rfl

noncomputable def contractible (F : Filling A) (hF : F.Lawful) : Contractible (family A a) := by
  let S := family A a
  let σ := projection S
  let b := fstOver A a σ (generic S)
  let p := pathOver A a σ (generic S)
  let c := Term.reindex (Term.reindex a σ) (projection (interval (total S)))
  let q := NativeSquare.fill (F.reindex σ) false c (pathApp p) c rfl (pathApp_zero p).symm
  let d := NativeSquare.slice q true
  let v : Term (homogeneousPath (intervalCoefficient (reindex A σ)) c d) :=
    pathLam q (NativeSquare.fill_source (F.reindex σ) (hF.reindex σ)
      false c (pathApp p) c rfl (pathApp_zero p).symm) rfl
  let body := introOver A a (projection (interval (total S)) ≫ σ) d v
  let center := introOver A a (𝟙 Γ) a (homogeneousRefl a)
  have hzero : Term.reindex body (endpointSub (total S) false) = Term.reindex center σ := by
    refine (introOver_reindex A a (projection (interval (total S)) ≫ σ)
      (endpointSub (total S) false) d v).trans ?_
    change introOver A a σ _ _ = _
    have hc : Term.reindex center σ = introOver A a σ (Term.reindex a σ)
        (homogeneousReindex (homogeneousRefl a) σ) :=
      introOver_reindex A a (𝟙 Γ) σ a (homogeneousRefl a)
    rw [hc]
    apply introOver_congr
    · exact NativeSquare.slice_left (F.reindex σ) (hF.reindex σ)
        false c (pathApp p) c rfl (pathApp_zero p).symm true
    · exact heq_of_eq (NativeSquare.fill_left (F.reindex σ) (hF.reindex σ)
        false c (pathApp p) c rfl (pathApp_zero p).symm)
  have hone : Term.reindex body (endpointSub (total S) true) = generic S := by
    refine (introOver_reindex A a (projection (interval (total S)) ≫ σ)
      (endpointSub (total S) true) d v).trans ?_
    change introOver A a σ _ _ = _
    rw [← introOver_eta A a σ (generic S)]
    apply introOver_congr
    · exact (NativeSquare.slice_right (F.reindex σ) (hF.reindex σ)
        false c (pathApp p) c rfl (pathApp_zero p).symm true).trans (pathApp_one p)
    · exact heq_of_eq (NativeSquare.fill_right (F.reindex σ) (hF.reindex σ)
        false c (pathApp p) c rfl (pathApp_zero p).symm)
  exact Contractible.ofContraction center (pathLam body hzero hone)

end ForwardSingleton
theorem Contractible.map_reindex {Γ Δ : Context.{u}} {A B : Family Γ}
    (e : A ≅ B) (c : Contractible A) (σ : Δ ⟶ Γ) :
    (Contractible.map e c).reindex σ =
      Contractible.map (Functor.isoWhiskerLeft σ.mapElements e) (c.reindex σ) := rfl

theorem Contractible.map_trans {Γ : Context.{u}} {A B C : Family Γ}
    (e : A ≅ B) (d : B ≅ C) (c : Contractible A) :
    Contractible.map d (Contractible.map e c) = Contractible.map (e ≪≫ d) c := rfl

theorem Homotopy.fiberReindexIso_comp {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (b : Term B) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    Functor.isoWhiskerLeft τ.mapElements (fiberReindexIso f b σ) ≪≫
      fiberReindexIso (Functor.whiskerLeft σ.mapElements f) (Term.reindex b σ) τ =
        fiberReindexIso f b (τ ≫ σ) := by
  apply Iso.ext
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem Homotopy.fiberReindexInverse_map {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (b : Term B) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (c : Contractible (fiber (Functor.whiskerLeft σ.mapElements f) (Term.reindex b σ))) :
    Contractible.map (fiberReindexIso f b (τ ≫ σ)).symm
      (Contractible.map (fiberReindexIso (Functor.whiskerLeft σ.mapElements f) (Term.reindex b σ) τ)
        (c.reindex τ)) =
      (Contractible.map (fiberReindexIso f b σ).symm c).reindex τ := by
  rw [Contractible.map_reindex, Contractible.map_trans]
  apply congrArg (fun e => Contractible.map e (c.reindex τ))
  rw [← fiberReindexIso_comp f b σ τ]
  simp
  rfl

namespace EquivalenceFamilies
theorem decodeContr_reindex {Γ Δ : Context.{u}} (A : Family Γ)
    (s : Term (contr A)) (σ : Δ ⟶ Γ) :
    decodeContr (Term.map (contrReindexIso A σ).hom (Term.reindex s σ)) =
      (decodeContr s).reindex σ := by
  apply Contractible.ext rfl
  intro x a y f r
  rfl

theorem encodeContr_reindex {Γ Δ : Context.{u}} {A : Family Γ}
    (c : Contractible A) (σ : Δ ⟶ Γ) :
    Term.map (contrReindexIso A σ).hom (Term.reindex (encodeContr c) σ) =
      encodeContr (c.reindex σ) := by
  apply (contrSections (reindex A σ)).symm.injective
  change decodeContr _ = decodeContr _
  rw [decodeContr_reindex, decode_encodeContr, decode_encodeContr]

theorem piInverse_reindex {Γ Δ Θ : Context.{u}} (A : Family Γ) (B : Family (total A))
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (p : Term (pi (reindex A σ) (reindex B (liftSub A σ)))) :
    Term.reindex (Term.map (piReindexIso A B σ).inv p) τ =
      Term.map (piReindexIso A B (τ ≫ σ)).inv
        (Term.map (piReindexIso (reindex A σ) (reindex B (liftSub A σ)) τ).hom (Term.reindex p τ)) := by
  let e := piReindexIso A B σ
  let d := piReindexIso (reindex A σ) (reindex B (liftSub A σ)) τ
  let c := piReindexIso A B (τ ≫ σ)
  apply Term.map_injective_of_iso c
  apply Term.ext
  intro x
  exact (congrArg (d.hom.app x) (e.inv_hom_id_app_apply (τ.mapElements.obj x)
    (p.val (τ.mapElements.obj x)))).trans
    (c.inv_hom_id_app_apply x (d.hom.app x (p.val (τ.mapElements.obj x)))).symm

theorem contrInverse_reindex {Γ Δ Θ : Context.{u}} (A : Family Γ)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (p : Term (contr (reindex A σ))) :
    Term.reindex (Term.map (contrReindexIso A σ).inv p) τ =
      Term.map (contrReindexIso A (τ ≫ σ)).inv
        (Term.map (contrReindexIso (reindex A σ) τ).hom (Term.reindex p τ)) := by
  let e := contrReindexIso A σ
  let d := contrReindexIso (reindex A σ) τ
  let c := contrReindexIso A (τ ≫ σ)
  apply Term.map_injective_of_iso c
  apply Term.ext
  intro x
  exact (congrArg (d.hom.app x) (e.inv_hom_id_app_apply (τ.mapElements.obj x)
    (p.val (τ.mapElements.obj x)))).trans
    (c.inv_hom_id_app_apply x (d.hom.app x (p.val (τ.mapElements.obj x)))).symm

/-- The reindexed section bridge agrees with native equivalence substitution, retaining choices. -/
theorem isEquivReindexSections_reindex {Γ Δ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (e : HomotopyEquivalence f) (σ : Δ ⟶ Γ) :
    isEquivReindexSections f σ (e.reindex σ) = Term.reindex (encodeIsEquiv e) σ := by
  let C := Homotopy.fiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)
  let τ := liftSub B σ
  let q := contrReindexIso C τ
  let p := piReindexIso B (contr C) σ
  let i := Homotopy.fiberReindexIso (Functor.whiskerLeft (projection B).mapElements f) (generic B) (liftSub B σ)
  have hc := contrTransport_roundtrip i (e.fibers.reindex τ)
  have hq : Term.map q.inv (encodeContr (e.fibers.reindex τ)) = Term.reindex (encodeContr e.fibers) τ :=
    (congrArg (Term.map q.inv) (encodeContr_reindex e.fibers τ).symm).trans
      (Term.map_iso_roundtrip q (Term.reindex (encodeContr e.fibers) τ))
  have hp : Term.map p.hom (Term.reindex (encodeIsEquiv e) σ) =
      lam (Term.reindex (encodeContr e.fibers) τ) := lam_reindex (encodeContr e.fibers) σ
  exact (congrArg (fun c => Term.map p.inv (lam (Term.map q.inv (encodeContr c)))) hc).trans
    ((congrArg (fun t => Term.map p.inv (lam t)) hq).trans
      ((congrArg (Term.map p.inv) hp.symm).trans
        (Term.map_iso_roundtrip p (Term.reindex (encodeIsEquiv e) σ))))

set_option backward.isDefEq.respectTransparency false in
theorem reindexedIsEquivSections_comp {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (c : Contractible (reindex (Homotopy.genericFiber f) (liftSub B σ))) :
    Term.reindex (reindexedIsEquivSections f σ c) τ =
      reindexedIsEquivSections f (τ ≫ σ) (c.reindex (liftSub (reindex B σ) τ)) := by
  let C := Homotopy.genericFiber f
  change Term.reindex (Term.map (piReindexIso B (contr C) σ).inv
    (lam (Term.map (contrReindexIso C (liftSub B σ)).inv (encodeContr c)))) τ =
      Term.map (piReindexIso B (contr C) (τ ≫ σ)).inv
        (lam (Term.map (contrReindexIso C (liftSub B (τ ≫ σ))).inv
          (encodeContr (c.reindex (liftSub (reindex B σ) τ)))))
  rw [piInverse_reindex]
  rw [show (piReindexIso (reindex B σ) (reindex (contr C) (liftSub B σ)) τ).hom =
    piReindex (reindex B σ) (reindex (contr C) (liftSub B σ)) τ from rfl]
  rw [lam_reindex]
  apply congrArg (Term.map (piReindexIso B (contr C) (τ ≫ σ)).inv)
  apply congrArg lam
  rw [contrInverse_reindex, encodeContr_reindex]
  rfl

/-- Sequential substitution preserves every chosen fiber contraction. -/
theorem isEquivReindexSections_comp {Γ Δ Θ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (E : HomotopyEquivalence (Functor.whiskerLeft σ.mapElements f)) :
    Term.reindex (isEquivReindexSections f σ E) τ =
      isEquivReindexSections f (τ ≫ σ) (E.reindex τ) := by
  let i := Homotopy.fiberReindexIso (Functor.whiskerLeft (projection B).mapElements f)
    (generic B) (liftSub B σ)
  change Term.reindex (reindexedIsEquivSections f σ (Contractible.map i.symm E.fibers)) τ = _
  rw [reindexedIsEquivSections_comp]
  apply congrArg (reindexedIsEquivSections f (τ ≫ σ))
  exact (Homotopy.fiberReindexInverse_map
    (Functor.whiskerLeft (projection B).mapElements f) (generic B) (liftSub B σ)
    (liftSub (reindex B σ) τ) E.fibers).symm

/-- Reindexing of the native map family retains every generalized argument. -/
noncomputable def mapReindexSections {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ) :
    (reindex A σ ⟶ reindex B σ) ≃ Term (reindex (maps A B) σ) :=
  (mapSections (reindex A σ) (reindex B σ)).trans {
    toFun := Term.map (piReindexIso A (reindex B (projection A)) σ).inv
    invFun := Term.map (piReindexIso A (reindex B (projection A)) σ).hom
    left_inv := Term.map_iso_roundtrip (piReindexIso A (reindex B (projection A)) σ).symm
    right_inv := Term.map_iso_roundtrip (piReindexIso A (reindex B (projection A)) σ) }

theorem mapReindexSections_reindex {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (σ : Δ ⟶ Γ) :
    mapReindexSections A B σ (Functor.whiskerLeft σ.mapElements f) =
      Term.reindex (encodeMap f) σ := by
  let p := piReindexIso A (reindex B (projection A)) σ
  apply Term.map_injective_of_iso p
  exact (Term.map_iso_roundtrip p.symm (encodeMap (Functor.whiskerLeft σ.mapElements f))).trans
    (lam_reindex (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A)) σ).symm

/-- Evaluate the generic map after a substituted, encoded family morphism. -/
theorem universalMap_reindex_encoded {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (f : reindex A σ ⟶ reindex B σ) :
    Functor.whiskerLeft (pair σ (mapReindexSections A B σ f)).mapElements (universalMap A B) = f := by
  let p := piReindexIso A (reindex B (projection A)) σ
  have h := Term.map_iso_roundtrip p.symm (encodeMap f)
  exact congrArg (@decodeMap Δ (reindex A σ) (reindex B σ)) h

/-- Full equivalence sections after substitution preserve the map and chosen fiber contractions. -/
noncomputable def equivReindexSections {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ) :
    (Σ f : reindex A σ ⟶ reindex B σ, HomotopyEquivalence f) ≃
      Term (reindex (equiv A B) σ) := by
  let mapsEq := mapReindexSections A B σ
  let fiberEq (f : reindex A σ ⟶ reindex B σ) : HomotopyEquivalence f ≃
      Term (reindex (isEquiv (universalMap A B)) (pair σ (mapsEq f))) :=
    (Equiv.cast (congrArg HomotopyEquivalence (universalMap_reindex_encoded A B σ f).symm)).trans
      (isEquivReindexSections (universalMap A B) (pair σ (mapsEq f)))
  exact (Equiv.sigmaCongr mapsEq fiberEq).trans
    (sigmaSections (reindex (maps A B) σ)
      (reindex (isEquiv (universalMap A B)) (liftSub (maps A B) σ)))

set_option backward.isDefEq.respectTransparency false in
theorem mapReindexSections_comp {Γ Δ Θ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (τ : Θ ⟶ Δ) (f : reindex A σ ⟶ reindex B σ) :
    Term.reindex (mapReindexSections A B σ f) τ =
      mapReindexSections A B (τ ≫ σ) (Functor.whiskerLeft τ.mapElements f) := by
  change Term.reindex (Term.map (piReindexIso A (reindex B (projection A)) σ).inv (encodeMap f)) τ = _
  rw [piInverse_reindex]
  apply congrArg (Term.map (piReindexIso A (reindex B (projection A)) (τ ≫ σ)).inv)
  exact lam_reindex (Term.map (Functor.whiskerLeft (projection (reindex A σ)).mapElements f) (generic (reindex A σ))) τ

set_option backward.isDefEq.respectTransparency false in
theorem equivReindexSections_comp {Γ Δ Θ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (τ : Θ ⟶ Δ) (f : reindex A σ ⟶ reindex B σ) (E : HomotopyEquivalence f) :
    Term.reindex (equivReindexSections A B σ ⟨f,E⟩) τ =
      equivReindexSections A B (τ ≫ σ) ⟨Functor.whiskerLeft τ.mapElements f,E.reindex τ⟩ := by
  apply Term.ext
  intro x
  apply Sigma.ext
  · exact congrArg (fun t => t.val x) (mapReindexSections_comp A B σ τ f)
  · let m := mapReindexSections A B σ f
    let m' := mapReindexSections A B (τ ≫ σ) (Functor.whiskerLeft τ.mapElements f)
    let s := pair σ m
    let s' := pair (τ ≫ σ) m'
    let h := universalMap_reindex_encoded A B σ f
    let h' := universalMap_reindex_encoded A B (τ ≫ σ) (Functor.whiskerLeft τ.mapElements f)
    let e : HomotopyEquivalence (Functor.whiskerLeft s.mapElements (universalMap A B)) := Equiv.cast (congrArg HomotopyEquivalence h.symm) E
    let e' : HomotopyEquivalence (Functor.whiskerLeft s'.mapElements (universalMap A B)) := Equiv.cast (congrArg HomotopyEquivalence h'.symm) (E.reindex τ)
    change HEq ((Term.reindex (isEquivReindexSections (universalMap A B) s e) τ).val x)
      ((isEquivReindexSections (universalMap A B) s' e').val x)
    rw [isEquivReindexSections_comp]
    have hs : τ ≫ s = s' := by
      have hm := mapReindexSections_comp A B σ τ f
      exact congrArg (pair (A := maps A B) (τ ≫ σ)) hm
    have he : HEq (e.reindex τ) e' := by
      have hcast {C D : Family Δ} {f g : C ⟶ D} (h : f = g) (E : HomotopyEquivalence f) :
          HEq ((Equiv.cast (congrArg HomotopyEquivalence h) E).reindex τ) (E.reindex τ) := by cases h; rfl
      exact (hcast h.symm E).trans (cast_heq (congrArg HomotopyEquivalence h'.symm) (E.reindex τ)).symm
    have congrSection (s t : Θ ⟶ total (maps A B))
        (e : HomotopyEquivalence (Functor.whiskerLeft s.mapElements (universalMap A B)))
        (e' : HomotopyEquivalence (Functor.whiskerLeft t.mapElements (universalMap A B)))
        (hs : s = t) (he : HEq e e') :
        HEq ((isEquivReindexSections (universalMap A B) s e).val x)
          ((isEquivReindexSections (universalMap A B) t e').val x) := by
      subst t
      cases he
      rfl
    exact congrSection _ _ _ _ hs he

noncomputable def isoPair {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B)
    (F : Filling B) (hF : F.Lawful) : Σ f : A ⟶ B, HomotopyEquivalence f :=
  ⟨e.hom, HomotopyEquivalence.ofIso e F hF⟩
noncomputable def isoSection {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (e : reindex A σ ≅ reindex B σ) (F : Filling (reindex B σ)) (hF : F.Lawful) :
    Term (reindex (equiv A B) σ) := equivReindexSections A B σ (isoPair e F hF)

theorem isoSection_reindex {Γ Δ Θ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (e : reindex A σ ≅ reindex B σ) (F : Filling (reindex B σ)) (hF : F.Lawful) (τ : Θ ⟶ Δ) :
    Term.reindex (isoSection A B σ e F hF) τ =
      isoSection A B (τ ≫ σ) (Functor.isoWhiskerLeft τ.mapElements e) (F.reindex τ) (hF.reindex τ) := by
  unfold isoSection isoPair
  rw [equivReindexSections_comp, HomotopyEquivalence.ofIso_reindex]
  rfl

noncomputable def identitySection {Γ : Context.{u}} (A : Family Γ) (F : Filling A) (hF : F.Lawful) :
    Term (equiv A A) := isoSection A A (𝟙 Γ) (Iso.refl A) F hF

theorem isoSection_endpoint {Γ : Context.{u}} (A : Family Γ) (F : Filling A) (hF : F.Lawful)
    (e : intervalCoefficient A ≅ intervalCoefficient A) (b : Bool)
    (he : Functor.isoWhiskerLeft (endpointSub Γ b).mapElements e = Iso.refl A) :
    Term.reindex (isoSection A A (projection (interval Γ)) e
      (F.reindex (projection (interval Γ))) (hF.reindex (projection (interval Γ)))) (endpointSub Γ b) =
      identitySection A F hF := by
  rw [isoSection_reindex]
  change isoSection A A (𝟙 Γ) _ F hF = _
  rw [he]
  rfl

noncomputable def isoLoop {Γ : Context.{u}} (A : Family Γ) (F : Filling A) (hF : F.Lawful)
    (e : intervalCoefficient A ≅ intervalCoefficient A)
    (he : ∀ b, Functor.isoWhiskerLeft (endpointSub Γ b).mapElements e = Iso.refl A) :
    Term (homogeneousPath (equiv A A) (identitySection A F hF) (identitySection A F hF)) :=
  pathLam (isoSection A A (projection (interval Γ)) e
      (F.reindex (projection (interval Γ))) (hF.reindex (projection (interval Γ))))
    (isoSection_endpoint A F hF e false (he false))
    (isoSection_endpoint A F hF e true (he true))

def evaluate {Γ : Context.{u}} {A B : Family Γ} (a : Term A) : equiv A B ⟶ B where
  app x := TypeCat.ofHom (fun E => E.1.val (𝟙 x) (a.val x))
  naturality x y f := by
    apply ConcreteCategory.hom_ext
    intro E
    have h := E.1.naturality (𝟙 x) f (a.val x)
    change B.map f (E.1.val (𝟙 x) (a.val x)) = E.1.val (𝟙 x ≫ f) (A.map f (a.val x)) at h
    rw [Category.id_comp] at h
    symm
    change B.map f (E.1.val (𝟙 x) (a.val x)) = E.1.val (f ≫ 𝟙 y) (a.val y)
    rw [Category.comp_id]
    exact h.trans (congrArg (fun v : A.obj y => (show B.obj y from E.1.val f v)) (a.property f))

theorem evaluate_isoSection {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (e : reindex A σ ≅ reindex B σ) (F : Filling (reindex B σ)) (hF : F.Lawful) (a : Term A) :
    Term.map (Functor.whiskerLeft σ.mapElements (evaluate (B := B) a))
      (isoSection A B σ e F hF) = Term.map e.hom (Term.reindex a σ) := by
  apply Term.ext
  intro x
  exact congrArg (fun f => f.app x ((Term.reindex a σ).val x))
    (universalMap_reindex_encoded A B σ e.hom)

def pathMap {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (a b : Term A) :
    homogeneousPath A a b ⟶ homogeneousPath B (Term.map f a) (Term.map f b) where
  app _x := TypeCat.ofHom (fun p => ⟨{
    val := fun {y} g r => f.app y (p.val.val g r)
    naturality := fun {_y z} g h r =>
      (f.naturality_apply h (p.val.val g r)).symm.trans
        (congrArg (f.app z) (p.val.naturality g h r)) },
    fun g => ⟨congrArg (f.app _) (p.property g).1, congrArg (f.app _) (p.property g).2⟩⟩)
  naturality _ _ _ := rfl

theorem evaluate_identity {Γ : Context.{u}} (A : Family Γ) (F : Filling A) (hF : F.Lawful)
    (a : Term A) : Term.map (evaluate a) (identitySection A F hF) = a :=
  evaluate_isoSection A A (𝟙 Γ) (Iso.refl A) F hF a

noncomputable def loopEvaluation {Γ : Context.{u}} (A : Family Γ) (F : Filling A) (hF : F.Lawful)
    (a : Term A) :
    homogeneousPath (equiv A A) (identitySection A F hF) (identitySection A F hF) ⟶
      homogeneousPath A a a :=
  pathMap (evaluate a) _ _ ≫ eqToHom (by rw [evaluate_identity])

theorem pathApp_cast {Γ : Context.{u}} (A : Family Γ) {a b c d : Term A}
    (ha : a = c) (hb : b = d) (p : Term (homogeneousPath A a b)) :
    pathApp (Term.map (eqToHom (congrArg₂ (homogeneousPath A) ha hb)) p) = pathApp p := by
  cases ha
  cases hb
  rfl

theorem loopEvaluation_body {Γ : Context.{u}} (A : Family Γ) (F : Filling A) (hF : F.Lawful)
    (a : Term A) (p : Term (homogeneousPath (equiv A A) (identitySection A F hF) (identitySection A F hF))) :
    pathApp (Term.map (loopEvaluation A F hF a) p) =
      Term.map (Functor.whiskerLeft (projection (interval Γ)).mapElements (evaluate a)) (pathApp p) := by
  exact pathApp_cast A (evaluate_identity A F hF a) (evaluate_identity A F hF a)
    (Term.map (pathMap (evaluate a) _ _) p)

theorem evaluate_isoLoop {Γ : Context.{u}} (A : Family Γ) (F : Filling A) (hF : F.Lawful)
    (a : Term A) (e : intervalCoefficient A ≅ intervalCoefficient A)
    (he : ∀ b, Functor.isoWhiskerLeft (endpointSub Γ b).mapElements e = Iso.refl A) :
    pathApp (Term.map (loopEvaluation A F hF a) (isoLoop A F hF e he)) =
      Term.map e.hom (Term.reindex a (projection (interval Γ))) :=
  (loopEvaluation_body A F hF a _).trans
    (evaluate_isoSection A A (projection (interval Γ)) e _ _ a)

end EquivalenceFamilies
namespace WeakConnection
variable {Γ : Context.{u}} {A : Family Γ} (F : Filling A) (hF : F.Lawful)
variable {a b : Term A} (p : Term (homogeneousPath A a b))
abbrev line := total (interval Γ)
abbrev square := total (interval (line (Γ := Γ)))
abbrev cubeBase := projection (interval (square (Γ := Γ))) ≫ NativeSquare.squareBase Γ
abbrev faceY := NativeSquare.sides (line (Γ := Γ))
abbrev faceX := (faceY (Γ := Γ)).reindex (swapIntervals Γ)
abbrev faces := (faceY (Γ := Γ)).join (faceX (Γ := Γ))
abbrev swapXY := intervalSub (swapIntervals Γ)
noncomputable def seed : Term (reindex A (NativeSquare.squareBase Γ)) :=
  NativeSquare.fill F false (Term.reindex a (projection (interval Γ)))
    (pathApp p) (Term.reindex a (projection (interval Γ))) rfl (pathApp_zero p).symm
noncomputable def tubeY : PartialSection (reindex A (cubeBase (Γ := Γ)))
    ((faceY (Γ := Γ)).reindex (projection (interval (square (Γ := Γ))))) :=
  NativeSquare.tube (A := intervalCoefficient A)
    (Term.reindex a (NativeSquare.squareBase Γ)) (Term.reindex (seed F p) (swapIntervals Γ))
noncomputable def tubeX : PartialSection (reindex A (cubeBase (Γ := Γ)))
    ((faceX (Γ := Γ)).reindex (projection (interval (square (Γ := Γ))))) :=
  (tubeY F p).reindex (swapXY (Γ := Γ))
include hF in
theorem seed_zero : Term.reindex (seed F p) (endpointSub (line (Γ := Γ)) false) =
    Term.reindex a (projection (interval Γ)) :=
  NativeSquare.fill_source F hF false (Term.reindex a (projection (interval Γ))) (pathApp p) (Term.reindex a (projection (interval Γ))) rfl (pathApp_zero p).symm

include hF in
theorem compatible : (tubeY F p).Compatible (tubeX F p) := by
  intro z hy hx
  rcases hy with hy | hy <;> rcases hx with hx | hx
  · exact (NativeSquare.tube_left (A := intervalCoefficient A) (Term.reindex a (NativeSquare.squareBase Γ)) (Term.reindex (seed F p) (swapIntervals Γ)) z hy).trans
      (NativeSquare.tube_left (A := intervalCoefficient A) (Term.reindex a (NativeSquare.squareBase Γ)) (Term.reindex (seed F p) (swapIntervals Γ)) ((swapXY (Γ := Γ)).mapElements.obj z) hx).symm
  · rw [show (tubeY F p).val z (Or.inl hy) = _ from NativeSquare.tube_left (A := intervalCoefficient A) (Term.reindex a (NativeSquare.squareBase Γ)) (Term.reindex (seed F p) (swapIntervals Γ)) z hy]
    change _ = (tubeY F p).val ((swapXY (Γ := Γ)).mapElements.obj z) (Or.inr hx)
    rw [show (tubeY F p).val ((swapXY (Γ := Γ)).mapElements.obj z) (Or.inr hx) = _ from
      NativeSquare.tube_right (A := intervalCoefficient A) (Term.reindex a (NativeSquare.squareBase Γ)) (Term.reindex (seed F p) (swapIntervals Γ)) ((swapXY (Γ := Γ)).mapElements.obj z) hx]
    have he := (NativeSquare.endpoint_iff false _).mp hy
    rcases z with @⟨I, ⟨⟨γ,x⟩,y⟩,k⟩
    change y = ⟨Cube.endpoint I.unop false⟩ at he
    subst y
    exact (congrArg (fun t => t.val (extendObj (interval Γ) (Γ.elementsMk I γ) k)) (seed_zero F hF p)).symm
  · change (tubeY F p).val z (Or.inr hy) = (tubeY F p).val ((swapXY (Γ := Γ)).mapElements.obj z) (Or.inl hx)
    rw [show (tubeY F p).val z (Or.inr hy) = _ from NativeSquare.tube_right (A := intervalCoefficient A) (Term.reindex a (NativeSquare.squareBase Γ)) (Term.reindex (seed F p) (swapIntervals Γ)) z hy,
      show (tubeY F p).val ((swapXY (Γ := Γ)).mapElements.obj z) (Or.inl hx) = _ from
        NativeSquare.tube_left (A := intervalCoefficient A) (Term.reindex a (NativeSquare.squareBase Γ)) (Term.reindex (seed F p) (swapIntervals Γ)) ((swapXY (Γ := Γ)).mapElements.obj z) hx]
    have he := (NativeSquare.endpoint_iff false _).mp hx
    rcases z with @⟨I, ⟨⟨γ,x⟩,y⟩,k⟩
    change x = ⟨Cube.endpoint I.unop false⟩ at he
    subst x
    exact congrArg (fun t => t.val (extendObj (interval Γ) (Γ.elementsMk I γ) k)) (seed_zero F hF p)
  · change (tubeY F p).val z (Or.inr hy) = (tubeY F p).val ((swapXY (Γ := Γ)).mapElements.obj z) (Or.inr hx)
    rw [show (tubeY F p).val z (Or.inr hy) = _ from NativeSquare.tube_right (A := intervalCoefficient A) (Term.reindex a (NativeSquare.squareBase Γ)) (Term.reindex (seed F p) (swapIntervals Γ)) z hy,
      show (tubeY F p).val ((swapXY (Γ := Γ)).mapElements.obj z) (Or.inr hx) = _ from
        NativeSquare.tube_right (A := intervalCoefficient A) (Term.reindex a (NativeSquare.squareBase Γ)) (Term.reindex (seed F p) (swapIntervals Γ)) ((swapXY (Γ := Γ)).mapElements.obj z) hx]
    have hey := (NativeSquare.endpoint_iff true _).mp hy
    have hex := (NativeSquare.endpoint_iff true _).mp hx
    rcases z with @⟨I, ⟨⟨γ,x⟩,y⟩,k⟩
    change y = ⟨Cube.endpoint I.unop true⟩ at hey
    change x = ⟨Cube.endpoint I.unop true⟩ at hex
    subst x
    subst y
    rfl

noncomputable def tube : PartialSection (reindex A (cubeBase (Γ := Γ)))
    ((faces (Γ := Γ)).reindex (projection (interval (square (Γ := Γ))))) :=
  (tubeY F p).glue (tubeX F p) (compatible F hF p)

include hF in
theorem tubeY_source (z : (square (Γ := Γ)).Elements) (h : (faceY (Γ := Γ)).Holds z) :
    (tubeY F p).val ((endpointSub (square (Γ := Γ)) false).mapElements.obj z) h =
      (Term.reindex a (NativeSquare.squareBase Γ)).val z := by
  rcases h with h | h
  · exact NativeSquare.tube_left (A := intervalCoefficient A) _ _ ((endpointSub (square (Γ := Γ)) false).mapElements.obj z) h
  · rw [show (tubeY F p).val ((endpointSub (square (Γ := Γ)) false).mapElements.obj z) (Or.inr h) = _ from
      NativeSquare.tube_right (A := intervalCoefficient A)
        (Term.reindex a (NativeSquare.squareBase Γ)) (Term.reindex (seed F p) (swapIntervals Γ)) ((endpointSub (square (Γ := Γ)) false).mapElements.obj z) h]
    exact congrArg (fun t => t.val ((projection (interval (line (Γ := Γ)))).mapElements.obj z))
      (NativeSquare.fill_left F hF false (Term.reindex a (projection (interval Γ)))
        (pathApp p) (Term.reindex a (projection (interval Γ))) rfl (pathApp_zero p).symm)

noncomputable def box : OpenBox (reindex A (cubeBase (Γ := Γ))) (faces (Γ := Γ))
    (endpoint (square (Γ := Γ)) false) where
  tube := tube F hF p
  base := Term.reindex a (NativeSquare.squareBase Γ)
  boundary z h := by
    rcases h with h | h
    · exact (glueValue_left (tubeY F p) (tubeX F p) _ (Or.inl h) h).trans (tubeY_source F hF p z h)
    · exact (glueValue_right (tubeY F p) (tubeX F p) (compatible F hF p) _ (Or.inr h) h).trans
        (tubeY_source F hF p ((swapIntervals Γ).mapElements.obj z) h)

noncomputable def filling : Term (reindex A (cubeBase (Γ := Γ))) :=
  F.fill (cubeBase (Γ := Γ)) (faces (Γ := Γ)) (endpoint (square (Γ := Γ)) false) (box F hF p)
noncomputable def squareTerm : Term (reindex A (NativeSquare.squareBase Γ)) :=
  Term.reindex (filling F hF p) (endpointSub (square (Γ := Γ)) true)

include hF in
theorem filling_onY (z : (total (interval (square (Γ := Γ)))).Elements)
    (h : (faceY (Γ := Γ)).Holds ((projection (interval (square (Γ := Γ)))).mapElements.obj z)) :
    (filling F hF p).val z = (tubeY F p).val z h :=
  ((hF.fills _ _ _ (box F hF p)).2 z (Or.inl h)).trans
    (glueValue_left (tubeY F p) (tubeX F p) z (Or.inl h) h)
include hF in
theorem filling_onX (z : (total (interval (square (Γ := Γ)))).Elements)
    (h : (faceX (Γ := Γ)).Holds ((projection (interval (square (Γ := Γ)))).mapElements.obj z)) :
    (filling F hF p).val z = (tubeX F p).val z h :=
  ((hF.fills _ _ _ (box F hF p)).2 z (Or.inr h)).trans
    (glueValue_right (tubeY F p) (tubeX F p) (compatible F hF p) z (Or.inr h) h)

include hF in
theorem bottom : Term.reindex (squareTerm F hF p) (endpointSub (line (Γ := Γ)) false) =
    Term.reindex a (projection (interval Γ)) := by
  apply Term.ext
  intro x
  let z := (endpointSub (square (Γ := Γ)) true).mapElements.obj
    ((endpointSub (line (Γ := Γ)) false).mapElements.obj x)
  exact (filling_onY F hF p z (Or.inl rfl)).trans
    (NativeSquare.tube_left (A := intervalCoefficient A) _ _ z rfl)

include hF in
theorem top : Term.reindex (squareTerm F hF p) (endpointSub (line (Γ := Γ)) true) = pathApp p := by
  apply Term.ext
  intro x
  let z := (endpointSub (square (Γ := Γ)) true).mapElements.obj
    ((endpointSub (line (Γ := Γ)) true).mapElements.obj x)
  exact (filling_onY F hF p z (Or.inr rfl)).trans
    ((NativeSquare.tube_right (A := intervalCoefficient A) _ _ z rfl).trans
      (congrArg (fun t => t.val x)
        (NativeSquare.fill_right F hF false (Term.reindex a (projection (interval Γ)))
          (pathApp p) (Term.reindex a (projection (interval Γ))) rfl (pathApp_zero p).symm)))

include hF in
theorem left : Term.reindex (squareTerm F hF p) (intervalSub (endpointSub Γ false)) =
    Term.reindex a (projection (interval Γ)) := by
  apply Term.ext
  intro x
  let z := (endpointSub (square (Γ := Γ)) true).mapElements.obj
    ((intervalSub (endpointSub Γ false)).mapElements.obj x)
  exact (filling_onX F hF p z (Or.inl rfl)).trans
    (NativeSquare.tube_left (A := intervalCoefficient A) _ _ ((swapXY (Γ := Γ)).mapElements.obj z) rfl)

include hF in
theorem right : Term.reindex (squareTerm F hF p) (intervalSub (endpointSub Γ true)) = pathApp p := by
  apply Term.ext
  intro x
  let z := (endpointSub (square (Γ := Γ)) true).mapElements.obj
    ((intervalSub (endpointSub Γ true)).mapElements.obj x)
  exact (filling_onX F hF p z (Or.inr rfl)).trans
    ((NativeSquare.tube_right (A := intervalCoefficient A) _ _ ((swapXY (Γ := Γ)).mapElements.obj z) rfl).trans
      (congrArg (fun t => t.val x)
        (NativeSquare.fill_right F hF false (Term.reindex a (projection (interval Γ)))
          (pathApp p) (Term.reindex a (projection (interval Γ))) rfl (pathApp_zero p).symm)))
end WeakConnection
namespace EquivalenceFamilies
theorem mapReindexSections_id {Γ : Context.{u}} (A B : Family Γ) (f : A ⟶ B) :
    mapReindexSections A B (𝟙 Γ) f = encodeMap f := by
  apply Term.ext
  intro x
  apply PiElement.ext
  intro y k a
  exact piInverseValue_map (A := A) (B := reindex B (projection A)) (𝟙 Γ) ((encodeMap f).val x) k a
private noncomputable def encodeAtFor {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (m : Term (reindex (maps A B) σ)) (f : reindex A σ ⟶ reindex B σ)
    (hf : Functor.whiskerLeft (pair σ m).mapElements (universalMap A B) = f)
    (E : HomotopyEquivalence f) : Term (reindex (equiv A B) σ) :=
  sigmaIntro (B := reindex (isEquiv (universalMap A B)) (liftSub (maps A B) σ)) m
    (isEquivReindexSections (universalMap A B) (pair σ m)
      (Equiv.cast (congrArg HomotopyEquivalence hf.symm) E))
private theorem encodeAtFor_congr {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (m n : Term (reindex (maps A B) σ)) (h : m = n)
    (f : reindex A σ ⟶ reindex B σ)
    (hm : Functor.whiskerLeft (pair σ m).mapElements (universalMap A B) = f)
    (hn : Functor.whiskerLeft (pair σ n).mapElements (universalMap A B) = f)
    (E : HomotopyEquivalence f) : encodeAtFor A B σ m f hm E = encodeAtFor A B σ n f hn E := by
  cases h; rfl
private theorem equivReindexSections_apply {Γ Δ : Context.{u}} (A B : Family Γ)
    (σ : Δ ⟶ Γ) (f : reindex A σ ⟶ reindex B σ) (E : HomotopyEquivalence f) :
    equivReindexSections A B σ ⟨f,E⟩ =
      encodeAtFor A B σ (mapReindexSections A B σ f) f
        (universalMap_reindex_encoded A B σ f) E := by
  apply Term.ext; intro x; rfl
private theorem equivSections_apply {Γ : Context.{u}} (A B : Family Γ)
    (f : A ⟶ B) (E : HomotopyEquivalence f) :
    equivSections A B ⟨f,E⟩ = encodeAtFor A B (𝟙 Γ) (encodeMap f) f rfl E := by
  apply Term.ext; intro x; rfl
theorem equivReindexSections_id {Γ : Context.{u}} (A B : Family Γ)
    (f : A ⟶ B) (E : HomotopyEquivalence f) :
    equivReindexSections A B (𝟙 Γ) ⟨f,E⟩ = equivSections A B ⟨f,E⟩ := by
  exact (equivReindexSections_apply A B (𝟙 Γ) f E).trans
    ((encodeAtFor_congr A B (𝟙 Γ) (mapReindexSections A B (𝟙 Γ) f) (encodeMap f)
      (mapReindexSections_id A B f) f (universalMap_reindex_encoded A B (𝟙 Γ) f) rfl E).trans
      (equivSections_apply A B f E).symm)
end EquivalenceFamilies

end SquareKit.Cubical.Cartesian

set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.EquivalenceFamilies
open CategoryTheory
universe u

private def mapOfSections {Γ : Context.{u}} {C D : Family Γ}
    (Φ : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ), Term (reindex C σ) → Term (reindex D σ)) : C ⟶ D where
  app x := TypeCat.ofHom (fun c => (Φ (projection C) (generic C)).val (extendObj C x c))
  naturality x y k := by
    apply ConcreteCategory.hom_ext
    intro c
    exact ((Φ (projection C) (generic C)).property (extendHom C k c)).symm

private theorem mapOfSections_apply {Γ : Context.{u}} {C D : Family Γ}
    (Φ : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ), Term (reindex C σ) → Term (reindex D σ))
    (hn : ∀ {Δ Θ : Context.{u}} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (s : Term (reindex C σ)),
      Φ (τ ≫ σ) (Term.reindex s τ) = Term.reindex (Φ σ s) τ)
    {Δ : Context.{u}} (σ : Δ ⟶ Γ) (s : Term (reindex C σ)) :
    Term.map (Functor.whiskerLeft σ.mapElements (mapOfSections Φ)) s = Φ σ s :=
  (hn (projection C) (pair σ s) (generic C)).symm

private noncomputable def reindexTo {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    {Θ : Context.{u}} (τ : Θ ⟶ Δ) (s : Term (reindex (equiv A B) (τ ≫ σ))) :
    Term (reindex (equiv (reindex A σ) (reindex B σ)) τ) :=
  equivReindexSections (reindex A σ) (reindex B σ) τ
    ((equivReindexSections A B (τ ≫ σ)).symm s)

private noncomputable def reindexFrom {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    {Θ : Context.{u}} (τ : Θ ⟶ Δ)
    (s : Term (reindex (equiv (reindex A σ) (reindex B σ)) τ)) :
    Term (reindex (equiv A B) (τ ≫ σ)) :=
  equivReindexSections A B (τ ≫ σ)
    ((equivReindexSections (reindex A σ) (reindex B σ) τ).symm s)

private theorem equivReindexSections_decode_comp {Γ Δ Θ : Context.{u}} (A B : Family Γ)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (s : Term (reindex (equiv A B) σ)) :
    (equivReindexSections A B (τ ≫ σ)).symm (Term.reindex s τ) =
      ⟨Functor.whiskerLeft τ.mapElements ((equivReindexSections A B σ).symm s).1,
        ((equivReindexSections A B σ).symm s).2.reindex τ⟩ := by
  apply (equivReindexSections A B (τ ≫ σ)).injective
  exact (Equiv.apply_symm_apply _ _).trans
    ((congrArg (fun t => Term.reindex t τ) (Equiv.apply_symm_apply (equivReindexSections A B σ) s)).symm.trans
      (equivReindexSections_comp A B σ τ _ _))

private theorem reindexTo_natural {Γ Δ Θ Ω : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (τ : Θ ⟶ Δ) (ρ : Ω ⟶ Θ) (s : Term (reindex (equiv A B) (τ ≫ σ))) :
    reindexTo A B σ (ρ ≫ τ) (Term.reindex s ρ) = Term.reindex (reindexTo A B σ τ s) ρ := by
  exact (congrArg (equivReindexSections (reindex A σ) (reindex B σ) (ρ ≫ τ))
    (equivReindexSections_decode_comp A B (τ ≫ σ) ρ s)).trans
    (equivReindexSections_comp (reindex A σ) (reindex B σ) τ ρ _ _).symm

private theorem reindexFrom_natural {Γ Δ Θ Ω : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (τ : Θ ⟶ Δ) (ρ : Ω ⟶ Θ)
    (s : Term (reindex (equiv (reindex A σ) (reindex B σ)) τ)) :
    reindexFrom A B σ (ρ ≫ τ) (Term.reindex s ρ) = Term.reindex (reindexFrom A B σ τ s) ρ := by
  exact (congrArg (equivReindexSections A B ((ρ ≫ τ) ≫ σ))
    (equivReindexSections_decode_comp (reindex A σ) (reindex B σ) τ ρ s)).trans
    (equivReindexSections_comp A B (τ ≫ σ) ρ _ _).symm

private theorem mapOfSections_inverse {Γ : Context.{u}} {C D : Family Γ}
    (Φ : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ), Term (reindex C σ) → Term (reindex D σ))
    (Ψ : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ), Term (reindex D σ) → Term (reindex C σ))
    (hΦ : ∀ {Δ Θ : Context.{u}} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (s : Term (reindex C σ)),
      Φ (τ ≫ σ) (Term.reindex s τ) = Term.reindex (Φ σ s) τ)
    (hΨ : ∀ {Δ Θ : Context.{u}} (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) (s : Term (reindex D σ)),
      Ψ (τ ≫ σ) (Term.reindex s τ) = Term.reindex (Ψ σ s) τ)
    (h : ∀ {Δ : Context.{u}} (σ : Δ ⟶ Γ) (s : Term (reindex C σ)), Ψ σ (Φ σ s) = s) :
    mapOfSections Φ ≫ mapOfSections Ψ = 𝟙 C := by
  let π := projection C
  have ht := mapOfSections_apply Ψ hΨ π
    (Term.map (Functor.whiskerLeft π.mapElements (mapOfSections Φ)) (generic C))
  have ht' := congrArg (Ψ π) (mapOfSections_apply Φ hΦ π (generic C))
  have hh := ht.trans (ht'.trans (h π (generic C)))
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro c
  exact congrArg (fun t => t.val (extendObj C x c)) hh

private theorem bridge_roundtrip {α β γ : Type*} (e : α ≃ β) (d : α ≃ γ) (x : β) :
    e (d.symm (d (e.symm x))) = x := by
  rw [d.symm_apply_apply, e.apply_symm_apply]

/-- A native isomorphism of the complete internal equivalence families.
Its maps are constructed from coherent generic sections, including chosen data. -/
noncomputable def equivReindexIso {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ) :
    reindex (equiv A B) σ ≅ equiv (reindex A σ) (reindex B σ) where
  hom := mapOfSections (reindexTo A B σ)
  inv := mapOfSections (reindexFrom A B σ)
  hom_inv_id := mapOfSections_inverse
    (C := reindex (equiv A B) σ) (D := equiv (reindex A σ) (reindex B σ))
    (reindexTo A B σ) (reindexFrom A B σ)
    (reindexTo_natural A B σ) (reindexFrom_natural A B σ)
    (fun τ s => bridge_roundtrip (equivReindexSections A B (τ ≫ σ))
      (equivReindexSections (reindex A σ) (reindex B σ) τ) s)
  inv_hom_id := mapOfSections_inverse
    (C := equiv (reindex A σ) (reindex B σ)) (D := reindex (equiv A B) σ)
    (reindexFrom A B σ) (reindexTo A B σ)
    (reindexFrom_natural A B σ) (reindexTo_natural A B σ)
    (fun τ s => bridge_roundtrip (equivReindexSections (reindex A σ) (reindex B σ) τ)
      (equivReindexSections A B (τ ≫ σ)) s)

/-- The native family map realizes the complete bridge after any further
substitution, so it can act on the generic sections used by clients. -/
theorem equivReindexIso_hom_reindex_sections {Γ Δ Θ : Context.{u}}
    (A B : Family Γ) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ)
    (s : Term (reindex (equiv A B) (τ ≫ σ))) :
    Term.map (Functor.whiskerLeft τ.mapElements (equivReindexIso A B σ).hom) s =
      equivReindexSections (reindex A σ) (reindex B σ) τ
        ((equivReindexSections A B (τ ≫ σ)).symm s) :=
  mapOfSections_apply (C := reindex (equiv A B) σ)
    (D := equiv (reindex A σ) (reindex B σ))
    (reindexTo A B σ) (reindexTo_natural A B σ) τ s

/-- The native family map realizes the original full chosen-data section bridge. -/
theorem equivReindexIso_hom_sections {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (s : Term (reindex (equiv A B) σ)) :
    Term.map (equivReindexIso A B σ).hom s =
      equivSections (reindex A σ) (reindex B σ) ((equivReindexSections A B σ).symm s) :=
  (mapOfSections_apply (C := reindex (equiv A B) σ) (D := equiv (reindex A σ) (reindex B σ)) (reindexTo A B σ) (reindexTo_natural A B σ) (𝟙 Δ) s).trans
    (equivReindexSections_id (reindex A σ) (reindex B σ) _ _)

/-- Reindexing the internal family preserves the supplied map and its exact
chosen fiber contractions together. -/
theorem equivReindexIso_hom_encode {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (f : reindex A σ ⟶ reindex B σ) (E : HomotopyEquivalence f) :
    Term.map (equivReindexIso A B σ).hom (equivReindexSections A B σ ⟨f,E⟩) =
      equivSections (reindex A σ) (reindex B σ) ⟨f,E⟩ :=
  (equivReindexIso_hom_sections A B σ _).trans
    (congrArg (equivSections (reindex A σ) (reindex B σ))
      ((equivReindexSections A B σ).symm_apply_apply ⟨f,E⟩))

theorem equivReindexIso_inv_encode {Γ Δ : Context.{u}} (A B : Family Γ) (σ : Δ ⟶ Γ)
    (f : reindex A σ ⟶ reindex B σ) (E : HomotopyEquivalence f) :
    Term.map (equivReindexIso A B σ).inv
      (equivSections (reindex A σ) (reindex B σ) ⟨f,E⟩) =
      equivReindexSections A B σ ⟨f,E⟩ :=
  (congrArg (Term.map (equivReindexIso A B σ).inv)
    (equivReindexIso_hom_encode A B σ f E)).symm.trans
      (Term.map_iso_roundtrip (equivReindexIso A B σ) _)

end SquareKit.Cubical.Cartesian.EquivalenceFamilies
