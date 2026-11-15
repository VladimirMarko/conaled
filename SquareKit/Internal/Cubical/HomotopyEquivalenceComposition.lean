import SquareKit.Internal.Cubical.ContractibleTotals

/-! Composition of native equivalences by relative extension of their fibers. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u
namespace EquivalenceComposition
theorem fillOver_reindex {Γ Δ Θ : Context.{u}} {X : Family Γ} {Y : Family (total X)}
    (F : Filling Y) (hF : F.Lawful) (σ : total (interval Δ) ⟶ Γ) {φ : Cofibration Δ}
    (b : OpenBox (reindex (sigma X Y) σ) φ) (x : Term (reindex X σ))
    (hx : (OpenBox.sigmaFst (B := reindex Y (liftSub X σ)) b).Fills x) (τ : Θ ⟶ Δ) :
    ContractibleTotals.fillOver F (liftSub (interval Δ) τ ≫ σ) (b.reindex τ)
      (x.reindex (liftSub (interval Δ) τ)) (hx.reindex τ) =
      (ContractibleTotals.fillOver F σ b x hx).reindex (liftSub (interval Δ) τ) := by
  exact congrArg (fun c => sigmaIntro (B := reindex Y (liftSub X (liftSub (interval Δ) τ ≫ σ)))
    (x.reindex (liftSub (interval Δ) τ)) c)
    ((congrArg (F.fill (pair (liftSub (interval Δ) τ ≫ σ) (x.reindex (liftSub (interval Δ) τ)))
      (φ.reindex τ)) (OpenBox.sigmaSnd_reindex (B := reindex Y (liftSub X σ)) b x hx τ).symm).trans
      (hF.uniform (pair σ x) φ (OpenBox.sigmaSnd (B := reindex Y (liftSub X σ)) b x hx) τ))

private theorem fillOver_congr {Γ Δ : Context.{u}} {X : Family Γ} {Y : Family (total X)}
    (F : Filling Y) (σ : total (interval Δ) ⟶ Γ) {φ : Cofibration Δ}
    (b b' : OpenBox (reindex (sigma X Y) σ) φ) (hb : b = b')
    (x x' : Term (reindex X σ)) (hx : x = x')
    (h : (OpenBox.sigmaFst (B := reindex Y (liftSub X σ)) b).Fills x)
    (h' : (OpenBox.sigmaFst (B := reindex Y (liftSub X σ)) b').Fills x') :
    ContractibleTotals.fillOver F σ b x h = ContractibleTotals.fillOver F σ b' x' h' := by
  cases hb
  cases hx
  rfl

variable {Γ Δ : Context.{u}} {A B C : Family Γ}
  (f : A ⟶ B) (g : B ⟶ C)

abbrev fiber (σ : Δ ⟶ total C) :=
  reindex (homotopyFiber (Functor.whiskerLeft (projection C).mapElements (f ≫ g)) (generic C)) σ

/-- Map a composite fiber into the second map's fiber, retaining its path. -/
def intermediate (σ : Δ ⟶ total C) (s : Term (fiber f g σ)) :
    Term (reindex (homotopyFiber (Functor.whiskerLeft (projection C).mapElements g) (generic C)) σ) :=
  genericFiberIntro g σ
    (Term.map (Functor.whiskerLeft (σ ≫ projection C).mapElements f)
      (genericFiberFst (f ≫ g) σ s)) (genericFiberPath (f ≫ g) σ s)

variable (E : HomotopyEquivalence f) (D : HomotopyEquivalence g)
  (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful)
  (FC : Filling C) (hFC : FC.Lawful)
  (σ : Δ ⟶ total C) {φ : Cofibration Δ} (s : PartialSection (fiber f g σ) φ)

def partialMiddle : PartialSection
    (reindex (homotopyFiber (Functor.whiskerLeft (projection C).mapElements g) (generic C)) σ) φ :=
  PartialSection.ofRestricted (intermediate f g (restrictInclusion φ ≫ σ) s.toRestricted)

theorem intermediate_reindex {Θ : Context.{u}} (σ : Δ ⟶ total C)
    (z : Term (fiber f g σ)) (τ : Θ ⟶ Δ) :
    intermediate f g (τ ≫ σ) (z.reindex τ) = (intermediate f g σ z).reindex τ :=
by
  exact (genericFiberIntro_congr g (τ ≫ σ) _ _ rfl _ _
    (pathTerm_hext _ _ rfl)).trans
      (genericFiberIntro_reindex g σ
        (Term.map (Functor.whiskerLeft (σ ≫ projection C).mapElements f)
          (genericFiberFst (f ≫ g) σ z)) (genericFiberPath (f ≫ g) σ z) τ)

theorem partialMiddle_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    partialMiddle f g (τ ≫ σ) (s.reindex τ) = (partialMiddle f g σ s).reindex τ := by
  apply PartialSection.ext
  intro x hx
  exact congrArg (fun t => t.val ((restrictContext (φ.reindex τ)).elementsMk x.obj ⟨x.val,hx⟩))
    (intermediate_reindex f g (restrictInclusion φ ≫ σ) s.toRestricted (restrictSubstitution φ τ))

noncomputable def middle := D.extendAlong FB hFB FC hFC σ
  (partialMiddle f g σ s)

theorem middle_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    middle f g D FB hFB FC hFC (τ ≫ σ) (s.reindex τ) =
      (middle f g D FB hFB FC hFC σ s).reindex τ := by
  unfold middle
  rw [partialMiddle_reindex]
  exact D.extendAlong_reindex FB hFB FC hFC σ _ τ

noncomputable def middlePoint := genericFiberFst g σ (middle f g D FB hFB FC hFC σ s)
noncomputable def target := pair (σ ≫ projection C) (middlePoint f g D FB hFB FC hFC σ s)

def partialSource : PartialSection (reindex A (σ ≫ projection C)) φ :=
  PartialSection.ofRestricted (genericFiberFst (f ≫ g) (restrictInclusion φ ≫ σ) s.toRestricted)

theorem partialSource_image :
    (partialSource f g σ s).map (Functor.whiskerLeft (σ ≫ projection C).mapElements f) =
      PartialSection.ofTerm φ (middlePoint f g D FB hFB FC hFC σ s) := by
  apply PartialSection.ext
  intro x hx
  exact (congrArg Sigma.fst (D.extendAlong_boundary FB hFB FC hFC σ
    (partialMiddle f g σ s) x hx)).symm

noncomputable def sourceFiber := E.extendAlong FA hFA FB hFB
  (target f g D FB hFB FC hFC σ s)
  (genericFiberPartialIntro f (target f g D FB hFB FC hFC σ s)
    (partialSource f g σ s) (partialSource_image f g D FB hFB FC hFC σ s))

private theorem extendAlong_point_congr (ρ : Δ ⟶ Γ)
    (p : PartialSection (reindex A ρ) φ) (b b' : Term (reindex B ρ)) (hb : b = b')
    (h : p.map (Functor.whiskerLeft ρ.mapElements f) = PartialSection.ofTerm φ b)
    (h' : p.map (Functor.whiskerLeft ρ.mapElements f) = PartialSection.ofTerm φ b') :
    HEq (E.extendAlong FA hFA FB hFB (pair ρ b) (genericFiberPartialIntro f (pair ρ b) p h))
      (E.extendAlong FA hFA FB hFB (pair ρ b') (genericFiberPartialIntro f (pair ρ b') p h')) := by
  cases hb
  rfl

theorem sourceFiber_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    HEq (sourceFiber f g E D FA hFA FB hFB FC hFC (τ ≫ σ) (s.reindex τ))
      ((sourceFiber f g E D FA hFA FB hFB FC hFC σ s).reindex τ) := by
  have hm : middlePoint f g D FB hFB FC hFC (τ ≫ σ) (s.reindex τ) =
      (middlePoint f g D FB hFB FC hFC σ s).reindex τ :=
    congrArg (genericFiberFst g (τ ≫ σ)) (middle_reindex f g D FB hFB FC hFC σ s τ)
  have h := genericFiberPartialIntro_reindex f
    (target f g D FB hFB FC hFC σ s) (partialSource f g σ s)
    (partialSource_image f g D FB hFB FC hFC σ s) τ
  exact (extendAlong_point_congr f E FA hFA FB hFB (τ ≫ σ ≫ projection C)
    (partialSource f g (τ ≫ σ) (s.reindex τ)) _ _ hm _ _).trans
    (heq_of_eq ((congrArg (E.extendAlong FA hFA FB hFB
      (τ ≫ target f g D FB hFB FC hFC σ s)) h).trans
      (E.extendAlong_reindex FA hFA FB hFB (target f g D FB hFB FC hFC σ s) _ τ)))

noncomputable def source := genericFiberFst f (target f g D FB hFB FC hFC σ s)
  (sourceFiber f g E D FA hFA FB hFB FC hFC σ s)

noncomputable def middleLine := pathApp (homogeneousReverse
  (genericFiberPath f (target f g D FB hFB FC hFC σ s)
    (sourceFiber f g E D FA hFA FB hFB FC hFC σ s)))

theorem target_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    target f g D FB hFB FC hFC (τ ≫ σ) (s.reindex τ) =
      τ ≫ target f g D FB hFB FC hFC σ s :=
  congrArg (fun z => pair (τ ≫ σ ≫ projection C) (genericFiberFst g (τ ≫ σ) z))
    (middle_reindex f g D FB hFB FC hFC σ s τ)

private theorem fiberFst_heq {Ω : Context.{u}} (ρ ρ' : Ω ⟶ total B) (hρ : ρ = ρ')
    (z : Term (reindex (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)) ρ))
    (z' : Term (reindex (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)) ρ'))
    (hz : HEq z z') : HEq (genericFiberFst f ρ z) (genericFiberFst f ρ' z') := by
  cases hρ
  cases hz
  rfl

private theorem fiberLine_heq {Ω : Context.{u}} (ρ ρ' : Ω ⟶ total B) (hρ : ρ = ρ')
    (z : Term (reindex (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)) ρ))
    (z' : Term (reindex (homotopyFiber (Functor.whiskerLeft (projection B).mapElements f) (generic B)) ρ'))
    (hz : HEq z z') : HEq (pathApp (homogeneousReverse (genericFiberPath f ρ z)))
      (pathApp (homogeneousReverse (genericFiberPath f ρ' z'))) := by
  cases hρ
  cases hz
  rfl

theorem source_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    source f g E D FA hFA FB hFB FC hFC (τ ≫ σ) (s.reindex τ) =
      (source f g E D FA hFA FB hFB FC hFC σ s).reindex τ :=
  eq_of_heq (fiberFst_heq f _ _ (target_reindex f g D FB hFB FC hFC σ s τ)
    _ _ (sourceFiber_reindex f g E D FA hFA FB hFB FC hFC σ s τ))

theorem middleLine_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    middleLine f g E D FA hFA FB hFB FC hFC (τ ≫ σ) (s.reindex τ) =
      (middleLine f g E D FA hFA FB hFB FC hFC σ s).reindex (liftSub (interval Δ) τ) :=
  eq_of_heq (fiberLine_heq f _ _ (target_reindex f g D FB hFB FC hFC σ s τ)
    _ _ (sourceFiber_reindex f g E D FA hFA FB hFB FC hFC σ s τ))

noncomputable def box : OpenBox
    (reindex (homotopyFiber (Functor.whiskerLeft (projection C).mapElements g) (generic C))
      (projection (interval Δ) ≫ σ)) φ where
  tube := (partialMiddle f g σ s).reindex (projection (interval Δ))
  base := middle f g D FB hFB FC hFC σ s
  boundary x hx := (D.extendAlong_boundary FB hFB FC hFC σ
    (partialMiddle f g σ s) x hx).symm

theorem middleLine_fills :
    (OpenBox.sigmaFst (B := reindex (genericFiberPathFamily g)
      (liftSub (reindex B (projection C)) (projection (interval Δ) ≫ σ)))
      (box f g D FB hFB FC hFC σ s)).Fills
      (middleLine f g E D FA hFA FB hFB FC hFC σ s) := by
  constructor
  · exact pathApp_zero (homogeneousReverse
      (genericFiberPath f (target f g D FB hFB FC hFC σ s)
        (sourceFiber f g E D FA hFA FB hFB FC hFC σ s)))
  · intro x hx
    exact (E.extendAlong_path_boundary FA hFA FB hFB
      (target f g D FB hFB FC hFC σ s) (partialSource f g σ s)
      (partialSource_image f g D FB hFB FC hFC σ s)
      ((projection (interval Δ)).mapElements.obj x) hx x.val.2).trans
      (congrArg Sigma.fst (D.extendAlong_boundary FB hFB FC hFC σ
        (partialMiddle f g σ s)
        ((projection (interval Δ)).mapElements.obj x) hx))

theorem box_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    box f g D FB hFB FC hFC (τ ≫ σ) (s.reindex τ) =
      (box f g D FB hFB FC hFC σ s).reindex τ := by
  apply OpenBox.ext
  · exact congrArg (fun z => z.reindex (projection (interval Θ)))
      (partialMiddle_reindex f g σ s τ)
  · exact middle_reindex f g D FB hFB FC hFC σ s τ

noncomputable def pathFiller : Filling (genericFiberPathFamily g) :=
  pathFilling (FC.reindex (projection (interval (total (reindex B (projection C)))) ≫
    projection (reindex B (projection C)) ≫ projection C)) (hFC.reindex _)
    (Term.map (Functor.whiskerLeft (projection (reindex B (projection C))).mapElements
      (Functor.whiskerLeft (projection C).mapElements g)) (generic (reindex B (projection C))))
    ((generic C).reindex (projection (reindex B (projection C))))

theorem pathFiller_lawful : (pathFiller g FC hFC).Lawful := pathFilling_lawful _ _ _ _

noncomputable def filled := ContractibleTotals.fillOver (pathFiller g FC hFC)
  (projection (interval Δ) ≫ σ) (box f g D FB hFB FC hFC σ s)
  (middleLine f g E D FA hFA FB hFB FC hFC σ s)
  (middleLine_fills f g E D FA hFA FB hFB FC hFC σ s)

theorem filled_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    filled f g E D FA hFA FB hFB FC hFC (τ ≫ σ) (s.reindex τ) =
      (filled f g E D FA hFA FB hFB FC hFC σ s).reindex (liftSub (interval Δ) τ) :=
  (fillOver_congr (pathFiller g FC hFC) (projection (interval Θ) ≫ τ ≫ σ) _ _
    (box_reindex f g D FB hFB FC hFC σ s τ) _ _
    (middleLine_reindex f g E D FA hFA FB hFB FC hFC σ s τ) _ _).trans
      (fillOver_reindex (pathFiller g FC hFC) (pathFiller_lawful g FC hFC)
        (projection (interval Δ) ≫ σ) _ _ _ τ)

noncomputable def endpoint := (filled f g E D FA hFA FB hFB FC hFC σ s).reindex (endpointSub Δ true)

theorem endpoint_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    endpoint f g E D FA hFA FB hFB FC hFC (τ ≫ σ) (s.reindex τ) =
      (endpoint f g E D FA hFA FB hFB FC hFC σ s).reindex τ :=
  congrArg (fun z => z.reindex (endpointSub Θ true))
    (filled_reindex f g E D FA hFA FB hFB FC hFC σ s τ)

theorem endpoint_fst : genericFiberFst g σ (endpoint f g E D FA hFA FB hFB FC hFC σ s) =
    Term.map (Functor.whiskerLeft (σ ≫ projection C).mapElements f)
      (source f g E D FA hFA FB hFB FC hFC σ s) :=
  pathApp_one (homogeneousReverse (genericFiberPath f (target f g D FB hFB FC hFC σ s)
    (sourceFiber f g E D FA hFA FB hFB FC hFC σ s)))

noncomputable def finalPath :=
  pathLam (pathApp (genericFiberPath g σ (endpoint f g E D FA hFA FB hFB FC hFC σ s)))
    ((pathApp_zero (genericFiberPath g σ (endpoint f g E D FA hFA FB hFB FC hFC σ s))).trans
      (congrArg (Term.map (Functor.whiskerLeft (σ ≫ projection C).mapElements g))
        (endpoint_fst f g E D FA hFA FB hFB FC hFC σ s)))
    (pathApp_one (genericFiberPath g σ (endpoint f g E D FA hFA FB hFB FC hFC σ s)))

noncomputable def extend : Term (fiber f g σ) :=
  genericFiberIntro (f ≫ g) σ (source f g E D FA hFA FB hFB FC hFC σ s)
    (finalPath f g E D FA hFA FB hFB FC hFC σ s)

theorem extend_reindex {Θ : Context.{u}} (τ : Θ ⟶ Δ) :
    extend f g E D FA hFA FB hFB FC hFC (τ ≫ σ) (s.reindex τ) =
      (extend f g E D FA hFA FB hFB FC hFC σ s).reindex τ := by
  have hp : pathApp (finalPath f g E D FA hFA FB hFB FC hFC (τ ≫ σ) (s.reindex τ)) =
      pathApp (homogeneousReindex (finalPath f g E D FA hFA FB hFB FC hFC σ s) τ) :=
    congrArg (fun z => pathApp (genericFiberPath g (τ ≫ σ) z))
      (endpoint_reindex f g E D FA hFA FB hFB FC hFC σ s τ)
  exact (genericFiberIntro_congr (f ≫ g) (τ ≫ σ) _ _
    (source_reindex f g E D FA hFA FB hFB FC hFC σ s τ) _ _ (pathTerm_hext _ _ hp)).trans
    (genericFiberIntro_reindex (f ≫ g) σ (source f g E D FA hFA FB hFB FC hFC σ s)
      (finalPath f g E D FA hFA FB hFB FC hFC σ s) τ)

theorem source_boundary (x : Δ.Elements) (hx : φ.full x) :
    (source f g E D FA hFA FB hFB FC hFC σ s).val x = (s.val x hx).1 :=
  congrArg Sigma.fst (E.extendAlong_boundary FA hFA FB hFB
    (target f g D FB hFB FC hFC σ s)
    (genericFiberPartialIntro f (target f g D FB hFB FC hFC σ s)
      (partialSource f g σ s) (partialSource_image f g D FB hFB FC hFC σ s)) x hx)

theorem endpoint_boundary (x : Δ.Elements) (hx : φ.full x) :
    (endpoint f g E D FA hFA FB hFB FC hFC σ s).val x =
      (partialMiddle f g σ s).val x hx :=
  (ContractibleTotals.fillOver_fills (pathFiller g FC hFC) (pathFiller_lawful g FC hFC)
    (projection (interval Δ) ≫ σ) (box f g D FB hFB FC hFC σ s)
    (middleLine f g E D FA hFA FB hFB FC hFC σ s)
    (middleLine_fills f g E D FA hFA FB hFB FC hFC σ s)).2
    ((endpointSub Δ true).mapElements.obj x) hx

theorem endpoint_restricted :
    (endpoint f g E D FA hFA FB hFB FC hFC σ s).reindex (restrictInclusion φ) =
      intermediate f g (restrictInclusion φ ≫ σ) s.toRestricted := by
  apply Term.ext
  intro x
  exact endpoint_boundary f g E D FA hFA FB hFB FC hFC σ s
    ((restrictInclusion φ).mapElements.obj x) x.val.property

theorem finalPath_restricted :
    pathApp (homogeneousReindex (finalPath f g E D FA hFA FB hFB FC hFC σ s)
      (restrictInclusion φ)) =
    pathApp (genericFiberPath (f ≫ g) (restrictInclusion φ ≫ σ) s.toRestricted) := by
  change pathApp (genericFiberPath g (restrictInclusion φ ≫ σ)
    ((endpoint f g E D FA hFA FB hFB FC hFC σ s).reindex (restrictInclusion φ))) = _
  rw [endpoint_restricted]
  exact congrArg pathApp (Term.map_iso_roundtrip
    (genericFiberPathIso g (restrictInclusion φ ≫ σ)
      (Term.map (Functor.whiskerLeft (restrictInclusion φ ≫ σ ≫ projection C).mapElements f)
        (genericFiberFst (f ≫ g) (restrictInclusion φ ≫ σ) s.toRestricted))).symm
    (genericFiberPath (f ≫ g) (restrictInclusion φ ≫ σ) s.toRestricted))

theorem extend_restricted :
    (extend f g E D FA hFA FB hFB FC hFC σ s).reindex (restrictInclusion φ) =
      s.toRestricted := by
  have ha : (source f g E D FA hFA FB hFB FC hFC σ s).reindex (restrictInclusion φ) =
      genericFiberFst (f ≫ g) (restrictInclusion φ ≫ σ) s.toRestricted := by
    apply Term.ext
    intro x
    exact source_boundary f g E D FA hFA FB hFB FC hFC σ s
      ((restrictInclusion φ).mapElements.obj x) x.val.property
  exact (genericFiberIntro_reindex (f ≫ g) σ
    (source f g E D FA hFA FB hFB FC hFC σ s)
    (finalPath f g E D FA hFA FB hFB FC hFC σ s) (restrictInclusion φ)).symm.trans
    ((genericFiberIntro_congr (f ≫ g) (restrictInclusion φ ≫ σ) _ _ ha _ _
      (pathTerm_hext _ _ (finalPath_restricted f g E D FA hFA FB hFB FC hFC σ s))).trans
      (genericFiberIntro_eta (f ≫ g) (restrictInclusion φ ≫ σ) s.toRestricted))

theorem extend_boundary (x : Δ.Elements) (hx : φ.full x) :
    (extend f g E D FA hFA FB hFB FC hFC σ s).val x = s.val x hx :=
  congrArg (fun t => t.val ((restrictContext φ).elementsMk x.obj ⟨x.val,hx⟩))
    (extend_restricted f g E D FA hFA FB hFB FC hFC σ s)

end EquivalenceComposition

/-- Composition preserves contractibility of native homotopy fibers. -/
noncomputable def HomotopyEquivalence.comp {Γ : Context.{u}} {A B C : Family Γ}
    {f : A ⟶ B} {g : B ⟶ C} (E : HomotopyEquivalence f) (D : HomotopyEquivalence g)
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful)
    (FC : Filling C) (hFC : FC.Lawful) : HomotopyEquivalence (f ≫ g) where
  fibers := HomotopyContractible.ofExtensions
    (fun σ _ s => EquivalenceComposition.extend f g E D FA hFA FB hFB FC hFC σ s)
    (fun σ _ s x hx => EquivalenceComposition.extend_boundary f g E D FA hFA FB hFB FC hFC σ s x hx)

end SquareKit.Cubical.Presheaf
