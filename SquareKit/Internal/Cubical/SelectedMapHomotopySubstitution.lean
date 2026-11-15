import SquareKit.Internal.Cubical.SelectedIntervalTransportSubstitution
import SquareKit.Internal.Cubical.SelectedEquivalenceIsoSubstitution
import SquareKit.Internal.Cubical.SelectedInverse
import SquareKit.Internal.Cubical.PathFillingSubstitution

/-! Naturality helpers for transport of complete native equivalence witnesses. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory EquivalenceFamilies
universe u

namespace SelectedMapHomotopySubstitution

open HomotopyEquivalence.MapHomotopyFiberLine in
theorem homotopyFiberFilling_reindex {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (b : Term B) (F : Filling A) (hF : F.Lawful)
    (G : Filling B) (hG : G.Lawful) (σ : Δ ⟶ Γ) :
    ((homotopyFiberFilling f b F hF G hG).reindex σ).transport (fiberReindexIso f b σ) =
      homotopyFiberFilling (Functor.whiskerLeft σ.mapElements f) (b.reindex σ)
        (F.reindex σ) (hF.reindex _) (G.reindex σ) (hG.reindex _) := by
  let a₀ := Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A)
  let a₁ := b.reindex (projection A)
  let R := G.reindex (projection (interval (total A)) ≫ projection A)
  have hR : R.Lawful := hG.reindex _
  exact (sigmaFilling_transport_second
    (pathReindexIso (Presheaf.reindex B (projection (interval (total A)) ≫ projection A)) a₀ a₁ (liftSub A σ)) (F.reindex σ) (hF.reindex _)
    ((pathFilling R hR a₀ a₁).reindex (liftSub A σ))).trans
      (congrArg (sigmaFilling (F.reindex σ) (hF.reindex _))
        (pathFilling_reindex_iso R hR a₀ a₁ (liftSub A σ)))

theorem conjugate_heq {Γ : Context.{u}} {A A' B B' : Family Γ} {f g : A ⟶ B}
    (hfg : f = g) {E : HomotopyEquivalence f} {D : HomotopyEquivalence g}
    (h : HEq E D) (i : A' ≅ A) (j : B ≅ B') : HEq (E.conjugateIso i j) (D.conjugateIso i j) := by
  cases hfg
  exact heq_of_eq (congrArg (fun K => K.conjugateIso i j) (eq_of_heq h))

theorem conjugate_presentations_heq {Γ : Context.{u}} {A A' B B' : Family Γ} {f : A ⟶ B}
    (E : HomotopyEquivalence f) {i i' : A' ≅ A} {j j' : B ≅ B'}
    (hi : i = i') (hj : j = j') : HEq (E.conjugateIso i j) (E.conjugateIso i' j') := by
  cases hi
  cases hj
  rfl

theorem interval_equivalence_congr {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {F G : Filling A} (h : F = G) (hF : F.Lawful) (hG : G.Lawful) :
    HEq (IntervalTransport.equivalence F hF) (IntervalTransport.equivalence G hG) := by
  cases h
  rfl

theorem interval_equivalence_reindex_transport {Γ Δ : Context.{u}}
    {A : Family (total (interval Γ))} {B : Family (total (interval Δ))}
    (F : Filling A) (hF : F.Lawful) (σ : Δ ⟶ Γ)
    (e : Presheaf.reindex A (liftSub (interval Γ) σ) ≅ B) :
    HEq (((IntervalTransport.equivalence F hF).reindex σ).conjugateIso
      (SelectedIntervalTransport.atEndpoint e false).symm (SelectedIntervalTransport.atEndpoint e true))
      (IntervalTransport.equivalence ((F.reindex (liftSub (interval Γ) σ)).transport e)
        (Filling.transport_lawful e _ (hF.reindex _))) :=
  (conjugate_heq (IntervalTransport.map_reindex F hF σ).symm
    (IntervalTransport.equivalence_reindex F hF σ) _ _).trans
      (SelectedIntervalTransport.equivalence_transport e _ (hF.reindex _))

theorem interval_presentations_reindex {Γ Δ : Context.{u}}
    {A : Family (total (interval Γ))} {B : Family (total (interval Δ))}
    {X Y : Family Γ} {X' Y' : Family Δ}
    (F : Filling A) (hF : F.Lawful) (K : Filling B) (hK : K.Lawful) (σ : Δ ⟶ Γ)
    (S : Presheaf.reindex A (endpointSub Γ false) ≅ X)
    (T : Presheaf.reindex A (endpointSub Γ true) ≅ Y)
    (S' : Presheaf.reindex B (endpointSub Δ false) ≅ X')
    (T' : Presheaf.reindex B (endpointSub Δ true) ≅ Y')
    (I : Presheaf.reindex X σ ≅ X') (J : Presheaf.reindex Y σ ≅ Y')
    (e : Presheaf.reindex A (liftSub (interval Γ) σ) ≅ B)
    (hf : (F.reindex (liftSub (interval Γ) σ)).transport e = K)
    (hs : Functor.isoWhiskerLeft σ.mapElements S ≪≫ I = SelectedIntervalTransport.atEndpoint e false ≪≫ S')
    (ht : Functor.isoWhiskerLeft σ.mapElements T ≪≫ J = SelectedIntervalTransport.atEndpoint e true ≪≫ T') :
    HEq ((((IntervalTransport.equivalence F hF).conjugateIso S.symm T).reindex σ).conjugateIso I.symm J)
      ((IntervalTransport.equivalence K hK).conjugateIso S'.symm T') := by
  let L := liftSub (interval Γ) σ
  let e₀ := SelectedIntervalTransport.atEndpoint e false
  let e₁ := SelectedIntervalTransport.atEndpoint e true
  let E := IntervalTransport.equivalence F hF
  have he := (interval_equivalence_reindex_transport F hF σ e).trans
    (interval_equivalence_congr hf (Filling.transport_lawful e _ (hF.reindex _)) hK)
  have hm : e₀.inv ≫ Functor.whiskerLeft σ.mapElements (IntervalTransport.map F) ≫ e₁.hom =
      IntervalTransport.map K :=
    (congrArg (fun k => e₀.inv ≫ k ≫ e₁.hom) (IntervalTransport.map_reindex F hF σ).symm).trans
      ((SelectedIntervalTransport.conjugate_map e (F.reindex L) (hF.reindex _)).trans
        (congrArg IntervalTransport.map hf))
  have hsi : I.symm ≪≫ Functor.isoWhiskerLeft σ.mapElements S.symm = S'.symm ≪≫ e₀.symm :=
    congrArg Iso.symm hs
  have h₁ := congrArg (fun D => D.conjugateIso I.symm J)
    (E.conjugateIso_reindex S.symm T σ)
  have h₂ := (E.reindex σ).conjugateIso_trans
    (Functor.isoWhiskerLeft σ.mapElements S.symm) (Functor.isoWhiskerLeft σ.mapElements T) I.symm J
  have h₃ := conjugate_presentations_heq (E.reindex σ) hsi ht
  have h₄ := (E.reindex σ).conjugateIso_trans e₀.symm e₁ S'.symm T'
  exact (heq_of_eq h₁).trans ((heq_of_eq h₂).trans (h₃.trans
    ((heq_of_eq h₄.symm).trans (conjugate_heq hm he S'.symm T'))))

set_option backward.isDefEq.respectTransparency false in
theorem interval_presentations_map_reindex {Γ Δ : Context.{u}}
    {A : Family (total (interval Γ))} {B : Family (total (interval Δ))}
    {X Y : Family Γ} {X' Y' : Family Δ}
    (F : Filling A) (hF : F.Lawful) (K : Filling B) (σ : Δ ⟶ Γ)
    (S : Presheaf.reindex A (endpointSub Γ false) ≅ X)
    (T : Presheaf.reindex A (endpointSub Γ true) ≅ Y)
    (S' : Presheaf.reindex B (endpointSub Δ false) ≅ X')
    (T' : Presheaf.reindex B (endpointSub Δ true) ≅ Y')
    (I : Presheaf.reindex X σ ≅ X') (J : Presheaf.reindex Y σ ≅ Y')
    (e : Presheaf.reindex A (liftSub (interval Γ) σ) ≅ B)
    (hf : (F.reindex (liftSub (interval Γ) σ)).transport e = K)
    (hs : Functor.isoWhiskerLeft σ.mapElements S ≪≫ I = SelectedIntervalTransport.atEndpoint e false ≪≫ S')
    (ht : Functor.isoWhiskerLeft σ.mapElements T ≪≫ J = SelectedIntervalTransport.atEndpoint e true ≪≫ T') :
    I.inv ≫ Functor.whiskerLeft σ.mapElements (S.inv ≫ IntervalTransport.map F ≫ T.hom) ≫ J.hom =
      S'.inv ≫ IntervalTransport.map K ≫ T'.hom := by
  let e₀ := SelectedIntervalTransport.atEndpoint e false
  let e₁ := SelectedIntervalTransport.atEndpoint e true
  have hm : e₀.inv ≫ Functor.whiskerLeft σ.mapElements (IntervalTransport.map F) ≫ e₁.hom =
      IntervalTransport.map K :=
    (congrArg (fun k => e₀.inv ≫ k ≫ e₁.hom) (IntervalTransport.map_reindex F hF σ).symm).trans
      ((SelectedIntervalTransport.conjugate_map e _ (hF.reindex _)).trans
        (congrArg IntervalTransport.map hf))
  calc
    _ = (Functor.isoWhiskerLeft σ.mapElements S ≪≫ I).inv ≫
        Functor.whiskerLeft σ.mapElements (IntervalTransport.map F) ≫
        (Functor.isoWhiskerLeft σ.mapElements T ≪≫ J).hom := by
      simp only [Iso.trans_inv, Iso.trans_hom, Functor.isoWhiskerLeft_inv,
        Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_comp, Category.assoc]
    _ = (e₀ ≪≫ S').inv ≫ Functor.whiskerLeft σ.mapElements (IntervalTransport.map F) ≫
        (e₁ ≪≫ T').hom := by rw [hs, ht]
    _ = S'.inv ≫ (e₀.inv ≫ Functor.whiskerLeft σ.mapElements (IntervalTransport.map F) ≫ e₁.hom) ≫
        T'.hom := by simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc]
    _ = _ := by rw [hm]

end SelectedMapHomotopySubstitution

namespace HomotopyEquivalence.MapHomotopyFiberLine
variable {Γ Δ : Context.{u}} {A B : Family Γ} {f : A ⟶ B} (g : A ⟶ B)
  (H : Term (homogeneousPath (Presheaf.reindex B (projection A))
    (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
    (Term.map (Functor.whiskerLeft (projection A).mapElements g) (generic A))))
  (σ : Δ ⟶ Γ)

theorem movingMap_reindex :
    Functor.whiskerLeft (liftSub (interval (total B)) (liftSub B σ)).mapElements (movingMap g H) =
      movingMap (f := Functor.whiskerLeft σ.mapElements f) (Functor.whiskerLeft σ.mapElements g) (homogeneousReindex H (liftSub A σ)) := by
  ext x a
  rfl

def reindexIso : Presheaf.reindex (line g H) (liftSub (interval (total B)) (liftSub B σ)) ≅
    line (f := Functor.whiskerLeft σ.mapElements f) (Functor.whiskerLeft σ.mapElements g) (homogeneousReindex H (liftSub A σ)) :=
  fiberReindexIso (movingMap g H) _ (liftSub (interval (total B)) (liftSub B σ)) ≪≫
    eqToIso (congrArg (fun k => homotopyFiber k
      ((generic (Presheaf.reindex B σ)).reindex (projection (interval (total (Presheaf.reindex B σ))))))
      (movingMap_reindex g H σ))

private theorem fiberReindexIso_comp {Ξ Ω Λ : Context.{u}} {C D : Family Ξ}
    (k : C ⟶ D) (b : Term D) (ρ : Ω ⟶ Ξ) (τ : Λ ⟶ Ω) :
    Functor.isoWhiskerLeft τ.mapElements (fiberReindexIso k b ρ) ≪≫
      fiberReindexIso (Functor.whiskerLeft ρ.mapElements k) (b.reindex ρ) τ =
      fiberReindexIso k b (τ ≫ ρ) := by
  apply Iso.ext
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem fiberPresentation_reindex {Ξ Ω Λ : Context.{u}} {C D : Family Ξ}
    (k : C ⟶ D) (b : Term D) (ρ : Ω ⟶ Ξ) (τ : Λ ⟶ Ω)
    {l : Presheaf.reindex C ρ ⟶ Presheaf.reindex D ρ}
    (h : Functor.whiskerLeft ρ.mapElements k = l) :
    Functor.isoWhiskerLeft τ.mapElements
      (fiberReindexIso k b ρ ≪≫ eqToIso (congrArg (fun m => homotopyFiber m (b.reindex ρ)) h)) ≪≫
      fiberReindexIso l (b.reindex ρ) τ =
    fiberReindexIso k b (τ ≫ ρ) ≪≫ eqToIso (congrArg
      (fun m => homotopyFiber m ((b.reindex ρ).reindex τ))
      (congrArg (Functor.whiskerLeft τ.mapElements) h)) := by
  cases h
  exact fiberReindexIso_comp k b ρ τ

set_option backward.isDefEq.respectTransparency false in
theorem start_reindex :
    Functor.isoWhiskerLeft (liftSub B σ).mapElements (start g H) ≪≫ genericFiberReindexIso f σ =
    Functor.isoWhiskerLeft (endpointSub (total (Presheaf.reindex B σ)) false).mapElements
      (reindexIso g H σ) ≪≫
      start (f := Functor.whiskerLeft σ.mapElements f) (Functor.whiskerLeft σ.mapElements g)
        (homogeneousReindex H (liftSub A σ)) := by
  let b := (generic B).reindex (projection (interval (total B)))
  have hl := fiberPresentation_reindex (movingMap g H) b
    (endpointSub (total B) false) (liftSub B σ) (movingMap_zero g H)
  have hr := fiberPresentation_reindex (movingMap g H) b
    (liftSub (interval (total B)) (liftSub B σ))
    (endpointSub (total (Presheaf.reindex B σ)) false) (movingMap_reindex g H σ)
  let q := eqToIso (congrArg (fun k => homotopyFiber k (generic (Presheaf.reindex B σ)))
    (movingMap_zero (f := Functor.whiskerLeft σ.mapElements f) (Functor.whiskerLeft σ.mapElements g)
      (homogeneousReindex H (liftSub A σ))))
  refine hl.trans ?_
  refine Eq.trans ?_ ((congrArg (fun i => i ≪≫ q) hr).symm.trans (Iso.trans_assoc _ _ _))
  apply Iso.ext
  dsimp only [q]
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem finish_reindex :
    Functor.isoWhiskerLeft (liftSub B σ).mapElements (finish g H) ≪≫ genericFiberReindexIso g σ =
    Functor.isoWhiskerLeft (endpointSub (total (Presheaf.reindex B σ)) true).mapElements
      (reindexIso g H σ) ≪≫
      finish (f := Functor.whiskerLeft σ.mapElements f) (Functor.whiskerLeft σ.mapElements g)
        (homogeneousReindex H (liftSub A σ)) := by
  let b := (generic B).reindex (projection (interval (total B)))
  have hl := fiberPresentation_reindex (movingMap g H) b
    (endpointSub (total B) true) (liftSub B σ) (movingMap_one g H)
  have hr := fiberPresentation_reindex (movingMap g H) b
    (liftSub (interval (total B)) (liftSub B σ))
    (endpointSub (total (Presheaf.reindex B σ)) true) (movingMap_reindex g H σ)
  let q := eqToIso (congrArg (fun k => homotopyFiber k (generic (Presheaf.reindex B σ)))
    (movingMap_one (f := Functor.whiskerLeft σ.mapElements f) (Functor.whiskerLeft σ.mapElements g)
      (homogeneousReindex H (liftSub A σ))))
  refine hl.trans ?_
  refine Eq.trans ?_ ((congrArg (fun i => i ≪≫ q) hr).symm.trans (Iso.trans_assoc _ _ _))
  apply Iso.ext
  dsimp only [q]
  simp only [Iso.trans_hom, eqToIso.hom, Category.assoc, eqToHom_trans]
  rfl

variable (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful)

private theorem fiberFilling_congr {Ξ : Context.{u}} {C D : Family Ξ} {k l : C ⟶ D}
    (h : k = l) (b : Term D) (F : Filling C) (hF : F.Lawful) (G : Filling D) (hG : G.Lawful) :
    (homotopyFiberFilling k b F hF G hG).transport
      (eqToIso (congrArg (fun m => homotopyFiber m b) h)) = homotopyFiberFilling l b F hF G hG := by
  cases h
  rfl

theorem filling_reindex :
    ((filling g H FA hFA FB hFB).reindex (liftSub (interval (total B)) (liftSub B σ))).transport
      (reindexIso g H σ) =
    filling (f := Functor.whiskerLeft σ.mapElements f) (Functor.whiskerLeft σ.mapElements g)
      (homogeneousReindex H (liftSub A σ)) (FA.reindex σ) (hFA.reindex _) (FB.reindex σ) (hFB.reindex _) := by
  let L := liftSub (interval (total B)) (liftSub B σ)
  let e := fiberReindexIso (movingMap g H) ((generic B).reindex (projection (interval (total B)))) L
  let q := eqToIso (congrArg (fun k => homotopyFiber k
    ((generic (Presheaf.reindex B σ)).reindex (projection (interval (total (Presheaf.reindex B σ))))))
    (movingMap_reindex g H σ))
  refine (Filling.transport_trans _ e q).symm.trans ?_
  refine (congrArg (Filling.transport q)
    (SelectedMapHomotopySubstitution.homotopyFiberFilling_reindex (movingMap g H) _
      (FA.reindex baseSub) (hFA.reindex _) (FB.reindex baseSub) (hFB.reindex _) L)).trans ?_
  exact fiberFilling_congr (movingMap_reindex g H σ) _ _ _ _ _

theorem equivalence_reindex :
    HEq (((equivalence g H FA hFA FB hFB).reindex (liftSub B σ)).conjugateIso
      (genericFiberReindexIso f σ).symm (genericFiberReindexIso g σ))
      (equivalence (f := Functor.whiskerLeft σ.mapElements f) (Functor.whiskerLeft σ.mapElements g)
        (homogeneousReindex H (liftSub A σ)) (FA.reindex σ) (hFA.reindex _) (FB.reindex σ) (hFB.reindex _)) := by
  exact SelectedMapHomotopySubstitution.interval_presentations_reindex
    (filling g H FA hFA FB hFB) (filling_lawful g H FA hFA FB hFB)
    (filling (f := Functor.whiskerLeft σ.mapElements f) (Functor.whiskerLeft σ.mapElements g)
      (homogeneousReindex H (liftSub A σ)) (FA.reindex σ) (hFA.reindex _) (FB.reindex σ) (hFB.reindex _))
    (filling_lawful _ _ _ _ _ _) (liftSub B σ) (start g H) (finish g H)
    (start (f := Functor.whiskerLeft σ.mapElements f) (Functor.whiskerLeft σ.mapElements g)
      (homogeneousReindex H (liftSub A σ)))
    (finish (f := Functor.whiskerLeft σ.mapElements f) (Functor.whiskerLeft σ.mapElements g)
      (homogeneousReindex H (liftSub A σ)))
    (genericFiberReindexIso f σ) (genericFiberReindexIso g σ) (reindexIso g H σ)
    (filling_reindex g H σ FA hFA FB hFB) (start_reindex g H σ) (finish_reindex g H σ)

theorem map_reindex :
    (genericFiberReindexIso f σ).inv ≫ Functor.whiskerLeft (liftSub B σ).mapElements
      (map g H FA hFA FB hFB) ≫ (genericFiberReindexIso g σ).hom =
    map (f := Functor.whiskerLeft σ.mapElements f) (Functor.whiskerLeft σ.mapElements g)
      (homogeneousReindex H (liftSub A σ)) (FA.reindex σ) (hFA.reindex _) (FB.reindex σ) (hFB.reindex _) := by
  exact SelectedMapHomotopySubstitution.interval_presentations_map_reindex
    (filling g H FA hFA FB hFB) (filling_lawful g H FA hFA FB hFB)
    (filling (f := Functor.whiskerLeft σ.mapElements f) (Functor.whiskerLeft σ.mapElements g)
      (homogeneousReindex H (liftSub A σ)) (FA.reindex σ) (hFA.reindex _) (FB.reindex σ) (hFB.reindex _))
    (liftSub B σ) (start g H) (finish g H)
    (start (f := Functor.whiskerLeft σ.mapElements f) (Functor.whiskerLeft σ.mapElements g)
      (homogeneousReindex H (liftSub A σ)))
    (finish (f := Functor.whiskerLeft σ.mapElements f) (Functor.whiskerLeft σ.mapElements g)
      (homogeneousReindex H (liftSub A σ)))
    (genericFiberReindexIso f σ) (genericFiberReindexIso g σ) (reindexIso g H σ)
    (filling_reindex g H σ FA hFA FB hFB) (start_reindex g H σ) (finish_reindex g H σ)

end HomotopyEquivalence.MapHomotopyFiberLine
namespace SelectedMapHomotopySubstitution
variable {Γ Δ : Context.{u}} {A A' B B' : Family Γ} {f : A ⟶ B}

theorem inverse_conjugate (E : HomotopyEquivalence f) (i : A' ≅ A) (j : B ≅ B') :
    (E.conjugateIso i j).selectedInverse = j.inv ≫ E.selectedInverse ≫ i.inv := by
  have h := EquivalenceIsoTransport.fiberIso_fst i j f (𝟙 (total B'))
    (E.fibers.center.reindex (EquivalenceIsoTransport.targetSub j))
  ext x b
  exact congrArg (fun t => t.val ((total B').elementsMk x.1 ⟨x.2,b⟩)) h

theorem right_conjugate (E : HomotopyEquivalence f) (i : A' ≅ A) (j : B ≅ B') :
    pathApp (E.conjugateIso i j).selectedRight =
    Term.map (Functor.whiskerLeft (projection (interval (total B')) ≫ projection B').mapElements j.hom)
      (pathApp (homogeneousReindex E.selectedRight (EquivalenceIsoTransport.targetSub j))) := by
  exact EquivalenceIsoTransport.fiberIso_pathApp i j f (𝟙 (total B'))
    (E.fibers.center.reindex (EquivalenceIsoTransport.targetSub j))

noncomputable def transfer (c : HomotopyContractible A) (F : Filling B) (hF : F.Lawful)
    (E : HomotopyEquivalence f) : HomotopyContractible B :=
  c.retract F hF f E.selectedInverse E.selectedRight

private theorem retract_congr (c : HomotopyContractible A) (F : Filling B) (hF : F.Lawful)
    {f f' : A ⟶ B} {g g' : B ⟶ A}
    (h : Term (homogeneousPath (Presheaf.reindex B (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements f)
        (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B))) (generic B)))
    (h' : Term (homogeneousPath (Presheaf.reindex B (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements f')
        (Term.map (Functor.whiskerLeft (projection B).mapElements g') (generic B))) (generic B)))
    (hf : f = f') (hg : g = g') (hh : pathApp h = pathApp h') :
    c.retract F hF f g h = c.retract F hF f' g' h' := by
  cases hf
  cases hg
  cases pathApp_injective hh
  rfl

theorem transfer_reindex (c : HomotopyContractible A) (F : Filling B) (hF : F.Lawful)
    (E : HomotopyEquivalence f) (σ : Δ ⟶ Γ) :
    (transfer c F hF E).reindex σ =
    transfer (c.reindex σ) (F.reindex σ) (hF.reindex σ) (E.reindex σ) := by
  refine (c.retract_reindex F hF f E.selectedInverse E.selectedRight σ).trans ?_
  apply retract_congr
  · rfl
  · ext x b
    rfl
  · apply Term.ext
    intro x
    rfl

private theorem retract_transport_selected
    (c : HomotopyContractible A) (i : A ≅ A') (j : B ≅ B')
    (F : Filling B) (hF : F.Lawful) (g : B ⟶ A)
    (h : Term (homogeneousPath (Presheaf.reindex B (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements f)
        (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B))) (generic B)))
    (g' : B' ⟶ A')
    (h' : Term (homogeneousPath (Presheaf.reindex B' (projection B'))
      (Term.map (Functor.whiskerLeft (projection B').mapElements (i.inv ≫ f ≫ j.hom))
        (Term.map (Functor.whiskerLeft (projection B').mapElements g') (generic B'))) (generic B')))
    (hg : g' = j.inv ≫ g ≫ i.hom)
    (hh : pathApp h' =
      Term.map (Functor.whiskerLeft (projection (interval (total B')) ≫ projection B').mapElements j.hom)
        (pathApp (homogeneousReindex h (EquivalenceIsoTransport.targetSub j)))) :
    (c.retract F hF f g h).transport j =
    (c.transport i).retract (F.transport j) (Filling.transport_lawful j F hF)
      (i.inv ≫ f ≫ j.hom) g' h' := by
  subst g'
  exact c.retract_transport i j F hF f g h h' hh

theorem transfer_transport (c : HomotopyContractible A) (i : A ≅ A') (j : B ≅ B')
    (F : Filling B) (hF : F.Lawful) (E : HomotopyEquivalence f) :
    (transfer c F hF E).transport j =
    transfer (c.transport i) (F.transport j) (Filling.transport_lawful j F hF)
      (E.conjugateIso i.symm j) :=
  retract_transport_selected c i j F hF E.selectedInverse E.selectedRight
    (E.conjugateIso i.symm j).selectedInverse (E.conjugateIso i.symm j).selectedRight
    (inverse_conjugate E i.symm j) (right_conjugate E i.symm j)

theorem transfer_congr (c : HomotopyContractible A) {F G : Filling B}
    (hF : F.Lawful) (hG : G.Lawful) {f g : A ⟶ B}
    (E : HomotopyEquivalence f) (D : HomotopyEquivalence g)
    (hf : f = g) (h : HEq E D) (hFG : F = G) :
    transfer c F hF E = transfer c G hG D := by
  cases hf
  cases hFG
  cases eq_of_heq h
  rfl

end SelectedMapHomotopySubstitution
namespace HomotopyEquivalence
open SelectedMapHomotopySubstitution
variable {Γ Δ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}

theorem ofMapHomotopy_reindex (E : HomotopyEquivalence f) (g : A ⟶ B)
    (H : Term (homogeneousPath (Presheaf.reindex B (projection A))
      (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
      (Term.map (Functor.whiskerLeft (projection A).mapElements g) (generic A))))
    (FA : Filling A) (hFA : FA.Lawful) (FB : Filling B) (hFB : FB.Lawful) (σ : Δ ⟶ Γ) :
    (E.ofMapHomotopy g H FA hFA FB hFB).reindex σ =
    (E.reindex σ).ofMapHomotopy (f := Functor.whiskerLeft σ.mapElements f) (Functor.whiskerLeft σ.mapElements g)
      (homogeneousReindex H (liftSub A σ)) (FA.reindex σ) (hFA.reindex _)
      (FB.reindex σ) (hFB.reindex _) := by
  apply HomotopyEquivalence.ext
  let D := MapHomotopyFiberLine.equivalence g H FA hFA FB hFB
  let F := genericFiberFilling g FA hFA FB hFB
  have hF := genericFiberFilling_lawful g FA hFA FB hFB
  have h₁ := congrArg (fun c => c.transport (genericFiberReindexIso g σ))
    (transfer_reindex E.fibers F hF D (liftSub B σ))
  have h₂ := transfer_transport (E.fibers.reindex (liftSub B σ))
    (genericFiberReindexIso f σ) (genericFiberReindexIso g σ)
    (F.reindex (liftSub B σ)) (hF.reindex _) (D.reindex (liftSub B σ))
  refine h₁.trans (h₂.trans ?_)
  exact transfer_congr _ (Filling.transport_lawful (genericFiberReindexIso g σ) _ (hF.reindex _))
    (genericFiberFilling_lawful (Functor.whiskerLeft σ.mapElements g)
      (FA.reindex σ) (hFA.reindex _) (FB.reindex σ) (hFB.reindex _)) _ _
    (MapHomotopyFiberLine.map_reindex g H σ FA hFA FB hFB)
    (MapHomotopyFiberLine.equivalence_reindex g H σ FA hFA FB hFB)
    (genericFiberFilling_reindex g FA hFA FB hFB σ)

end HomotopyEquivalence
end SquareKit.Cubical.Presheaf
