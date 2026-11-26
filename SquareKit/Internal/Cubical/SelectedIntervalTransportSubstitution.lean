import SquareKit.Internal.Cubical.NativeEquivalenceLine
import SquareKit.Internal.Cubical.NativePathComposition

/-! Transport of selected interval-fiber constructions through family presentations. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.SelectedPathTransport
open CategoryTheory
universe u
variable {Γ : Context.{u}} {A B : Family (total (interval Γ))}

def map (e : A ⟶ B)
    (a₀ : Term (reindex A (endpointSub Γ false)))
    (a₁ : Term (reindex A (endpointSub Γ true))) :
    path A a₀ a₁ ⟶ path B
      (Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements e) a₀)
      (Term.map (Functor.whiskerLeft (endpointSub Γ true).mapElements e) a₁) where
  app x := TypeCat.ofHom (fun p => ⟨(EquivalenceFamilies.piSecondMap (interval Γ) e).app x p.val,
    fun {y} k => ⟨congrArg (e.app (extendObj (interval Γ) y ((endpoint Γ false).val y))) (p.property k).1,
      congrArg (e.app (extendObj (interval Γ) y ((endpoint Γ true).val y))) (p.property k).2⟩⟩)
  naturality _ _ _ := rfl

def iso (e : A ≅ B)
    (a₀ : Term (reindex A (endpointSub Γ false)))
    (a₁ : Term (reindex A (endpointSub Γ true))) :
    path A a₀ a₁ ≅ path B
      (Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements e.hom) a₀)
      (Term.map (Functor.whiskerLeft (endpointSub Γ true).mapElements e.hom) a₁) where
  hom := map e.hom a₀ a₁
  inv :=
    { app := fun x => TypeCat.ofHom (fun p =>
        ⟨(EquivalenceFamilies.piSecondMap (interval Γ) e.inv).app x p.val,
        fun {y} k =>
          ⟨(congrArg (e.inv.app _) (p.property k).1).trans
              (congrArg (fun m => m.app ((endpointSub Γ false).mapElements.obj y) (a₀.val y)) e.hom_inv_id),
            (congrArg (e.inv.app _) (p.property k).2).trans
              (congrArg (fun m => m.app ((endpointSub Γ true).mapElements.obj y) (a₁.val y)) e.hom_inv_id)⟩⟩)
      naturality := fun _ _ _ => rfl }
  hom_inv_id := by
    ext x p
    apply Subtype.ext
    apply PiElement.ext
    intro y k r
    exact congrArg (fun m => m.app (extendObj (interval Γ) y r) (p.val.val k r)) e.hom_inv_id
  inv_hom_id := by
    ext x p
    apply Subtype.ext
    apply PiElement.ext
    intro y k r
    exact congrArg (fun m => m.app (extendObj (interval Γ) y r) (p.val.val k r)) e.inv_hom_id

theorem endpointBoundary_map (e : A ⟶ B)
    (a₀ : Term (reindex A (endpointSub Γ false)))
    (a₁ : Term (reindex A (endpointSub Γ true))) :
    endpointBoundary B
      (Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements e) a₀)
      (Term.map (Functor.whiskerLeft (endpointSub Γ true).mapElements e) a₁) =
      (endpointBoundary A a₀ a₁).map e :=
  (PartialSection.glue_congr (endpointSection_map e false a₀) (endpointSection_map e true a₁) _ _).trans
    (Glue.partialGlue_map e _ _ _).symm

theorem boundary_map (e : A ⟶ B)
    {a₀ : Term (reindex A (endpointSub Γ false))}
    {a₁ : Term (reindex A (endpointSub Γ true))}
    {φ : Cofibration Γ} (s : PartialSection (path A a₀ a₁) φ) :
    (s.map (map e a₀ a₁)).pathBoundary = s.pathBoundary.map e := by
  have ha : (s.map (map e a₀ a₁)).pathApp = s.pathApp.map e := by
    apply PartialSection.ext
    intro x hx
    rfl
  exact (PartialSection.glue_congr ha (endpointBoundary_map e a₀ a₁) _ _).trans
    (Glue.partialGlue_map e s.pathApp (endpointBoundary A a₀ a₁) s.pathApp_boundary_compatible).symm

theorem box_map {Δ : Context.{u}} (e : A ⟶ B)
    {a₀ : Term (reindex A (endpointSub Γ false))}
    {a₁ : Term (reindex A (endpointSub Γ true))}
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (path A a₀ a₁) p) φ) :
    pathFillingBox p φ (b.map (Functor.whiskerLeft p.mapElements (map e a₀ a₁))) =
      (pathFillingBox p φ b).map (Functor.whiskerLeft (pathFillingContext p).mapElements e) := by
  apply OpenBox.ext
  · exact congrArg (fun s => s.reindex (swapIntervals Δ))
      (boundary_map (Functor.whiskerLeft (liftSub (interval Γ) p).mapElements e)
        (b.tube.map (pathReindex A a₀ a₁ p)))
  · rfl

/-- A morphism preserving the chosen body fillings preserves the chosen path filling. -/
theorem filling_map (e : A ⟶ B) (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (he : ∀ {Ξ : Context.{u}} (q : total (interval Ξ) ⟶ total (interval Γ)) (ψ : Cofibration Ξ)
      (c : OpenBox (reindex A q) ψ),
      G.fill q ψ (c.map (Functor.whiskerLeft q.mapElements e)) =
        Term.map (Functor.whiskerLeft q.mapElements e) (F.fill q ψ c))
    (a₀ : Term (reindex A (endpointSub Γ false)))
    (a₁ : Term (reindex A (endpointSub Γ true)))
    {Δ : Context.{u}} (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (path A a₀ a₁) p) φ) :
    (pathFilling G hG
      (Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements e) a₀)
      (Term.map (Functor.whiskerLeft (endpointSub Γ true).mapElements e) a₁)).fill p φ
      (b.map (Functor.whiskerLeft p.mapElements (map e a₀ a₁))) =
    Term.map (Functor.whiskerLeft p.mapElements (map e a₀ a₁))
      ((pathFilling F hF a₀ a₁).fill p φ b) := by
  let b' := b.map (Functor.whiskerLeft p.mapElements (map e a₀ a₁))
  have hg := pathFillingResult_normalize p φ b' _ (hG.fills _ _ (pathFillingBox p φ b'))
  have hf := pathFillingResult_normalize p φ b _ (hF.fills _ _ (pathFillingBox p φ b))
  have hbody := (congrArg (G.fill (pathFillingContext p) (pathBoundaryFace φ))
    (box_map e p φ b)).trans (he _ _ (pathFillingBox p φ b))
  have h := congrArg (fun t => t.reindex (swapIntervals Δ)) hbody
  apply Term.map_injective_of_iso (pathReindexIso B _ _ p)
  apply pathApp_injective
  exact (congrArg pathApp hg).trans (h.trans
    (congrArg (fun t => Term.map (Functor.whiskerLeft (liftSub (interval Γ) p).mapElements e)
      (pathApp t)) hf).symm)

/-- Transporting a body filler transports its entire selected path filler. -/
theorem filling_transport (e : A ≅ B) (F : Filling A) (hF : F.Lawful)
    (a₀ : Term (reindex A (endpointSub Γ false)))
    (a₁ : Term (reindex A (endpointSub Γ true))) :
    (pathFilling F hF a₀ a₁).transport (iso e a₀ a₁) =
    pathFilling (F.transport e) (Filling.transport_lawful e F hF)
      (Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements e.hom) a₀)
      (Term.map (Functor.whiskerLeft (endpointSub Γ true).mapElements e.hom) a₁) := by
  apply Filling.transport_eq
  exact filling_map e.hom F hF (F.transport e) (Filling.transport_lawful e F hF)
    (fun q ψ c => congrArg (Term.map (Functor.whiskerLeft q.mapElements e.hom))
      (congrArg (F.fill q ψ) (OpenBox.map_iso_roundtrip (Functor.isoWhiskerLeft q.mapElements e).symm c))) a₀ a₁

theorem reindex_inverse_map {Δ : Context.{u}} (e : A ⟶ B)
    (a₀ : Term (reindex A (endpointSub Γ false)))
    (a₁ : Term (reindex A (endpointSub Γ true))) (σ : Δ ⟶ Γ)
    (p : Term (path (reindex A (liftSub (interval Γ) σ)) (a₀.reindex σ) (a₁.reindex σ))) :
    Term.map (pathReindex B
      (Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements e) a₀)
      (Term.map (Functor.whiskerLeft (endpointSub Γ true).mapElements e) a₁) σ)
      (Term.map (Functor.whiskerLeft σ.mapElements (map e a₀ a₁))
        (Term.map (pathReindexIso A a₀ a₁ σ).inv p)) =
    Term.map (map (Functor.whiskerLeft (liftSub (interval Γ) σ).mapElements e)
      (a₀.reindex σ) (a₁.reindex σ)) p :=
  congrArg (Term.map (map (Functor.whiskerLeft (liftSub (interval Γ) σ).mapElements e)
      (a₀.reindex σ) (a₁.reindex σ)))
    (Term.map_iso_roundtrip (pathReindexIso A a₀ a₁ σ).symm p)


end SquareKit.Cubical.Presheaf.SelectedPathTransport

namespace SquareKit.Cubical.Presheaf.SelectedIntervalTransport
open CategoryTheory
universe u
variable {Γ Δ : Context.{u}} {A B : Family (total (interval Γ))}
  (e : A ≅ B) (F : Filling A) (hF : F.Lawful)

abbrev atEndpoint (v : Bool) := Functor.isoWhiskerLeft (endpointSub Γ v).mapElements e

theorem fill_map {Ξ : Context.{u}} (p : total (interval Ξ) ⟶ total (interval Γ))
    (φ : Cofibration Ξ) (b : OpenBox (reindex A p) φ) :
    (F.transport e).fill p φ (b.map (Functor.whiskerLeft p.mapElements e.hom)) =
      Term.map (Functor.whiskerLeft p.mapElements e.hom) (F.fill p φ b) :=
  congrArg (Term.map (Functor.whiskerLeft p.mapElements e.hom))
    (congrArg (F.fill p φ) (OpenBox.map_iso_roundtrip (Functor.isoWhiskerLeft p.mapElements e).symm b))

theorem forward_map (σ : Δ ⟶ Γ)
    (a : Term (reindex A (endpointSub Δ false ≫ liftSub (interval Γ) σ))) :
    IntervalTransport.forward (F.transport e) σ
      (Term.map (Functor.whiskerLeft (endpointSub Δ false ≫ liftSub (interval Γ) σ).mapElements e.hom) a) =
      Term.map (Functor.whiskerLeft (liftSub (interval Γ) σ).mapElements e.hom)
        (IntervalTransport.forward F σ a) := by
  have hb : OpenBox.empty (reindex B (liftSub (interval Γ) σ))
      (Term.map (Functor.whiskerLeft (endpointSub Δ false ≫ liftSub (interval Γ) σ).mapElements e.hom) a) =
    (OpenBox.empty (reindex A (liftSub (interval Γ) σ)) a).map
      (Functor.whiskerLeft (liftSub (interval Γ) σ).mapElements e.hom) := by
    apply OpenBox.ext
    · apply PartialSection.ext
      intro x hx
      exact (Bool.false_ne_true hx).elim
    · rfl
  exact (congrArg ((F.transport e).fill (liftSub (interval Γ) σ) (Cofibration.bot Δ)) hb).trans
    (fill_map e F _ _ _)

include hF in
theorem map_commute :
    IntervalTransport.map F ≫ (atEndpoint e true).hom =
      (atEndpoint e false).hom ≫ IntervalTransport.map (F.transport e) := by
  let σ := projection (reindex A (endpointSub Γ false))
  let a := generic (reindex A (endpointSub Γ false))
  let b := Term.map (Functor.whiskerLeft σ.mapElements (atEndpoint e false).hom) a
  have h := IntervalTransport.map_section ((F.transport e).reindex (liftSub (interval Γ) σ))
    ((Filling.transport_lawful e F hF).reindex _) b
  have hm := IntervalTransport.map_reindex (F.transport e) (Filling.transport_lawful e F hF) σ
  have h' := (congrArg (fun k => Term.map k b) hm).symm.trans h
  have hf := congrArg (fun t => t.reindex (endpointSub (total (reindex A (endpointSub Γ false))) true))
    (forward_map e F σ a)
  ext x a₀
  exact (congrArg (fun t => t.val (extendObj (reindex A (endpointSub Γ false)) x a₀)) (h'.trans hf)).symm


section Endpoint
variable (a : Term (reindex A (endpointSub Γ false))) (b : Term (reindex A (endpointSub Γ true)))
  (q : Term (homogeneousPath (reindex A (endpointSub Γ true)) (Term.map (IntervalTransport.map F) a) b))

def endpointPath : Term (homogeneousPath (reindex B (endpointSub Γ true))
    (Term.map (IntervalTransport.map (F.transport e)) (Term.map (atEndpoint e false).hom a))
    (Term.map (atEndpoint e true).hom b)) :=
  pathLam (Term.map (Functor.whiskerLeft (projection (interval Γ)).mapElements (atEndpoint e true).hom)
    (pathApp q))
    ((congrArg (Term.map (atEndpoint e true).hom) (pathApp_zero q)).trans
      (congrArg (fun k => Term.map k a) (map_commute e F hF)))
    (congrArg (Term.map (atEndpoint e true).hom) (pathApp_one q))

theorem endpointInitial_map :
    IntervalTransport.endpointInitial (F.transport e) (Filling.transport_lawful e F hF)
      (Term.map (atEndpoint e false).hom a) (Term.map (atEndpoint e true).hom b)
      (endpointPath e F hF a b q) =
    Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements
      (SelectedPathTransport.map
        (Functor.whiskerLeft (liftSub (interval Γ) (projection (interval Γ))).mapElements e.hom)
        (a.reindex (projection (interval Γ))) (pathApp q)))
      (IntervalTransport.endpointInitial F hF a b q) := by
  let e' := Functor.whiskerLeft (liftSub (interval Γ) (projection (interval Γ))).mapElements e.hom
  let p := pathLam (IntervalTransport.forward F (𝟙 Γ) a) (IntervalTransport.forward_zero F hF (𝟙 Γ) a)
    ((IntervalTransport.map_section F hF a).symm.trans (pathApp_zero q).symm)
  let i := pathReindexIso (IntervalTransport.endpointBody (A := B))
    ((Term.map (atEndpoint e false).hom a).reindex (projection (interval Γ)))
    (pathApp (endpointPath e F hF a b q)) (endpointSub Γ false)
  have hl := Term.map_iso_roundtrip i.symm
    (pathLam (IntervalTransport.forward (F.transport e) (𝟙 Γ) (Term.map (atEndpoint e false).hom a))
      (IntervalTransport.forward_zero (F.transport e) (Filling.transport_lawful e F hF) (𝟙 Γ) _)
      ((IntervalTransport.map_section (F.transport e) (Filling.transport_lawful e F hF) _).symm.trans
        (pathApp_zero (endpointPath e F hF a b q)).symm))
  have hr := SelectedPathTransport.reindex_inverse_map e'
    (a.reindex (projection (interval Γ))) (pathApp q) (endpointSub Γ false) p
  apply Term.map_injective_of_iso i
  apply pathApp_injective
  exact (congrArg pathApp hl).trans ((forward_map e F (𝟙 Γ) a).trans (congrArg pathApp hr).symm)
theorem endpointLift_map :
    IntervalTransport.endpointLift (F.transport e) (Filling.transport_lawful e F hF)
      (Term.map (atEndpoint e false).hom a) (Term.map (atEndpoint e true).hom b)
      (endpointPath e F hF a b q) =
    Term.map (SelectedPathTransport.map
      (Functor.whiskerLeft (liftSub (interval Γ) (projection (interval Γ))).mapElements e.hom)
      (a.reindex (projection (interval Γ))) (pathApp q))
      (IntervalTransport.endpointLift F hF a b q) := by
  let τ := liftSub (interval Γ) (projection (interval Γ))
  let m := SelectedPathTransport.map (Functor.whiskerLeft τ.mapElements e.hom)
    (a.reindex (projection (interval Γ))) (pathApp q)
  let c := OpenBox.empty _ (IntervalTransport.endpointInitial F hF a b q)
  let c' := OpenBox.empty _ (IntervalTransport.endpointInitial (F.transport e)
    (Filling.transport_lawful e F hF) (Term.map (atEndpoint e false).hom a)
    (Term.map (atEndpoint e true).hom b) (endpointPath e F hF a b q))
  have hc : c' = c.map m := by
    apply OpenBox.ext
    · apply PartialSection.ext
      intro x hx
      exact (Bool.false_ne_true hx).elim
    · exact endpointInitial_map e F hF a b q
  have hm := SelectedPathTransport.filling_map (Functor.whiskerLeft τ.mapElements e.hom)
    (F.reindex τ) (hF.reindex _) ((F.transport e).reindex τ)
    ((Filling.transport_lawful e F hF).reindex _) (fun p ψ c => fill_map e F (p ≫ τ) ψ c)
    (a.reindex (projection (interval Γ))) (pathApp q) (𝟙 _) (Cofibration.bot Γ) c
  exact (congrArg ((pathFilling ((F.transport e).reindex τ)
    ((Filling.transport_lawful e F hF).reindex _)
    ((Term.map (atEndpoint e false).hom a).reindex (projection (interval Γ)))
    (pathApp (endpointPath e F hF a b q))).fill (𝟙 _) (Cofibration.bot Γ)) hc).trans hm

theorem endpointSquare_map :
    IntervalTransport.endpointSquare (F.transport e) (Filling.transport_lawful e F hF)
      (Term.map (atEndpoint e false).hom a) (Term.map (atEndpoint e true).hom b)
      (endpointPath e F hF a b q) =
    Term.map (Functor.whiskerLeft (projection (interval (total (interval Γ)))).mapElements e.hom)
      (IntervalTransport.endpointSquare F hF a b q) :=
  congrArg (fun t => (pathApp t).reindex (swapIntervals Γ)) (endpointLift_map e F hF a b q)

theorem adjustedPath_map :
    IntervalTransport.adjustedPath (F.transport e) (Filling.transport_lawful e F hF)
      (Term.map (atEndpoint e false).hom a) (Term.map (atEndpoint e true).hom b)
      (endpointPath e F hF a b q) =
    Term.map e.hom (IntervalTransport.adjustedPath F hF a b q) :=
  congrArg (fun t => t.reindex (endpointSub (total (interval Γ)) true))
    (endpointSquare_map e F hF a b q)

end Endpoint

section Backward
variable (φ : Cofibration Γ) (t : PartialSection A (φ.reindex (projection (interval Γ))))
  (b : Term (reindex A (endpointSub Γ true)))
  (hb : ∀ x (hx : φ.Full x), t.val ((endpointSub Γ true).mapElements.obj x) hx = b.val x)

theorem backwardBox_map :
    IntervalTransport.backwardBox φ (t.map e.hom) (Term.map (atEndpoint e true).hom b)
      (fun x hx => congrArg (e.hom.app _) (hb x hx)) =
    (IntervalTransport.backwardBox φ t b hb).map (Functor.whiskerLeft (reverseInterval Γ).mapElements e.hom) := by
  apply OpenBox.ext
  · rfl
  · exact (Term.map_convert_sub e.hom (reverseInterval_endpoint Γ false).symm b).symm

theorem backwardRelative_map :
    IntervalTransport.backwardRelative (F.transport e) φ (t.map e.hom) (Term.map (atEndpoint e true).hom b)
      (fun x hx => congrArg (e.hom.app _) (hb x hx)) =
    Term.map e.hom (IntervalTransport.backwardRelative F φ t b hb) := by
  have hc := backwardBox_map e φ t b hb
  have hf := (congrArg ((F.transport e).fill (reverseInterval Γ) φ) hc).trans
    (fill_map e F (reverseInterval Γ) φ (IntervalTransport.backwardBox φ t b hb))
  have h := congrArg (fun z => (z.reindex (reverseInterval Γ)).convert
    (congrArg (reindex B) (reverseInterval_twice Γ))) hf
  exact h.trans (Term.map_convert_sub e.hom (reverseInterval_twice Γ)
    ((F.fill (reverseInterval Γ) φ (IntervalTransport.backwardBox φ t b hb)).reindex (reverseInterval Γ))).symm
end Backward

end SquareKit.Cubical.Presheaf.SelectedIntervalTransport

namespace SquareKit.Cubical.Presheaf.EquivalenceIsoTransport
open CategoryTheory
universe u
variable {Γ Δ : Context.{u}} {A A' B B' : Family Γ}
  (i : A' ≅ A) (j : B ≅ B') (f : A ⟶ B)
  (ρ : Δ ⟶ total B') (z : Term (reindex (oldFiber j f) ρ))

private theorem forward_apply :
    Term.map (Functor.whiskerLeft ρ.mapElements (fiberIso i j f).hom) z = forward i j f ρ z :=
  (forward_natural i j f (projection (oldFiber j f)) (pair ρ z) (generic (oldFiber j f))).symm

theorem fiberIso_fst :
    genericFiberFst (conjugate i j f) ρ
      (Term.map (Functor.whiskerLeft ρ.mapElements (fiberIso i j f).hom) z) =
    Term.map (Functor.whiskerLeft (ρ ≫ projection B').mapElements i.inv)
      (genericFiberFst f (ρ ≫ targetSub j) z) :=
  congrArg (genericFiberFst (conjugate i j f) ρ) (forward_apply i j f ρ z)

theorem fiberIso_pathApp :
    pathApp (genericFiberPath (conjugate i j f) ρ
      (Term.map (Functor.whiskerLeft ρ.mapElements (fiberIso i j f).hom) z)) =
    Term.map (Functor.whiskerLeft (projection (interval Δ) ≫ ρ ≫ projection B').mapElements j.hom)
      (pathApp (genericFiberPath f (ρ ≫ targetSub j) z)) := by
  have h := congrArg (fun s => pathApp (genericFiberPath (conjugate i j f) ρ s))
    (forward_apply i j f ρ z)
  exact h.trans (congrArg pathApp (genericFiberPath_intro (conjugate i j f) ρ _ (forwardPath i j f ρ z)))

end SquareKit.Cubical.Presheaf.EquivalenceIsoTransport

namespace SquareKit.Cubical.Presheaf.SelectedIntervalTransport
open CategoryTheory
universe u
variable {Γ Δ : Context.{u}} {A B : Family (total (interval Γ))}
  (e : A ≅ B) (F : Filling A) (hF : F.Lawful)

include hF in
theorem conjugate_map :
    (atEndpoint e false).inv ≫ IntervalTransport.map F ≫ (atEndpoint e true).hom =
      IntervalTransport.map (F.transport e) := by
  exact (congrArg (fun k => (atEndpoint e false).inv ≫ k) (map_commute e F hF)).trans
    (Iso.inv_hom_id_assoc (atEndpoint e false) (IntervalTransport.map (F.transport e)))

private theorem endpointSquare_congr
    (a a' : Term (reindex A (endpointSub Γ false))) (ha : a = a')
    (b b' : Term (reindex A (endpointSub Γ true))) (hb : b = b')
    (q : Term (homogeneousPath (reindex A (endpointSub Γ true)) (Term.map (IntervalTransport.map F) a) b))
    (q' : Term (homogeneousPath (reindex A (endpointSub Γ true)) (Term.map (IntervalTransport.map F) a') b'))
    (hq : HEq q q') :
    IntervalTransport.endpointSquare F hF a b q = IntervalTransport.endpointSquare F hF a' b' q' := by
  cases ha
  cases hb
  cases hq
  rfl

end SquareKit.Cubical.Presheaf.SelectedIntervalTransport

namespace SquareKit.Cubical.Presheaf.SelectedIntervalTransport.FiberNaturality
open CategoryTheory
open IntervalTransport
universe u
variable {Γ Δ : Context.{u}} {A B : Family (total (interval Γ))}
  (e : A ≅ B) (F : Filling A) (hF : F.Lawful)

abbrev original := IntervalTransport.map F
abbrev changed := EquivalenceIsoTransport.conjugate (atEndpoint e false).symm (atEndpoint e true) (original F)
noncomputable abbrev fiberIso := EquivalenceIsoTransport.fiberIso (atEndpoint e false).symm (atEndpoint e true) (original F)
abbrev target := EquivalenceIsoTransport.targetSub (atEndpoint e true)

variable (ρ : Δ ⟶ total (reindex B (endpointSub Γ true))) {φ : Cofibration Δ}
  (z : PartialSection (reindex (EquivalenceIsoTransport.oldFiber (atEndpoint e true) (original F)) ρ) φ)

noncomputable abbrev input := z.map (Functor.whiskerLeft ρ.mapElements (fiberIso e F).hom)

theorem localSource_map :
    FiberExtension.localSource (changed e F) ρ (input e F ρ z) =
    Term.map (Functor.whiskerLeft (FiberExtension.localBase (φ := φ) ρ).mapElements
      (atEndpoint e false).hom)
      (FiberExtension.localSource (original F) (ρ ≫ target e) z) :=
  EquivalenceIsoTransport.fiberIso_fst (atEndpoint e false).symm (atEndpoint e true)
    (original F) (restrictInclusion φ ≫ ρ) z.toRestricted

theorem localTarget_map :
    FiberExtension.localTarget (φ := φ) ρ =
    Term.map (Functor.whiskerLeft (FiberExtension.localBase (φ := φ) ρ).mapElements
      (atEndpoint e true).hom)
      (FiberExtension.localTarget (φ := φ) (ρ ≫ target e)) := by
  apply Term.ext
  intro x
  exact (ConcreteCategory.congr_hom (NatTrans.congr_app (atEndpoint e true).inv_hom_id
    ((FiberExtension.localBase (φ := φ) ρ).mapElements.obj x)) _).symm

theorem localPath_map :
    pathApp (FiberExtension.localPath (F.transport e) (Filling.transport_lawful e F hF)
      (changed e F) (conjugate_map e F hF) ρ (input e F ρ z)) =
    Term.map (Functor.whiskerLeft
      (projection (interval (restrictContext φ)) ≫ FiberExtension.localBase (φ := φ) ρ).mapElements
      (atEndpoint e true).hom)
      (pathApp (FiberExtension.localPath F hF (original F) rfl (ρ ≫ target e) z)) :=
  EquivalenceIsoTransport.fiberIso_pathApp (atEndpoint e false).symm (atEndpoint e true)
    (original F) (restrictInclusion φ ≫ ρ) z.toRestricted

theorem localSquare_map :
    FiberExtension.localSquare (F.transport e) (Filling.transport_lawful e F hF)
      (changed e F) (conjugate_map e F hF) ρ (input e F ρ z) =
    Term.map (Functor.whiskerLeft
      (projection (interval (total (interval (restrictContext φ)))) ≫
        liftSub (interval Γ) (FiberExtension.localBase (φ := φ) ρ)).mapElements e.hom)
      (FiberExtension.localSquare F hF (original F) rfl (ρ ≫ target e) z) := by
  let τ := liftSub (interval Γ) (FiberExtension.localBase (φ := φ) ρ)
  let d := Functor.isoWhiskerLeft τ.mapElements e
  let a := FiberExtension.localSource (original F) (ρ ≫ target e) z
  let b := FiberExtension.localTarget (φ := φ) (ρ ≫ target e)
  let q := FiberExtension.localPath F hF (original F) rfl (ρ ≫ target e) z
  have hp : HEq (FiberExtension.localPath (F.transport e) (Filling.transport_lawful e F hF)
      (changed e F) (conjugate_map e F hF) ρ (input e F ρ z))
      (endpointPath d (F.reindex τ) (hF.reindex τ) a b q) :=
    pathTerm_hext _ _ (localPath_map e F hF ρ z)
  exact (endpointSquare_congr ((F.transport e).reindex τ)
    ((Filling.transport_lawful e F hF).reindex τ) _ _ (localSource_map e F ρ z)
      _ _ (localTarget_map e ρ) _ _ hp).trans
    (endpointSquare_map d (F.reindex τ) (hF.reindex τ) a b q)

theorem localAdjusted_map :
    FiberExtension.localAdjusted (F.transport e) (Filling.transport_lawful e F hF)
      (changed e F) (conjugate_map e F hF) ρ (input e F ρ z) =
    Term.map (Functor.whiskerLeft
      (liftSub (interval Γ) (FiberExtension.localBase (φ := φ) ρ)).mapElements e.hom)
      (FiberExtension.localAdjusted F hF (original F) rfl (ρ ≫ target e) z) :=
  congrArg (fun t => t.reindex (endpointSub (total (interval (restrictContext φ))) true))
    (localSquare_map e F hF ρ z)

theorem partialAdjusted_map :
    FiberExtension.partialAdjusted (F.transport e) (Filling.transport_lawful e F hF)
      (changed e F) (conjugate_map e F hF) ρ (input e F ρ z) =
    (FiberExtension.partialAdjusted F hF (original F) rfl (ρ ≫ target e) z).map
      (Functor.whiskerLeft (liftSub (interval Γ) (FiberExtension.base ρ)).mapElements e.hom) := by
  apply PartialSection.ext
  intro x hx
  exact congrArg (fun t => t.val ((restrictedInterval φ).mapElements.obj (Glue.faceObj
    (φ.reindex (projection (interval Δ))) x hx))) (localAdjusted_map e F hF ρ z)


private theorem backwardRelative_congr {Ω : Context.{u}} {C : Family (total (interval Ω))}
    (G : Filling C) (ψ : Cofibration Ω)
    (t t' : PartialSection C (ψ.reindex (projection (interval Ω)))) (ht : t = t')
    (b b' : Term (reindex C (endpointSub Ω true))) (hb : b = b')
    (h : ∀ x (hx : ψ.Full x), t.val ((endpointSub Ω true).mapElements.obj x) hx = b.val x)
    (h' : ∀ x (hx : ψ.Full x), t'.val ((endpointSub Ω true).mapElements.obj x) hx = b'.val x) :
    backwardRelative G ψ t b h = backwardRelative G ψ t' b' h' := by
  cases ht
  cases hb
  rfl

theorem fullPath_map :
    FiberExtension.fullPath (F.transport e) (Filling.transport_lawful e F hF)
      (changed e F) (conjugate_map e F hF) ρ (input e F ρ z) =
    Term.map (Functor.whiskerLeft (liftSub (interval Γ) (FiberExtension.base ρ)).mapElements e.hom)
      (FiberExtension.fullPath F hF (original F) rfl (ρ ≫ target e) z) := by
  let τ := liftSub (interval Γ) (FiberExtension.base ρ)
  let d := Functor.isoWhiskerLeft τ.mapElements e
  have hb : (generic (reindex B (endpointSub Γ true))).reindex ρ =
      Term.map (atEndpoint d true).hom
        ((generic (reindex A (endpointSub Γ true))).reindex (ρ ≫ target e)) := by
    apply Term.ext
    intro x
    exact (ConcreteCategory.congr_hom (NatTrans.congr_app (atEndpoint e true).inv_hom_id
      ((FiberExtension.base ρ).mapElements.obj x)) _).symm
  exact (backwardRelative_congr ((F.transport e).reindex τ) φ _ _
    (partialAdjusted_map e F hF ρ z) _ _ hb _ _).trans
    (backwardRelative_map d (F.reindex τ) φ _ _
      (FiberExtension.partialAdjusted_one F hF (original F) rfl (ρ ≫ target e) z))

theorem fullSource_map :
    FiberExtension.fullSource (F.transport e) (Filling.transport_lawful e F hF)
      (changed e F) (conjugate_map e F hF) ρ (input e F ρ z) =
    Term.map (Functor.whiskerLeft (FiberExtension.base ρ).mapElements (atEndpoint e false).hom)
      (FiberExtension.fullSource F hF (original F) rfl (ρ ≫ target e) z) :=
  congrArg (fun t => t.reindex (endpointSub Δ false)) (fullPath_map e F hF ρ z)

theorem fullForward_map :
    FiberExtension.fullForward (F.transport e) (Filling.transport_lawful e F hF)
      (changed e F) (conjugate_map e F hF) ρ (input e F ρ z) =
    Term.map (Functor.whiskerLeft (liftSub (interval Γ) (FiberExtension.base ρ)).mapElements e.hom)
      (FiberExtension.fullForward F hF (original F) rfl (ρ ≫ target e) z) := by
  let τ := liftSub (interval Γ) (FiberExtension.base ρ)
  exact (congrArg (forward ((F.transport e).reindex τ) (𝟙 Δ))
    (fullSource_map e F hF ρ z)).trans
    (forward_map (Functor.isoWhiskerLeft τ.mapElements e) (F.reindex τ) (𝟙 Δ) _)

end SquareKit.Cubical.Presheaf.SelectedIntervalTransport.FiberNaturality

namespace SquareKit.Cubical.Presheaf.SelectedPathTransport
open CategoryTheory
universe u
variable {Γ Δ : Context.{u}} {B : Family (total (interval Γ))}

theorem reindexed_hext
    (a a' : Term (reindex B (endpointSub Γ false))) (ha : a = a')
    (b b' : Term (reindex B (endpointSub Γ true))) (hb : b = b')
    (σ : Δ ⟶ Γ) (p : Term (reindex (path B a b) σ)) (p' : Term (reindex (path B a' b') σ))
    (h : pathApp (Term.map (pathReindex B a b σ) p) =
      pathApp (Term.map (pathReindex B a' b' σ) p')) : HEq p p' := by
  cases ha
  cases hb
  apply heq_of_eq
  apply Term.map_injective_of_iso (pathReindexIso B a b σ)
  exact pathApp_injective h

theorem partial_hext
    (a a' : Term (reindex B (endpointSub Γ false))) (ha : a = a')
    (b b' : Term (reindex B (endpointSub Γ true))) (hb : b = b')
    (φ : Cofibration Γ) (p : PartialSection (path B a b) φ) (p' : PartialSection (path B a' b') φ)
    (h : pathApp (Term.map (pathReindex B a b (restrictInclusion φ)) p.toRestricted) =
      pathApp (Term.map (pathReindex B a' b' (restrictInclusion φ)) p'.toRestricted)) : HEq p p' := by
  have hp := reindexed_hext a a' ha b b' hb (restrictInclusion φ) p.toRestricted p'.toRestricted h
  cases ha
  cases hb
  exact heq_of_eq (congrArg PartialSection.ofRestricted (eq_of_heq hp))

theorem filling_map_heq {A : Family (total (interval Γ))}
    (e : A ⟶ B) (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (he : ∀ {Ξ : Context.{u}} (q : total (interval Ξ) ⟶ total (interval Γ)) (ψ : Cofibration Ξ)
      (c : OpenBox (reindex A q) ψ),
      G.fill q ψ (c.map (Functor.whiskerLeft q.mapElements e)) =
        Term.map (Functor.whiskerLeft q.mapElements e) (F.fill q ψ c))
    (a₀ : Term (reindex A (endpointSub Γ false)))
    (a₁ : Term (reindex A (endpointSub Γ true)))
    (b₀ : Term (reindex B (endpointSub Γ false)))
    (b₁ : Term (reindex B (endpointSub Γ true)))
    (h₀ : b₀ = Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements e) a₀)
    (h₁ : b₁ = Term.map (Functor.whiskerLeft (endpointSub Γ true).mapElements e) a₁)
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (c : OpenBox (reindex (path A a₀ a₁) p) φ)
    (d : OpenBox (reindex (path B b₀ b₁) p) φ)
    (ht : HEq d.tube (c.map (Functor.whiskerLeft p.mapElements (map e a₀ a₁))).tube)
    (hb : HEq d.base (c.map (Functor.whiskerLeft p.mapElements (map e a₀ a₁))).base) :
    HEq ((pathFilling G hG b₀ b₁).fill p φ d)
      (Term.map (Functor.whiskerLeft p.mapElements (map e a₀ a₁))
        ((pathFilling F hF a₀ a₁).fill p φ c)) := by
  subst b₀
  subst b₁
  have hd : d = c.map (Functor.whiskerLeft p.mapElements (map e a₀ a₁)) :=
    OpenBox.ext (eq_of_heq ht) (eq_of_heq hb)
  exact heq_of_eq ((congrArg ((pathFilling G hG _ _).fill p φ) hd).trans
    (filling_map e F hF G hG he a₀ a₁ p φ c))

theorem pathApp_of_heq
    (a a' : Term (reindex B (endpointSub Γ false))) (ha : a = a')
    (b b' : Term (reindex B (endpointSub Γ true))) (hb : b = b')
    (p : Term (path B a b)) (p' : Term (path B a' b')) (hp : HEq p p') :
    pathApp p = pathApp p' := by
  cases ha
  cases hb
  exact congrArg pathApp (eq_of_heq hp)

end SquareKit.Cubical.Presheaf.SelectedPathTransport

namespace SquareKit.Cubical.Presheaf.SelectedIntervalTransport.FiberNaturality
open CategoryTheory
open IntervalTransport
universe u
variable {Γ Δ : Context.{u}} {A B : Family (total (interval Γ))}
  (e : A ≅ B) (F : Filling A) (hF : F.Lawful)
  (ρ : Δ ⟶ total (reindex B (endpointSub Γ true))) {φ : Cofibration Δ}
  (z : PartialSection (reindex (EquivalenceIsoTransport.oldFiber (atEndpoint e true) (original F)) ρ) φ)

noncomputable abbrev comparisonMap := SelectedPathTransport.map
  (Functor.whiskerLeft
    (projection (interval (total (interval Δ))) ≫ liftSub (interval Γ) (FiberExtension.base ρ)).mapElements e.hom)
  (FiberExtension.fullForward F hF (original F) rfl (ρ ≫ target e) z)
  (FiberExtension.fullPath F hF (original F) rfl (ρ ≫ target e) z)

theorem partialComparison_map : HEq
    (FiberExtension.partialComparison (F.transport e) (Filling.transport_lawful e F hF)
      (changed e F) (conjugate_map e F hF) ρ (input e F ρ z))
    ((FiberExtension.partialComparison F hF (original F) rfl (ρ ≫ target e) z).map
      (comparisonMap e F hF ρ z)) := by
  apply SelectedPathTransport.partial_hext _ _ (fullForward_map e F hF ρ z)
    _ _ (fullPath_map e F hF ρ z)
  let χ := φ.reindex (projection (interval Δ))
  have hn := Term.map_iso_roundtrip
    (pathReindexIso (FiberExtension.comparisonBody ρ)
      (FiberExtension.fullForward (F.transport e) (Filling.transport_lawful e F hF)
        (changed e F) (conjugate_map e F hF) ρ (input e F ρ z))
      (FiberExtension.fullPath (F.transport e) (Filling.transport_lawful e F hF)
        (changed e F) (conjugate_map e F hF) ρ (input e F ρ z))
      (restrictInclusion χ)).symm
    (homogeneousReindex (FiberExtension.localComparison (F.transport e)
      (Filling.transport_lawful e F hF) (changed e F) (conjugate_map e F hF)
      ρ (input e F ρ z)) (restrictedInterval φ))
  have ho := SelectedPathTransport.reindex_inverse_map
    (Functor.whiskerLeft
      (projection (interval (total (interval Δ))) ≫ liftSub (interval Γ) (FiberExtension.base ρ)).mapElements e.hom)
    (FiberExtension.fullForward F hF (original F) rfl (ρ ≫ target e) z)
    (FiberExtension.fullPath F hF (original F) rfl (ρ ≫ target e) z)
    (restrictInclusion χ)
    (homogeneousReindex (FiberExtension.localComparison F hF (original F) rfl
      (ρ ≫ target e) z) (restrictedInterval φ))
  exact (congrArg pathApp hn).trans
    ((congrArg (fun t => t.reindex (liftSub (interval (total (interval (restrictContext φ)))) (restrictedInterval φ)))
      (localSquare_map e F hF ρ z)).trans (congrArg pathApp ho).symm)

theorem comparisonInitial_map : HEq
    (FiberExtension.comparisonInitial (F.transport e) (Filling.transport_lawful e F hF)
      (changed e F) (conjugate_map e F hF) ρ (input e F ρ z))
    (Term.map (Functor.whiskerLeft (endpointSub Δ false).mapElements (comparisonMap e F hF ρ z))
      (FiberExtension.comparisonInitial F hF (original F) rfl (ρ ≫ target e) z)) := by
  apply SelectedPathTransport.reindexed_hext _ _ (fullForward_map e F hF ρ z)
    _ _ (fullPath_map e F hF ρ z)
  have hn := Term.map_iso_roundtrip
    (pathReindexIso (FiberExtension.comparisonBody ρ)
      (FiberExtension.fullForward (F.transport e) (Filling.transport_lawful e F hF)
        (changed e F) (conjugate_map e F hF) ρ (input e F ρ z))
      (FiberExtension.fullPath (F.transport e) (Filling.transport_lawful e F hF)
        (changed e F) (conjugate_map e F hF) ρ (input e F ρ z))
      (endpointSub Δ false)).symm
    (pathLam ((FiberExtension.fullSource (F.transport e) (Filling.transport_lawful e F hF)
      (changed e F) (conjugate_map e F hF) ρ (input e F ρ z)).reindex (projection (interval Δ)))
      (forward_zero ((F.transport e).reindex (liftSub (interval Γ) (FiberExtension.base ρ)))
        ((Filling.transport_lawful e F hF).reindex _) (𝟙 Δ) _).symm rfl)
  have ho := SelectedPathTransport.reindex_inverse_map
    (Functor.whiskerLeft
      (projection (interval (total (interval Δ))) ≫ liftSub (interval Γ) (FiberExtension.base ρ)).mapElements e.hom)
    (FiberExtension.fullForward F hF (original F) rfl (ρ ≫ target e) z)
    (FiberExtension.fullPath F hF (original F) rfl (ρ ≫ target e) z)
    (endpointSub Δ false)
    (pathLam ((FiberExtension.fullSource F hF (original F) rfl (ρ ≫ target e) z).reindex (projection (interval Δ)))
      (forward_zero (F.reindex (liftSub (interval Γ) (FiberExtension.base ρ)))
        (hF.reindex _) (𝟙 Δ) _).symm rfl)
  exact (congrArg pathApp hn).trans
    ((congrArg (fun t => t.reindex (projection (interval Δ)))
      (fullSource_map e F hF ρ z)).trans (congrArg pathApp ho).symm)

theorem comparisonFilled_map : HEq
    (FiberExtension.comparisonFilled (F.transport e) (Filling.transport_lawful e F hF)
      (changed e F) (conjugate_map e F hF) ρ (input e F ρ z))
    (Term.map (comparisonMap e F hF ρ z)
      (FiberExtension.comparisonFilled F hF (original F) rfl (ρ ≫ target e) z)) := by
  let τ := projection (interval (total (interval Δ))) ≫ liftSub (interval Γ) (FiberExtension.base ρ)
  exact SelectedPathTransport.filling_map_heq (Functor.whiskerLeft τ.mapElements e.hom)
    (F.reindex τ) (hF.reindex _) ((F.transport e).reindex τ)
    ((Filling.transport_lawful e F hF).reindex _)
    (fun p ψ c => fill_map e F (p ≫ τ) ψ c)
    _ _ _ _ (fullForward_map e F hF ρ z) (fullPath_map e F hF ρ z)
    (𝟙 _) φ _ _ (partialComparison_map e F hF ρ z) (comparisonInitial_map e F hF ρ z)


theorem finalPath_map :
    pathApp (FiberExtension.finalPath (F.transport e) (Filling.transport_lawful e F hF)
      (changed e F) (conjugate_map e F hF) ρ (input e F ρ z)) =
    Term.map (Functor.whiskerLeft
      (projection (interval Δ) ≫ FiberExtension.base ρ).mapElements (atEndpoint e true).hom)
      (pathApp (FiberExtension.finalPath F hF (original F) rfl (ρ ≫ target e) z)) := by
  have hp := SelectedPathTransport.pathApp_of_heq _ _ (fullForward_map e F hF ρ z)
    _ _ (fullPath_map e F hF ρ z) _ _ (comparisonFilled_map e F hF ρ z)
  exact congrArg (fun t => t.reindex
    (liftSub (interval (total (interval Δ))) (endpointSub Δ true))) hp

theorem extend_map :
    FiberExtension.extend (F.transport e) (Filling.transport_lawful e F hF)
      (changed e F) (conjugate_map e F hF) ρ (input e F ρ z) =
    Term.map (Functor.whiskerLeft ρ.mapElements (fiberIso e F).hom)
      (FiberExtension.extend F hF (original F) rfl (ρ ≫ target e) z) := by
  apply genericFiberTerm_ext (changed e F) ρ
  · exact (fullSource_map e F hF ρ z).trans
      (EquivalenceIsoTransport.fiberIso_fst (atEndpoint e false).symm (atEndpoint e true)
        (original F) ρ (FiberExtension.extend F hF (original F) rfl (ρ ≫ target e) z)).symm
  · apply pathTerm_hext
    have hn := genericFiberPath_intro (changed e F) ρ
      (FiberExtension.fullSource (F.transport e) (Filling.transport_lawful e F hF)
        (changed e F) (conjugate_map e F hF) ρ (input e F ρ z))
      (FiberExtension.finalPath (F.transport e) (Filling.transport_lawful e F hF)
        (changed e F) (conjugate_map e F hF) ρ (input e F ρ z))
    have ho := genericFiberPath_intro (original F) (ρ ≫ target e)
      (FiberExtension.fullSource F hF (original F) rfl (ρ ≫ target e) z)
      (FiberExtension.finalPath F hF (original F) rfl (ρ ≫ target e) z)
    exact (congrArg pathApp hn).trans ((finalPath_map e F hF ρ z).trans
      ((congrArg (fun q => Term.map (Functor.whiskerLeft
        (projection (interval Δ) ≫ FiberExtension.base ρ).mapElements (atEndpoint e true).hom)
        (pathApp q)) ho).symm.trans
        (EquivalenceIsoTransport.fiberIso_pathApp (atEndpoint e false).symm (atEndpoint e true)
          (original F) ρ (FiberExtension.extend F hF (original F) rfl (ρ ≫ target e) z)).symm))

end SquareKit.Cubical.Presheaf.SelectedIntervalTransport.FiberNaturality

namespace SquareKit.Cubical.Presheaf.SelectedIntervalTransport
open CategoryTheory
universe u
variable {Γ : Context.{u}} {A B : Family (total (interval Γ))}
  (e : A ≅ B) (F : Filling A) (hF : F.Lawful)

private theorem fibers_transport_step :
    (HomotopyContractible.ofExtensions
      (fun ρ _ z => IntervalTransport.FiberExtension.extend F hF (IntervalTransport.map F) rfl
        (ρ ≫ FiberNaturality.target e) z)
      (fun ρ _ z x hx => IntervalTransport.FiberExtension.extend_boundary F hF (IntervalTransport.map F) rfl
        (ρ ≫ FiberNaturality.target e) z x hx)).transport (FiberNaturality.fiberIso e F) =
    (IntervalTransport.equivalenceOf (F.transport e) (Filling.transport_lawful e F hF)
      (FiberNaturality.changed e F) (conjugate_map e F hF)).fibers := by
  let f := IntervalTransport.map F
  let τ := FiberNaturality.target e
  let E := fun {Δ : Context.{u}} (ρ : Δ ⟶ total (reindex A (endpointSub Γ true)))
    (φ : Cofibration Δ) (z : PartialSection _ φ) => IntervalTransport.FiberExtension.extend F hF f rfl ρ z
  let hb := fun {Δ : Context.{u}} (ρ : Δ ⟶ total (reindex A (endpointSub Γ true)))
    (φ : Cofibration Δ) (z : PartialSection _ φ) x hx => IntervalTransport.FiberExtension.extend_boundary F hF f rfl ρ z x hx
  let hu := fun {Δ Θ : Context.{u}} (ρ : Δ ⟶ total (reindex A (endpointSub Γ true)))
    (φ : Cofibration Δ) (z : PartialSection _ φ) (ν : Θ ⟶ Δ) => IntervalTransport.FiberExtension.extend_reindex F hF f rfl ρ z ν
  exact HomotopyContractible.ofExtensions_iso
        (A := EquivalenceIsoTransport.oldFiber (atEndpoint e true) f)
        (B := EquivalenceIsoTransport.fiber (FiberNaturality.changed e F))
        (fun ρ φ z => E (ρ ≫ τ) φ z) (fun ρ φ z x hx => hb (ρ ≫ τ) φ z x hx)
        (fun ρ φ z ν => hu (ρ ≫ τ) φ z ν)
        (fun ρ _ z => IntervalTransport.FiberExtension.extend (F.transport e)
          (Filling.transport_lawful e F hF) (FiberNaturality.changed e F)
          (conjugate_map e F hF) ρ z)
        (fun ρ _ z x hx => IntervalTransport.FiberExtension.extend_boundary (F.transport e)
          (Filling.transport_lawful e F hF) (FiberNaturality.changed e F)
          (conjugate_map e F hF) ρ z x hx) (FiberNaturality.fiberIso e F)
        (fun ρ _ z => (FiberNaturality.extend_map e F hF ρ z).symm)

private theorem fibers_transport :
    (((IntervalTransport.equivalence F hF).fibers).reindex (FiberNaturality.target e)).transport
      (FiberNaturality.fiberIso e F) =
    (IntervalTransport.equivalenceOf (F.transport e) (Filling.transport_lawful e F hF)
      (FiberNaturality.changed e F) (conjugate_map e F hF)).fibers := by
  have h := HomotopyContractible.ofExtensions_reindex
    (fun ρ _ z => IntervalTransport.FiberExtension.extend F hF (IntervalTransport.map F) rfl ρ z)
    (fun ρ _ z x hx => IntervalTransport.FiberExtension.extend_boundary F hF (IntervalTransport.map F) rfl ρ z x hx)
    (fun ρ _ z ν => IntervalTransport.FiberExtension.extend_reindex F hF (IntervalTransport.map F) rfl ρ z ν)
    (FiberNaturality.target e)
  exact (congrArg (fun c => c.transport (FiberNaturality.fiberIso e F)) h).trans
    (fibers_transport_step e F hF)

theorem equivalenceOf_transport :
    (IntervalTransport.equivalence F hF).conjugateIso (atEndpoint e false).symm (atEndpoint e true) =
    IntervalTransport.equivalenceOf (F.transport e) (Filling.transport_lawful e F hF)
      (FiberNaturality.changed e F) (conjugate_map e F hF) :=
  congrArg HomotopyEquivalence.mk (fibers_transport e F hF)

theorem equivalence_transport :
    HEq ((IntervalTransport.equivalence F hF).conjugateIso (atEndpoint e false).symm (atEndpoint e true))
      (IntervalTransport.equivalence (F.transport e) (Filling.transport_lawful e F hF)) :=
  (heq_of_eq (equivalenceOf_transport e F hF)).trans
    (IntervalTransport.equivalenceOf_heq _ _ _ _)

end SquareKit.Cubical.Presheaf.SelectedIntervalTransport

namespace SquareKit.Cubical.Presheaf.HomotopyContractible
open CategoryTheory
universe u
variable {Γ Δ : Context.{u}} {A B : Family Γ}

theorem retract_reindex (c : HomotopyContractible A) (F : Filling B) (hF : F.Lawful)
    (f : A ⟶ B) (g : B ⟶ A)
    (h : Term (homogeneousPath (Presheaf.reindex B (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements f)
        (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B))) (generic B)))
    (σ : Δ ⟶ Γ) :
    (c.retract F hF f g h).reindex σ =
    (c.reindex σ).retract (F.reindex σ) (hF.reindex σ)
      (Functor.whiskerLeft σ.mapElements f) (Functor.whiskerLeft σ.mapElements g)
      (homogeneousReindex h (liftSub B σ)) := by
  refine HomotopyContractible.ext ?_ ?_
  · rfl
  apply pathTerm_hext
  let p := homogeneousPathMap (Functor.whiskerLeft (projection B).mapElements f)
    ((c.reindex (projection B)).pathTo
      (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B)))
  have hc := homogeneousConcat_reindex (F.reindex (projection B)) (hF.reindex _) p h (liftSub B σ)
  have hp : homogeneousReindex p (liftSub B σ) =
      homogeneousPathMap (Functor.whiskerLeft (projection (Presheaf.reindex B σ)).mapElements
        (Functor.whiskerLeft σ.mapElements f))
        (((c.reindex σ).reindex (projection (Presheaf.reindex B σ))).pathTo
          (Term.map (Functor.whiskerLeft (projection (Presheaf.reindex B σ)).mapElements
            (Functor.whiskerLeft σ.mapElements g)) (generic (Presheaf.reindex B σ)))) := by
    apply pathApp_injective
    apply Term.ext
    intro x
    rfl
  exact (congrArg pathApp hc).trans (congrArg (fun q => pathApp
    (homogeneousConcat ((F.reindex σ).reindex (projection (Presheaf.reindex B σ)))
      ((hF.reindex σ).reindex _) q (homogeneousReindex h (liftSub B σ)))) hp)

end SquareKit.Cubical.Presheaf.HomotopyContractible

namespace SquareKit.Cubical.Presheaf.NativeConcat
open CategoryTheory
universe u
variable {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B)
  (F : Filling A) (hF : F.Lawful) {a b c : Term A}
  (p : Term (homogeneousPath A a b)) (q : Term (homogeneousPath A b c))

def transportLineIso : line (a := a) q ≅
    line (a := Term.map e.hom a) (homogeneousPathMap e.hom q) :=
  SelectedPathTransport.iso (Functor.isoWhiskerLeft
    (projection (interval (total (interval Γ))) ≫ projection (interval Γ)).mapElements e)
    (a.reindex (projection (interval Γ))) (pathApp q)

theorem filling_transport :
    (filling (a := a) q F hF).transport (transportLineIso (a := a) e q) =
    filling (a := Term.map e.hom a) (homogeneousPathMap e.hom q) (F.transport e) (Filling.transport_lawful e F hF) :=
  SelectedPathTransport.filling_transport
    (Functor.isoWhiskerLeft
      (projection (interval (total (interval Γ))) ≫ projection (interval Γ)).mapElements e)
    (F.reindex (projection (interval (total (interval Γ))) ≫ projection (interval Γ)))
    (hF.reindex _) (a.reindex (projection (interval Γ))) (pathApp q)

theorem initial_transport :
    Term.map (Functor.whiskerLeft (endpointSub Γ false).mapElements (transportLineIso e q).hom)
      (Term.map (startIso q).inv p) =
    Term.map (startIso (homogeneousPathMap e.hom q)).inv (homogeneousPathMap e.hom p) := by
  apply Term.map_injective_of_iso (startIso (homogeneousPathMap e.hom q))
  apply pathApp_injective
  have h := (startIso_app q (Term.map (startIso q).inv p)).symm.trans
    (congrArg pathApp (Term.map_iso_roundtrip (startIso q).symm p))
  exact (startIso_app (homogeneousPathMap e.hom q) _).trans
    ((congrArg (Term.map (Functor.whiskerLeft (projection (interval Γ)).mapElements e.hom)) h).trans
      (congrArg pathApp (Term.map_iso_roundtrip
        (startIso (homogeneousPathMap e.hom q)).symm (homogeneousPathMap e.hom p))).symm)

theorem squarePath_transport :
    squarePath (F.transport e) (Filling.transport_lawful e F hF)
      (homogeneousPathMap e.hom p) (homogeneousPathMap e.hom q) =
    Term.map (transportLineIso e q).hom (squarePath F hF p q) := by
  let d := transportLineIso (a := a) e q
  let t := Term.map (startIso q).inv p
  have hs := congrArg (fun K => IntervalTransport.forward K (𝟙 Γ)
    (Term.map (startIso (homogeneousPathMap e.hom q)).inv (homogeneousPathMap e.hom p)))
    (filling_transport (a := a) e F hF q).symm
  have ht := congrArg (IntervalTransport.forward ((filling q F hF).transport d) (𝟙 Γ))
    (initial_transport e p q).symm
  exact hs.trans (ht.trans (SelectedIntervalTransport.forward_map d (filling q F hF) (𝟙 Γ) t))

end SquareKit.Cubical.Presheaf.NativeConcat

namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem homogeneousConcat_transport {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B)
    (F : Filling A) (hF : F.Lawful) {a b c : Term A}
    (p : Term (homogeneousPath A a b)) (q : Term (homogeneousPath A b c)) :
    homogeneousConcat (F.transport e) (Filling.transport_lawful e F hF)
      (homogeneousPathMap e.hom p) (homogeneousPathMap e.hom q) =
    homogeneousPathMap e.hom (homogeneousConcat F hF p q) := by
  apply pathApp_injective
  have hs := congrArg pathApp (NativeConcat.squarePath_transport e F hF p q)
  have he := congrArg (fun t => t.reindex
    (liftSub (interval (total (interval Γ))) (endpointSub Γ true))) hs
  exact (NativeConcat.square_one (F.transport e) (Filling.transport_lawful e F hF)
    (homogeneousPathMap e.hom p) (homogeneousPathMap e.hom q)).symm.trans
      (he.trans (congrArg (Term.map (Functor.whiskerLeft (projection (interval Γ)).mapElements e.hom))
        (NativeConcat.square_one F hF p q)))

end SquareKit.Cubical.Presheaf

namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

private theorem concat_body_congr {Γ : Context.{u}} {A : Family Γ}
    (F : Filling A) (hF : F.Lawful) {a b c a' b' c' : Term A}
    (p : Term (homogeneousPath A a b)) (q : Term (homogeneousPath A b c))
    (p' : Term (homogeneousPath A a' b')) (q' : Term (homogeneousPath A b' c'))
    (hp : pathApp p = pathApp p') (hq : pathApp q = pathApp q') :
    pathApp (homogeneousConcat F hF p q) = pathApp (homogeneousConcat F hF p' q') := by
  have ha := (pathApp_zero p).symm.trans
    ((congrArg (fun t => t.reindex (endpointSub Γ false)) hp).trans (pathApp_zero p'))
  have hb := (pathApp_one p).symm.trans
    ((congrArg (fun t => t.reindex (endpointSub Γ true)) hp).trans (pathApp_one p'))
  have hc := (pathApp_one q).symm.trans
    ((congrArg (fun t => t.reindex (endpointSub Γ true)) hq).trans (pathApp_one q'))
  subst a'
  subst b'
  subst c'
  cases pathApp_injective hp
  cases pathApp_injective hq
  rfl

namespace HomotopyContractible
variable {Γ : Context.{u}} {A A' B B' : Family Γ}
  (c : HomotopyContractible A) (i : A ≅ A') (j : B ≅ B')
  (F : Filling B) (hF : F.Lawful) (f : A ⟶ B) (g : B ⟶ A)

private theorem transport_contraction_body :
    pathApp (c.transport i).contraction =
    Term.map (Functor.whiskerLeft (projection (interval (total A')) ≫ projection A').mapElements i.hom)
      (pathApp (homogeneousReindex c.contraction (EquivalenceIsoTransport.targetSub i))) := by
  apply Term.ext
  intro x
  rfl

private theorem retract_first_body :
    pathApp (homogeneousPathMap
      (Functor.whiskerLeft (projection B').mapElements (i.inv ≫ f ≫ j.hom))
      (((c.transport i).reindex (projection B')).pathTo
        (Term.map (Functor.whiskerLeft (projection B').mapElements (j.inv ≫ g ≫ i.hom)) (generic B')))) =
    Term.map (Functor.whiskerLeft (projection (interval (total B')) ≫ projection B').mapElements j.hom)
      (pathApp (homogeneousReindex
        (homogeneousPathMap (Functor.whiskerLeft (projection B).mapElements f)
          ((c.reindex (projection B)).pathTo
            (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B))))
        (EquivalenceIsoTransport.targetSub j))) := by
  let z := Term.map (Functor.whiskerLeft (projection B').mapElements (j.inv ≫ g)) (generic B')
  have hz := Term.map_iso_roundtrip (Functor.isoWhiskerLeft (projection B').mapElements i) z
  have hp := congrArg (fun a => pathApp ((c.reindex (projection B')).pathTo a)) hz
  have hm := congrArg (fun t => Term.map
    (Functor.whiskerLeft (projection (interval (total B')) ≫ projection B').mapElements (f ≫ j.hom)) t) hp
  apply Term.ext
  intro x
  have h := congrArg (fun t => t.val x) hm
  have hi := ConcreteCategory.congr_hom (NatTrans.congr_app i.hom_inv_id
    (((projection (interval (total B')) ≫ projection B').mapElements.obj x)))
  exact (congrArg (fun v => j.hom.app _ (f.app _ v)) (hi _)).trans h

theorem retract_transport
    (h : Term (homogeneousPath (Presheaf.reindex B (projection B))
      (Term.map (Functor.whiskerLeft (projection B).mapElements f)
        (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B))) (generic B)))
    (h' : Term (homogeneousPath (Presheaf.reindex B' (projection B'))
      (Term.map (Functor.whiskerLeft (projection B').mapElements (i.inv ≫ f ≫ j.hom))
        (Term.map (Functor.whiskerLeft (projection B').mapElements (j.inv ≫ g ≫ i.hom)) (generic B')))
      (generic B')))
    (hh : pathApp h' =
      Term.map (Functor.whiskerLeft (projection (interval (total B')) ≫ projection B').mapElements j.hom)
        (pathApp (homogeneousReindex h (EquivalenceIsoTransport.targetSub j)))) :
    (c.retract F hF f g h).transport j =
    (c.transport i).retract (F.transport j) (Filling.transport_lawful j F hF)
      (i.inv ≫ f ≫ j.hom) (j.inv ≫ g ≫ i.hom) h' := by
  refine HomotopyContractible.ext ?_ ?_
  · apply Term.ext
    intro x
    exact (congrArg (fun v => j.hom.app x (f.app x v))
      (ConcreteCategory.congr_hom (NatTrans.congr_app i.hom_inv_id x) (c.center.val x))).symm
  · apply pathTerm_hext
    let σ := EquivalenceIsoTransport.targetSub j
    let d := Functor.isoWhiskerLeft (projection B').mapElements j
    let p := homogeneousPathMap (Functor.whiskerLeft (projection B).mapElements f)
      ((c.reindex (projection B)).pathTo
        (Term.map (Functor.whiskerLeft (projection B).mapElements g) (generic B)))
    let p' := homogeneousPathMap
      (Functor.whiskerLeft (projection B').mapElements (i.inv ≫ f ≫ j.hom))
      (((c.transport i).reindex (projection B')).pathTo
        (Term.map (Functor.whiskerLeft (projection B').mapElements (j.inv ≫ g ≫ i.hom)) (generic B')))
    have hn := homogeneousConcat_reindex (F.reindex (projection B)) (hF.reindex _) p h σ
    have ht := homogeneousConcat_transport d (F.reindex (projection B')) (hF.reindex _)
      (homogeneousReindex p σ) (homogeneousReindex h σ)
    have hc := concat_body_congr ((F.transport j).reindex (projection B'))
      ((Filling.transport_lawful j F hF).reindex _)
      (homogeneousPathMap d.hom (homogeneousReindex p σ))
      (homogeneousPathMap d.hom (homogeneousReindex h σ)) p' h'
      (retract_first_body c i j f g).symm hh.symm
    exact (transport_contraction_body (c.retract F hF f g h) j).trans
      ((congrArg (fun q => Term.map
        (Functor.whiskerLeft (projection (interval (total B')) ≫ projection B').mapElements j.hom)
        (pathApp q)) hn).trans ((congrArg pathApp ht).symm.trans hc))

end HomotopyContractible
end SquareKit.Cubical.Presheaf
