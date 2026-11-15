import SquareKit.Internal.Cubical.EquivalenceIsoTransport
import SquareKit.Internal.Cubical.HomotopyEquivalenceSubstitution

/-! Complete selected fiber witnesses under presentation change. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf.EquivalenceIsoTransport
open CategoryTheory
universe u
variable {Γ Δ Θ : Context.{u}} {A A' B B' : Family Γ}
  (i : A' ≅ A) (j : B ≅ B') (f : A ⟶ B)

private theorem fiberIso_apply (ρ : Δ ⟶ total B') (z : Term (reindex (oldFiber j f) ρ)) :
    Term.map (Functor.whiskerLeft ρ.mapElements (fiberIso i j f).hom) z = forward i j f ρ z :=
  (forward_natural i j f (projection (oldFiber j f)) (pair ρ z) (generic (oldFiber j f))).symm

private theorem forward_input_reindex (σ : Δ ⟶ Γ) (ρ : Θ ⟶ total (reindex B' σ))
    (z : Term (reindex (oldFiber j f) (ρ ≫ liftSub B' σ))) :
    forward (Functor.isoWhiskerLeft σ.mapElements i) (Functor.isoWhiskerLeft σ.mapElements j)
      (Functor.whiskerLeft σ.mapElements f) ρ
      (Term.map (Functor.whiskerLeft (ρ ≫ targetSub (Functor.isoWhiskerLeft σ.mapElements j)).mapElements
        (genericFiberReindexIso f σ).hom) z) =
    Term.map (Functor.whiskerLeft ρ.mapElements (genericFiberReindexIso (conjugate i j f) σ).hom)
      (forward i j f (ρ ≫ liftSub B' σ) z) := by
  let a := Term.map (Functor.whiskerLeft (ρ ≫ liftSub B' σ ≫ projection B').mapElements i.inv)
    (genericFiberFst f (ρ ≫ liftSub B' σ ≫ targetSub j) z)
  let p := forwardPath i j f (ρ ≫ liftSub B' σ) z
  have h := genericFiberIntro_input_reindex (conjugate i j f) σ ρ a p
  apply Eq.trans ?_ h.symm
  apply genericFiberIntro_congr
  · rfl
  · apply pathTerm_hext
    apply Term.ext
    intro x
    rfl

/-- The fiber presentation used for conjugation commutes with input substitution. -/
theorem fiberIso_reindex (σ : Δ ⟶ Γ) :
    Functor.isoWhiskerLeft (liftSub B' σ).mapElements (fiberIso i j f) ≪≫
      genericFiberReindexIso (conjugate i j f) σ =
    Functor.isoWhiskerLeft (targetSub (Functor.isoWhiskerLeft σ.mapElements j)).mapElements
      (genericFiberReindexIso f σ) ≪≫
      fiberIso (Functor.isoWhiskerLeft σ.mapElements i) (Functor.isoWhiskerLeft σ.mapElements j)
        (Functor.whiskerLeft σ.mapElements f) := by
  let C := reindex (oldFiber j f) (liftSub B' σ)
  let ρ := projection C
  let z := generic C
  let m := Functor.whiskerLeft ρ.mapElements (genericFiberReindexIso (conjugate i j f) σ).hom
  let n := Functor.whiskerLeft (ρ ≫ targetSub (Functor.isoWhiskerLeft σ.mapElements j)).mapElements
    (genericFiberReindexIso f σ).hom
  have h₀ := congrArg (Term.map m) (fiberIso_apply i j f (ρ ≫ liftSub B' σ) z)
  have h₁ := forward_input_reindex i j f σ ρ z
  have h₂ := fiberIso_apply (Functor.isoWhiskerLeft σ.mapElements i)
    (Functor.isoWhiskerLeft σ.mapElements j) (Functor.whiskerLeft σ.mapElements f) ρ
    (Term.map n z)
  have h := h₀.trans (h₁.symm.trans h₂.symm)
  apply Iso.ext
  ext x c
  exact congrArg (fun t => t.val (extendObj C x c)) h

theorem forward_trans {A'' B'' : Family Γ} (k : A'' ≅ A') (l : B' ≅ B'')
    (ρ : Δ ⟶ total B'') (z : Term (reindex (oldFiber (j ≪≫ l) f) ρ)) :
    forward k l (conjugate i j f) ρ (forward i j f (ρ ≫ targetSub l) z) =
      forward (k ≪≫ i) (j ≪≫ l) f ρ z := by
  apply genericFiberTerm_ext (conjugate (k ≪≫ i) (j ≪≫ l) f) ρ
  · rfl
  · apply pathTerm_hext
    have hp := genericFiberPath_intro (conjugate i j f) (ρ ≫ targetSub l)
      (Term.map (Functor.whiskerLeft (ρ ≫ targetSub l ≫ projection B').mapElements i.inv)
        (genericFiberFst f (ρ ≫ targetSub l ≫ targetSub j) z))
      (forwardPath i j f (ρ ≫ targetSub l) z)
    have hh := congrArg (fun p => Term.map
      (Functor.whiskerLeft (projection (interval Δ) ≫ ρ ≫ projection B'').mapElements l.hom)
      (pathApp p)) hp
    have hleft := genericFiberPath_intro (conjugate k l (conjugate i j f)) ρ
      (Term.map (Functor.whiskerLeft (ρ ≫ projection B'').mapElements k.inv)
        (genericFiberFst (conjugate i j f) (ρ ≫ targetSub l)
          (forward i j f (ρ ≫ targetSub l) z)))
      (forwardPath k l (conjugate i j f) ρ (forward i j f (ρ ≫ targetSub l) z))
    have hright := genericFiberPath_intro (conjugate (k ≪≫ i) (j ≪≫ l) f) ρ
      (Term.map (Functor.whiskerLeft (ρ ≫ projection B'').mapElements (k ≪≫ i).inv)
        (genericFiberFst f (ρ ≫ targetSub (j ≪≫ l)) z))
      (forwardPath (k ≪≫ i) (j ≪≫ l) f ρ z)
    exact (congrArg pathApp hleft).trans (hh.trans (congrArg pathApp hright).symm)

/-- Composing source/target presentations preserves the entire selected fiber
isomorphism, including its native path component. -/
theorem fiberIso_trans {A'' B'' : Family Γ} (k : A'' ≅ A') (l : B' ≅ B'') :
    Functor.isoWhiskerLeft (targetSub l).mapElements (fiberIso i j f) ≪≫
      fiberIso k l (conjugate i j f) = fiberIso (k ≪≫ i) (j ≪≫ l) f := by
  let C := oldFiber (j ≪≫ l) f
  let ρ := projection C
  let z := generic C
  let m := Functor.whiskerLeft ρ.mapElements (fiberIso k l (conjugate i j f)).hom
  have h₀ := congrArg (Term.map m) (fiberIso_apply i j f (ρ ≫ targetSub l) z)
  have h₁ := fiberIso_apply k l (conjugate i j f) ρ (forward i j f (ρ ≫ targetSub l) z)
  have h₂ := forward_trans i j f k l ρ z
  have h₃ := fiberIso_apply (k ≪≫ i) (j ≪≫ l) f ρ z
  have h := h₀.trans (h₁.trans (h₂.trans h₃.symm))
  apply Iso.ext
  ext x c
  exact congrArg (fun t => t.val (extendObj C x c)) h

end SquareKit.Cubical.Presheaf.EquivalenceIsoTransport

namespace SquareKit.Cubical.Presheaf.HomotopyEquivalence
open CategoryTheory
universe u
/-- Substitution preserves the complete chosen contractible fibers of conjugation. -/
theorem conjugateIso_reindex {Γ Δ : Context.{u}} {A A' B B' : Family Γ}
    {f : A ⟶ B} (E : HomotopyEquivalence f) (i : A' ≅ A) (j : B ≅ B') (σ : Δ ⟶ Γ) :
    (E.conjugateIso i j).reindex σ =
      (E.reindex σ).conjugateIso (Functor.isoWhiskerLeft σ.mapElements i)
        (Functor.isoWhiskerLeft σ.mapElements j) := by
  apply HomotopyEquivalence.ext
  have hl := E.fibers.reindex_transport_comp (EquivalenceIsoTransport.targetSub j)
    (EquivalenceIsoTransport.fiberIso i j f) (liftSub B' σ)
    (genericFiberReindexIso (i.hom ≫ f ≫ j.hom) σ)
  have hr := E.fibers.reindex_transport_comp (liftSub B σ) (genericFiberReindexIso f σ)
    (EquivalenceIsoTransport.targetSub (Functor.isoWhiskerLeft σ.mapElements j))
    (EquivalenceIsoTransport.fiberIso (Functor.isoWhiskerLeft σ.mapElements i)
      (Functor.isoWhiskerLeft σ.mapElements j) (Functor.whiskerLeft σ.mapElements f))
  exact hl.trans ((congrArg (fun e =>
    (E.fibers.reindex (liftSub B' σ ≫ EquivalenceIsoTransport.targetSub j)).transport e)
      (EquivalenceIsoTransport.fiberIso_reindex i j f σ)).trans hr.symm)

/-- Sequential presentation changes equal their composite on the full chosen
contractible-fiber record, rather than only on the underlying map. -/
theorem conjugateIso_trans {Γ : Context.{u}} {A A' A'' B B' B'' : Family Γ}
    {f : A ⟶ B} (E : HomotopyEquivalence f) (i : A' ≅ A) (j : B ≅ B')
    (k : A'' ≅ A') (l : B' ≅ B'') :
    (E.conjugateIso i j).conjugateIso k l = E.conjugateIso (k ≪≫ i) (j ≪≫ l) := by
  apply HomotopyEquivalence.ext
  have h := E.fibers.reindex_transport_comp (EquivalenceIsoTransport.targetSub j)
    (EquivalenceIsoTransport.fiberIso i j f) (EquivalenceIsoTransport.targetSub l)
    (EquivalenceIsoTransport.fiberIso k l (EquivalenceIsoTransport.conjugate i j f))
  exact h.trans (congrArg (fun e =>
    (E.fibers.reindex (EquivalenceIsoTransport.targetSub l ≫ EquivalenceIsoTransport.targetSub j)).transport e)
      (EquivalenceIsoTransport.fiberIso_trans i j f k l))

end SquareKit.Cubical.Presheaf.HomotopyEquivalence
