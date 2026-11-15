import SquareKit.Internal.Cubical.FunctionBox
import SquareKit.Internal.Cubical.CompositionFilling

/-! Compose a dependent function by extending its argument backwards, then
composing its dependent result along that selected extension. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

namespace FunctionComposition
variable {Γ Δ : Context.{u}} {A : Family Γ} {B : Family (total A)}

abbrev Args (A : Family Γ) (p : total (interval Δ) ⟶ Γ) : Context :=
  total (reindex A (endpointSub Δ true ≫ p))

def argumentPath (p : total (interval Δ) ⟶ Γ) : total (interval (Args A p)) ⟶ Γ :=
  liftSub (interval Δ) (projection (reindex A (endpointSub Δ true ≫ p))) ≫ p

def argument (F : Filling A) (p : total (interval Δ) ⟶ Γ) :
    Term (reindex A (argumentPath (A := A) p)) :=
  F.backwards (argumentPath p) (generic (reindex A (endpointSub Δ true ≫ p)))

theorem argument_one (F : Filling A) (hF : F.Lawful) (p : total (interval Δ) ⟶ Γ) :
    (argument F p).reindex (endpointSub (Args A p) true) =
      generic (reindex A (endpointSub Δ true ≫ p)) :=
  F.backwards_one hF _ _

theorem argument_pair_one (F : Filling A) (hF : F.Lawful) (p : total (interval Δ) ⟶ Γ) :
    endpointSub (Args A p) true ≫ pair (argumentPath p) (argument F p) =
      liftSub A (endpointSub Δ true ≫ p) :=
  congrArg (pair (projection (reindex A (endpointSub Δ true ≫ p)) ≫ endpointSub Δ true ≫ p))
    (argument_one F hF p)

def bodyAlong (G : Composition B) (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (pi A B) p) φ)
    (v : Term (reindex A (argumentPath (A := A) p)))
    (hv : v.reindex (endpointSub (Args A p) true) =
      generic (reindex A (endpointSub Δ true ≫ p))) :
    Term (reindex B (liftSub A (endpointSub Δ true ≫ p))) :=
  (G.comp (pair (argumentPath p) v)
    (φ.reindex (projection (reindex A (endpointSub Δ true ≫ p))))
    (b.applyAlong p φ (projection (reindex A (endpointSub Δ true ≫ p))) v)).convert
      (congrArg (fun σ => reindex B σ)
        (congrArg (pair (projection (reindex A (endpointSub Δ true ≫ p)) ≫ endpointSub Δ true ≫ p)) hv))

def body (F : Filling A) (hF : F.Lawful) (G : Composition B)
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (pi A B) p) φ) :
    Term (reindex B (liftSub A (endpointSub Δ true ≫ p))) :=
  bodyAlong G p φ b (argument F p) (argument_one F hF p)

def comp (F : Filling A) (hF : F.Lawful) (G : Composition B)
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (pi A B) p) φ) : Term (reindex (pi A B) (endpointSub Δ true ≫ p)) :=
  Term.map (piReindexIso A B (endpointSub Δ true ≫ p)).inv (lam (body F hF G p φ b))

theorem comp_normalize (F : Filling A) (hF : F.Lawful) (G : Composition B)
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (pi A B) p) φ) :
    Term.map (piReindex A B (endpointSub Δ true ≫ p)) (comp F hF G p φ b) =
      lam (body F hF G p φ b) :=
  Term.map_iso_roundtrip (piReindexIso A B (endpointSub Δ true ≫ p)).symm _

theorem comp_boundary (F : Filling A) (hF : F.Lawful) (G : Composition B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (pi A B) p) φ) (x : Δ.Elements) (hx : φ.full x) :
    (comp F hF G p φ b).val x = b.tube.val ((endpointSub Δ true).mapElements.obj x) hx := by
  apply ((piReindexIso A B (endpointSub Δ true ≫ p)).app x).toEquiv.injective
  change (Term.map (piReindex A B (endpointSub Δ true ≫ p)) (comp F hF G p φ b)).val x = _
  rw [comp_normalize]
  apply PiElement.ext
  intro y f a
  let z := extendObj (reindex A (endpointSub Δ true ≫ p)) y a
  have hy := φ.full_natural f hx
  have hc := hG.boundary (pair (argumentPath p) (argument F p))
    (φ.reindex (projection (reindex A (endpointSub Δ true ≫ p))))
    (b.applyAlong p φ (projection (reindex A (endpointSub Δ true ≫ p))) (argument F p)) z hy
  have ha := congrArg (fun t => t.val z) (argument_one F hF p)
  have hp := congrArg (fun q => q.val (𝟙 _) a)
    (b.tube.property ((endpointSub Δ true).mapElements.map f) hx)
  apply eq_of_heq
  apply (Term.convert_val_heq _ _ z).trans
  apply (heq_of_eq hc).trans
  have hv : ∀ (v w : A.obj ((endpointSub Δ true ≫ p).mapElements.obj y)), v = w →
      HEq ((b.tube.val ((endpointSub Δ true).mapElements.obj y) hy).val (𝟙 _) v)
        ((b.tube.val ((endpointSub Δ true).mapElements.obj y) hy).val (𝟙 _) w) := by
    intro v w h
    cases h
    rfl
  apply (hv _ _ ha).trans
  apply heq_of_eq
  change (b.tube.val ((endpointSub Δ true).mapElements.obj x) hx).val
    (((endpointSub Δ true ≫ p).mapElements.map f) ≫ 𝟙 _) a =
    (b.tube.val ((endpointSub Δ true).mapElements.obj y) hy).val (𝟙 _) a at hp
  exact (congrArg (fun k => (b.tube.val ((endpointSub Δ true).mapElements.obj x) hx).val k a)
    (Category.comp_id _)).symm.trans hp |>.symm

theorem argument_uniform (F : Filling A) (hF : F.Lawful)
    (p : total (interval Δ) ⟶ Γ) {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    argument F (liftSub (interval Δ) σ ≫ p) =
      (argument F p).reindex
        (liftSub (interval (Args A p)) (liftSub (reindex A (endpointSub Δ true ≫ p)) σ)) :=
  F.backwards_uniform hF (argumentPath p) (generic (reindex A (endpointSub Δ true ≫ p))) (liftSub (reindex A (endpointSub Δ true ≫ p)) σ)

theorem bodyAlong_uniform (G : Composition B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (pi A B) p) φ)
    (v : Term (reindex A (argumentPath (A := A) p)))
    (hv : v.reindex (endpointSub (Args A p) true) =
      generic (reindex A (endpointSub Δ true ≫ p)))
    {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    bodyAlong G (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ)
      (v.reindex (liftSub (interval (Args A p)) (liftSub (reindex A (endpointSub Δ true ≫ p)) σ)))
      (congrArg (fun t => t.reindex (liftSub (reindex A (endpointSub Δ true ≫ p)) σ)) hv) =
      (bodyAlong G p φ b v hv).reindex (liftSub (reindex A (endpointSub Δ true ≫ p)) σ) := by
  let τ := liftSub (reindex A (endpointSub Δ true ≫ p)) σ
  have h := hG.uniform (pair (argumentPath p) v)
    (φ.reindex (projection (reindex A (endpointSub Δ true ≫ p))))
    (b.applyAlong p φ (projection (reindex A (endpointSub Δ true ≫ p))) v) τ
  apply Term.ext
  intro x
  apply eq_of_heq
  apply (Term.convert_val_heq _ _ x).trans
  apply HEq.trans _ (Term.convert_val_heq _ _ (τ.mapElements.obj x)).symm
  exact heq_of_eq (congrArg (fun t => t.val x) h)

theorem body_uniform (F : Filling A) (hF : F.Lawful) (G : Composition B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (pi A B) p) φ) {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    body F hF G (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ) =
      (body F hF G p φ b).reindex (liftSub (reindex A (endpointSub Δ true ≫ p)) σ) := by
  let p' := liftSub (interval Δ) σ ≫ p
  let τ := liftSub (reindex A (endpointSub Δ true ≫ p)) σ
  let k : {v : Term (reindex A (argumentPath (A := A) p')) //
      v.reindex (endpointSub (Args A p') true) = generic (reindex A (endpointSub Θ true ≫ p'))} →
      Term (reindex B (liftSub A (endpointSub Θ true ≫ p'))) :=
    fun v => bodyAlong G p' (φ.reindex σ) (b.reindex σ) v.val v.property
  have he : (⟨argument F p',argument_one F hF p'⟩ :
      {v : Term (reindex A (argumentPath (A := A) p')) //
        v.reindex (endpointSub (Args A p') true) = generic (reindex A (endpointSub Θ true ≫ p'))}) =
      ⟨(argument F p).reindex (liftSub (interval (Args A p)) τ),
        congrArg (fun t => t.reindex τ) (argument_one F hF p)⟩ :=
    Subtype.ext (argument_uniform F hF p σ)
  exact (congrArg k he).trans (bodyAlong_uniform G hG p φ b _ _ σ)

set_option maxHeartbeats 800000 in
theorem comp_uniform (F : Filling A) (hF : F.Lawful) (G : Composition B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Cofibration Δ)
    (b : OpenBox (reindex (pi A B) p) φ) {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    comp F hF G (liftSub (interval Δ) σ ≫ p) (φ.reindex σ) (b.reindex σ) =
      (comp F hF G p φ b).reindex σ := by
  apply Term.map_injective_of_iso (piReindexIso A B (σ ≫ endpointSub Δ true ≫ p))
  have hn := congrArg (fun s => Term.map
    (piReindex (reindex A (endpointSub Δ true ≫ p))
      (reindex B (liftSub A (endpointSub Δ true ≫ p))) σ) (s.reindex σ))
    (comp_normalize F hF G p φ b)
  exact (comp_normalize F hF G _ _ _).trans
    ((congrArg lam (body_uniform F hF G hG p φ b σ)).trans hn.symm)

end FunctionComposition
end SquareKit.Cubical.Presheaf
