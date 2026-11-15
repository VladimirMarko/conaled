import SquareKit.Internal.Cubical.IntervalReversal
import SquareKit.Internal.Cubical.Filling
import SquareKit.Internal.Cubical.Conversion

/-! A chosen domain filler extends a far-endpoint argument backwards. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

theorem OpenBox.hext {Δ : Context.{u}} {A B : Family (total (interval Δ))}
    (e : A = B) {φ : Cofibration Δ} {b : OpenBox A φ} {c : OpenBox B φ}
    (ht : ∀ x h, HEq (b.tube.val x h) (c.tube.val x h))
    (hb : ∀ x, HEq (b.base.val x) (c.base.val x)) : HEq b c := by
  cases e
  apply heq_of_eq
  apply OpenBox.ext
  · exact PartialSection.ext (fun x h => eq_of_heq (ht x h))
  · exact Term.ext (fun x => eq_of_heq (hb x))

namespace Filling
variable {Γ Δ : Context.{u}} {A : Family Γ}

def backwards (F : Filling A) (p : total (interval Δ) ⟶ Γ)
    (a : Term (Presheaf.reindex A (endpointSub Δ true ≫ p))) : Term (Presheaf.reindex A p) :=
  let q := reverseInterval Δ ≫ p
  let cap : Term (Presheaf.reindex A (endpointSub Δ false ≫ q)) :=
    a.convert (congrArg (fun σ => Presheaf.reindex A σ)
      ((congrArg (fun σ => σ ≫ p) (reverseInterval_endpoint Δ false)).symm))
  let b := OpenBox.empty (Presheaf.reindex A q) cap
  ((F.fill q (Cofibration.bot Δ) b).reindex (reverseInterval Δ)).convert
    (congrArg (fun σ => Presheaf.reindex A σ)
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (fun σ => σ ≫ p) (reverseInterval_twice Δ)).trans (Category.id_comp p))))

theorem backwards_one (F : Filling A) (h : F.Lawful)
    (p : total (interval Δ) ⟶ Γ) (a : Term (Presheaf.reindex A (endpointSub Δ true ≫ p))) :
    (F.backwards p a).reindex (endpointSub Δ true) = a := by
  apply Term.ext
  intro x
  apply eq_of_heq
  unfold backwards
  apply (Term.convert_val_heq _ _ _).trans
  have e := congrArg (fun σ : Δ ⟶ total (interval Δ) => σ.mapElements.obj x)
    (reverseInterval_endpoint Δ true)
  let cap := a.convert (congrArg (fun σ => Presheaf.reindex A σ)
    ((congrArg (fun σ => σ ≫ p) (reverseInterval_endpoint Δ false)).symm))
  let b := OpenBox.empty (Presheaf.reindex A (reverseInterval Δ ≫ p)) cap
  let t := F.fill (reverseInterval Δ ≫ p) (Cofibration.bot Δ) b
  have hv : HEq (t.val ((reverseInterval Δ).mapElements.obj
      ((endpointSub Δ true).mapElements.obj x)))
      (t.val ((endpointSub Δ false).mapElements.obj x)) := by
    have hv : ∀ {y z}, y = z → HEq (t.val y) (t.val z) := by
      intro y z h
      cases h
      rfl
    exact hv e
  have hc := congrArg (fun t => t.val x) (h.fills _ _ b).1
  exact hv.trans ((heq_of_eq hc).trans (Term.convert_val_heq _ a x))

theorem fill_heq (F : Filling A) {p q : total (interval Δ) ⟶ Γ} (e : p = q)
    {φ : Cofibration Δ} {b : OpenBox (Presheaf.reindex A p) φ}
    {c : OpenBox (Presheaf.reindex A q) φ} (h : HEq b c) :
    HEq (F.fill p φ b) (F.fill q φ c) := by
  cases e
  cases h
  rfl

theorem backwards_uniform (F : Filling A) (h : F.Lawful)
    (p : total (interval Δ) ⟶ Γ) (a : Term (Presheaf.reindex A (endpointSub Δ true ≫ p)))
    {Θ : Context.{u}} (σ : Θ ⟶ Δ) :
    F.backwards (liftSub (interval Δ) σ ≫ p) (a.reindex σ) =
      (F.backwards p a).reindex (liftSub (interval Δ) σ) := by
  let L := liftSub (interval Δ) σ
  let cap := a.convert (congrArg (fun σ => Presheaf.reindex A σ)
    ((congrArg (fun σ => σ ≫ p) (reverseInterval_endpoint Δ false)).symm))
  let cap' := (a.reindex σ).convert (congrArg (fun τ => Presheaf.reindex A τ)
    ((congrArg (fun τ => τ ≫ (L ≫ p)) (reverseInterval_endpoint Θ false)).symm))
  let b := OpenBox.empty (Presheaf.reindex A (reverseInterval Δ ≫ p)) cap
  let b' := OpenBox.empty (Presheaf.reindex A (reverseInterval Θ ≫ (L ≫ p))) cap'
  have e : reverseInterval Θ ≫ (L ≫ p) = L ≫ (reverseInterval Δ ≫ p) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun τ => τ ≫ p) (reverseInterval_natural σ)).trans (Category.assoc _ _ _))
  have hb : HEq b' (b.reindex σ) := by
    apply OpenBox.hext (congrArg (fun τ => Presheaf.reindex A τ) e)
    · intro x hx
      exact (Bool.false_ne_true hx).elim
    · intro x
      exact (Term.convert_val_heq _ _ _).trans (Term.convert_val_heq _ a (σ.mapElements.obj x)).symm
  have hf := (F.fill_heq e hb).trans (heq_of_eq (h.uniform _ _ b σ))
  apply Term.ext
  intro x
  apply eq_of_heq
  unfold backwards
  apply (Term.convert_val_heq _ _ _).trans
  apply HEq.trans _ (Term.convert_val_heq _ _ _).symm
  apply (Term.val_heq_of_heq (congrArg (fun τ => Presheaf.reindex A τ) e) hf
    (x := (reverseInterval Θ).mapElements.obj x) rfl).trans
  exact Term.val_heq_of_heq rfl (HEq.rfl (a := F.fill _ _ b))
    (congrArg (fun τ : total (interval Θ) ⟶ total (interval Δ) => τ.mapElements.obj x)
      (reverseInterval_natural σ))

end Filling
end SquareKit.Cubical.Presheaf
