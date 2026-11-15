import SquareKit.Internal.Cubical.DependentFilling

/-! Dependent projections of compatible partial sections. -/
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

def Term.sigmaSndOver {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (s : Term (sigma A B)) (a : Term A) (h : a = Presheaf.sigmaFst s) :
    Term (Presheaf.reindex B (pair (𝟙 Γ) a)) := h.symm ▸ Presheaf.sigmaSnd s

theorem Term.sigmaSndOver_val {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (s : Term (sigma A B)) (a : Term A) (h : a = Presheaf.sigmaFst s) (x : Γ.Elements) :
    HEq ((s.sigmaSndOver a h).val x) (s.val x).2 := by
  cases h
  rfl

def PartialSection.sigmaFst {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {φ : Cofibration Γ} (s : PartialSection (sigma A B) φ) : PartialSection A φ where
  val x h := (s.val x h).1
  property f h := congrArg Sigma.fst (s.property f h)

def PartialSection.sigmaSnd {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {φ : Cofibration Γ} (s : PartialSection (sigma A B) φ) (a : Term A)
    (h : ∀ x p, a.val x = (s.val x p).1) :
    PartialSection (Presheaf.reindex B (pair (𝟙 Γ) a)) φ := by
  let i := restrictInclusion φ
  have hf : Presheaf.sigmaFst (B := Presheaf.reindex B (liftSub A i)) s.toRestricted = a.reindex i := by
    apply Term.ext
    intro x
    exact (h (i.mapElements.obj x) x.val.property).symm
  exact PartialSection.ofRestricted (Term.sigmaSndOver (B := Presheaf.reindex B (liftSub A i)) s.toRestricted (a.reindex i) hf.symm)

theorem PartialSection.sigmaSnd_val {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {φ : Cofibration Γ} (s : PartialSection (sigma A B) φ) (a : Term A)
    (h : ∀ x p, a.val x = (s.val x p).1) (x : Γ.Elements) (p : φ.full x) :
    HEq ((s.sigmaSnd a h).val x p) (s.val x p).2 := by
  dsimp only [PartialSection.sigmaSnd, PartialSection.ofRestricted]
  exact Term.sigmaSndOver_val (B := Presheaf.reindex B (liftSub A (restrictInclusion φ))) s.toRestricted (a.reindex (restrictInclusion φ)) _
    ((restrictContext φ).elementsMk x.obj ⟨x.val,p⟩)

def OpenBox.sigmaFst {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {B : Family (total A)} {φ : Cofibration Γ} (b : OpenBox (sigma A B) φ) : OpenBox A φ where
  tube := b.tube.sigmaFst
  base := Presheaf.sigmaFst (B := Presheaf.reindex B (liftSub A (endpointSub Γ false))) b.base
  boundary x h := congrArg Sigma.fst (b.boundary x h)

def OpenBox.sigmaSnd {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {B : Family (total A)} {φ : Cofibration Γ} (b : OpenBox (sigma A B) φ)
    (a : Term A) (ha : b.sigmaFst.Fills a) :
    OpenBox (Presheaf.reindex B (pair (𝟙 _) a)) φ where
  tube := b.tube.sigmaSnd a ha.2
  base := Term.sigmaSndOver (B := Presheaf.reindex B (liftSub A (endpointSub Γ false)))
    b.base (a.reindex (endpointSub Γ false)) ha.1
  boundary x h := by
    apply eq_of_heq
    exact (PartialSection.sigmaSnd_val b.tube a ha.2 _ h).trans
      ((Sigma.mk.inj (b.boundary x h)).2.trans
        (Term.sigmaSndOver_val (B := Presheaf.reindex B (liftSub A (endpointSub Γ false)))
          b.base (a.reindex (endpointSub Γ false)) ha.1 x).symm)

theorem OpenBox.sigmaIntro_fills {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {B : Family (total A)} {φ : Cofibration Γ} (b : OpenBox (sigma A B) φ)
    (a : Term A) (ha : b.sigmaFst.Fills a)
    (c : Term (Presheaf.reindex B (pair (𝟙 _) a)))
    (hc : (b.sigmaSnd a ha).Fills c) : b.Fills (Presheaf.sigmaIntro a c) := by
  constructor
  · apply Term.ext
    intro x
    apply Sigma.ext (congrArg (fun t => t.val x) ha.1)
    exact (heq_of_eq (congrArg (fun t => t.val x) hc.1)).trans
      (Term.sigmaSndOver_val (B := Presheaf.reindex B (liftSub A (endpointSub Γ false)))
        b.base (a.reindex (endpointSub Γ false)) ha.1 x)
  · intro x h
    apply Sigma.ext (ha.2 x h)
    exact (heq_of_eq (hc.2 x h)).trans (PartialSection.sigmaSnd_val b.tube a ha.2 x h)

theorem OpenBox.sigmaSnd_reindex {Γ Δ : Context.{u}} {A : Family (total (interval Γ))}
    {B : Family (total A)} {φ : Cofibration Γ} (b : OpenBox (sigma A B) φ)
    (a : Term A) (ha : b.sigmaFst.Fills a) (σ : Δ ⟶ Γ) :
    (b.sigmaSnd a ha).reindex σ =
      OpenBox.sigmaSnd (B := Presheaf.reindex B (liftSub A (liftSub (interval Γ) σ)))
        (b.reindex σ) (a.reindex (liftSub (interval Γ) σ)) (ha.reindex σ) := by
  apply OpenBox.ext
  · apply PartialSection.ext
    intro x h
    apply eq_of_heq
    exact (PartialSection.sigmaSnd_val b.tube a ha.2
      ((liftSub (interval Γ) σ).mapElements.obj x) h).trans
      (PartialSection.sigmaSnd_val (B := Presheaf.reindex B (liftSub A (liftSub (interval Γ) σ)))
        (b.tube.reindex (liftSub (interval Γ) σ)) (a.reindex (liftSub (interval Γ) σ))
        (ha.reindex σ).2 x h).symm
  · apply Term.ext
    intro x
    apply eq_of_heq
    exact (Term.sigmaSndOver_val (B := Presheaf.reindex B (liftSub A (endpointSub Γ false)))
      b.base (a.reindex (endpointSub Γ false)) ha.1 (σ.mapElements.obj x)).trans
      (Term.sigmaSndOver_val (B := Presheaf.reindex B
        (liftSub A (endpointSub Δ false ≫ liftSub (interval Γ) σ)))
        (b.base.reindex σ) ((a.reindex (liftSub (interval Γ) σ)).reindex (endpointSub Δ false))
        (ha.reindex σ).1 x).symm

end SquareKit.Cubical.Presheaf
