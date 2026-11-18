import SquareKit.Internal.Cubical.SequentialFilling
import SquareKit.Internal.Cubical.CartesianLocalFilling
import SquareKit.Internal.Cubical.CartesianCofibrations
import SquareKit.Internal.Cubical.CartesianDependentFamilies

/-! Dependent Cartesian filling and extension from actual contraction data. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian
open CategoryTheory SquareKit.SequentialFilling
universe u

def Filling.reindex {Γ Δ : Context.{u}} {A : Family Γ} (F : Filling A)
    (σ : Δ ⟶ Γ) : Filling (Cartesian.reindex A σ) where
  fill p φ r b := F.fill (p ≫ σ) φ r b

theorem Filling.Lawful.reindex {Γ Δ : Context.{u}} {A : Family Γ}
    {F : Filling A} (hF : F.Lawful) (σ : Δ ⟶ Γ) : (F.reindex σ).Lawful where
  fills p φ r b := hF.fills (p ≫ σ) φ r b
  uniform p φ r b f := hF.uniform (p ≫ σ) φ r b f

theorem OpenBox.Fills.reindex {Γ Δ : Context.{u}} {A : Family (total (interval Γ))}
    {φ : Subcontext Γ} {r : Term (interval Γ)} {b : OpenBox A φ r} {t : Term A}
    (h : b.Fills t) (σ : Δ ⟶ Γ) :
    (b.reindex σ).Fills (Term.reindex t (intervalSub σ)) :=
  ⟨congrArg (fun z => Term.reindex z σ) h.1, fun x hx => h.2 ((intervalSub σ).mapElements.obj x) hx⟩

def Term.sigmaSndOver {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (s : Term (sigma A B)) (a : Term A) (h : a = Cartesian.sigmaFst s) :
    Term (Cartesian.reindex B (pair (𝟙 Γ) a)) := h.symm ▸ Cartesian.sigmaSnd s

theorem Term.sigmaSndOver_val {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (s : Term (sigma A B)) (a : Term A) (h : a = Cartesian.sigmaFst s) (x : Γ.Elements) :
    HEq ((Term.sigmaSndOver s a h).val x) (s.val x).2 := by
  cases h
  rfl

def PartialSection.sigmaFst {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {φ : Subcontext Γ} (s : PartialSection (sigma A B) φ) : PartialSection A φ where
  val x h := (s.val x h).1
  natural f h := congrArg Sigma.fst (s.natural f h)

def PartialSection.sigmaSnd {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {φ : Subcontext Γ} (s : PartialSection (sigma A B) φ) (a : Term A)
    (h : ∀ x p, a.val x = (s.val x p).1) :
    PartialSection (Cartesian.reindex B (pair (𝟙 Γ) a)) φ := by
  let i := restrictInclusion φ
  have hf : Cartesian.sigmaFst (B := Cartesian.reindex B (liftSub A i)) s.toRestricted = Term.reindex a i := by
    apply Term.ext
    intro x
    exact (h (i.mapElements.obj x) x.val.property).symm
  exact PartialSection.ofRestricted (Term.sigmaSndOver (B := Cartesian.reindex B (liftSub A i)) s.toRestricted (Term.reindex a i) hf.symm)

theorem PartialSection.sigmaSnd_val {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    {φ : Subcontext Γ} (s : PartialSection (sigma A B) φ) (a : Term A)
    (h : ∀ x p, a.val x = (s.val x p).1) (x : Γ.Elements) (p : φ.holds x) :
    HEq ((s.sigmaSnd a h).val x p) (s.val x p).2 := by
  dsimp only [PartialSection.sigmaSnd, PartialSection.ofRestricted]
  exact Term.sigmaSndOver_val (B := Cartesian.reindex B (liftSub A (restrictInclusion φ))) s.toRestricted (Term.reindex a (restrictInclusion φ)) _
    ((restrictContext φ).elementsMk x.obj ⟨x.val,p⟩)

def OpenBox.sigmaFst {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {B : Family (total A)} {φ : Subcontext Γ} {r : Term (interval Γ)} (b : OpenBox (sigma A B) φ r) : OpenBox A φ r where
  tube := b.tube.sigmaFst
  base := Cartesian.sigmaFst (B := Cartesian.reindex B (liftSub A (graph r))) b.base
  boundary x h := congrArg Sigma.fst (b.boundary x h)

def OpenBox.sigmaSnd {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {B : Family (total A)} {φ : Subcontext Γ} {r : Term (interval Γ)} (b : OpenBox (sigma A B) φ r)
    (a : Term A) (ha : b.sigmaFst.Fills a) :
    OpenBox (Cartesian.reindex B (pair (𝟙 _) a)) φ r where
  tube := b.tube.sigmaSnd a ha.2
  base := Term.sigmaSndOver (B := Cartesian.reindex B (liftSub A (graph r)))
    b.base (Term.reindex a (graph r)) ha.1
  boundary x h := by
    apply eq_of_heq
    exact (PartialSection.sigmaSnd_val b.tube a ha.2 _ h).trans
      ((Sigma.mk.inj (b.boundary x h)).2.trans
        (Term.sigmaSndOver_val (B := Cartesian.reindex B (liftSub A (graph r)))
          b.base (Term.reindex a (graph r)) ha.1 x).symm)

theorem OpenBox.sigmaIntro_fills {Γ : Context.{u}} {A : Family (total (interval Γ))}
    {B : Family (total A)} {φ : Subcontext Γ} {r : Term (interval Γ)} (b : OpenBox (sigma A B) φ r)
    (a : Term A) (ha : b.sigmaFst.Fills a)
    (c : Term (Cartesian.reindex B (pair (𝟙 _) a)))
    (hc : (b.sigmaSnd a ha).Fills c) : b.Fills (Cartesian.sigmaIntro a c) := by
  constructor
  · apply Term.ext
    intro x
    apply Sigma.ext (congrArg (fun t => t.val x) ha.1)
    exact (heq_of_eq (congrArg (fun t => t.val x) hc.1)).trans
      (Term.sigmaSndOver_val (B := Cartesian.reindex B (liftSub A (graph r)))
        b.base (Term.reindex a (graph r)) ha.1 x)
  · intro x h
    apply Sigma.ext (ha.2 x h)
    exact (heq_of_eq (hc.2 x h)).trans (PartialSection.sigmaSnd_val b.tube a ha.2 x h)

theorem OpenBox.sigmaSnd_reindex {Γ Δ : Context.{u}} {A : Family (total (interval Γ))}
    {B : Family (total A)} {φ : Subcontext Γ} {r : Term (interval Γ)} (b : OpenBox (sigma A B) φ r)
    (a : Term A) (ha : b.sigmaFst.Fills a) (σ : Δ ⟶ Γ) :
    (b.sigmaSnd a ha).reindex σ =
      OpenBox.sigmaSnd (B := Cartesian.reindex B (liftSub A (intervalSub σ)))
        (b.reindex σ) (Term.reindex a (intervalSub σ)) (ha.reindex σ) := by
  apply OpenBox.ext
  · apply PartialSection.ext
    intro x h
    apply eq_of_heq
    exact (PartialSection.sigmaSnd_val b.tube a ha.2
      ((intervalSub σ).mapElements.obj x) h).trans
      (PartialSection.sigmaSnd_val (B := Cartesian.reindex B (liftSub A (intervalSub σ)))
        (b.tube.reindex (intervalSub σ)) (Term.reindex a (intervalSub σ))
        (ha.reindex σ).2 x h).symm
  · apply Term.ext
    intro x
    apply eq_of_heq
    exact (Term.sigmaSndOver_val (B := Cartesian.reindex B (liftSub A (graph r)))
      b.base (Term.reindex a (graph r)) ha.1 (σ.mapElements.obj x)).trans
      (Term.sigmaSndOver_val (B := Cartesian.reindex B
        (liftSub A (graph (Term.reindex r σ) ≫ intervalSub σ)))
        (Term.reindex b.base σ) (Term.reindex (Term.reindex a (intervalSub σ)) (graph (Term.reindex r σ)))
        (ha.reindex σ).1 x).symm


def sigmaFilling {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) : Filling (sigma A B) where
  fill p φ r b :=
    let a := F.fill p φ r (OpenBox.sigmaFst (B := reindex B (liftSub A p)) b)
    let ha := (hF.fills p φ r (OpenBox.sigmaFst (B := reindex B (liftSub A p)) b))
    let c := G.fill (pair p a) φ r (OpenBox.sigmaSnd (B := reindex B (liftSub A p)) b a ha)
    Cartesian.sigmaIntro (B := reindex B (liftSub A p)) a c

/-- Native data for the shared two-stage selection proof. -/
def sigmaProblem {Γ Δ : Context.{u}} {A : Family Γ} {B : Family (total A)} (F : Filling A) (hF : F.Lawful) (G : Filling B)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ)) (b : OpenBox (reindex (sigma A B) p) φ r) : Problem where
  FirstBox := OpenBox (reindex A p) φ r
  First := Term (reindex A p)
  firstBox := OpenBox.sigmaFst (B := reindex B (liftSub A p)) b
  firstFill := F.fill p φ r
  FirstFills := OpenBox.Fills
  first_fills := hF.fills p φ r
  SecondBox a := OpenBox (reindex B (pair p a)) φ r
  Second a := Term (reindex B (pair p a))
  secondBox a ha := OpenBox.sigmaSnd (B := reindex B (liftSub A p)) b a ha
  secondFill a := G.fill (pair p a) φ r
  Whole := Term (reindex (sigma A B) p)
  pair := Cartesian.sigmaIntro (B := reindex B (liftSub A p))

/-- The shared selection retains the native algorithm exactly. -/
theorem sigmaProblem_fill {Γ Δ : Context.{u}} {A : Family Γ} {B : Family (total A)} (F : Filling A) (hF : F.Lawful) (G : Filling B)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ)) (b : OpenBox (reindex (sigma A B) p) φ r) :
    (sigmaProblem F hF G p φ r b).fill = (sigmaFilling F hF G).fill p φ r b := rfl

set_option backward.isDefEq.respectTransparency false in
def sigmaSubstitution {Γ Δ Θ : Context.{u}} {A : Family Γ} {B : Family (total A)} (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ)) (b : OpenBox (reindex (sigma A B) p) φ r) (σ : Θ ⟶ Δ) :
    Substitution (sigmaProblem F hF G p φ r b)
      (sigmaProblem F hF G (intervalSub σ ≫ p) (φ.reindex σ) (Term.reindex r σ) (b.reindex σ)) where
  firstBox b := b.reindex σ
  first a := Term.reindex a (intervalSub σ)
  firstBox_eq := rfl
  first_uniform b := hF.uniform p φ r b σ
  first_fills _a ha := ha.reindex σ
  secondBox _a b := b.reindex σ
  second _a c := Term.reindex c (intervalSub σ)
  whole c := Term.reindex c (intervalSub σ)
  secondBox_eq a ha := (OpenBox.sigmaSnd_reindex (B := reindex B (liftSub A p)) b a ha σ).symm
  second_uniform a b := hG.uniform (pair p a) φ r b σ
  pair_eq _ _ := rfl

theorem sigmaFilling_fills {Γ Δ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ)) (b : OpenBox (reindex (sigma A B) p) φ r) :
    b.Fills ((sigmaFilling F hF G).fill p φ r b) :=
  (sigmaProblem F hF G p φ r b).fills
    (fun _ c t => c.Fills t) b.Fills
    (fun a c => hG.fills (pair p a) φ r c)
    (fun a ha c hc => OpenBox.sigmaIntro_fills (B := reindex B (liftSub A p)) b a ha c hc)

set_option backward.isDefEq.respectTransparency false in
theorem sigmaFilling_uniform {Γ Δ Θ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful)
    (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ) (r : Term (interval Δ)) (b : OpenBox (reindex (sigma A B) p) φ r)
    (σ : Θ ⟶ Δ) :
    (sigmaFilling F hF G).fill (intervalSub σ ≫ p) (φ.reindex σ) (Term.reindex r σ) (b.reindex σ) =
      Term.reindex ((sigmaFilling F hF G).fill p φ r b) (intervalSub σ) :=
  (sigmaSubstitution F hF G hG p φ r b σ).uniform

theorem sigmaFilling_lawful {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
    (F : Filling A) (hF : F.Lawful) (G : Filling B) (hG : G.Lawful) :
    (sigmaFilling F hF G).Lawful where
  fills := sigmaFilling_fills F hF G hG
  uniform := sigmaFilling_uniform F hF G hG


def PartialSection.Compatible {Γ : Context.{u}} {A : Family Γ} {φ ψ : Subcontext Γ}
    (a : PartialSection A φ) (b : PartialSection A ψ) : Prop :=
  ∀ x p q, a.val x p = b.val x q

noncomputable def glueValue {Γ : Context.{u}} {A : Family Γ} {φ ψ : Subcontext Γ}
    (a : PartialSection A φ) (b : PartialSection A ψ) (x : Γ.Elements) (p : (φ.join ψ).holds x) : A.obj x := by
  classical
  exact if h : φ.holds x then a.val x h else b.val x (p |>.resolve_left h)

theorem glueValue_left {Γ : Context.{u}} {A : Family Γ} {φ ψ : Subcontext Γ}
    (a : PartialSection A φ) (b : PartialSection A ψ) (x : Γ.Elements)
    (p : (φ.join ψ).holds x) (h : φ.holds x) : glueValue a b x p = a.val x h := by
  simp only [glueValue,dite_eq_left h]

theorem glueValue_right {Γ : Context.{u}} {A : Family Γ} {φ ψ : Subcontext Γ}
    (a : PartialSection A φ) (b : PartialSection A ψ) (c : a.Compatible b) (x : Γ.Elements)
    (p : (φ.join ψ).holds x) (h : ψ.holds x) : glueValue a b x p = b.val x h := by
  classical
  by_cases q : φ.holds x
  · exact (glueValue_left a b x p q).trans (c x q h)
  · simp only [glueValue,dite_eq_right q]

noncomputable def PartialSection.glue {Γ : Context.{u}} {A : Family Γ} {φ ψ : Subcontext Γ}
    (a : PartialSection A φ) (b : PartialSection A ψ) (c : a.Compatible b) : PartialSection A (φ.join ψ) where
  val := glueValue a b
  natural {x y} f p := by
    rcases (show φ.holds x ∨ ψ.holds x from p) with h | h
    · rw [glueValue_left a b x p h,glueValue_left a b y _ (φ.natural f h)]
      exact a.natural f h
    · rw [glueValue_right a b c x p h,glueValue_right a b c y _ (ψ.natural f h)]
      exact b.natural f h

theorem PartialSection.glue_congr {Γ : Context.{u}} {A : Family Γ} {φ ψ : Subcontext Γ}
    {a a' : PartialSection A φ} {b b' : PartialSection A ψ}
    (ha : a = a') (hb : b = b') (c : a.Compatible b) (c' : a'.Compatible b') :
    a.glue b c = a'.glue b' c' := by
  cases ha
  cases hb
  rfl

theorem PartialSection.Compatible.reindex {Γ Δ : Context.{u}} {A : Family Γ} {φ ψ : Subcontext Γ}
    {a : PartialSection A φ} {b : PartialSection A ψ} (c : a.Compatible b) (σ : Δ ⟶ Γ) :
    (a.reindex σ).Compatible (b.reindex σ) := fun x p q => c (σ.mapElements.obj x) p q

theorem PartialSection.glue_reindex {Γ Δ : Context.{u}} {A : Family Γ} {φ ψ : Subcontext Γ}
    (a : PartialSection A φ) (b : PartialSection A ψ) (c : a.Compatible b) (σ : Δ ⟶ Γ) :
    (a.glue b c).reindex σ = (a.reindex σ).glue (b.reindex σ) (c.reindex σ) := by
  apply PartialSection.ext
  intro x p
  rfl

theorem PartialSection.reindex_comp {Γ Δ Θ : Context.{u}} {A : Family Γ} {φ : Subcontext Γ}
    (a : PartialSection A φ) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    (a.reindex σ).reindex τ = a.reindex (τ ≫ σ) := rfl


namespace Contractible
variable {Γ : Context.{u}} {A : Family Γ} (c : Contractible A)

def extensionTube {φ : Subcontext Γ} (a : PartialSection A φ) :
    PartialSection (Cartesian.reindex A (projection (interval Γ)))
      (φ.reindex (projection (interval Γ))) where
  val x hx := (c.contraction ((projection (interval Γ)).mapElements.obj x)
    (a.val _ hx)).val.val (𝟙 _) x.val.2
  natural {x y} f hx := by
    let q := (projection (interval Γ)).mapElements.map f
    have h := (c.contraction ((projection (interval Γ)).mapElements.obj x)
      (a.val _ hx)).val.naturality (𝟙 _) q x.val.2
    have hr : (interval Γ).map q x.val.2 = y.val.2 :=
      eq_of_heq (Sigma.mk.inj f.map_val).2
    change A.map q _ = _
    change A.map q _ = (c.contraction ((projection (interval Γ)).mapElements.obj x)
      (a.val _ hx)).val.val ((𝟙 _) ≫ q) ((interval Γ).map q x.val.2) at h
    rw [Category.id_comp, hr] at h
    apply h.trans
    have hc := c.naturality q (𝟙 _) (a.val _ hx) y.val.2
    rw [Category.comp_id, a.natural q hx] at hc
    exact hc

def extensionBox {φ : Subcontext Γ} (a : PartialSection A φ) :
    OpenBox (Cartesian.reindex A (projection (interval Γ))) φ (endpoint Γ false) where
  tube := c.extensionTube a
  base := c.center
  boundary x hx := ((c.contraction x (a.val x hx)).property (𝟙 x)).1.trans
    (ConcreteCategory.congr_hom (A.map_id x) _)

def extend (F : Filling A) {φ : Subcontext Γ} (a : PartialSection A φ) : Term A :=
  F.comp (projection (interval Γ)) φ (endpoint Γ false) (endpoint Γ true)
    (c.extensionBox a)

theorem extend_boundary (F : Filling A) (hF : F.Lawful)
    {φ : Subcontext Γ} (a : PartialSection A φ) (x : Γ.Elements) (hx : φ.holds x) :
    (c.extend F a).val x = a.val x hx :=
  (Filling.comp_tube hF (projection (interval Γ)) φ (endpoint Γ false)
    (endpoint Γ true) (c.extensionBox a) x hx).trans
      (((c.contraction x (a.val x hx)).property (𝟙 x)).2.trans
        (ConcreteCategory.congr_hom (A.map_id x) _))

theorem extend_reindex {Δ : Context.{u}} (F : Filling A) (hF : F.Lawful)
    {φ : Subcontext Γ} (a : PartialSection A φ) (σ : Δ ⟶ Γ) :
    (c.reindex σ).extend (F.reindex σ) (a.reindex σ) = Term.reindex (c.extend F a) σ :=
  congrArg (fun t => Term.reindex t (graph (endpoint Δ true)))
    (hF.uniform (projection (interval Γ)) φ (endpoint Γ false) (c.extensionBox a) σ)

end Contractible
def Filling.transport {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B) (F : Filling A) : Filling B where
  fill p φ r b := Term.map (Functor.whiskerLeft p.mapElements e.hom)
    (F.fill p φ r (b.map (Functor.whiskerLeft p.mapElements e.inv)))

theorem Filling.transport_lawful {Γ : Context.{u}} {A B : Family Γ} (e : A ≅ B)
    (F : Filling A) (hF : F.Lawful) : (F.transport e).Lawful where
  fills p φ r b := by
    have h := hF.fills p φ r (b.map (Functor.whiskerLeft p.mapElements e.inv))
    constructor
    · apply Term.ext
      intro x
      exact (congrArg (e.hom.app ((graph r ≫ p).mapElements.obj x))
        (congrArg (fun t => t.val x) h.1)).trans
          (congrArg (fun f => f.app ((graph r ≫ p).mapElements.obj x) (b.base.val x)) e.inv_hom_id)
    · intro x hx
      exact (congrArg (e.hom.app (p.mapElements.obj x)) (h.2 x hx)).trans
        (congrArg (fun f => f.app (p.mapElements.obj x) (b.tube.val x hx)) e.inv_hom_id)
  uniform p φ r b σ := by
    exact congrArg (Term.map (Functor.whiskerLeft
      (intervalSub σ ≫ p).mapElements e.hom))
      (hF.uniform p φ r (b.map (Functor.whiskerLeft p.mapElements e.inv)) σ)

@[ext] theorem Filling.ext {Γ : Context.{u}} {A : Family Γ} {F G : Filling A}
    (h : ∀ {Δ : Context.{u}} (p : total (interval Δ) ⟶ Γ) (φ : Subcontext Δ)
      (r : Term (interval Δ)) (b : OpenBox (Cartesian.reindex A p) φ r), F.fill p φ r b = G.fill p φ r b) : F = G := by
  cases F
  cases G
  congr 1
  funext Δ p φ r b
  exact h p φ r b

theorem OpenBox.map_iso_roundtrip {Γ : Context.{u}} {A B : Family (total (interval Γ))}
    (e : A ≅ B) {φ : Subcontext Γ} {r : Term (interval Γ)} (b : OpenBox B φ r) : (b.map e.inv).map e.hom = b := by
  apply OpenBox.ext
  · apply PartialSection.ext
    intro x hx
    exact congrArg (fun η => η.app x (b.tube.val x hx)) e.inv_hom_id
  · apply Term.ext
    intro x
    exact congrArg (fun η => η.app ((graph r).mapElements.obj x) (b.base.val x)) e.inv_hom_id

end SquareKit.Cubical.Cartesian
