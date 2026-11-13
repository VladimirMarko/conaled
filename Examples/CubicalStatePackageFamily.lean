import Examples.CubicalStateTransport
import Examples.CubicalUnivalenceTransport
import SquareKit.Internal.Cubical.SmallFamilyConstructors

/-! A proof-bearing state package over a varying native carrier. Every field is
an internal dependent sum or product; proposition and proof fibers are discrete.
The selected package filler is constructed from the carrier filler. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalStatePackageFamily
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalGlue

variable {Γ : Context.{0}}

noncomputable def endomorphisms (A : LocalFamily Γ) : LocalFamily Γ :=
  A.pi (A.reindex (projection A.family))

noncomputable def predicates (A : LocalFamily Γ) : LocalFamily Γ :=
  A.pi (constantLocal (total A.family) Prop)

noncomputable def data (A : LocalFamily Γ) : LocalFamily Γ :=
  A.sigma (((endomorphisms A).reindex (projection A.family)).sigma
    ((predicates A).reindex
      (projection ((endomorphisms A).reindex (projection A.family)).family ≫ projection A.family)))

noncomputable abbrev dataContext (A : LocalFamily Γ) := total (data A).family

noncomputable def carrier (A : LocalFamily Γ) : LocalFamily (dataContext A) :=
  A.reindex (projection (data A).family)

noncomputable def initial (A : LocalFamily Γ) : Term (carrier A).family where
  val x := x.val.2.1
  property f := congrArg (fun z => z.1) ((generic (data A).family).property f)

noncomputable def rawStep (A : LocalFamily Γ) :
    Term (reindex (endomorphisms A).family (projection (data A).family)) where
  val x := x.val.2.2.1
  property {_x y} f := congrArg
    (fun z => (z.2.1 : (endomorphisms A).family.obj ((projection (data A).family).mapElements.obj y)))
    ((generic (data A).family).property f)

noncomputable def rawInvariant (A : LocalFamily Γ) :
    Term (reindex (predicates A).family (projection (data A).family)) where
  val x := x.val.2.2.2
  property {_x y} f := congrArg
    (fun z => (z.2.2 : (predicates A).family.obj ((projection (data A).family).mapElements.obj y)))
    ((generic (data A).family).property f)

noncomputable def step (A : LocalFamily Γ) : Term (endomorphisms (carrier A)).family :=
  Term.map (piReindex A.family (reindex A.family (projection A.family))
    (projection (data A).family)) (rawStep A)

noncomputable def invariant (A : LocalFamily Γ) : Term (predicates (carrier A)).family :=
  Term.map (piReindex A.family (constantFamily (total A.family) Prop)
    (projection (data A).family)) (rawInvariant A)

def applyTerm {A : Family Γ} {B : Family (total A)}
    (f : Term (pi A B)) (a : Term A) : Term (reindex B (pair (𝟙 Γ) a)) :=
  (app f).reindex (pair (𝟙 Γ) a)

def proofFamily (q : Term (constantFamily Γ Prop)) : LocalFamily Γ :=
  LocalFamily.discrete q (fun p => PLift p)

noncomputable def initialValid (A : LocalFamily Γ) : LocalFamily (dataContext A) :=
  proofFamily (applyTerm (invariant A) (initial A))

noncomputable def premise (A : LocalFamily Γ) :
    Term (constantFamily (total (carrier A).family) Prop) := app (invariant A)

noncomputable def conclusion (A : LocalFamily Γ) :
    Term (constantFamily (total (carrier A).family) Prop) :=
  (app (invariant A)).reindex (pair (projection (carrier A).family) (app (step A)))

def implies (p q : Term (constantFamily Γ Prop)) : Term (constantFamily Γ Prop) where
  val x := p.val x → q.val x
  property f := by
    change (p.val _ → q.val _) = (p.val _ → q.val _)
    exact congrArg₂ (fun a b : Prop => a → b) (p.property f) (q.property f)

noncomputable def preserves (A : LocalFamily Γ) : LocalFamily (dataContext A) :=
  (carrier A).pi (proofFamily (implies (premise A) (conclusion A)))

noncomputable def package (A : LocalFamily Γ) : LocalFamily Γ :=
  (data A).sigma ((initialValid A).sigma
    ((preserves A).reindex (projection (initialValid A).family)))

/-- No package filler or law is assumed: both are derived through native Σ/Π
and the discrete proof-family constructor. -/
theorem package_filling_lawful (A : LocalFamily Γ) : (package A).toNative.filling.Lawful :=
  (package A).toNative.lawful

end Examples.CubicalStatePackageFamily

namespace Examples.CubicalStatePackageFamily
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalGlue Examples.CubicalStateTransport
variable {Γ : Context.{0}}

/-- Reading a generalized element retains its initial state, operation,
predicate, and both proof fields. -/
noncomputable def readOut (A : LocalFamily Γ) (x : Γ.Elements)
    (z : (package A).family.obj x) : StatePackage (A.family.obj x) where
  initial := z.1.1
  step a := z.1.2.1.val (𝟙 _) a
  invariant a := z.1.2.2.val (𝟙 _) a
  initial_valid := z.2.1.down
  preserves a h := (z.2.2.val (𝟙 _) a).down h


end Examples.CubicalStatePackageFamily

namespace Examples.CubicalStatePackageFamily
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
variable {Γ : Context.{0}}

noncomputable def initialSection {A : LocalFamily Γ} (s : Term (package A).family) :
    Term A.family := sigmaFst (sigmaFst s)

noncomputable def stepSection {A : LocalFamily Γ} (s : Term (package A).family) :
    Term (endomorphisms A).family where
  val x := (s.val x).1.2.1
  property {_x y} f := congrArg (fun z => (z.1.2.1 : (endomorphisms A).family.obj y)) (s.property f)

noncomputable def invariantSection {A : LocalFamily Γ} (s : Term (package A).family) :
    Term (predicates A).family where
  val x := (s.val x).1.2.2
  property {_x y} f := congrArg (fun z => (z.1.2.2 : (predicates A).family.obj y)) (s.property f)

theorem readOut_initial {A : LocalFamily Γ} (s : Term (package A).family) (x : Γ.Elements) :
    (readOut A x (s.val x)).initial = (initialSection s).val x := rfl

theorem readOut_step {A : LocalFamily Γ} (s : Term (package A).family) (x : Γ.Elements)
    (a : A.family.obj x) :
    (readOut A x (s.val x)).step a = ((stepSection s).val x).val (𝟙 _) a := rfl

theorem readOut_invariant {A : LocalFamily Γ} (s : Term (package A).family) (x : Γ.Elements)
    (a : A.family.obj x) :
    (readOut A x (s.val x)).invariant a = ((invariantSection s).val x).val (𝟙 _) a := rfl

end Examples.CubicalStatePackageFamily

namespace Examples.CubicalStatePackageFamily
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalStateTransport
variable {Γ : Context.{0}} {S : Type}

private theorem iso_hom_inv (A : Family Γ) (e : A ≅ constantFamily Γ S)
    (x : Γ.Elements) (s : S) : e.hom.app x (e.inv.app x s) = s :=
  congrArg (fun h => h.app x s) e.inv_hom_id

private theorem iso_inv_hom (A : Family Γ) (e : A ≅ constantFamily Γ S)
    (x : Γ.Elements) (a : A.obj x) : e.inv.app x (e.hom.app x a) = a :=
  congrArg (fun h => h.app x a) e.hom_inv_id

theorem package_ext (A : LocalFamily Γ) (x : Γ.Elements)
    (z w : (package A).family.obj x) (h : z.1 = w.1) : z = w := by
  rcases z with ⟨d, hi, hs⟩
  rcases w with ⟨d', hi', hs'⟩
  cases h
  have hiEq : hi = hi' := by apply PLift.ext; apply Subsingleton.elim
  cases hiEq
  have hsEq : hs = hs' := by
    apply PiElement.ext
    intros
    apply PLift.ext
    apply Subsingleton.elim
  cases hsEq
  rfl

noncomputable def pullData (A : LocalFamily Γ) (e : A.family ≅ constantFamily Γ S)
    (s : StatePackage S) : Term (data A).family where
  val x := ⟨e.inv.app x s.initial, ⟨
    { val := fun {y} _ a => e.inv.app y (s.step (e.hom.app y a))
      naturality := by
        intro y z f g a
        change A.family.map g (e.inv.app y (s.step (e.hom.app y a))) =
          e.inv.app z (s.step (e.hom.app z (A.family.map g a)))
        rw [← e.inv.naturality_apply, e.hom.naturality_apply]
        rfl },
    { val := fun {y} _ a => s.invariant (e.hom.app y a)
      naturality := by
        intro y z f g a
        change s.invariant (e.hom.app y a) = s.invariant (e.hom.app z (A.family.map g a))
        rw [e.hom.naturality_apply]
        rfl }⟩⟩
  property := by
    intro x y f
    apply Sigma.ext
    · exact e.inv.naturality_apply f s.initial |>.symm
    · apply HEq.rfl

noncomputable def pullInitialProof (A : LocalFamily Γ) (e : A.family ≅ constantFamily Γ S)
    (s : StatePackage S) :
    Term (reindex (initialValid A).family (pair (𝟙 Γ) (pullData A e s))) where
  val x := ⟨by
    change s.invariant (e.hom.app x (e.inv.app x s.initial))
    rw [iso_hom_inv]
    exact s.initial_valid⟩
  property := by intro _x _y _f; apply PLift.ext; apply Subsingleton.elim

noncomputable def pullPreservesBody (A : LocalFamily Γ) (e : A.family ≅ constantFamily Γ S)
    (s : StatePackage S) :
    Term (reindex (proofFamily (implies (premise A) (conclusion A))).family
      (liftSub (carrier A).family (pair (𝟙 Γ) (pullData A e s)))) where
  val x := ⟨by
    change s.invariant (e.hom.app _ x.val.2) →
      s.invariant (e.hom.app _ (e.inv.app _ (s.step (e.hom.app _ x.val.2))))
    rw [iso_hom_inv]
    exact s.preserves _⟩
  property := by intro _x _y _f; apply PLift.ext; apply Subsingleton.elim

noncomputable def pullPreserves (A : LocalFamily Γ) (e : A.family ≅ constantFamily Γ S)
    (s : StatePackage S) :
    Term (reindex (preserves A).family (pair (𝟙 Γ) (pullData A e s))) :=
  Term.map (piReindexIso (carrier A).family
    (proofFamily (implies (premise A) (conclusion A))).family
    (pair (𝟙 Γ) (pullData A e s))).inv (lam (pullPreservesBody A e s))

/-- Pull a complete host package back through a carrier presentation. Native
product substitution extends the preservation proof to all generalized arguments. -/
noncomputable def pullPackage (A : LocalFamily Γ) (e : A.family ≅ constantFamily Γ S)
    (s : StatePackage S) : Term (package A).family :=
  sigmaIntro (B := ((initialValid A).sigma
    ((preserves A).reindex (projection (initialValid A).family))).family)
    (pullData A e s)
    (sigmaIntro (B := reindex (preserves A).family
      (projection (reindex (initialValid A).family (pair (𝟙 Γ) (pullData A e s))) ≫
        pair (𝟙 Γ) (pullData A e s))) (pullInitialProof A e s) (pullPreserves A e s))

end Examples.CubicalStatePackageFamily
namespace Examples.CubicalStatePackageFamily
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalStateTransport
variable {Γ : Context.{0}}

theorem statePackage_ext {S : Type} (p q : StatePackage S)
    (ha : p.initial = q.initial) (hs : p.step = q.step) (hi : p.invariant = q.invariant) : p = q := by
  cases p
  cases q
  cases ha
  cases hs
  cases hi
  rfl

theorem step_natural {A : LocalFamily Γ} (s : Term (package A).family)
    {x y : Γ.Elements} (f : x ⟶ y) (a : A.family.obj x) :
    (readOut A y (s.val y)).step (A.family.map f a) =
      A.family.map f ((readOut A x (s.val x)).step a) := by
  have ht := congrArg (fun p => p.val (𝟙 y) (A.family.map f a)) ((stepSection s).property f)
  have hn := ((stepSection s).val x).naturality (𝟙 x) f a
  change ((stepSection s).val x).val (f ≫ 𝟙 y) (A.family.map f a) = _ at ht
  simp only [Category.id_comp, Category.comp_id] at ht hn
  exact ht.symm.trans hn.symm

theorem invariant_natural {A : LocalFamily Γ} (s : Term (package A).family)
    {x y : Γ.Elements} (f : x ⟶ y) (a : A.family.obj x) :
    (readOut A y (s.val y)).invariant (A.family.map f a) =
      (readOut A x (s.val x)).invariant a := by
  have ht := congrArg (fun p => p.val (𝟙 y) (A.family.map f a)) ((invariantSection s).property f)
  have hn := ((invariantSection s).val x).naturality (𝟙 x) f a
  change ((invariantSection s).val x).val (f ≫ 𝟙 y) (A.family.map f a) = _ at ht
  simp only [Category.id_comp, Category.comp_id] at ht hn
  exact ht.symm.trans hn.symm

noncomputable def observe {S : Type} (A : LocalFamily Γ)
    (e : A.family ≅ constantFamily Γ S) (s : Term (package A).family) :
    Term (constantFamily Γ (StatePackage S)) where
  val x := (readOut A x (s.val x)).conjugate (e.app x).toEquiv
  property := by
    intro x y f
    apply statePackage_ext
    · change e.hom.app x ((initialSection s).val x) = e.hom.app y ((initialSection s).val y)
      rw [← (initialSection s).property f, e.hom.naturality_apply]
      rfl
    · funext b
      change e.hom.app x ((readOut A x (s.val x)).step (e.inv.app x b)) =
        e.hom.app y ((readOut A y (s.val y)).step (e.inv.app y b))
      have hb : e.inv.app y b = A.family.map f (e.inv.app x b) := e.inv.naturality_apply f b
      rw [hb, step_natural s f, e.hom.naturality_apply]
      rfl
    · funext b
      change (readOut A x (s.val x)).invariant (e.inv.app x b) =
        (readOut A y (s.val y)).invariant (e.inv.app y b)
      have hb : e.inv.app y b = A.family.map f (e.inv.app x b) := e.inv.naturality_apply f b
      rw [hb, invariant_natural s f]

end Examples.CubicalStatePackageFamily

namespace Examples.CubicalStatePackageFamily
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalStateTransport
variable {Γ : Context.{0}} {S : Type}

theorem observe_pull (A : LocalFamily Γ) (e : A.family ≅ constantFamily Γ S)
    (s : StatePackage S) : observe A e (pullPackage A e s) =
      (⟨fun _ => s, fun _ => rfl⟩ : Term (constantFamily _ (StatePackage S))) := by
  apply Term.ext
  intro x
  apply statePackage_ext
  · change e.hom.app x (e.inv.app x s.initial) = s.initial
    exact iso_hom_inv _ e x _
  · funext b
    change e.hom.app x (e.inv.app x (s.step (e.hom.app x (e.inv.app x b)))) = s.step b
    rw [iso_hom_inv, iso_hom_inv]
  · funext b
    change s.invariant (e.hom.app x (e.inv.app x b)) = s.invariant b
    rw [iso_hom_inv]

noncomputable def filledPackage (A : LocalFamily (total (interval Γ)))
    (e : A.family ≅ constantFamily (total (interval Γ)) S) (s : StatePackage S) :
    Term (package A).family :=
  IntervalTransport.forward (package A).toNative.filling (𝟙 Γ)
    ((pullPackage A e s).reindex (endpointSub Γ false))

/-- This observes the chosen Σ/Π package filler, whose only input from the
constructed pullback section is its initial restriction. -/
theorem filledPackage_observed (A : LocalFamily (total (interval Γ)))
    (e : A.family ≅ constantFamily (total (interval Γ)) S) (s : StatePackage S) :
    observe A e (filledPackage A e s) = (⟨fun _ => s, fun _ => rfl⟩ : Term (constantFamily _ (StatePackage S))) := by
  apply Term.ext
  intro x
  rcases x with @⟨I, ⟨γ, r⟩⟩
  let y := Γ.elementsMk I γ
  let z := extendObj (interval Γ) y ((endpoint Γ false).val y)
  have h₀ := congrArg (fun t => t.val y)
    (IntervalTransport.forward_zero (package A).toNative.filling (package A).toNative.lawful
      (𝟙 Γ) ((pullPackage A e s).reindex (endpointSub Γ false)))
  calc
    _ = (observe A e (filledPackage A e s)).val z :=
      constant_section_interval _ y r ((endpoint Γ false).val y)
    _ = (observe A e (pullPackage A e s)).val z :=
      congrArg (fun v => (readOut A z v).conjugate (e.app z).toEquiv) h₀
    _ = s := congrArg (fun t => t.val z) (observe_pull A e s)

end Examples.CubicalStatePackageFamily

namespace Examples.CubicalStatePackageFamily
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf
open Examples.CubicalStateTransport
variable {Γ : Context.{0}} {S T U : Type}

theorem readOut_pull (A : LocalFamily Γ) (e : A.family ≅ constantFamily Γ S)
    (s : StatePackage S) (x : Γ.Elements) :
    readOut A x ((pullPackage A e s).val x) = s.conjugate (e.app x).toEquiv.symm := by
  apply statePackage_ext <;> rfl

theorem conjugate_trans (s : StatePackage S) (e : S ≃ T) (f : T ≃ U) :
    (s.conjugate e).conjugate f = s.conjugate (e.trans f) := by
  apply statePackage_ext <;> rfl

theorem conjugate_symm (s : StatePackage S) (e : S ≃ T) :
    (s.conjugate e).conjugate e.symm = s := by
  apply statePackage_ext
  · exact e.symm_apply_apply _
  · funext a
    change e.symm (e (s.step (e.symm (e a)))) = s.step a
    rw [e.symm_apply_apply, e.symm_apply_apply]
  · funext a
    change s.invariant (e.symm (e a)) = s.invariant a
    rw [e.symm_apply_apply]

end Examples.CubicalStatePackageFamily
