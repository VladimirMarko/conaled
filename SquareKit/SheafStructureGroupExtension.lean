import SquareKit.SheafAssociatedBundleDescent
import SquareKit.SheafTorsorDescent

/-! Extension along arbitrary group-sheaf homomorphisms. The fiber action is
right multiplication by the inverse image, so left multiplication descends. -/
noncomputable section
namespace SquareKit.SheafStructureGroupExtension
open CategoryTheory Opposite
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H K : Sheaf J GrpCat.{w}}

set_option backward.isDefEq.respectTransparency false in
/-- The action defining extension of a left torsor along `φ`. -/
def rightInverseAction (φ : G ⟶ H) :
    SheafActionQuotient.Action G (SheafTorsor.groupSheaf H) where
  act U g h := (show H.obj.obj U from h) * (φ.hom.app U g)⁻¹
  one_act U h := by simp only [(φ.hom.app U).hom.map_one, inv_one, mul_one]
  mul_act U g k h := by
    simp only [(φ.hom.app U).hom.map_mul, mul_inv_rev, mul_assoc]
  natural {U V} f g h := by
    change H.obj.map f ((show H.obj.obj U from h) * (φ.hom.app U g)⁻¹) = _
    rw [(H.obj.map f).hom.map_mul, (H.obj.map f).hom.map_inv]
    congr 2
    exact (congrArg (fun k => k g) (φ.hom.naturality f)).symm

set_option backward.isDefEq.respectTransparency false in
theorem left_mul_commutes (φ : G ⟶ H) (U : Cᵒᵖ)
    (g : G.obj.obj U) (h k : H.obj.obj U) :
    (rightInverseAction φ).act U g (h * k) =
      h * (show H.obj.obj U from (rightInverseAction φ).act U g k) := by
  change (h * k) * (φ.hom.app U g)⁻¹ = h * (k * (φ.hom.app U g)⁻¹)
  exact mul_assoc _ _ _

section Descent
variable {G H K : Sheaf J GrpCat.{max u v}} {X : Sheaf J (Type (max u v))}
open SheafTorsor SheafAssociatedBundle

set_option backward.isDefEq.respectTransparency false in
/-- The associated transition maps preserve the regular left H-action. -/
def extensionDatum (φ : G ⟶ H) (P : Torsor G X) :
    Descent.Datum P.family (trivial H (SplitSheaf.Ext P.family)) where
  transport := (datum P (rightInverseAction φ)).transport
  identity := (datum P (rightInverseAction φ)).identity
  cocycle := (datum P (rightInverseAction φ)).cocycle
  natural := (datum P (rightInverseAction φ)).natural
  equivariant x p q h k := left_mul_commutes φ x.obj (fiberDifference P x p q) h k

@[simp] theorem extensionDatum_display (φ : G ⟶ H) (P : Torsor G X) :
    (extensionDatum φ P).toDisplayDatum = datum P (rightInverseAction φ) := rfl

/-- Effective descent proves principality and local existence of the extension. -/
def extension (φ : G ⟶ H) (P : Torsor G X) : Torsor H X :=
  Descent.torsor (extensionDatum φ P)

@[simp] theorem extension_family (φ : G ⟶ H) (P : Torsor G X) :
    (extension φ P).family = associated P (rightInverseAction φ) := rfl

set_option backward.isDefEq.respectTransparency false in
theorem evaluate_act (φ : G ⟶ H) (P : Torsor G X) (x : X.obj.Elements)
    (p : P.family.family.obj x) (h : H.obj.obj x.obj)
    (s : (extension φ P).family.family.obj x) :
    evaluate P (rightInverseAction φ) x p ((extension φ P).act x h s) =
      h * (show H.obj.obj x.obj from evaluate P (rightInverseAction φ) x p s) :=
  Descent.evaluation_equivariant (extensionDatum φ P) (Descent.point P.family x p) h s

set_option backward.isDefEq.respectTransparency false in
theorem act_classOf (φ : G ⟶ H) (P : Torsor G X) (x : X.obj.Elements)
    (p : P.family.family.obj x) (h k : H.obj.obj x.obj) :
    (extension φ P).act x h (classOf P (rightInverseAction φ) x p k) =
      classOf P (rightInverseAction φ) x p (h * k) := by
  apply (evaluate P (rightInverseAction φ) x p).injective
  rw [evaluate_act, evaluate_classOf, evaluate_classOf]

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map into the extended torsor is semilinear along φ. -/
def unit (φ : G ⟶ H) (P : Torsor G X) : SemilinearMap φ P (extension φ P) where
  hom := {
    app x := ↾fun p => classOf P (rightInverseAction φ) x p (1 : H.obj.obj x.obj)
    naturality {x y} f := by
      ext p
      symm
      change (associated P (rightInverseAction φ)).family.map f
          (classOf P (rightInverseAction φ) x p (1 : H.obj.obj x.obj)) =
        classOf P (rightInverseAction φ) y (P.family.family.map f p) (1 : H.obj.obj y.obj)
      rw [classOf_natural]
      congr 1
      exact (H.obj.map f.hom).hom.map_one }
  equivariant x g p := by
    change classOf P (rightInverseAction φ) x (P.act x g p) (1 : H.obj.obj x.obj) =
      (extension φ P).act x (φ.hom.app x.obj g)
        (classOf P (rightInverseAction φ) x p (1 : H.obj.obj x.obj))
    rw [act_classOf, mul_one]
    have hh := classOf_diagonal P (rightInverseAction φ) x g p (φ.hom.app x.obj g)
    simpa only [rightInverseAction, mul_inv_cancel] using hh

variable {φ : G ⟶ H} {P : Torsor G X} {Q : Torsor H X}

set_option backward.isDefEq.respectTransparency false in
/-- A semilinear map defines the expected invariant map `[p,h] ↦ h • f(p)`. -/
def invariantOfSemilinear (f : SemilinearMap φ P Q) :
    InvariantMap P (rightInverseAction φ) Q.family where
  value x p h := Q.act x h (f.hom.app x p)
  natural k p h := by
    rw [Q.natural, ← NatTrans.naturality_apply]
    rfl
  invariant x g p h := by
    rw [f.equivariant]
    change Q.act x ((show H.obj.obj x.obj from h) * (φ.hom.app x.obj g)⁻¹)
      (Q.act x (φ.hom.app x.obj g) (f.hom.app x p)) = _
    rw [← Q.mul_act, mul_assoc, inv_mul_cancel, mul_one]

set_option backward.isDefEq.respectTransparency false in
/-- The invariant map also respects the residual H-action before descent. -/
def liftDatum (f : SemilinearMap φ P Q) :
    Descent.Map (extensionDatum φ P) (Descent.canonicalDatum P.family Q) where
  hom := (invariantOfSemilinear f).datumMap.hom
  equivariant z h k := Q.mul_act (X.obj.elementsMk z.obj z.val.1) h k (f.hom.app _ z.val.2)
  transport := (invariantOfSemilinear f).datumMap.transport

/-- The extension of a semilinear map is an ordinary H-torsor arrow. -/
def lift (f : SemilinearMap φ P Q) : Arrow (extension φ P) Q :=
  (liftDatum f).arrow.comp (Descent.canonicalRecovery P.family Q)

set_option backward.isDefEq.respectTransparency false in
private theorem recovery_evaluate (x : X.obj.Elements) (p : P.family.family.obj x)
    (s : (Descent.family (Descent.canonicalDatum P.family Q)).family.obj x) :
    (Descent.canonicalRecovery P.family Q).iso.hom.app x s =
      Descent.evaluationEquiv (Descent.canonicalDatum P.family Q) x p s := by
  let e := Descent.canonicalRecovery P.family Q
  have he := congrArg (fun k => k.app x s) e.iso.hom_inv_id
  have hh := congrArg (Descent.evaluationEquiv (Descent.canonicalDatum P.family Q) x p) he
  have hv := Descent.canonicalValue_evaluate P.family Q (𝟙 x) (e.iso.hom.app x s) p
  rw [SplitFunctionDiagram.restrict_id] at hv
  have hm := congrArg (fun k => k (e.iso.hom.app x s)) (Q.family.family.map_id x)
  exact (hv.trans hm).symm.trans hh

set_option backward.isDefEq.respectTransparency false in
theorem lift_classOf (f : SemilinearMap φ P Q) (x : X.obj.Elements)
    (p : P.family.family.obj x) (h : H.obj.obj x.obj) :
    (lift f).iso.hom.app x (classOf P (rightInverseAction φ) x p h) =
      Q.act x h (f.hom.app x p) := by
  change (Descent.canonicalRecovery P.family Q).iso.hom.app x
    ((liftDatum f).descend.app x (classOf P (rightInverseAction φ) x p h)) = _
  rw [recovery_evaluate (P := P) x p, Descent.Map.evaluation]
  change Q.act x (evaluate P (rightInverseAction φ) x p
    (classOf P (rightInverseAction φ) x p h)) (f.hom.app x p) = _
  rw [evaluate_classOf]

set_option backward.isDefEq.respectTransparency false in
/-- Restrict an H-equivariant arrow along the canonical semilinear map. -/
def restrictLift (f : Arrow (extension φ P) Q) : SemilinearMap φ P Q where
  hom := (unit φ P).hom ≫ f.iso.hom
  equivariant x g p := by
    change f.iso.hom.app x ((unit φ P).hom.app x (P.act x g p)) = _
    rw [(unit φ P).equivariant, f.equivariant]
    rfl

set_option backward.isDefEq.respectTransparency false in
theorem restrictLift_lift (f : SemilinearMap φ P Q) : restrictLift (lift f) = f := by
  apply SemilinearMap.ext
  ext x p
  change (lift f).iso.hom.app x (classOf P (rightInverseAction φ) x p (1 : H.obj.obj x.obj)) = _
  rw [lift_classOf, Q.one_act]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem lift_restrictLift (f : Arrow (extension φ P) Q) : lift (restrictLift f) = f := by
  apply SheafTorsor.Arrow.ext
  change (show associated P (rightInverseAction φ) ⟶ Q.family from
    (lift (restrictLift f)).iso.hom) = (show associated P (rightInverseAction φ) ⟶ Q.family from f.iso.hom)
  apply SheafAssociatedBundle.hom_ext
  intro x p h
  change (lift (restrictLift f)).iso.hom.app x (classOf P (rightInverseAction φ) x p h) =
    f.iso.hom.app x (classOf P (rightInverseAction φ) x p h)
  rw [lift_classOf]
  change Q.act x h (f.iso.hom.app x
    (classOf P (rightInverseAction φ) x p (1 : H.obj.obj x.obj))) = _
  rw [← f.equivariant, act_classOf, mul_one]

/-- The full universal property retains arrows, not merely isomorphism classes. -/
def universal (φ : G ⟶ H) (P : Torsor G X) (Q : Torsor H X) :
    Arrow (extension φ P) Q ≃ SemilinearMap φ P Q where
  toFun := restrictLift
  invFun := lift
  left_inv := lift_restrictLift
  right_inv := restrictLift_lift

/-- Equivariance can be checked after a locally inhabited display, without a
chosen global section or surjectivity of the group homomorphism. -/
theorem equivariant_of_cover {A : SplitSheaf.Ty X}
    [Presheaf.IsLocallySurjective J (SplitSheaf.p A).hom]
    {σ : G ⟶ H} {R : Torsor G X} {S : Torsor H X}
    (h : R.family.family ⟶ S.family.family)
    (he : ∀ x, A.family.obj x → ∀ g r,
      h.app x (R.act x g r) = S.act x (σ.hom.app x.obj g) (h.app x r))
    (x : X.obj.Elements) (g : G.obj.obj x.obj) (r : R.family.family.obj x) :
    h.app x (R.act x g r) = S.act x (σ.hom.app x.obj g) (h.app x r) := by
  apply SplitSheafDescent.fiber_ext S.family x
    (Presheaf.imageSieve (SplitSheaf.p A).hom x.val)
    (Presheaf.imageSieve_mem J (SplitSheaf.p A).hom x.val)
  rintro V k ⟨⟨z,p⟩,hz⟩
  change z = X.obj.map k.op x.val at hz
  subst z
  let y := X.obj.elementsMk (op V) (X.obj.map k.op x.val)
  let l := ElementFamilies.along X.obj k.op x.val
  change S.family.family.map l (h.app x (R.act x g r)) =
    S.family.family.map l (S.act x (σ.hom.app x.obj g) (h.app x r))
  rw [← NatTrans.naturality_apply h l, R.natural, he y p, S.natural,
    ← NatTrans.naturality_apply h l]
  exact congrArg (fun t => S.act y t (h.app y (R.family.family.map l r)))
    (congrArg (fun t => t g) (σ.hom.naturality l.hom))

variable {ψ : H ⟶ K} {R : Torsor K X}

set_option backward.isDefEq.respectTransparency false in
/-- A second group homomorphism acts on the local extension coordinate. -/
def compositeInvariant (f : SemilinearMap (φ ≫ ψ) P R) :
    InvariantMap P (rightInverseAction φ) R.family where
  value x p h := R.act x (ψ.hom.app x.obj h) (f.hom.app x p)
  natural k p h := by
    rw [R.natural, ← NatTrans.naturality_apply f.hom k]
    congr 1
    exact (congrArg (fun t => t h) (ψ.hom.naturality k.hom)).symm
  invariant x g p h := by
    rw [f.equivariant]
    change R.act x (ψ.hom.app x.obj ((show H.obj.obj x.obj from h) * (φ.hom.app x.obj g)⁻¹))
      (R.act x (ψ.hom.app x.obj (φ.hom.app x.obj g)) (f.hom.app x p)) = _
    rw [(ψ.hom.app x.obj).hom.map_mul, (ψ.hom.app x.obj).hom.map_inv,
      ← R.mul_act, mul_assoc, inv_mul_cancel, mul_one]

set_option backward.isDefEq.respectTransparency false in
/-- Extension also descends maps semilinear along a further homomorphism. -/
def semilinearLift (f : SemilinearMap (φ ≫ ψ) P R) : SemilinearMap ψ (extension φ P) R where
  hom := (compositeInvariant f).descend
  equivariant := equivariant_of_cover (A := P.family) (R := extension φ P) (S := R)
    (σ := ψ) (compositeInvariant f).descend (by
    intro x p h s
    change (compositeInvariant f).descend.app x ((extension φ P).act x h s) =
      R.act x (ψ.hom.app x.obj h) ((compositeInvariant f).descend.app x s)
    rw [← classOf_evaluate P (rightInverseAction φ) x p s]
    rw [act_classOf, (compositeInvariant f).descend_classOf x p _,
      (compositeInvariant f).descend_classOf x p _]
    change R.act x (ψ.hom.app x.obj (h * _)) _ = R.act x (ψ.hom.app x.obj h) (R.act x _ _)
    rw [(ψ.hom.app x.obj).hom.map_mul, R.mul_act])

set_option backward.isDefEq.respectTransparency false in
theorem semilinearLift_classOf (f : SemilinearMap (φ ≫ ψ) P R) (x : X.obj.Elements)
    (p : P.family.family.obj x) (h : H.obj.obj x.obj) :
    (semilinearLift f).hom.app x (classOf P (rightInverseAction φ) x p h) =
      R.act x (ψ.hom.app x.obj h) (f.hom.app x p) :=
  (compositeInvariant f).descend_classOf x p h

/-- The identity extension has the expected map `[p,h] ↦ h • p`. -/
def identityComparison (P : Torsor G X) : Arrow (extension (𝟙 G) P) P :=
  lift (SemilinearMap.ident P)

/-- Changing structure group twice agrees with changing it along the composite. -/
def compositionComparison (φ : G ⟶ H) (ψ : H ⟶ K) (P : Torsor G X) :
    Arrow (extension ψ (extension φ P)) (extension (φ ≫ ψ) P) :=
  lift (semilinearLift (φ := φ) (ψ := ψ) (unit (φ ≫ ψ) P))

set_option backward.isDefEq.respectTransparency false in
theorem compositionComparison_classOf (φ : G ⟶ H) (ψ : H ⟶ K) (P : Torsor G X)
    (x : X.obj.Elements) (p : P.family.family.obj x) (h : H.obj.obj x.obj) (k : K.obj.obj x.obj) :
    (compositionComparison φ ψ P).iso.hom.app x
      (classOf (extension φ P) (rightInverseAction ψ) x (classOf P (rightInverseAction φ) x p h) k) =
    classOf P (rightInverseAction (φ ≫ ψ)) x p (k * ψ.hom.app x.obj h) := by
  rw [show compositionComparison φ ψ P = lift (semilinearLift (φ := φ) (ψ := ψ)
    (unit (φ ≫ ψ) P)) from rfl, lift_classOf, semilinearLift_classOf]
  change (extension (φ ≫ ψ) P).act x k ((extension (φ ≫ ψ) P).act x (ψ.hom.app x.obj h)
    (classOf P (rightInverseAction (φ ≫ ψ)) x p (1 : K.obj.obj x.obj))) = _
  rw [← (extension (φ ≫ ψ) P).mul_act, act_classOf, mul_one]

/-- Every ordinary torsor arrow induces a map of its extensions. -/
def extensionMap (φ : G ⟶ H) {P Q : Torsor G X} (f : P ⟶ Q) :
    Arrow (extension φ P) (extension φ Q) :=
  lift ((SemilinearMap.ofArrow f).comp (unit φ Q))

set_option backward.isDefEq.respectTransparency false in
theorem extensionMap_classOf (φ : G ⟶ H) {P Q : Torsor G X} (f : P ⟶ Q)
    (x : X.obj.Elements) (p : P.family.family.obj x) (h : H.obj.obj x.obj) :
    (extensionMap φ f).iso.hom.app x (classOf P (rightInverseAction φ) x p h) =
      classOf Q (rightInverseAction φ) x (f.iso.hom.app x p) h := by
  have he := lift_classOf ((SemilinearMap.ofArrow f).comp (unit φ Q)) x p h
  change (extensionMap φ f).iso.hom.app x (classOf P (rightInverseAction φ) x p h) =
    (extension φ Q).act x h (classOf Q (rightInverseAction φ) x (f.iso.hom.app x p) (1 : H.obj.obj x.obj)) at he
  exact he.trans (by rw [act_classOf, mul_one])

set_option backward.isDefEq.respectTransparency false in
theorem extensionMap_underlying (φ : G ⟶ H) {P Q : Torsor G X} (f : P ⟶ Q) :
    (extensionMap φ f).iso.hom = (SheafAssociatedBundle.functor (rightInverseAction φ) X).map f := by
  change (show associated P (rightInverseAction φ) ⟶ associated Q (rightInverseAction φ)
    from (extensionMap φ f).iso.hom) = _
  apply SheafAssociatedBundle.hom_ext
  intro x p h
  exact (extensionMap_classOf φ f x p h).trans (functor_map_classOf f x p h).symm

/-- Extension is a functor on all torsor arrows. -/
def extensionFunctor (φ : G ⟶ H) (X : Sheaf J (Type (max u v))) :
    Torsor G X ⥤ Torsor H X where
  obj P := extension φ P
  map f := extensionMap φ f
  map_id P := by
    apply SheafTorsor.Arrow.ext
    rw [extensionMap_underlying]
    exact (SheafAssociatedBundle.functor (rightInverseAction φ) X).map_id P
  map_comp f g := by
    apply SheafTorsor.Arrow.ext
    change (extensionMap φ (f ≫ g)).iso.hom = (extensionMap φ f).iso.hom ≫ (extensionMap φ g).iso.hom
    rw [extensionMap_underlying, extensionMap_underlying, extensionMap_underlying, Functor.map_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in
/-- The extension comparison is an equivariant arrow over an arbitrary base change. -/
def reindexComparison (φ : G ⟶ H) (P : Torsor G X)
    {Y : Sheaf J (Type (max u v))} (f : Y ⟶ X) :
    Arrow (extension φ (reindex P f)) (reindex (extension φ P) f) :=
  EquivariantMap.toArrow {
    hom := reindexMap P (rightInverseAction φ) f
    equivariant := equivariant_of_cover (A := (reindex P f).family)
      (R := extension φ (reindex P f)) (S := reindex (extension φ P) f) (σ := 𝟙 H)
      (reindexMap P (rightInverseAction φ) f) (by
        intro x p h s
        change (reindexMap P (rightInverseAction φ) f).app x
          ((extension φ (reindex P f)).act x h s) =
          (extension φ P).act (f.hom.mapElements.obj x) h
            ((reindexMap P (rightInverseAction φ) f).app x s)
        rw [← classOf_evaluate (reindex P f) (rightInverseAction φ) x p s,
          act_classOf, reindexMap_classOf, reindexMap_classOf, act_classOf]) }

@[simp] theorem reindexComparison_hom (φ : G ⟶ H) (P : Torsor G X)
    {Y : Sheaf J (Type (max u v))} (f : Y ⟶ X) :
    (reindexComparison φ P f).iso.hom = reindexMap P (rightInverseAction φ) f := rfl

set_option backward.isDefEq.respectTransparency false in
theorem reindexComparison_id (φ : G ⟶ H) (P : Torsor G X) :
    reindexComparison φ P (𝟙 X) = Arrow.ident (extension φ P) := by
  apply SheafTorsor.Arrow.ext
  exact reindexMap_id P (rightInverseAction φ)

set_option backward.isDefEq.respectTransparency false in
theorem reindexComparison_comp (φ : G ⟶ H) (P : Torsor G X)
    {Y Z : Sheaf J (Type (max u v))} (f : Y ⟶ X) (g : Z ⟶ Y) :
    reindexComparison φ P (g ≫ f) =
      (reindexComparison φ (reindex P f) g).comp ((reindexComparison φ P f).reindex g) := by
  apply SheafTorsor.Arrow.ext
  exact reindexMap_comp P (rightInverseAction φ) f g

set_option backward.isDefEq.respectTransparency false in
theorem reindexComparison_natural (φ : G ⟶ H) {P Q : Torsor G X} (h : P ⟶ Q)
    {Y : Sheaf J (Type (max u v))} (f : Y ⟶ X) :
    (extensionMap φ (h.reindex f)).comp (reindexComparison φ Q f) =
      (reindexComparison φ P f).comp ((extensionMap φ h).reindex f) := by
  apply SheafTorsor.Arrow.ext
  change (extensionMap φ (h.reindex f)).iso.hom ≫ (reindexComparison φ Q f).iso.hom =
    (reindexComparison φ P f).iso.hom ≫ (SplitSheaf.restriction f).map (extensionMap φ h).iso.hom
  rw [extensionMap_underlying, extensionMap_underlying, reindexComparison_hom, reindexComparison_hom]
  exact reindexMap_map P (rightInverseAction φ) f (SemilinearMap.ofArrow h) (ActionMap.ident _)

set_option backward.isDefEq.respectTransparency false in
/-- An extension arrow is determined by its values on quotient representatives. -/
theorem arrow_ext_class {T : Torsor H X} (f g : Arrow (extension φ P) T)
    (h : ∀ (x : X.obj.Elements) (p : P.family.family.obj x) (k : H.obj.obj x.obj),
      f.iso.hom.app x (classOf P (rightInverseAction φ) x p k) =
        g.iso.hom.app x (classOf P (rightInverseAction φ) x p k)) : f = g := by
  apply SheafTorsor.Arrow.ext
  exact SheafAssociatedBundle.hom_ext (P := P) (a := rightInverseAction φ)
    (Y := T.family) _ _ h

set_option backward.isDefEq.respectTransparency false in
theorem identityComparison_classOf (P : Torsor G X) (x : X.obj.Elements)
    (p : P.family.family.obj x) (g : G.obj.obj x.obj) :
    (identityComparison P).iso.hom.app x
      (classOf P (rightInverseAction (𝟙 G)) x p g) = P.act x g p :=
  lift_classOf (SemilinearMap.ident P) x p g

set_option backward.isDefEq.respectTransparency false in
theorem identityComparison_natural {P Q : Torsor G X} (f : P ⟶ Q) :
    (extensionMap (𝟙 G) f).comp (identityComparison Q) =
      (identityComparison P).comp f := by
  apply arrow_ext_class
  intro x p g
  change (identityComparison Q).iso.hom.app x
      ((extensionMap (𝟙 G) f).iso.hom.app x (classOf P (rightInverseAction (𝟙 G)) x p g)) =
    f.iso.hom.app x ((identityComparison P).iso.hom.app x
      (classOf P (rightInverseAction (𝟙 G)) x p g))
  rw [extensionMap_classOf, identityComparison_classOf, identityComparison_classOf,
    f.equivariant]

set_option backward.isDefEq.respectTransparency false in
/-- Semilinear maps out of an extension are determined on its canonical image. -/
theorem semilinear_ext_unit {ψ : H ⟶ K} {T : Torsor K X}
    (f g : SemilinearMap ψ (extension φ P) T)
    (h : (unit φ P).comp f = (unit φ P).comp g) : f = g := by
  apply SemilinearMap.ext
  apply SheafAssociatedBundle.hom_ext (P := P) (a := rightInverseAction φ) (Y := T.family)
  intro x p k
  have hh := congrArg (fun t => t.hom.app x p) h
  change f.hom.app x (classOf P (rightInverseAction φ) x p (1 : H.obj.obj x.obj)) =
    g.hom.app x (classOf P (rightInverseAction φ) x p (1 : H.obj.obj x.obj)) at hh
  have hc : classOf P (rightInverseAction φ) x p k =
      (extension φ P).act x k (classOf P (rightInverseAction φ) x p (1 : H.obj.obj x.obj)) := by
    rw [act_classOf, mul_one]
  rw [hc]
  exact (f.equivariant x k _).trans
    ((congrArg (T.act x (ψ.hom.app x.obj k)) hh).trans
      (g.equivariant x k _).symm)

set_option backward.isDefEq.respectTransparency false in
theorem compositionComparison_unit (φ : G ⟶ H) (ψ : H ⟶ K) (P : Torsor G X) :
    ((unit φ P).comp (unit ψ (extension φ P))).comp
        (SemilinearMap.ofArrow (compositionComparison φ ψ P)) = unit (φ ≫ ψ) P := by
  apply SemilinearMap.ext
  ext x p
  change (compositionComparison φ ψ P).iso.hom.app x
      (classOf (extension φ P) (rightInverseAction ψ) x
        (classOf P (rightInverseAction φ) x p (1 : H.obj.obj x.obj)) (1 : K.obj.obj x.obj)) = _
  rw [compositionComparison_classOf, (ψ.hom.app x.obj).hom.map_one, one_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem identityComparison_unit (P : Torsor G X) :
    (unit (𝟙 G) P).comp (SemilinearMap.ofArrow (identityComparison P)) =
      SemilinearMap.ident P := by
  apply SemilinearMap.ext
  ext x p
  change (identityComparison P).iso.hom.app x
    (classOf P (rightInverseAction (𝟙 G)) x p (1 : G.obj.obj x.obj)) = _
  rw [identityComparison_classOf, P.one_act]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem arrow_ext_unit {T : Torsor H X} (f g : Arrow (extension φ P) T)
    (h : (unit φ P).comp (SemilinearMap.ofArrow f) =
      (unit φ P).comp (SemilinearMap.ofArrow g)) : f = g := by
  apply SheafTorsor.Arrow.ext
  exact congrArg SemilinearMap.hom
    (semilinear_ext_unit (SemilinearMap.ofArrow f) (SemilinearMap.ofArrow g) h)

set_option backward.isDefEq.respectTransparency false in
theorem extensionMap_unit (φ : G ⟶ H) {P Q : Torsor G X} (f : P ⟶ Q) :
    (unit φ P).comp (SemilinearMap.ofArrow (extensionMap φ f)) =
      (SemilinearMap.ofArrow f).comp (unit φ Q) := by
  apply SemilinearMap.ext
  ext x p
  exact extensionMap_classOf φ f x p (1 : H.obj.obj x.obj)

set_option backward.isDefEq.respectTransparency false in
/-- The two routes through three successive group changes agree as actual arrows. -/
theorem compositionComparison_assoc {L : Sheaf J GrpCat.{max u v}}
    (φ : G ⟶ H) (ψ : H ⟶ K) (χ : K ⟶ L) (P : Torsor G X) :
    (extensionMap χ (compositionComparison φ ψ P)).comp
        (compositionComparison (φ ≫ ψ) χ P) =
      (compositionComparison ψ χ (extension φ P)).comp
        (compositionComparison φ (ψ ≫ χ) P) := by
  apply arrow_ext_unit
  apply semilinear_ext_unit
  apply semilinear_ext_unit
  apply SemilinearMap.ext
  ext x p
  change (compositionComparison (φ ≫ ψ) χ P).iso.hom.app x
      ((extensionMap χ (compositionComparison φ ψ P)).iso.hom.app x
        (classOf (extension ψ (extension φ P)) (rightInverseAction χ) x
          (classOf (extension φ P) (rightInverseAction ψ) x
            (classOf P (rightInverseAction φ) x p (1 : H.obj.obj x.obj))
            (1 : K.obj.obj x.obj)) (1 : L.obj.obj x.obj))) =
    (compositionComparison φ (ψ ≫ χ) P).iso.hom.app x
      ((compositionComparison ψ χ (extension φ P)).iso.hom.app x
        (classOf (extension ψ (extension φ P)) (rightInverseAction χ) x
          (classOf (extension φ P) (rightInverseAction ψ) x
            (classOf P (rightInverseAction φ) x p (1 : H.obj.obj x.obj))
            (1 : K.obj.obj x.obj)) (1 : L.obj.obj x.obj)))
  rw [extensionMap_classOf, compositionComparison_classOf, compositionComparison_classOf,
    compositionComparison_classOf, compositionComparison_classOf]
  simp only [(ψ.hom.app x.obj).hom.map_one, (χ.hom.app x.obj).hom.map_one,
    ((ψ ≫ χ).hom.app x.obj).hom.map_one, one_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem compositionComparison_left_identity (φ : G ⟶ H) (P : Torsor G X) :
    compositionComparison (𝟙 G) φ P = extensionMap φ (identityComparison P) := by
  apply arrow_ext_unit
  apply semilinear_ext_unit
  apply SemilinearMap.ext
  ext x p
  change (compositionComparison (𝟙 G) φ P).iso.hom.app x
      (classOf (extension (𝟙 G) P) (rightInverseAction φ) x
        (classOf P (rightInverseAction (𝟙 G)) x p (1 : G.obj.obj x.obj)) (1 : H.obj.obj x.obj)) =
    (extensionMap φ (identityComparison P)).iso.hom.app x
      (classOf (extension (𝟙 G) P) (rightInverseAction φ) x
        (classOf P (rightInverseAction (𝟙 G)) x p (1 : G.obj.obj x.obj)) (1 : H.obj.obj x.obj))
  rw [compositionComparison_classOf, extensionMap_classOf, identityComparison_classOf,
    P.one_act, (φ.hom.app x.obj).hom.map_one, one_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem compositionComparison_right_identity (φ : G ⟶ H) (P : Torsor G X) :
    compositionComparison φ (𝟙 H) P = identityComparison (extension φ P) := by
  apply arrow_ext_unit
  apply semilinear_ext_unit
  apply SemilinearMap.ext
  ext x p
  change (compositionComparison φ (𝟙 H) P).iso.hom.app x
      (classOf (extension φ P) (rightInverseAction (𝟙 H)) x
        (classOf P (rightInverseAction φ) x p (1 : H.obj.obj x.obj)) (1 : H.obj.obj x.obj)) =
    (identityComparison (extension φ P)).iso.hom.app x
      (classOf (extension φ P) (rightInverseAction (𝟙 H)) x
        (classOf P (rightInverseAction φ) x p (1 : H.obj.obj x.obj)) (1 : H.obj.obj x.obj))
  rw [compositionComparison_classOf, identityComparison_classOf, (extension φ P).one_act]
  simp only [map_one, one_mul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Composition of group changes is natural on every torsor arrow. -/
theorem compositionComparison_natural (φ : G ⟶ H) (ψ : H ⟶ K)
    {P Q : Torsor G X} (f : P ⟶ Q) :
    (extensionMap ψ (extensionMap φ f)).comp (compositionComparison φ ψ Q) =
      (compositionComparison φ ψ P).comp (extensionMap (φ ≫ ψ) f) := by
  apply arrow_ext_unit
  apply semilinear_ext_unit
  apply SemilinearMap.ext
  ext x p
  change (compositionComparison φ ψ Q).iso.hom.app x
      ((extensionMap ψ (extensionMap φ f)).iso.hom.app x
        (classOf (extension φ P) (rightInverseAction ψ) x
          (classOf P (rightInverseAction φ) x p (1 : H.obj.obj x.obj)) (1 : K.obj.obj x.obj))) =
    (extensionMap (φ ≫ ψ) f).iso.hom.app x
      ((compositionComparison φ ψ P).iso.hom.app x
        (classOf (extension φ P) (rightInverseAction ψ) x
          (classOf P (rightInverseAction φ) x p (1 : H.obj.obj x.obj)) (1 : K.obj.obj x.obj)))
  rw [extensionMap_classOf, extensionMap_classOf, compositionComparison_classOf,
    compositionComparison_classOf, extensionMap_classOf]


set_option backward.isDefEq.respectTransparency false in
theorem reindexComparison_inv (φ : G ⟶ H) (P : Torsor G X)
    {Y : Sheaf J (Type (max u v))} (f : Y ⟶ X) :
    (reindexComparison φ P f).iso.inv = (reindexIso P (rightInverseAction φ) f).hom := by
  apply (cancel_mono (reindexComparison φ P f).iso.hom).mp
  rw [(reindexComparison φ P f).iso.inv_hom_id]
  exact (reindexIso P (rightInverseAction φ) f).hom_inv_id.symm

section Family
variable {I : Type (max u v)} {B : I → Sheaf J (Type (max u v))}
    (φ : G ⟶ H) (f : ∀ i, B i ⟶ X)

set_option backward.isDefEq.respectTransparency false in
/-- Extend the given local torsors and their overlap maps before gluing. -/
def extensionData (d : (SheafTorsor.Stack.pseudofunctor G).DescentData f) :
    (SheafTorsor.Stack.pseudofunctor H).DescentData f where
  obj i := extension φ (d.obj i)
  hom W q i j l r hl hr :=
    (reindexComparison φ (d.obj i) l).inverse ≫ extensionMap φ (d.hom q l r hl hr) ≫
      reindexComparison φ (d.obj j) r
  pullHom_hom W' W k q q' hq i j l r hl hr kl kr hkl hkr := by
    subst kl; subst kr; subst q'
    apply SheafTorsor.Arrow.ext
    change (SplitSheaf.restriction k).map
      ((reindexComparison φ (d.obj i) l).iso.inv ≫
        (extensionMap φ (d.hom q l r hl hr)).iso.hom ≫
          (reindexComparison φ (d.obj j) r).iso.hom) =
      (reindexComparison φ (d.obj i) (k ≫ l)).iso.inv ≫
        (extensionMap φ (d.hom (k ≫ q) (k ≫ l) (k ≫ r) _ _)).iso.hom ≫
          (reindexComparison φ (d.obj j) (k ≫ r)).iso.hom
    rw [reindexComparison_inv, reindexComparison_inv, reindexComparison_hom,
      reindexComparison_hom, extensionMap_underlying, extensionMap_underlying]
    exact (associatedData (rightInverseAction φ) f d).pullHom_hom
      k q (k ≫ q) rfl l r hl hr (k ≫ l) (k ≫ r) rfl rfl
  hom_self W q i l hl := by
    apply SheafTorsor.Arrow.ext
    change (reindexComparison φ (d.obj i) l).iso.inv ≫
      (extensionMap φ (d.hom q l l hl hl)).iso.hom ≫
        (reindexComparison φ (d.obj i) l).iso.hom = 𝟙 _
    rw [reindexComparison_inv, reindexComparison_hom, extensionMap_underlying]
    exact (associatedData (rightInverseAction φ) f d).hom_self q l hl
  hom_comp W q i j k l r t hl hr ht := by
    apply SheafTorsor.Arrow.ext
    change ((reindexComparison φ (d.obj i) l).iso.inv ≫
      (extensionMap φ (d.hom q l r hl hr)).iso.hom ≫
        (reindexComparison φ (d.obj j) r).iso.hom) ≫
      ((reindexComparison φ (d.obj j) r).iso.inv ≫
        (extensionMap φ (d.hom q r t hr ht)).iso.hom ≫
          (reindexComparison φ (d.obj k) t).iso.hom) =
      (reindexComparison φ (d.obj i) l).iso.inv ≫
        (extensionMap φ (d.hom q l t hl ht)).iso.hom ≫
          (reindexComparison φ (d.obj k) t).iso.hom
    rw [reindexComparison_inv, reindexComparison_inv, reindexComparison_hom,
      reindexComparison_hom, extensionMap_underlying, extensionMap_underlying,
      extensionMap_underlying]
    exact (associatedData (rightInverseAction φ) f d).hom_comp q l r t hl hr ht

set_option backward.isDefEq.respectTransparency false in
theorem extensionData_hom (d : (SheafTorsor.Stack.pseudofunctor G).DescentData f)
    {W : Sheaf J (Type (max u v))} (q : W ⟶ X) {i j : I}
    (l : W ⟶ B i) (r : W ⟶ B j) (hl : l ≫ f i = q) (hr : r ≫ f j = q) :
    ((extensionData φ f d).hom q l r hl hr).iso.hom =
      (associatedData (rightInverseAction φ) f d).hom q l r hl hr := by
  change (reindexComparison φ (d.obj i) l).iso.inv ≫
    (extensionMap φ (d.hom q l r hl hr)).iso.hom ≫
      (reindexComparison φ (d.obj j) r).iso.hom = _
  rw [reindexComparison_inv, reindexComparison_hom, extensionMap_underlying]
  rfl

set_option backward.isDefEq.respectTransparency false in
def extensionDataMap {d e : (SheafTorsor.Stack.pseudofunctor G).DescentData f}
    (h : d ⟶ e) : extensionData φ f d ⟶ extensionData φ f e where
  hom i := extensionMap φ (h.hom i)
  comm W q i j l r hl hr := by
    apply SheafTorsor.Arrow.ext
    change (SplitSheaf.restriction l).map (extensionMap φ (h.hom i)).iso.hom ≫
      ((extensionData φ f e).hom q l r hl hr).iso.hom =
      ((extensionData φ f d).hom q l r hl hr).iso.hom ≫
        (SplitSheaf.restriction r).map (extensionMap φ (h.hom j)).iso.hom
    rw [extensionData_hom, extensionData_hom, extensionMap_underlying, extensionMap_underlying]
    exact (associatedDataMap (rightInverseAction φ) f h).comm q l r hl hr

def extensionDataFunctor : (SheafTorsor.Stack.pseudofunctor G).DescentData f ⥤
    (SheafTorsor.Stack.pseudofunctor H).DescentData f where
  obj := extensionData φ f
  map := extensionDataMap φ f
  map_id d := by
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    exact (extensionFunctor φ (B i)).map_id (d.obj i)
  map_comp h k := by
    apply Pseudofunctor.DescentData.hom_ext
    intro i
    exact (extensionFunctor φ (B i)).map_comp (h.hom i) (k.hom i)

private theorem eqToHom_underlying {P Q : Torsor H X} (h : P = Q) :
    (eqToHom h).iso.hom = (eqToHom (congrArg (fun T : Torsor H X => T.family) h) : P.family ⟶ Q.family) := by
  cases h
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem canonical_underlying (T : Torsor H X)
    {W : Sheaf J (Type (max u v))} (q : W ⟶ X) {i j : I}
    (l : W ⟶ B i) (r : W ⟶ B j) (hl : l ≫ f i = q) (hr : r ≫ f j = q) :
    ((((SheafTorsor.Stack.pseudofunctor H).toDescentData f).obj T).hom q l r hl hr).iso.hom =
      (((SplitSheaf.pseudofunctor (J := J)).toDescentData f).obj T.family).hom q l r hl hr := by
  simp [Pseudofunctor.toDescentData, Pseudofunctor.DescentData.ofObj,
    Pseudofunctor.mapComp', SheafTorsor.Stack.pseudofunctor, SplitSheaf.pseudofunctor,
    Functor.toPseudofunctor', pseudofunctorOfIsLocallyDiscrete]
  change (eqToHom (congrArg (SheafTorsor.reindex T) (hl.trans hr.symm))).iso.hom =
    (eqToHom (congrArg (SplitSheaf.tySub T.family) (hl.trans hr.symm)) :
      SplitSheaf.tySub T.family (l ≫ f i) ⟶ SplitSheaf.tySub T.family (r ≫ f j))
  exact eqToHom_underlying _

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
def extensionDataOfGlobal (P : Torsor G X) :
    ((SheafTorsor.Stack.pseudofunctor H).toDescentData f).obj (extension φ P) ≅
      extensionData φ f (((SheafTorsor.Stack.pseudofunctor G).toDescentData f).obj P) :=
  Pseudofunctor.DescentData.isoMk (fun i => (reindexComparison φ P (f i)).toIso.symm) (by
    intro W q i j l r hl hr
    apply SheafTorsor.Arrow.ext
    change (SplitSheaf.restriction l).map (reindexComparison φ P (f i)).iso.inv ≫
      ((extensionData φ f (((SheafTorsor.Stack.pseudofunctor G).toDescentData f).obj P)).hom q l r hl hr).iso.hom =
      ((((SheafTorsor.Stack.pseudofunctor H).toDescentData f).obj (extension φ P)).hom q l r hl hr).iso.hom ≫
        (SplitSheaf.restriction r).map (reindexComparison φ P (f j)).iso.inv
    rw [reindexComparison_inv, reindexComparison_inv, extensionData_hom, canonical_underlying]
    exact (associatedDataOfGlobal (rightInverseAction φ) f P).hom.comm q l r hl hr)

variable (hf : SheafFamilyCover.JointlyLocallySurjective f)

set_option backward.isDefEq.respectTransparency false in
/-- The extension of the recovered torsor has the independently extended local data. -/
def extensionDescentComparison :
    (SheafFamilyDescent.torsorEquivalence G f hf).inverse ⋙ extensionFunctor φ X ⋙
      (SheafTorsor.Stack.pseudofunctor H).toDescentData f ≅ extensionDataFunctor φ f :=
  NatIso.ofComponents (fun d =>
    extensionDataOfGlobal φ f ((SheafFamilyDescent.torsorEquivalence G f hf).inverse.obj d) ≪≫
      (extensionDataFunctor φ f).mapIso ((SheafFamilyDescent.torsorEquivalence G f hf).counitIso.app d))
    (by
      intro d e h
      apply Pseudofunctor.DescentData.hom_ext
      intro i
      apply SheafTorsor.Arrow.ext
      change (SplitSheaf.restriction (f i)).map
          (extensionMap φ ((SheafFamilyDescent.torsorEquivalence G f hf).inverse.map h)).iso.hom ≫
        ((reindexComparison φ ((SheafFamilyDescent.torsorEquivalence G f hf).inverse.obj e) (f i)).iso.inv ≫
          (extensionMap φ (((SheafFamilyDescent.torsorEquivalence G f hf).counitIso.app e).hom.hom i)).iso.hom) =
        ((reindexComparison φ ((SheafFamilyDescent.torsorEquivalence G f hf).inverse.obj d) (f i)).iso.inv ≫
          (extensionMap φ (((SheafFamilyDescent.torsorEquivalence G f hf).counitIso.app d).hom.hom i)).iso.hom) ≫
            (extensionMap φ (h.hom i)).iso.hom
      rw [reindexComparison_inv, reindexComparison_inv, extensionMap_underlying,
        extensionMap_underlying, extensionMap_underlying, extensionMap_underlying]
      exact descentLocalComparison_natural (rightInverseAction φ) f hf h i)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 400000 in
/-- Effective gluing commutes with extension on objects and all compatible local arrows. -/
def extensionDataRecovery :
    extensionDataFunctor φ f ⋙ (SheafFamilyDescent.torsorEquivalence H f hf).inverse ≅
      (SheafFamilyDescent.torsorEquivalence G f hf).inverse ⋙ extensionFunctor φ X :=
  Functor.isoWhiskerRight (extensionDescentComparison φ f hf).symm _ ≪≫
    Functor.isoWhiskerLeft
      ((SheafFamilyDescent.torsorEquivalence G f hf).inverse ⋙ extensionFunctor φ X)
      (SheafFamilyDescent.torsorEquivalence H f hf).unitIso.symm


end Family

set_option backward.isDefEq.respectTransparency false in
/-- The extension functor commutes with arbitrary base restriction. -/
def extensionFunctorReindex (φ : G ⟶ H) {Y : Sheaf J (Type (max u v))}
    (f : Y ⟶ X) :
    SheafTorsor.restriction f ⋙ extensionFunctor φ Y ≅
      extensionFunctor φ X ⋙ SheafTorsor.restriction f :=
  NatIso.ofComponents (fun P => (reindexComparison φ P f).toIso) (by
    intro P Q h
    exact reindexComparison_natural φ h f)

section FamilyRefinement
variable {I L : Type (max u v)} {B : I → Sheaf J (Type (max u v))}
    {Y : Sheaf J (Type (max u v))} {D : L → Sheaf J (Type (max u v))}
    {f : ∀ i, B i ⟶ X} {g : ∀ j, D j ⟶ Y}
    (φ : G ⟶ H) (hf : SheafFamilyCover.JointlyLocallySurjective f)
    (hg : SheafFamilyCover.JointlyLocallySurjective g)
    (r : L → I) (p : Y ⟶ X) (b : ∀ j, D j ⟶ B (r j))
    (w : ∀ j, b j ≫ f (r j) = g j ≫ p)

set_option backward.isDefEq.respectTransparency false in
/-- Gluing independently extended local torsors commutes with covering refinement
and base change, naturally on all compatible local arrows. -/
def extensionDataRefinement :
    Pseudofunctor.DescentData.pullFunctor (SheafTorsor.Stack.pseudofunctor G) w ⋙
      extensionDataFunctor φ g ⋙ (SheafFamilyDescent.torsorEquivalence H g hg).inverse ≅
    extensionDataFunctor φ f ⋙ (SheafFamilyDescent.torsorEquivalence H f hf).inverse ⋙
      SheafTorsor.restriction p := by
  have := ((SheafTorsor.Stack.pseudofunctor G).isStackFor_ofArrows_iff _).mp
    (SheafFamilyDescent.torsor_isStackFor G f hf)
  have := ((SheafTorsor.Stack.pseudofunctor G).isStackFor_ofArrows_iff _).mp
    (SheafFamilyDescent.torsor_isStackFor G g hg)
  exact Functor.isoWhiskerLeft _ (extensionDataRecovery φ g hg) ≪≫
    Functor.isoWhiskerRight
      (SheafFamilyDescent.recoveryNaturality (SheafTorsor.Stack.pseudofunctor G) r p b w)
      (extensionFunctor φ Y) ≪≫
    Functor.isoWhiskerLeft (SheafFamilyDescent.torsorEquivalence G f hf).inverse
      (extensionFunctorReindex φ p) ≪≫
    Functor.isoWhiskerRight (extensionDataRecovery φ f hf).symm (SheafTorsor.restriction p)

end FamilyRefinement

end Descent

namespace Site
universe s
variable {C D : Type s} [Category.{s} C] [Category.{s} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (F : C ⥤ D)
  [F.IsContinuous J K] [F.IsCocontinuous J K]
  {G H : Sheaf K GrpCat.{s}} {X : Sheaf K (Type s)}
  (φ : G ⟶ H) (P : SheafTorsor.Torsor G X)

set_option backward.isDefEq.respectTransparency false in
/-- Extension commutes with continuous, cocontinuous site restriction. -/
def comparison : SheafTorsor.Arrow
    (extension ((SheafSiteComparison.groupRestriction J K F).map φ)
      (SheafSiteComparison.torsor J K F P))
    (SheafSiteComparison.torsor J K F (extension φ P)) :=
  SheafTorsor.EquivariantMap.toArrow {
    hom := SheafAssociatedBundle.Site.comparison J K F P (rightInverseAction φ)
    equivariant := equivariant_of_cover
      (A := (SheafSiteComparison.torsor J K F P).family)
      (R := extension ((SheafSiteComparison.groupRestriction J K F).map φ)
        (SheafSiteComparison.torsor J K F P))
      (S := SheafSiteComparison.torsor J K F (extension φ P))
      (σ := 𝟙 (SheafSiteComparison.group J K F H))
      (SheafAssociatedBundle.Site.comparison J K F P (rightInverseAction φ)) (by
        intro x p h t
        change (SheafAssociatedBundle.Site.comparison J K F P (rightInverseAction φ)).app x
            ((extension ((SheafSiteComparison.groupRestriction J K F).map φ)
              (SheafSiteComparison.torsor J K F P)).act x h t) =
          (extension φ P).act ((SheafSiteComparison.elements K F X).obj x) h
            ((SheafAssociatedBundle.Site.comparison J K F P (rightInverseAction φ)).app x t)
        rw [← SheafAssociatedBundle.classOf_evaluate (SheafSiteComparison.torsor J K F P)
          (rightInverseAction ((SheafSiteComparison.groupRestriction J K F).map φ)) x p t,
          act_classOf]
        exact (SheafAssociatedBundle.Site.comparison_classOf J K F P (rightInverseAction φ)
          x p _).trans
            ((act_classOf φ P ((SheafSiteComparison.elements K F X).obj x) p h _).symm.trans
              (congrArg ((extension φ P).act ((SheafSiteComparison.elements K F X).obj x) h)
                (SheafAssociatedBundle.Site.comparison_classOf J K F P (rightInverseAction φ)
                  x p _).symm))) }

set_option backward.isDefEq.respectTransparency false in
theorem comparison_classOf (x : (SheafSiteComparison.sheaf J K F X).obj.Elements)
    (p : (SheafSiteComparison.torsor J K F P).family.family.obj x)
    (h : (SheafSiteComparison.group J K F H).obj.obj x.obj) :
    (comparison J K F φ P).iso.hom.app x
      (SheafAssociatedBundle.classOf (SheafSiteComparison.torsor J K F P)
        (rightInverseAction ((SheafSiteComparison.groupRestriction J K F).map φ)) x p h) =
      SheafAssociatedBundle.classOf P (rightInverseAction φ)
        ((SheafSiteComparison.elements K F X).obj x) p h :=
  SheafAssociatedBundle.Site.comparison_classOf J K F P (rightInverseAction φ) x p h

set_option backward.isDefEq.respectTransparency false in
/-- The site comparison retains every extended torsor arrow. -/
theorem comparison_natural {Q : SheafTorsor.Torsor G X} (h : P ⟶ Q) :
    (extensionMap ((SheafSiteComparison.groupRestriction J K F).map φ)
      ((SheafSiteComparison.torsorFunctor J K F).map h)).comp (comparison J K F φ Q) =
    (comparison J K F φ P).comp
      ((SheafSiteComparison.torsorFunctor J K F).map (extensionMap φ h)) := by
  apply arrow_ext_class
  intro x p k
  change (comparison J K F φ Q).iso.hom.app x
      ((extensionMap ((SheafSiteComparison.groupRestriction J K F).map φ)
        ((SheafSiteComparison.torsorFunctor J K F).map h)).iso.hom.app x
          (SheafAssociatedBundle.classOf (SheafSiteComparison.torsor J K F P)
            (rightInverseAction ((SheafSiteComparison.groupRestriction J K F).map φ)) x p k)) =
    (extensionMap φ h).iso.hom.app ((SheafSiteComparison.elements K F X).obj x)
      ((comparison J K F φ P).iso.hom.app x
        (SheafAssociatedBundle.classOf (SheafSiteComparison.torsor J K F P)
          (rightInverseAction ((SheafSiteComparison.groupRestriction J K F).map φ)) x p k))
  exact (congrArg ((comparison J K F φ Q).iso.hom.app x)
    (extensionMap_classOf ((SheafSiteComparison.groupRestriction J K F).map φ)
      ((SheafSiteComparison.torsorFunctor J K F).map h) x p k)).trans
    ((comparison_classOf J K F φ Q x _ k).trans
      ((extensionMap_classOf φ h ((SheafSiteComparison.elements K F X).obj x) p k).symm.trans
        (congrArg ((extensionMap φ h).iso.hom.app ((SheafSiteComparison.elements K F X).obj x))
          (comparison_classOf J K F φ P x p k).symm)))

set_option backward.isDefEq.respectTransparency false in
theorem comparison_unit (x : (SheafSiteComparison.sheaf J K F X).obj.Elements)
    (p : (SheafSiteComparison.torsor J K F P).family.family.obj x) :
    (comparison J K F φ P).iso.hom.app x
      ((unit ((SheafSiteComparison.groupRestriction J K F).map φ)
        (SheafSiteComparison.torsor J K F P)).hom.app x p) =
      (unit φ P).hom.app ((SheafSiteComparison.elements K F X).obj x) p :=
  comparison_classOf J K F φ P x p 1

end Site

end SquareKit.SheafStructureGroupExtension
