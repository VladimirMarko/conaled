import SquareKit.Internal.Cubical.CartesianEquivalenceExtension
import SquareKit.Internal.RepresentableClassification

/-! Dependent native functions change domains through actual family maps. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.PiDomain
open CategoryTheory
universe u
variable {Γ : Context.{u}} {A B : Family Γ}

def baseMap (f : A ⟶ B) : total A ⟶ total B :=
  pair (projection A) (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))

/-- Precompose every generalized argument; dependent outputs remain in their original fibers. -/
def precompose (f : A ⟶ B) (C : Family (total B)) :
    pi B C ⟶ pi A (reindex C (baseMap f)) where
  app x := TypeCat.ofHom (fun p => {
    val := fun g a => p.val g (f.app _ a)
    naturality := fun {y z} g h a => by
      have e := f.naturality_apply h a
      have hm := RepresentableClassification.family_map_heq C
        ((baseMap f).mapElements.map (extendHom A h a))
        (extendHom B h (f.app y a))
        (congrArg (extendObj B z) e) HEq.rfl (p.val g (f.app y a))
      exact eq_of_heq (hm.trans ((heq_of_eq (p.naturality g h (f.app y a))).trans
        (congr_arg_heq (fun b => p.val (g ≫ h) b) e.symm))) })
  naturality x y g := by
    apply ConcreteCategory.hom_ext
    intro p
    apply PiElement.ext
    intro z h a
    rfl


theorem baseMap_inv_hom (e : A ≅ B) : baseMap e.inv ≫ baseMap e.hom = 𝟙 (total B) := by
  apply NatTrans.ext
  funext x
  apply ConcreteCategory.hom_ext
  intro z
  change (⟨z.1, e.hom.app _ (e.inv.app _ z.2)⟩ : Σ a, B.obj (Γ.elementsMk x a)) = z
  exact congrArg (fun b => (⟨z.1, b⟩ : Σ a, B.obj (Γ.elementsMk x a)))
    (e.inv_hom_id_app_apply (Γ.elementsMk x z.1) z.2)

private theorem eqToIso_hom_value {Δ : Context.{u}} {C D : Family Δ} (h : C = D)
    (x : Δ.Elements) (c : C.obj x) : HEq ((eqToIso h).hom.app x c) c := by
  cases h
  rfl

def codomainIso (e : A ≅ B) (C : Family (total B)) :
    reindex (reindex C (baseMap e.hom)) (baseMap e.inv) ≅ C :=
  eqToIso (congrArg (reindex C) (baseMap_inv_hom e))

/-- Change the native dependent function domain through a family isomorphism. -/
def congr (e : A ≅ B) (C : Family (total B)) :
    pi A (reindex C (baseMap e.hom)) ≅ pi B C where
  hom := precompose e.inv (reindex C (baseMap e.hom)) ≫
    (EquivalenceFamilies.piSecondIso B (codomainIso e C)).hom
  inv := precompose e.hom C
  hom_inv_id := by
    ext x p
    apply PiElement.ext
    intro y g a
    apply eq_of_heq
    exact (eqToIso_hom_value (congrArg (reindex C) (baseMap_inv_hom e))
      (extendObj B y (e.hom.app y a)) (p.val g (e.inv.app y (e.hom.app y a)))).trans
      (congr_arg_heq (fun a => p.val g a) (e.hom_inv_id_app_apply y a))
  inv_hom_id := by
    ext x p
    apply PiElement.ext
    intro y g b
    apply eq_of_heq
    exact (eqToIso_hom_value (congrArg (reindex C) (baseMap_inv_hom e))
      (extendObj B y b) (p.val g (e.hom.app y (e.inv.app y b)))).trans
      (congr_arg_heq (fun b => p.val g b) (e.inv_hom_id_app_apply y b))

/-- The inverse substitutes the forward domain map at every generalized argument. -/
@[simp] theorem congr_inv_value (e : A ≅ B) (C : Family (total B))
    {x y : Γ.Elements} (p : PiElement B C x) (g : x ⟶ y) (a : A.obj y) :
    ((congr e C).inv.app x p).val g a = p.val g (e.hom.app y a) := rfl

/-- The forward map uses the supplied inverse, retaining the dependent output value. -/
theorem congr_hom_value (e : A ≅ B) (C : Family (total B))
    {x y : Γ.Elements} (p : PiElement A (reindex C (baseMap e.hom)) x)
    (g : x ⟶ y) (b : B.obj y) :
    HEq (((congr e C).hom.app x p).val g b) (p.val g (e.inv.app y b)) :=
  eqToIso_hom_value (congrArg (reindex C) (baseMap_inv_hom e))
    (extendObj B y b) (p.val g (e.inv.app y b))

/-- Change the first component while preserving its dependent field. -/
def sigmaMap (f : A ⟶ B) (C : Family (total B)) :
    sigma A (reindex C (baseMap f)) ⟶ sigma B C where
  app x := TypeCat.ofHom (fun z => ⟨f.app x z.1, z.2⟩)
  naturality x y g := by
    apply ConcreteCategory.hom_ext
    intro z
    exact (sigmaMap_ofHom B C g (a := f.app x z.1)
      (a' := f.app y (A.map g z.1)) (f.naturality_apply g z.1).symm z.2).symm

private theorem eqToIso_inv_value {Δ : Context.{u}} {C D : Family Δ} (h : C = D)
    (x : Δ.Elements) (d : D.obj x) : HEq ((eqToIso h).inv.app x d) d := by
  cases h
  rfl

/-- Change a dependent sum domain using the supplied isomorphism. -/
def sigmaCongr (e : A ≅ B) (C : Family (total B)) :
    sigma A (reindex C (baseMap e.hom)) ≅ sigma B C where
  hom := sigmaMap e.hom C
  inv := (Homotopy.sigmaSecondIso B (codomainIso e C)).inv ≫
    sigmaMap e.inv (reindex C (baseMap e.hom))
  hom_inv_id := by
    ext x z
    apply Sigma.ext
    · exact e.hom_inv_id_app_apply x z.1
    · exact eqToIso_inv_value (congrArg (reindex C) (baseMap_inv_hom e))
        (extendObj B x (e.hom.app x z.1)) z.2
  inv_hom_id := by
    ext x z
    apply Sigma.ext
    · exact e.inv_hom_id_app_apply x z.1
    · exact eqToIso_inv_value (congrArg (reindex C) (baseMap_inv_hom e))
        (extendObj B x z.1) z.2

end SquareKit.Cubical.Cartesian.PiDomain
