import SquareKit.SheafTorsor

/-! Fiber displacements and equivariant maps along arbitrary group-sheaf
homomorphisms. Such maps need not be invertible. -/
noncomputable section
namespace SquareKit.SheafTorsor
open CategoryTheory Opposite
universe u v w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {G H K L : Sheaf J GrpCat.{w}} {X Y Z : Sheaf J (Type w)}

/-- The unique group section carrying `p` to `q` in one torsor fiber. -/
def fiberDifference (P : Torsor G X) (x : X.obj.Elements)
    (p q : P.family.family.obj x) : G.obj.obj x.obj :=
  (fiberEquiv P x p).symm q

theorem fiberDifference_act (P : Torsor G X) (x : X.obj.Elements)
    (p q : P.family.family.obj x) : P.act x (fiberDifference P x p q) p = q :=
  (fiberEquiv P x p).apply_symm_apply q

theorem fiberDifference_eq (P : Torsor G X) (x : X.obj.Elements)
    (p q : P.family.family.obj x) (g : G.obj.obj x.obj) (h : P.act x g p = q) :
    fiberDifference P x p q = g := by
  apply (fiberEquiv P x p).injective
  exact (fiberDifference_act P x p q).trans h.symm

@[simp] theorem fiberDifference_self (P : Torsor G X) (x : X.obj.Elements)
    (p : P.family.family.obj x) : fiberDifference P x p p = 1 :=
  fiberDifference_eq P x p p 1 (P.one_act x p)

theorem fiberDifference_natural (P : Torsor G X) {x y : X.obj.Elements}
    (f : x ⟶ y) (p q : P.family.family.obj x) :
    G.obj.map f.hom (fiberDifference P x p q) =
      fiberDifference P y (P.family.family.map f p) (P.family.family.map f q) := by
  symm
  apply fiberDifference_eq
  rw [← P.natural, fiberDifference_act]

/-- Displacements compose in the order imposed by the left action. -/
theorem fiberDifference_comp (P : Torsor G X) (x : X.obj.Elements)
    (p q r : P.family.family.obj x) :
    fiberDifference P x p r = fiberDifference P x q r * fiberDifference P x p q := by
  apply fiberDifference_eq
  rw [P.mul_act, fiberDifference_act, fiberDifference_act]

theorem fiberDifference_spec (P : Torsor G X) (x : X.obj.Elements)
    (p q : P.family.family.obj x) : P.act x (fiberDifference P x p q) p = q :=
  fiberDifference_act P x p q

@[simp] theorem fiberDifference_act_self (P : Torsor G X) (x : X.obj.Elements)
    (p : P.family.family.obj x) (g : G.obj.obj x.obj) :
    fiberDifference P x p (P.act x g p) = g :=
  fiberDifference_eq P x p _ g rfl

theorem fiberDifference_act_right (P : Torsor G X) (x : X.obj.Elements)
    (p q : P.family.family.obj x) (g : G.obj.obj x.obj) :
    fiberDifference P x p (P.act x g q) = g * fiberDifference P x p q := by
  apply fiberDifference_eq
  rw [P.mul_act, fiberDifference_act]

theorem fiberDifference_act_left (P : Torsor G X) (x : X.obj.Elements)
    (p q : P.family.family.obj x) (g : G.obj.obj x.obj) :
    fiberDifference P x (P.act x g p) q = fiberDifference P x p q * g⁻¹ := by
  apply fiberDifference_eq
  rw [P.mul_act, ← P.mul_act x g⁻¹ g p, inv_mul_cancel, P.one_act,
    fiberDifference_act]

theorem fiberDifference_inv (P : Torsor G X) (x : X.obj.Elements)
    (p q : P.family.family.obj x) :
    fiberDifference P x q p = (fiberDifference P x p q)⁻¹ := by
  apply fiberDifference_eq
  calc
    P.act x (fiberDifference P x p q)⁻¹ q =
        P.act x (fiberDifference P x p q)⁻¹ (P.act x (fiberDifference P x p q) p) :=
      congrArg (P.act x (fiberDifference P x p q)⁻¹) (fiberDifference_act P x p q).symm
    _ = p := by rw [← P.mul_act, inv_mul_cancel, P.one_act]

theorem fiberDifference_reindex (P : Torsor G X) (f : Y ⟶ X)
    (y : Y.obj.Elements) (p q : (reindex P f).family.family.obj y) :
    fiberDifference (reindex P f) y p q =
      fiberDifference P (f.hom.mapElements.obj y) p q := rfl

/-- A map of torsors over the same base, equivariant along a specified group
homomorphism. No inverse is requested or inferred. -/
structure SemilinearMap (φ : G ⟶ H) (P : Torsor G X) (Q : Torsor H X) where
  hom : P.family.family ⟶ Q.family.family
  equivariant (x : X.obj.Elements) (g : G.obj.obj x.obj) (p : P.family.family.obj x) :
    hom.app x (P.act x g p) = Q.act x (φ.hom.app x.obj g) (hom.app x p)

namespace SemilinearMap
variable {φ : G ⟶ H} {ψ : H ⟶ K} {χ : K ⟶ L}
variable {P : Torsor G X} {Q : Torsor H X} {R : Torsor K X} {S : Torsor L X}

@[ext] theorem ext (f g : SemilinearMap φ P Q) (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

def ident (P : Torsor G X) : SemilinearMap (𝟙 G) P P where
  hom := 𝟙 _
  equivariant _ _ _ := rfl

def comp (f : SemilinearMap φ P Q) (g : SemilinearMap ψ Q R) :
    SemilinearMap (φ ≫ ψ) P R where
  hom := f.hom ≫ g.hom
  equivariant x h p := by
    change g.hom.app x (f.hom.app x (P.act x h p)) = _
    rw [f.equivariant, g.equivariant]
    rfl

@[simp] theorem ident_comp (f : SemilinearMap φ P Q) : (ident P).comp f = f := by
  apply ext
  exact Category.id_comp _

@[simp] theorem comp_ident (f : SemilinearMap φ P Q) : f.comp (ident Q) = f := by
  apply ext
  exact Category.comp_id _

theorem comp_assoc (f : SemilinearMap φ P Q) (g : SemilinearMap ψ Q R)
    (h : SemilinearMap χ R S) : (f.comp g).comp h = f.comp (g.comp h) := by
  apply ext
  exact Category.assoc _ _ _

def reindex (f : SemilinearMap φ P Q) (a : Y ⟶ X) :
    SemilinearMap φ (SheafTorsor.reindex P a) (SheafTorsor.reindex Q a) where
  hom := Functor.whiskerLeft a.hom.mapElements f.hom
  equivariant y := f.equivariant (a.hom.mapElements.obj y)

@[simp] theorem reindex_id (f : SemilinearMap φ P Q) : f.reindex (𝟙 X) = f := rfl

@[simp] theorem reindex_comp (f : SemilinearMap φ P Q) (a : Y ⟶ X) (b : Z ⟶ Y) :
    (f.reindex a).reindex b = f.reindex (b ≫ a) := rfl

theorem comp_reindex (f : SemilinearMap φ P Q) (g : SemilinearMap ψ Q R)
    (a : Y ⟶ X) : (f.comp g).reindex a = (f.reindex a).comp (g.reindex a) := rfl

theorem map_fiberDifference (f : SemilinearMap φ P Q) (x : X.obj.Elements)
    (p q : P.family.family.obj x) :
    φ.hom.app x.obj (fiberDifference P x p q) =
      fiberDifference Q x (f.hom.app x p) (f.hom.app x q) := by
  symm
  apply fiberDifference_eq
  rw [← f.equivariant, fiberDifference_act]

def ofEquivariantMap {P Q : Torsor G X} (f : EquivariantMap P Q) :
    SemilinearMap (𝟙 G) P Q where
  hom := f.hom
  equivariant := f.equivariant

def toEquivariantMap {P Q : Torsor G X} (f : SemilinearMap (𝟙 G) P Q) :
    EquivariantMap P Q where
  hom := f.hom
  equivariant := f.equivariant

def ofArrow {P Q : Torsor G X} (f : Arrow P Q) : SemilinearMap (𝟙 G) P Q where
  hom := f.iso.hom
  equivariant := f.equivariant

/-- The identity-group case recovers the existing all-map interface exactly. -/
def equivariantMapEquiv (P Q : Torsor G X) :
    SemilinearMap (𝟙 G) P Q ≃ EquivariantMap P Q where
  toFun := toEquivariantMap
  invFun := ofEquivariantMap
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every group homomorphism acts on the corresponding regular torsors. -/
def regular (φ : G ⟶ H) (X : Sheaf J (Type w)) :
    SemilinearMap φ (trivial G X) (trivial H X) where
  hom := {
    app x := ↾fun g => φ.hom.app x.obj g
    naturality {x y} f := by
      apply ConcreteCategory.hom_ext
      intro g
      exact congrArg (fun k => k g) (φ.hom.naturality f.hom) }
  equivariant x g p := (φ.hom.app x.obj).hom.map_mul g p

theorem regular_comp (φ : G ⟶ H) (ψ : H ⟶ K) (X : Sheaf J (Type w)) :
    (regular φ X).comp (regular ψ X) = regular (φ ≫ ψ) X := rfl

theorem regular_reindex (φ : G ⟶ H) (a : Y ⟶ X) :
    (regular φ X).reindex a = regular φ Y := rfl

end SemilinearMap
end SquareKit.SheafTorsor
