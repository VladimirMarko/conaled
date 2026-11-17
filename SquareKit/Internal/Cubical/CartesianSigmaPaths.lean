import SquareKit.Internal.Cubical.CartesianPathFilling
import SquareKit.Internal.Cubical.CartesianHomotopyEquivalences

/-! Paths in dependent sums retain both the base path and its dependent field path. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Cartesian.SigmaPaths
open CategoryTheory
universe u
variable {Γ : Context.{u}} {A : Family Γ} {B : Family (total A)}
variable (z₀ z₁ : Term (sigma A B))
abbrev base : Family Γ := homogeneousPath A (sigmaFst z₀) (sigmaFst z₁)
abbrev whole : Family Γ := homogeneousPath (sigma A B) z₀ z₁

/-- The base projection of a path retains every generalized interval evaluation. -/
def first {x : Γ.Elements} (p : (whole z₀ z₁).obj x) : (base z₀ z₁).obj x :=
  ⟨{ val := fun f r => (p.val.val f r).1
     naturality := fun f g r => congrArg Sigma.fst (p.val.naturality f g r) },
   fun f => ⟨congrArg Sigma.fst (p.property f).1, congrArg Sigma.fst (p.property f).2⟩⟩

/-- A dependent field path along a specified base path, with native restrictions and endpoints. -/
structure DependentPath {x : Γ.Elements} (p : (base z₀ z₁).obj x) where
  val : ∀ {y : Γ.Elements} (f : x ⟶ y) (r : (interval Γ).obj y),
    B.obj (extendObj A y (p.val.val f r))
  naturality : ∀ {y w : Γ.Elements} (f : x ⟶ y) (g : y ⟶ w) (r : (interval Γ).obj y),
    B.map (extendAlong A g (p.val.naturality f g r)) (val f r) =
      val (f ≫ g) ((interval Γ).map g r)
  zero : ∀ {y : Γ.Elements} (f : x ⟶ y),
    (⟨p.val.val f ((endpoint Γ false).val y), val f ((endpoint Γ false).val y)⟩ :
      (sigma A B).obj y) = z₀.val y
  one : ∀ {y : Γ.Elements} (f : x ⟶ y),
    (⟨p.val.val f ((endpoint Γ true).val y), val f ((endpoint Γ true).val y)⟩ :
      (sigma A B).obj y) = z₁.val y

@[ext] theorem DependentPath.ext {x : Γ.Elements} {p : (base z₀ z₁).obj x}
    {q r : DependentPath z₀ z₁ p} (h : ∀ {y} (f : x ⟶ y) t, q.val f t = r.val f t) : q = r := by
  cases q
  cases r
  congr
  funext y f t
  exact h f t

def second {x : Γ.Elements} (p : (whole z₀ z₁).obj x) : DependentPath z₀ z₁ (first z₀ z₁ p) where
  val f r := (p.val.val f r).2
  naturality f g r := by
    have h := p.val.naturality f g r
    have e := sigmaMap_ofHom A B g (congrArg Sigma.fst h) (p.val.val f r).2
    exact (Sigma.mk.inj (e.symm.trans h)).2.eq
  zero f := (p.property f).1
  one f := (p.property f).2

def assemble {x : Γ.Elements} (p : (base z₀ z₁).obj x) (q : DependentPath z₀ z₁ p) :
    (whole z₀ z₁).obj x :=
  ⟨{ val := fun f r => ⟨p.val.val f r, q.val f r⟩
     naturality := fun f g r =>
       (sigmaMap_ofHom A B g (p.val.naturality f g r) (q.val f r)).trans
         (congrArg (Sigma.mk _) (q.naturality f g r)) }, fun f => ⟨q.zero f,q.one f⟩⟩

def equiv (x : Γ.Elements) : (whole z₀ z₁).obj x ≃
    (p : (base z₀ z₁).obj x) × DependentPath z₀ z₁ p where
  toFun p := ⟨first z₀ z₁ p, second z₀ z₁ p⟩
  invFun q := assemble z₀ z₁ q.1 q.2
  left_inv p := by
    apply Subtype.ext
    apply PiElement.ext
    intro y f r
    rfl
  right_inv q := by
    rcases q with ⟨p,q⟩
    rfl

/-- The independent pair of base and dependent paths forms a native presheaf family. -/
def components : Family Γ where
  obj x := (p : (base z₀ z₁).obj x) × DependentPath z₀ z₁ p
  map f := TypeCat.ofHom (fun q => equiv z₀ z₁ _ ((whole z₀ z₁).map f ((equiv z₀ z₁ _).symm q)))
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro q
    simp
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro q
    simp

/-- A family isomorphism, not just a bijection of closed sections. -/
def decomposition : whole z₀ z₁ ≅ components z₀ z₁ :=
  NatIso.ofComponents (fun x => (equiv z₀ z₁ x).toIso) (by
    intro x y f
    apply ConcreteCategory.hom_ext
    intro p
    change equiv z₀ z₁ y ((whole z₀ z₁).map f p) =
      equiv z₀ z₁ y ((whole z₀ z₁).map f ((equiv z₀ z₁ x).symm (equiv z₀ z₁ x p)))
    rw [Equiv.symm_apply_apply])

@[simp] theorem restrict_base {x y : Γ.Elements} (f : x ⟶ y)
    (q : (components z₀ z₁).obj x) {w : Γ.Elements} (g : y ⟶ w)
    (r : (interval Γ).obj w) :
    ((components z₀ z₁).map f q).1.val.val g r = q.1.val.val (f ≫ g) r := rfl

@[simp] theorem restrict_field {x y : Γ.Elements} (f : x ⟶ y)
    (q : (components z₀ z₁).obj x) {w : Γ.Elements} (g : y ⟶ w)
    (r : (interval Γ).obj w) :
    ((components z₀ z₁).map f q).2.val g r = q.2.val (f ≫ g) r := rfl

noncomputable def filling (F : Filling (sigma A B)) (hF : F.Lawful) :
    {G : Filling (components z₀ z₁) // G.Lawful} :=
  let H := pathFilling (F.reindex (projection (interval Γ)))
    (hF.reindex (projection (interval Γ))) z₀ z₁
  ⟨H.transport (decomposition z₀ z₁), Filling.transport_lawful _ H
    (pathFilling_lawful (F.reindex (projection (interval Γ)))
      (hF.reindex (projection (interval Γ))) z₀ z₁)⟩

end SquareKit.Cubical.Cartesian.SigmaPaths
