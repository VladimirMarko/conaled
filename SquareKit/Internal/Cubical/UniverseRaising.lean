import SquareKit.Internal.Cubical.Univalence
import SquareKit.Internal.Cubical.UniverseDecode

/-! Raising native families changes their Lean universe while retaining sections
and native paths, including their chosen data. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

namespace Raising

def lowerElements (Γ : Context.{u}) : (raisedContext Γ).Elements ⥤ Γ.Elements where
  obj x := Γ.elementsMk x.obj x.val.down
  map f := Functor.Elements.homMk f.hom (congrArg ULift.down f.map_val)
  map_id _ := rfl
  map_comp _ _ := rfl

def family {Γ : Context.{u}} (A : Family Γ) : Family (raisedContext Γ) where
  obj x := ULift.{u+1} (A.obj ((lowerElements Γ).obj x))
  map f := TypeCat.ofHom (fun a => ⟨A.map ((lowerElements Γ).map f) a.down⟩)
  map_id x := by
    apply ConcreteCategory.hom_ext
    intro a
    exact congrArg ULift.up (ConcreteCategory.congr_hom (A.map_id _) a.down)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    exact congrArg ULift.up (ConcreteCategory.congr_hom (A.map_comp ((lowerElements Γ).map f) ((lowerElements Γ).map g)) a.down)

def raiseTerm {Γ : Context.{u}} {A : Family Γ} (a : Term A) : Term (family A) where
  val x := ⟨a.val ((lowerElements Γ).obj x)⟩
  property f := congrArg ULift.up (a.property ((lowerElements Γ).map f))

def lowerTerm {Γ : Context.{u}} {A : Family Γ} (a : Term (family A)) : Term A where
  val x := (a.val ((raisedElements Γ).obj x)).down
  property f := congrArg ULift.down (a.property ((raisedElements Γ).map f))

theorem lower_raise {Γ : Context.{u}} {A : Family Γ} (a : Term A) :
    lowerTerm (raiseTerm a) = a := rfl

theorem raise_lower {Γ : Context.{u}} {A : Family Γ} (a : Term (family A)) :
    raiseTerm (lowerTerm a) = a := rfl

def map {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) : family A ⟶ family B where
  app x := TypeCat.ofHom (fun a => ⟨f.app ((lowerElements Γ).obj x) a.down⟩)
  naturality x y g := by
    apply ConcreteCategory.hom_ext
    intro a
    exact congrArg ULift.up (ConcreteCategory.congr_hom (f.naturality ((lowerElements Γ).map g)) a.down)

def lowerMap {Γ : Context.{u}} {A B : Family Γ} (f : family A ⟶ family B) : A ⟶ B where
  app x := TypeCat.ofHom (fun a => (f.app ((raisedElements Γ).obj x) ⟨a⟩).down)
  naturality x y g := by
    apply ConcreteCategory.hom_ext
    intro a
    exact congrArg ULift.down (ConcreteCategory.congr_hom (f.naturality ((raisedElements Γ).map g)) ⟨a⟩)

def totalIso {Γ : Context.{u}} (A : Family Γ) :
    raisedContext (total A) ≅ total (family A) where
  hom :=
    { app := fun _ => TypeCat.ofHom (fun x => ⟨⟨x.down.1⟩,⟨x.down.2⟩⟩)
      naturality := fun _ _ _ => rfl }
  inv :=
    { app := fun _ => TypeCat.ofHom (fun x => ⟨⟨x.1.down,x.2.down⟩⟩)
      naturality := fun _ _ _ => rfl }
  hom_inv_id := rfl
  inv_hom_id := rfl

def lowerPath {Γ : Context.{u}} {A : Family Γ} {a b : Term (family A)}
    (p : Term (homogeneousPath (family A) a b)) :
    Term (homogeneousPath A (lowerTerm a) (lowerTerm b)) :=
  pathLam (lowerTerm ((pathApp p).reindex (SmallUniverse.raisedIntervalIso Γ).hom))
    (congrArg lowerTerm (pathApp_zero p)) (congrArg lowerTerm (pathApp_one p))

def raisePath {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    (p : Term (homogeneousPath A a b)) :
    Term (homogeneousPath (family A) (raiseTerm a) (raiseTerm b)) :=
  pathLam ((raiseTerm (pathApp p)).reindex (SmallUniverse.raisedIntervalIso Γ).inv)
    (congrArg raiseTerm (pathApp_zero p)) (congrArg raiseTerm (pathApp_one p))

theorem lower_raise_path {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    (p : Term (homogeneousPath A a b)) : lowerPath (raisePath p) = p :=
  pathLam_app p

theorem raise_lower_path {Γ : Context.{u}} {A : Family Γ} {a b : Term (family A)}
    (p : Term (homogeneousPath (family A) a b)) : raisePath (lowerPath p) = p :=
  pathLam_app p

def raisePathElement {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    {x : (raisedContext Γ).Elements}
    (p : (homogeneousPath A a b).obj ((lowerElements Γ).obj x)) :
    (homogeneousPath (family A) (raiseTerm a) (raiseTerm b)).obj x :=
  ⟨{ val := fun f i => ⟨p.val.val ((lowerElements Γ).map f) ⟨i.down⟩⟩
     naturality := fun f g i => congrArg ULift.up
       (p.val.naturality ((lowerElements Γ).map f) ((lowerElements Γ).map g) ⟨i.down⟩) },
   fun f => ⟨congrArg ULift.up (p.property ((lowerElements Γ).map f)).1,
     congrArg ULift.up (p.property ((lowerElements Γ).map f)).2⟩⟩

def lowerPathElement {Γ : Context.{u}} {A : Family Γ} {a b : Term A}
    {x : (raisedContext Γ).Elements}
    (p : (homogeneousPath (family A) (raiseTerm a) (raiseTerm b)).obj x) :
    (homogeneousPath A a b).obj ((lowerElements Γ).obj x) :=
  ⟨{ val := fun f i => (p.val.val ((raisedElements Γ).map f) ⟨i.down⟩).down
     naturality := fun f g i => congrArg ULift.down
       (p.val.naturality ((raisedElements Γ).map f) ((raisedElements Γ).map g) ⟨i.down⟩) },
   fun f => ⟨congrArg ULift.down (p.property ((raisedElements Γ).map f)).1,
     congrArg ULift.down (p.property ((raisedElements Γ).map f)).2⟩⟩

def pathIso {Γ : Context.{u}} {A : Family Γ} (a b : Term A) :
    family (homogeneousPath A a b) ≅
      homogeneousPath (family A) (raiseTerm a) (raiseTerm b) :=
  NatIso.ofComponents (fun _ =>
    { hom := TypeCat.ofHom (fun p => raisePathElement p.down)
      inv := TypeCat.ofHom (fun p => ⟨lowerPathElement p⟩)
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        intro p
        apply congrArg ULift.up
        apply Subtype.ext
        apply PiElement.ext
        intro y f i
        rfl
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        intro p
        apply Subtype.ext
        apply PiElement.ext
        intro y f i
        rfl }) (by intro x y f; rfl)

def lowerContractible {Γ : Context.{u}} {A : Family Γ}
    (c : HomotopyContractible (family A)) : HomotopyContractible A where
  center := lowerTerm c.center
  contraction := lowerPath (A := reindex A (projection A)) (Term.map
    (pathReindex (reindex (reindex (family A) (projection (family A)))
      (projection (interval (total (family A)))))
      (c.center.reindex (projection (family A))) (generic (family A)) (totalIso A).hom)
    (c.contraction.reindex (totalIso A).hom))

def sigmaIso {Γ : Context.{u}} (A : Family Γ) (B : Family (total A)) :
    family (sigma A B) ≅ sigma (family A) (reindex (family B) (totalIso A).inv) :=
  NatIso.ofComponents (fun _ =>
    { hom := TypeCat.ofHom (fun z => ⟨⟨z.down.1⟩,⟨z.down.2⟩⟩)
      inv := TypeCat.ofHom (fun z => ⟨⟨z.1.down,z.2.down⟩⟩)
      hom_inv_id := rfl
      inv_hom_id := rfl }) (by intro x y f; rfl)

def fiberIso {Γ : Context.{u}} {A B : Family Γ} (f : A ⟶ B) (b : Term B) :
    family (homotopyFiber f b) ≅ homotopyFiber (map f) (raiseTerm b) :=
  sigmaIso A _ ≪≫ sigmaSecondIso _
    (Functor.isoWhiskerLeft (totalIso A).inv.mapElements
      (pathIso (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
        (b.reindex (projection A))) ≪≫
      pathReindexIso _ _ _ (totalIso A).inv)

def fiberReindexIso {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : A ⟶ B) (b : Term B) (σ : Δ ⟶ Γ) :
    reindex (homotopyFiber f b) σ ≅
      homotopyFiber (Functor.whiskerLeft σ.mapElements f) (b.reindex σ) :=
  sigmaSecondIso _ (pathReindexIso
    (reindex (reindex B (projection A)) (projection (interval (total A))))
    (Term.map (Functor.whiskerLeft (projection A).mapElements f) (generic A))
    (b.reindex (projection A)) (liftSub A σ))

def lowerEquivalence {Γ : Context.{u}} {A B : Family Γ} {f : A ⟶ B}
    (E : HomotopyEquivalence (map f)) : HomotopyEquivalence f where
  fibers := lowerContractible (((E.fibers.reindex (totalIso B).hom).transport
    (fiberReindexIso (Functor.whiskerLeft (projection (family B)).mapElements (map f))
      (generic (family B)) (totalIso B).hom)).transport
        (fiberIso (Functor.whiskerLeft (projection B).mapElements f) (generic B)).symm)

theorem lowerMap_reindex {Γ Δ : Context.{u}} {A B : Family Γ}
    (f : family A ⟶ family B) (σ : Δ ⟶ Γ) :
    lowerMap (A := reindex A σ) (B := reindex B σ)
      (Functor.whiskerLeft (raisedSub σ).mapElements f) =
      Functor.whiskerLeft σ.mapElements (lowerMap f) := rfl

theorem lowerContractible_reindex {Γ Δ : Context.{u}} {A : Family Γ}
    (c : HomotopyContractible (family A)) (σ : Δ ⟶ Γ) :
    lowerContractible (A := reindex A σ) (c.reindex (raisedSub σ)) = (lowerContractible c).reindex σ := rfl


end Raising
namespace SmallUniverse

theorem liftedDecode_raised {Γ : Context.{u}} (a : raisedContext Γ ⟶ smallFamilyCodes.{u}) :
    liftedDecode a = Raising.family (Presheaf.decode a) := rfl

def lowerChartMap {Γ : Context.{u}} {Ξ : Context.{u+1}}
    (a b : Ξ ⟶ smallFamilyCodes.{u}) (σ : raisedContext Γ ⟶ Ξ)
    (f : liftedDecode a ⟶ liftedDecode b) :
    Presheaf.decode (σ ≫ a) ⟶ Presheaf.decode (σ ≫ b) :=
  Raising.lowerMap (Functor.whiskerLeft σ.mapElements f)

def lowerChartEquivalence {Γ : Context.{u}} {Ξ : Context.{u+1}}
    (a b : Ξ ⟶ smallFamilyCodes.{u}) (σ : raisedContext Γ ⟶ Ξ)
    (f : liftedDecode a ⟶ liftedDecode b) (E : HomotopyEquivalence f) :
    HomotopyEquivalence (lowerChartMap a b σ f) :=
  Raising.lowerEquivalence (E.reindex σ)

theorem lowerChartMap_reindex {Γ Θ : Context.{u}} {Ξ : Context.{u+1}}
    (a b : Ξ ⟶ smallFamilyCodes.{u}) (σ : raisedContext Γ ⟶ Ξ)
    (f : liftedDecode a ⟶ liftedDecode b) (τ : Θ ⟶ Γ) :
    lowerChartMap a b (raisedSub τ ≫ σ) f =
      Functor.whiskerLeft τ.mapElements (lowerChartMap a b σ f) := rfl

end SmallUniverse
end SquareKit.Cubical.Presheaf
