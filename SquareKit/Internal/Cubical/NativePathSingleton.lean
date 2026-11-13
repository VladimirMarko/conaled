import SquareKit.Internal.Cubical.HomotopyEquivalences

/-! Native path reversal and the contractible based path singleton. -/
set_option autoImplicit false
set_option warningAsError true
namespace SquareKit.Cubical.Presheaf
open CategoryTheory
universe u

namespace NativePathSingleton
variable {Γ : Context.{u}} {A : Family Γ} {a b : Term A}

def reverseElement {x : Γ.Elements} (p : (homogeneousPath A a b).obj x) :
    (homogeneousPath A b a).obj x :=
  ⟨{ val := fun f i => p.val.val f ⟨Cube.comp i.down Cube.reversal⟩
     naturality := fun {_ y} f g i =>
       (p.val.naturality f g ⟨Cube.comp i.down Cube.reversal⟩).trans
         (congrArg (fun r : Cube.Hom y.obj.unop ⟨1⟩ => (show A.obj y from p.val.val (f ≫ g) (show (interval Γ).obj y from ⟨r⟩)))
           (Category.assoc g.hom.unop i.down Cube.reversal).symm) }, by
    intro y f
    constructor
    · exact (congrArg (fun r : Cube.Hom y.obj.unop ⟨1⟩ => (show A.obj y from p.val.val f (show (interval Γ).obj y from ⟨r⟩))) (Cube.endpoint_reversal y.obj.unop false)).trans
        (p.property f).2
    · exact (congrArg (fun r : Cube.Hom y.obj.unop ⟨1⟩ => (show A.obj y from p.val.val f (show (interval Γ).obj y from ⟨r⟩))) (Cube.endpoint_reversal y.obj.unop true)).trans
        (p.property f).1⟩

theorem reverse_twice {x : Γ.Elements} (p : (homogeneousPath A a b).obj x) :
    reverseElement (reverseElement p) = p := by
  apply Subtype.ext
  apply PiElement.ext
  intro y f i
  exact congrArg (fun r : Cube.Hom y.obj.unop ⟨1⟩ => (show A.obj y from p.val.val f (show (interval Γ).obj y from ⟨r⟩)))
    (((@Category.assoc Cube _ y.obj.unop ⟨1⟩ ⟨1⟩ ⟨1⟩ i.down Cube.reversal Cube.reversal).trans
      (congrArg (Cube.comp i.down) Cube.reversal_twice)).trans (@Category.comp_id Cube _ y.obj.unop ⟨1⟩ i.down))

def reverseIso (a b : Term A) : homogeneousPath A a b ≅ homogeneousPath A b a :=
  NatIso.ofComponents (fun _ =>
    { hom := TypeCat.ofHom reverseElement
      inv := TypeCat.ofHom reverseElement
      hom_inv_id := by
        apply ConcreteCategory.hom_ext
        exact reverse_twice
      inv_hom_id := by
        apply ConcreteCategory.hom_ext
        exact reverse_twice }) (by
    intro x y f
    apply ConcreteCategory.hom_ext
    intro p
    apply Subtype.ext
    apply PiElement.ext
    intro z g i
    rfl)

abbrev singleton (a : Term A) : Family Γ :=
  sigma A (homogeneousPath (reindex A (projection A)) (a.reindex (projection A)) (generic A))

/-- Native fibers of a genuine equivalence remain contractible at an actual section. -/
def fiberAt {B : Family Γ} {f : A ⟶ B} (E : HomotopyEquivalence f) (b : Term B) :
    HomotopyContractible (homotopyFiber f b) :=
  (E.fibers.reindex (pair (𝟙 Γ) b)).transport
    (sigmaSecondIso _ (pathReindexIso
      (reindex (reindex (reindex B (projection B)) (projection (reindex A (projection B))))
        (projection (interval (total (reindex A (projection B))))))
      (Term.map (Functor.whiskerLeft (projection (reindex A (projection B))).mapElements
        (Functor.whiskerLeft (projection B).mapElements f)) (generic (reindex A (projection B))))
      ((generic B).reindex (projection (reindex A (projection B))))
      (liftSub (reindex A (projection B)) (pair (𝟙 Γ) b))))

/-- The path singleton is obtained from the actual identity-map fiber by
reversing its paths, with the constructed native fiber contraction retained. -/
def contractible (a : Term A) : HomotopyContractible (singleton a) :=
  (fiberAt (HomotopyEquivalence.ofIso (Iso.refl A)) a).transport
    (sigmaSecondIso A (reverseIso (generic A) (a.reindex (projection A))))

end NativePathSingleton
end SquareKit.Cubical.Presheaf
