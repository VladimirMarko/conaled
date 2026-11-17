import SquareKit.Internal.Cubical.NativeStructureDescriptions
import SquareKit.Internal.Cubical.CartesianNativeStructureDescriptions
import SquareKit.Internal.Cubical.SigmaPaths
import SquareKit.Internal.Cubical.CartesianSigmaPaths

/-! Dependent-sum paths in both native cubical models. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.SigmaPaths
open CategoryTheory

namespace Presheaf
open SquareKit.Cubical.Presheaf
universe u
variable {Γ : Context.{u}}

def bit (b : Bool) : Term (constantFamily Γ (ULift.{u} Bool)) :=
  ⟨fun _ => ⟨b⟩, fun _ => rfl⟩
def edge (b : Bool) : Term (sigma (interval Γ)
    (constantFamily (total (interval Γ)) (ULift.{u} Bool))) :=
  sigmaIntro (endpoint Γ b) (bit false)

/-- The interval coordinate moves from zero to one; the field retains false. -/
def moving : Term (homogeneousPath _ (edge (Γ := Γ) false) (edge true)) :=
  pathLam ⟨(fun x => ⟨(generic (interval Γ)).val x, ⟨false⟩⟩), fun f => congrArg (fun r => Sigma.mk (β := fun _ => ULift.{u} Bool) r (ULift.up false)) ((generic (interval Γ)).property f)⟩ rfl rfl

def splitMoving := Term.map (SigmaPaths.decomposition (edge (Γ := Γ) false) (edge true)).hom moving

example (x : Γ.Elements) {y : Γ.Elements} (f : x ⟶ y) (r : (interval Γ).obj y) :
    ((splitMoving.val x).1).val.val f r = r := rfl
example (x : Γ.Elements) {y : Γ.Elements} (f : x ⟶ y) (r : (interval Γ).obj y) :
    ((splitMoving.val x).2).val f r = ULift.up false := rfl
example : Term.map (SigmaPaths.decomposition (edge (Γ := Γ) false) (edge true)).inv
    splitMoving = moving := by
  apply Term.ext
  intro x
  exact (SigmaPaths.equiv _ _ x).symm_apply_apply _

/-- Fibers have genuinely different cardinalities as the natural-number base varies. -/
def finiteFiber (q : Term (constantFamily Γ (ULift.{u} Nat))) : Family Γ where
  obj x := ULift.{u} (Fin ((q.val x).down+1))
  map f := TypeCat.ofHom (cast (congrArg (fun n : ULift.{u} Nat => ULift.{u} (Fin (n.down+1))) (q.property f)))
  map_id _ := rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (cast_cast _ _ a).symm

def indexedPair (n : Nat) : Term (sigma (constantFamily Γ (ULift.{u} Nat))
    (finiteFiber (generic (constantFamily Γ (ULift.{u} Nat))))) :=
  ⟨fun _ => ⟨⟨n⟩, ⟨⟨n, Nat.lt_succ_self n⟩⟩⟩, fun _ => rfl⟩
example (n : Nat) (x : Γ.Elements) :
    ((SigmaPaths.equiv (indexedPair (Γ := Γ) n) (indexedPair n) x)
      ((homogeneousRefl (indexedPair n)).val x)).2.val (𝟙 x)
        ((endpoint Γ true).val x) = ULift.up (⟨n, Nat.lt_succ_self n⟩ : Fin (n+1)) := rfl

/-- A field fixed to false cannot satisfy a true target endpoint. -/
def fixedPair (b : Bool) : Term (sigma (constantFamily Γ (ULift.{u} Bool))
    (constantFamily (total (constantFamily Γ (ULift.{u} Bool))) (ULift.{u} Bool))) :=
  sigmaIntro (bit false) (bit b)
example (x : Γ.Elements) (p : (SigmaPaths.base (fixedPair false) (fixedPair true)).obj x)
    (q : SigmaPaths.DependentPath (fixedPair false) (fixedPair true) p)
    (h : q.val (𝟙 x) ((endpoint Γ true).val x) = ULift.up false) : False := by
  have e := congrArg (fun z => z.2.down) (q.one (𝟙 x))
  rw [h] at e
  cases e

/-- The construction applies to the admitted universe of structures and has a lawful filler. -/
noncomputable def structuredPaths {Δ : Context.{u+1}} (D : SquareKit.StructureIdentity.Description.{u})
    (a b : Term (StructureIdentity.Native.objects D Δ)) :=
  SigmaPaths.filling a b (StructureIdentity.Native.objectsFilling D Δ).1
    (StructureIdentity.Native.objectsFilling D Δ).2
example {Δ : Context.{u+1}} (D : SquareKit.StructureIdentity.Description.{u})
    (a b : Term (StructureIdentity.Native.objects D Δ)) : (structuredPaths D a b).1.Lawful :=
  (structuredPaths D a b).2
end Presheaf

namespace Cartesian
open SquareKit.Cubical.Cartesian
universe u
variable {Γ : Context.{u}}

def bit (b : Bool) : Term (constantFamily Γ (ULift.{u} Bool)) :=
  ⟨fun _ => ⟨b⟩, fun _ => rfl⟩
def edge (b : Bool) : Term (sigma (interval Γ)
    (constantFamily (total (interval Γ)) (ULift.{u} Bool))) :=
  sigmaIntro (endpoint Γ b) (bit false)

/-- The interval coordinate moves from zero to one; the field retains false. -/
def moving : Term (homogeneousPath _ (edge (Γ := Γ) false) (edge true)) :=
  pathLam ⟨(fun x => ⟨(generic (interval Γ)).val x, ⟨false⟩⟩), fun f => congrArg (fun r => Sigma.mk (β := fun _ => ULift.{u} Bool) r (ULift.up false)) ((generic (interval Γ)).property f)⟩ rfl rfl

def splitMoving := Term.map (SigmaPaths.decomposition (edge (Γ := Γ) false) (edge true)).hom moving

example (x : Γ.Elements) {y : Γ.Elements} (f : x ⟶ y) (r : (interval Γ).obj y) :
    ((splitMoving.val x).1).val.val f r = r := rfl
example (x : Γ.Elements) {y : Γ.Elements} (f : x ⟶ y) (r : (interval Γ).obj y) :
    ((splitMoving.val x).2).val f r = ULift.up false := rfl
example : Term.map (SigmaPaths.decomposition (edge (Γ := Γ) false) (edge true)).inv
    splitMoving = moving := by
  apply Term.ext
  intro x
  exact (SigmaPaths.equiv _ _ x).symm_apply_apply _

/-- Fibers have genuinely different cardinalities as the natural-number base varies. -/
def finiteFiber (q : Term (constantFamily Γ (ULift.{u} Nat))) : Family Γ where
  obj x := ULift.{u} (Fin ((q.val x).down+1))
  map f := TypeCat.ofHom (cast (congrArg (fun n : ULift.{u} Nat => ULift.{u} (Fin (n.down+1))) (q.property f)))
  map_id _ := rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (cast_cast _ _ a).symm

def indexedPair (n : Nat) : Term (sigma (constantFamily Γ (ULift.{u} Nat))
    (finiteFiber (generic (constantFamily Γ (ULift.{u} Nat))))) :=
  ⟨fun _ => ⟨⟨n⟩, ⟨⟨n, Nat.lt_succ_self n⟩⟩⟩, fun _ => rfl⟩
example (n : Nat) (x : Γ.Elements) :
    ((SigmaPaths.equiv (indexedPair (Γ := Γ) n) (indexedPair n) x)
      ((homogeneousRefl (indexedPair n)).val x)).2.val (𝟙 x)
        ((endpoint Γ true).val x) = ULift.up (⟨n, Nat.lt_succ_self n⟩ : Fin (n+1)) := rfl

/-- A field fixed to false cannot satisfy a true target endpoint. -/
def fixedPair (b : Bool) : Term (sigma (constantFamily Γ (ULift.{u} Bool))
    (constantFamily (total (constantFamily Γ (ULift.{u} Bool))) (ULift.{u} Bool))) :=
  sigmaIntro (bit false) (bit b)
example (x : Γ.Elements) (p : (SigmaPaths.base (fixedPair false) (fixedPair true)).obj x)
    (q : SigmaPaths.DependentPath (fixedPair false) (fixedPair true) p)
    (h : q.val (𝟙 x) ((endpoint Γ true).val x) = ULift.up false) : False := by
  have e := congrArg (fun z => z.2.down) (q.one (𝟙 x))
  rw [h] at e
  cases e

/-- The construction applies to the admitted universe of structures and has a lawful filler. -/
noncomputable def structuredPaths {Δ : Context.{u+1}} (D : SquareKit.StructureIdentity.Description.{u})
    (a b : Term (StructureIdentity.Native.objects D Δ)) :=
  SigmaPaths.filling a b (StructureIdentity.Native.objectsFilling D Δ).1
    (StructureIdentity.Native.objectsFilling D Δ).2
example {Δ : Context.{u+1}} (D : SquareKit.StructureIdentity.Description.{u})
    (a b : Term (StructureIdentity.Native.objects D Δ)) : (structuredPaths D a b).1.Lawful :=
  (structuredPaths D a b).2
end Cartesian

end Examples.SigmaPaths
