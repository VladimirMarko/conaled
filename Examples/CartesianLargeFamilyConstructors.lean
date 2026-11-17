import SquareKit.Internal.Cubical.CartesianLargeFamilySubstitution
import Mathlib.Data.Fintype.Card

/-! Fixed-small-universe admission over a context containing a generic code.
The dependent fiber at n has n+1 elements; substitutions change a separate
natural parameter. Constructor decoders and whole fillers are exercised below. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CartesianLargeFamilyConstructors
open CategoryTheory SquareKit.Cubical.Cartesian SmallUniverse

noncomputable def constant (Γ : Context.{1}) (S : Type) :
    LargeConstructors.Result (constantFamily Γ (ULift.{1} S)) :=
  LargeConstructors.construct
    { fiber := fun _ => S, equiv := fun _ => Equiv.ulift.symm }
    (presentedFilling (Iso.refl _)) (presentedFilling_lawful (Iso.refl _))

abbrev context : Context.{1} := total (constantFamily smallFamilyCodes.{0} (ULift.{1} Nat))
def parameter : context ⟶ smallFamilyCodes.{0} := projection _
noncomputable def domain := constant context Nat
noncomputable def genericSum := LargeConstructors.sigma parameter (projection (liftedDecode parameter) ≫ parameter)
noncomputable def genericProduct := LargeConstructors.pi parameter (projection (liftedDecode parameter) ≫ parameter)

def point (n : Nat) : context.Elements := context.elementsMk (Opposite.op ⟨0⟩)
  ⟨LocalFamily.ofFilling (constantFamily (representable ⟨0⟩) Nat)
    (presentedFilling (Iso.refl _)) (presentedFilling_lawful (Iso.refl _)), ⟨n⟩⟩

def parameterMap (f : Nat → Nat) : context ⟶ context where
  app _ := TypeCat.ofHom (fun z => ⟨z.1,⟨f z.2.down⟩⟩)
  naturality _ _ _ := rfl
abbrev successor := parameterMap (fun n => n+1)
abbrev twice := parameterMap (fun n => 2*n)

theorem successor_nonidentity : successor ≠ 𝟙 context := by
  intro h
  have e := congrArg (fun f : context ⟶ context => (f.app (Opposite.op ⟨0⟩) (point 0).val).2.down) h
  cases e

theorem twice_nonidentity : twice ≠ 𝟙 context := by
  intro h
  have e := congrArg (fun f : context ⟶ context => (f.app (Opposite.op ⟨0⟩) (point 1).val).2.down) h
  cases e

/-- Twicing two then incrementing gives five, not six. -/
example : ((twice ≫ successor).app (Opposite.op ⟨0⟩) (point 2).val).2.down = 5 := rfl

noncomputable def argument : Term (constantFamily (total (liftedDecode domain.code)) (ULift.{1} Nat)) :=
  Term.map (Functor.whiskerLeft (projection (liftedDecode domain.code)).mapElements domain.decoding.hom)
    (generic (liftedDecode domain.code))

def indexed {Γ : Context.{1}} (q : Term (constantFamily Γ (ULift.{1} Nat))) : Family Γ where
  obj x := ULift.{1} (Fin ((q.val x).down+1))
  map f := TypeCat.ofHom (cast (congrArg (fun n : ULift.{1} Nat => ULift.{1} (Fin (n.down+1))) (q.property f)))
  map_id _ := rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro a
    exact (cast_cast _ _ a).symm

theorem indexed_bijective {Γ : Context.{1}} (q : Term (constantFamily Γ (ULift.{1} Nat))) :
    BijectiveRestrictions (indexed q) := by
  intro x y f
  exact (Equiv.cast _).bijective

noncomputable def indexedAdmission {Γ : Context.{1}}
    (q : Term (constantFamily Γ (ULift.{1} Nat))) : LargeConstructors.Result (indexed q) :=
  LargeConstructors.construct
    { fiber := fun x => Fin ((q.val x).down+1), equiv := fun _ => Equiv.ulift.symm }
    (bijectiveFilling (indexed_bijective q)) (bijectiveFilling_lawful (indexed_bijective q))
noncomputable def dependent := indexedAdmission argument
noncomputable def sum := LargeConstructors.sigma domain.code dependent.code
noncomputable def product := LargeConstructors.pi domain.code dependent.code

noncomputable def atArgument (n : Nat) : (total (liftedDecode domain.code)).Elements :=
  extendObj _ (point 0) (domain.decoding.inv.app (point 0) ⟨n⟩)

noncomputable def varyingFiber (n : Nat) :
    (liftedDecode dependent.code).obj (atArgument n) ≃ Fin (n+1) := by
  have h : domain.decoding.hom.app (point 0) (domain.decoding.inv.app (point 0) (ULift.up n)) =
      (ULift.up n : ULift.{1} Nat) :=
    congrArg (fun k => k.app (point 0) (ULift.up n : ULift.{1} Nat)) domain.decoding.inv_hom_id
  exact ((dependent.decoding.app (atArgument n)).toEquiv.trans Equiv.ulift).trans
    (Equiv.cast (congrArg (fun z : ULift.{1} Nat => Fin (z.down+1)) h))

theorem varying_fibers : ¬ Nonempty
    ((liftedDecode dependent.code).obj (atArgument 0) ≃
      (liftedDecode dependent.code).obj (atArgument 1)) := by
  rintro ⟨e⟩
  have h := Fintype.card_congr ((varyingFiber 0).symm.trans (e.trans (varyingFiber 1)))
  simp at h

noncomputable def countIndex : Term (constantFamily context (ULift.{1} Nat)) := generic _
noncomputable def counts := indexedAdmission countIndex
noncomputable def countSum := LargeConstructors.sigma counts.code (projection (liftedDecode counts.code) ≫ parameter)
noncomputable def countProduct := LargeConstructors.pi counts.code (projection (liftedDecode counts.code) ≫ parameter)
noncomputable def countFiber (n : Nat) : (liftedDecode counts.code).obj (point n) ≃ Fin (n+1) :=
  (counts.decoding.app (point n)).toEquiv.trans Equiv.ulift
noncomputable def successorCount : (liftedDecode (successor ≫ counts.code)).obj (point 2) ≃ Fin 4 := countFiber 3
noncomputable def twiceCount : (liftedDecode (twice ≫ counts.code)).obj (point 2) ≃ Fin 5 := countFiber 4
noncomputable def compositeCount : (liftedDecode (twice ≫ successor ≫ counts.code)).obj (point 2) ≃ Fin 6 := countFiber 5

noncomputable def sumSuccessor := LargeConstructors.sigmaSubstitution domain.code dependent.code successor
noncomputable def sumTwice := LargeConstructors.sigmaSubstitution domain.code dependent.code twice
noncomputable def sumComposite := LargeConstructors.sigmaSubstitution domain.code dependent.code (twice ≫ successor)
noncomputable def productSuccessor := LargeConstructors.piSubstitution domain.code dependent.code successor
noncomputable def productTwice := LargeConstructors.piSubstitution domain.code dependent.code twice
noncomputable def productComposite := LargeConstructors.piSubstitution domain.code dependent.code (twice ≫ successor)

example : (sum.filling.reindex (twice ≫ successor)).transport sumComposite =
    (LargeConstructors.sigma ((twice ≫ successor) ≫ domain.code)
      (liftSub (liftedDecode domain.code) (twice ≫ successor) ≫ dependent.code)).filling :=
  LargeConstructors.sigmaSubstitution_filling _ _ _

example : (product.filling.reindex (twice ≫ successor)).transport productComposite =
    (LargeConstructors.pi ((twice ≫ successor) ≫ domain.code)
      (liftSub (liftedDecode domain.code) (twice ≫ successor) ≫ dependent.code)).filling :=
  LargeConstructors.piSubstitution_filling _ _ _

example := LargeConstructors.sigmaSubstitution_comp domain.code dependent.code successor twice

noncomputable def emptyDomain := constant context Empty
noncomputable def emptySum := LargeConstructors.sigma emptyDomain.code
  (projection (liftedDecode emptyDomain.code) ≫ parameter)
noncomputable def emptyProduct := LargeConstructors.pi emptyDomain.code
  (projection (liftedDecode emptyDomain.code) ≫ emptyDomain.code)

noncomputable def emptyFiber (x : context.Elements) : (liftedDecode emptyDomain.code).obj x ≃ Empty :=
  (emptyDomain.decoding.app x).toEquiv.trans Equiv.ulift

theorem empty_sum_rejected (x : context.Elements) : IsEmpty ((liftedDecode emptySum.code).obj x) :=
  ⟨fun z => Empty.elim (emptyFiber x (emptySum.decoding.hom.app x z).1)⟩

noncomputable def emptyBody : Term (liftedDecode (projection (liftedDecode emptyDomain.code) ≫ emptyDomain.code)) where
  val x := Empty.elim (emptyFiber ((projection (liftedDecode emptyDomain.code)).mapElements.obj x) x.val.2)
  property {x} _ := Empty.elim (emptyFiber ((projection (liftedDecode emptyDomain.code)).mapElements.obj x) x.val.2)
noncomputable def emptyFunction : Term (liftedDecode emptyProduct.code) :=
  Term.map emptyProduct.decoding.inv (lam emptyBody)

theorem emptyFunction_unique (z : Term (liftedDecode emptyProduct.code)) : z = emptyFunction := by
  apply Term.map_injective_of_iso emptyProduct.decoding
  apply Term.ext
  intro x
  apply PiElement.ext
  intro y f a
  exact Empty.elim (emptyFiber y a)

noncomputable def naturalSection (n : Nat) : Term (liftedDecode domain.code) :=
  Term.map domain.decoding.inv ⟨fun _ => ⟨n⟩, fun _ => rfl⟩
noncomputable def incompatiblePath := LargeConstructors.path
  (projection (interval context) ≫ domain.code) (naturalSection 0) (naturalSection 1)

theorem incompatible_endpoints_rejected : ¬ Nonempty (Term (liftedDecode incompatiblePath.code)) := by
  rintro ⟨z⟩
  let q := homogeneousPathMap domain.decoding.hom (Term.map incompatiblePath.decoding.hom z)
  have h := constant_section_interval (pathApp q) (point 0)
    ((endpoint context false).val (point 0)) ((endpoint context true).val (point 0))
  have h₀ := congrArg (fun t => t.val (point 0)) (pathApp_zero q)
  have h₁ := congrArg (fun t => t.val (point 0)) (pathApp_one q)
  have e := h₀.symm.trans (h.trans h₁)
  have hzero := congrArg (fun k => k.app (point 0) (ULift.up 0 : ULift.{1} Nat)) domain.decoding.inv_hom_id
  have hone := congrArg (fun k => k.app (point 0) (ULift.up 1 : ULift.{1} Nat)) domain.decoding.inv_hom_id
  exact Nat.zero_ne_one (congrArg ULift.down (hzero.symm.trans (e.trans hone)))

noncomputable def pathSuccessor := LargeConstructors.pathSubstitution
  (projection (interval context) ≫ domain.code) (naturalSection 0) (naturalSection 1) successor
noncomputable def pathTwice := LargeConstructors.pathSubstitution
  (projection (interval context) ≫ domain.code) (naturalSection 0) (naturalSection 1) twice
noncomputable def pathComposite := LargeConstructors.pathSubstitution
  (projection (interval context) ≫ domain.code) (naturalSection 0) (naturalSection 1) (twice ≫ successor)

example : (incompatiblePath.filling.reindex (twice ≫ successor)).transport pathComposite =
    (LargeConstructors.path (liftSub (interval context) (twice ≫ successor) ≫
      projection (interval context) ≫ domain.code)
      (Term.reindex (naturalSection 0) (twice ≫ successor))
      (Term.reindex (naturalSection 1) (twice ≫ successor))).filling :=
  LargeConstructors.pathSubstitution_filling _ _ _ _

noncomputable def reflexivePath := LargeConstructors.path
  (projection (interval context) ≫ domain.code) (naturalSection 0) (naturalSection 0)
noncomputable def reflexiveSection : Term (liftedDecode reflexivePath.code) :=
  Term.map reflexivePath.decoding.inv (homogeneousRefl (naturalSection 0))

end Examples.CartesianLargeFamilyConstructors
