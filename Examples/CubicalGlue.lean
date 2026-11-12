import SquareKit.Internal.Cubical.UniverseComposition
import Examples.CubicalStateTransport

/-! Rejection uses native homotopy-fiber contraction and discrete path rigidity. -/
set_option autoImplicit false
set_option warningAsError true
namespace Examples.CubicalGlue
open CategoryTheory SquareKit.Cubical SquareKit.Cubical.Presheaf

def boolFamily : Family terminal.{0} := constantFamily terminal Bool
def unitFamily : Family terminal.{0} := constantFamily terminal Unit

def collapse : boolFamily ⟶ unitFamily where
  app _ := TypeCat.ofHom (fun _ => ())
  naturality _ _ _ := rfl

def collapseFiber : Family (total unitFamily) :=
  homotopyFiber (Functor.whiskerLeft (projection unitFamily).mapElements collapse) (generic unitFamily)

def boolSection (b : Bool) : Term (reindex boolFamily (projection unitFamily)) where
  val _ := b
  property _ := rfl

def fiberPoint (b : Bool) : Term collapseFiber where
  val _ := ⟨b,⟨{
    val := fun {_} _ _ => ()
    naturality := fun _ _ _ => rfl }, fun {_} _ =>
      ⟨rfl, Unit.ext _ _⟩⟩⟩
  property _ := rfl

def observe : collapseFiber ⟶ constantFamily (total unitFamily) Bool where
  app _ := TypeCat.ofHom (fun z => z.1)
  naturality _ _ _ := rfl

/-- The constant map fails the actual contraction requirement, not a class search. -/
theorem collapse_not_equivalence : ¬ Nonempty (HomotopyEquivalence collapse) := by
  rintro ⟨e⟩
  have h := e.fibers.discrete_observations observe (fiberPoint false) (fiberPoint true)
  let x : (total unitFamily).Elements :=
    (total unitFamily).elementsMk (Opposite.op ⟨0⟩) ⟨PUnit.unit,()⟩
  have impossible : false = true := congrArg (fun t => t.val x) h
  exact Bool.noConfusion impossible

def unitIdentityFiber : Family (total unitFamily) :=
  homotopyFiber (Functor.whiskerLeft (projection unitFamily).mapElements (𝟙 unitFamily))
    (generic unitFamily)

instance unitIdentityFiber_subsingleton (x : (total unitFamily).Elements) :
    Subsingleton (unitIdentityFiber.obj x) where
  allEq a b := by
    rcases a with ⟨⟨⟩,p⟩
    rcases b with ⟨⟨⟩,q⟩
    apply congrArg (Sigma.mk ())
    apply Subtype.ext
    apply PiElement.ext
    intro y f r
    exact Unit.ext _ _

def unitFiberCenter : Term unitIdentityFiber where
  val _ := ⟨(),⟨{ val := fun {_} _ _ => (), naturality := fun _ _ _ => rfl },
    fun {_} _ => ⟨rfl, Unit.ext _ _⟩⟩⟩
  property _ := rfl

/-- The equivalence interface admits a constructed contraction as a positive control. -/
def unitIdentityEquivalence : HomotopyEquivalence (𝟙 unitFamily) where
  fibers := {
    center := unitFiberCenter
    contraction := pathLam
      ((unitFiberCenter.reindex (projection unitIdentityFiber)).reindex
        (projection (interval (total unitIdentityFiber)))) rfl
      (by
        apply Term.ext
        intro x
        exact (unitIdentityFiber_subsingleton ((projection unitIdentityFiber).mapElements.obj x)).elim _ _) }

def constantIso {S T : Type} (e : S ≃ T) :
    constantFamily terminal.{0} S ≅ constantFamily terminal T :=
  NatIso.ofComponents (fun _ => e.toIso) (by intro x y f; rfl)

def booleanTransposition : Bool ≃ Bool where
  toFun := Bool.not
  invFun := Bool.not
  left_inv b := by cases b <;> rfl
  right_inv b := by cases b <;> rfl

def booleanIso : boolFamily ≅ boolFamily := constantIso booleanTransposition

/-- The positive Boolean client supplies a constructed native fiber contraction. -/
def booleanEquivalence : HomotopyEquivalence booleanIso.hom := HomotopyEquivalence.ofIso booleanIso

def successorIso : constantFamily terminal.{0} Int ≅ constantFamily terminal Int :=
  constantIso CubicalStateTransport.successor

def successorEquivalence : HomotopyEquivalence successorIso.hom := HomotopyEquivalence.ofIso successorIso

def predecessorEquivalence : HomotopyEquivalence successorIso.inv := HomotopyEquivalence.ofIso successorIso.symm

def ambientBoolean (b : Bool) : Term boolFamily where
  val _ := b
  property _ := rfl

def fullFaceBoolean (b : Bool) :
    Term (reindex boolFamily (restrictInclusion (Cofibration.top terminal.{0}))) :=
  (ambientBoolean b).reindex (restrictInclusion (Cofibration.top terminal.{0}))

/-- Contradictory full-face data cannot satisfy Glue introduction's compatibility premise. -/
theorem malformed_full_face :
    Term.map (𝟙 (reindex boolFamily (restrictInclusion (Cofibration.top terminal.{0}))))
      (fullFaceBoolean true) ≠
    (ambientBoolean false).reindex (restrictInclusion (Cofibration.top terminal.{0})) := by
  intro h
  let x := (restrictContext (Cofibration.top terminal.{0})).elementsMk (Opposite.op ⟨0⟩)
    ⟨PUnit.unit,rfl⟩
  have impossible : true = false := congrArg (fun t => t.val x) h
  exact Bool.noConfusion impossible


def booleanIntervalIndex : Term (constantFamily (total (interval terminal.{0})) Unit) where
  val _ := ()
  property _ := rfl

def booleanIntervalFilling : Filling (constantFamily (total (interval terminal.{0})) Bool) :=
  discreteFilling booleanIntervalIndex (fun _ => Bool)

theorem booleanIntervalFilling_lawful : booleanIntervalFilling.Lawful :=
  discreteFilling_lawful booleanIntervalIndex (fun _ => Bool)

/-- This uses the constructed transport-fiber contraction, not the isomorphism adapter. -/
noncomputable def booleanTransportEquivalence : HomotopyEquivalence (IntervalTransport.map booleanIntervalFilling) :=
  IntervalTransport.equivalence booleanIntervalFilling booleanIntervalFilling_lawful

theorem boolean_transport_identity : IntervalTransport.map booleanIntervalFilling = 𝟙 boolFamily := rfl

def constantIndex (Γ : Context.{0}) : Term (constantFamily Γ Unit) where
  val _ := ()
  property _ := rfl

def constantLocal (Γ : Context.{0}) (S : Type) : LocalFamily Γ :=
  LocalFamily.ofNative ⟨⟨constantFamily Γ S, discreteFilling (constantIndex Γ) (fun _ => S)⟩,
    discreteFilling_lawful (constantIndex Γ) (fun _ => S)⟩

/-- Different endpoint codes form a boundary system even without an equivalence.
This is deliberately not a path or a claim that every boundary extends. -/
def booleanUnitBoundary := CodeSystem.boundary
  (constantLocal terminal Bool).code (constantLocal terminal Unit).code

theorem boolean_boundary_zero :
    raisedSub (CodeSystem.boundaryZero terminal) ≫ booleanUnitBoundary =
      (constantLocal terminal Bool).code :=
  CodeSystem.boundary_zero _ _

theorem unit_boundary_one :
    raisedSub (CodeSystem.boundaryOne terminal) ≫ booleanUnitBoundary =
      (constantLocal terminal Unit).code :=
  CodeSystem.boundary_one _ _

/-- The constant Boolean box exercises a nonempty cap/tube intersection and
recovers the entire selected code on the assembled partial family. -/
theorem boolean_box_partial :
    (CodeSystem.Box.constant (Cofibration.top terminal.{0}) (constantLocal terminal Bool).code).partialCode =
      raisedSub (restrictInclusion (CodeSystem.Box.face (φ := Cofibration.top terminal.{0})) ≫
        projection (interval terminal)) ≫ (constantLocal terminal Bool).code :=
  CodeSystem.Box.constant_partial _

theorem incompatible_boolean_unit_cap :
    raisedSub (CodeSystem.tubeCap (Cofibration.top terminal.{0})) ≫
      (CodeSystem.Box.constant (Cofibration.top terminal.{0}) (constantLocal terminal Unit).code).tube ≠
    raisedSub (restrictInclusion (Cofibration.top terminal.{0})) ≫ (constantLocal terminal Bool).code := by
  intro h
  let I : Cubeᵒᵖ := Opposite.op ⟨0⟩
  let x : (raisedContext (restrictContext (Cofibration.top terminal.{0}))).obj I :=
    ⟨⟨PUnit.unit,rfl⟩⟩
  have hc := congrArg (fun a => (a.app I x).family.obj (representableGeneric I.unop)) h
  change Unit = Bool at hc
  have impossible : false = true := (Equiv.cast hc.symm).injective (Subsingleton.elim _ _)
  exact Bool.noConfusion impossible

/-- The constructed small-context filler recovers the supplied Boolean cap,
including its chosen filling structure encoded in the code. -/
theorem boolean_filled_cap :
    raisedSub (endpointSub terminal false) ≫
      (CodeSystem.Box.constant (Cofibration.top terminal.{0}) (constantLocal terminal Bool).code).fillCode =
      (constantLocal terminal Bool).code :=
  CodeSystem.Box.fillCode_cap _

/-- With the entire base face present, the constructed filler recovers the
whole supplied tube, not only the underlying Boolean carrier. -/
theorem boolean_filled_tube :
    raisedSub (restrictInclusion ((Cofibration.top terminal.{0}).reindex (projection (interval terminal)))) ≫
      (CodeSystem.Box.constant (Cofibration.top terminal.{0}) (constantLocal terminal Bool).code).fillCode =
    (CodeSystem.Box.constant (Cofibration.top terminal.{0}) (constantLocal terminal Bool).code).tube :=
  CodeSystem.Box.fillCode_tube _

end Examples.CubicalGlue
