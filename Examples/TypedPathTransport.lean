import Examples.GroupoidTransport
import SquareKit.Internal.PathTransport.Authoring
import SquareKit.Internal.PathTransport.GroupoidSoundness
import SquareKit.Internal.PathTransport.JNaturality

/-! Checked applications of the typed identity fragment to ordinary groupoids. -/
noncomputable section
namespace Examples.TypedPathTransport
open CategoryTheory
open SquareKit.Internal.PathTransport
open Typed
universe u v w

/-- Different object, arrow and primitive-fiber universes use the same source
rules. The explicit universe lift preserves arrows as data. -/
example (C : Type u) [Groupoid.{v} C] (B : C ⥤ Type w) :
    Model.{max u v w + 1} := GroupoidModel.Instance.universeModel C B

example (C : Type u) [Groupoid.{v} C] {x y : C} :
    ((AsSmall.up : C ⥤ AsSmall.{w} C).obj x ⟶
      (AsSmall.up : C ⥤ AsSmall.{w} C).obj y) ≃ (x ⟶ y) := Equiv.ulift

/-- Every generated source term conversion has equal interpreted sections in
this constructed model, including the contextual reflexive computation rule. -/
theorem conversion_in_groupoids (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u)
    {Γ γ A a t ξ s ν}
    (ht : TmDeriv Γ γ A a t ξ) (hs : TmDeriv Γ γ A a s ν)
    (e : TmEqDeriv Γ γ A a t ξ s ν) :
    interpretTm (GroupoidModel.Instance.fullModel C B) ht =
      interpretTm (GroupoidModel.Instance.fullModel C B) hs := by
  rw [interpretTm_agrees, interpretTm_agrees, termSound e]

/-- Reindexing the actual two-comprehension path context agrees with the
structural map used in the model's source rules. -/
example (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u)
    {Γ Δ : Grpd.{u,u}} (A : Γ ⥤ Grpd.{u,u}) (x : GroupoidModel.Section A)
    (σ : Δ ⥤ Γ) :
    (StructuralModel.pathSub (GroupoidModel.Instance.structuralModel C B) A ⟨x⟩ ⟨σ⟩).down =
      GroupoidModel.PathComparison.substitution A x σ := rfl

/-- The retained named J derivation computes through this same constructed
model, with its z/q/b telescope and dependent identity motive. -/
example (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u) :
    HEq (interpretTm (GroupoidModel.Instance.fullModel C B)
      Authoring.NamedCaller.reflexiveApplication)
      (Authoring.NamedCaller.pathInductionGeneralizingZQB.motive.branchCode
        (GroupoidModel.Instance.fullModel C B)) :=
  Authoring.NamedCaller.interpreted_beta (GroupoidModel.Instance.fullModel C B)

/-- Rebuilding the same named source J after weakening agrees with substitution
in the ordinary-groupoid interpretation. -/
example (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u) :
    interpretTm (GroupoidModel.Instance.fullModel C B) Authoring.NamedCaller.substitutedOriginal =
      interpretTm (GroupoidModel.Instance.fullModel C B)
        Authoring.NamedCaller.weakenedCommand.genericTerm :=
  Authoring.NamedCaller.rebuilt_interpretation (GroupoidModel.Instance.fullModel C B)

/-- Beta conversion remains available inside another J, not only at its root. -/
example (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u) :
    interpretTm (GroupoidModel.Instance.fullModel C B)
      Authoring.CongruenceCaller.nestedLeft =
    interpretTm (GroupoidModel.Instance.fullModel C B)
      Authoring.CongruenceCaller.nestedRight :=
  Authoring.CongruenceCaller.nestedBeta_sound (GroupoidModel.Instance.fullModel C B)

/-- The endpoint-instantiated outer J consumes the same inner conversion. -/
example (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u) :
    interpretTm (GroupoidModel.Instance.fullModel C B)
      Authoring.CongruenceCaller.outerLeft.reflexiveTerm =
    interpretTm (GroupoidModel.Instance.fullModel C B)
      Authoring.CongruenceCaller.outerRight.reflexiveTerm :=
  Authoring.CongruenceCaller.nestedAtBeta_sound (GroupoidModel.Instance.fullModel C B)

/-- A beta conversion in the identity motive transports the existing branch
through generated type conversion before rebuilding J. -/
example (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u) :
    HEq (interpretTm (GroupoidModel.Instance.fullModel C B)
      Authoring.CongruenceCaller.changedMotiveLeft)
      (interpretTm (GroupoidModel.Instance.fullModel C B)
        Authoring.CongruenceCaller.changedMotiveRight) :=
  Authoring.CongruenceCaller.motiveBeta_sound (GroupoidModel.Instance.fullModel C B)

/-- A simultaneous substitution's later identity proof depends on the earlier
component changed by beta conversion. -/
example (C : Type u) [Groupoid.{u} C] (B : C ⥤ Type u) :
    interpretSub (GroupoidModel.Instance.fullModel C B)
      Authoring.CongruenceCaller.dependentPairedLeft =
    interpretSub (GroupoidModel.Instance.fullModel C B)
      Authoring.CongruenceCaller.dependentPairedRight :=
  Authoring.CongruenceCaller.dependentPairedBeta_sound (GroupoidModel.Instance.fullModel C B)

section Labels
open Examples.GroupoidTransport
local notation "M" => GroupoidModel.Instance.fullModel C4 ineffective
def loopSection : GroupoidModel.Section (GroupoidModel.constant (Γ := C4) C4) :=
  GroupoidModel.constantSection (𝟭 C4)
/-- A nonidentity label in the full model with an ineffective primitive family. -/
def newLabel : ((M).identity (Γ := Grpd.of C4) (GroupoidModel.constant (Γ := C4) C4)
    ⟨loopSection⟩ ⟨loopSection⟩).obj point := Discrete.mk (label 1)
example : newLabel ≠ ((M).reflexivity (Γ := Grpd.of C4) (GroupoidModel.constant (Γ := C4) C4) ⟨loopSection⟩).down.obj point := by
  intro h
  have h' := congrArg (GroupoidModel.identityFiberEquiv _ loopSection loopSection point) h
  change Multiplicative.ofAdd (1 : ZMod 4) = 𝟙 point at h'
  exact (by decide : Multiplicative.ofAdd (1 : ZMod 4) ≠ 𝟙 point) h'
end Labels

end Examples.TypedPathTransport
