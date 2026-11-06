import Examples.GroupoidTransport
import Examples.TwoFamilyModelData
import Examples.TwoFamilyFrozenMemo
import SquareKit.Internal.PathTransport.TwoFamilyFullModel
import SquareKit.Internal.PathTransport.TwoIdentityTransport
/-! The ordinary C4 path action is retained by the same full model used for
the nonzero higher witness. An explicit fiber equivalence commutes with the
existing faithful action, and the unchanged frozen client retains its pair
and certificate action under both substitutions. -/
noncomputable section
namespace Examples.TwoFamilyLowerPath
open CategoryTheory Bicategory SquareKit
open SquareKit.Internal.PathTransport HigherInterpretation
open Examples.GroupoidTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

def cyclicContext : Context where
  carrier := LocallyDiscrete C4
  bicategory := inferInstance
  strict := inferInstance
  groupoid := by
    refine ⟨fun f => ?_⟩
    exact ⟨⟨⟨inv f.as⟩, Discrete.ext (IsIso.hom_inv_id f.as), Discrete.ext (IsIso.inv_hom_id f.as)⟩⟩
  locallyGroupoid := by
    intro a b
    change IsGroupoid (Discrete (a.as ⟶ b.as))
    infer_instance
open Examples.TwoFamilyModelData
abbrev lowerModel := fullModel integerContext integerContext
abbrev emptyA := Family.constant Context.empty cyclicContext

def fixedLift : StrictPseudofunctor Context.empty emptyA.total :=
  StrictPseudofunctor.mk'' {
    obj := fun γ => ⟨γ, ⟨point⟩⟩
    map := fun p => ⟨p, ⟨𝟙 point⟩⟩
    map₂ := fun α => ⟨α, 𝟙 _⟩
  }
def fixed : TwoFamily.Section emptyA.data where
  lift := fixedLift
  over := strictFunctorData_ext rfl
abbrev emptyB : Family emptyA.total := Family.identity
  (emptyA.reindex (TwoFamily.projectionHigher emptyA.data))
  (fixed.reindex emptyA.data (TwoFamily.projectionHigher emptyA.data))
  (TwoFamily.variableSection emptyA.data)
def basePoint : emptyA.total := ⟨⟨⟨PUnit.unit⟩⟩, ⟨point⟩⟩
def baseArrow (n : ZMod 4) : basePoint ⟶ basePoint := ⟨𝟙 _,⟨label n⟩⟩
def pathPoint (n : ZMod 4) : emptyB.data.obj basePoint := ⟨⟨label n⟩⟩
abbrev fiberA : Family emptyA.total := emptyA.reindex (TwoFamily.projectionHigher emptyA.data)
abbrev fixedOver := fixed.reindex emptyA.data (TwoFamily.projectionHigher emptyA.data)
abbrev variableOver := TwoFamily.variableSection emptyA.data

theorem fixed_normal (n : ZMod 4) :
    ((fixedOver.normalMap fiberA.data (baseArrow n)).fiber).as = label 0 := by
  have hn := congr_arg_heq (fun s : TwoFamily.Section fiberA.data => (s.lift.map (baseArrow n)).fiber)
    (fixedOver.normalized_eq fiberA.data)
  have hr := fixed.reindex_map_fiber emptyA.data (TwoFamily.projectionHigher emptyA.data) (baseArrow n)
  exact congrArg Discrete.as (eq_of_heq (hn.trans hr))

theorem variable_normal (n : ZMod 4) :
    ((variableOver.normalMap fiberA.data (baseArrow n)).fiber).as = label n := by
  have hn := congr_arg_heq (fun s : TwoFamily.Section fiberA.data => (s.lift.map (baseArrow n)).fiber)
    (variableOver.normalized_eq fiberA.data)
  exact congrArg Discrete.as (eq_of_heq hn)

theorem fixed_inverse_normal (n : ZMod 4) :
    (inv (fixedOver.normalMap fiberA.data (baseArrow n)).fiber).as = label 0 := by
  have h := congrArg Discrete.as (IsIso.hom_inv_id (fixedOver.normalMap fiberA.data (baseArrow n)).fiber)
  change (show Multiplicative (ZMod 4) from (inv (fixedOver.normalMap fiberA.data (baseArrow n)).fiber).as) *
    (show Multiplicative (ZMod 4) from (fixedOver.normalMap fiberA.data (baseArrow n)).fiber.as) = 1 at h
  rw [fixed_normal] at h
  change _ * 1 = 1 at h
  change (show Multiplicative (ZMod 4) from (inv (fixedOver.normalMap fiberA.data (baseArrow n)).fiber).as) = 1
  exact (mul_one _).symm.trans h

theorem faithful_transport (n k : ZMod 4) :
    ((emptyB.data.map (baseArrow n)).obj (pathPoint k)).as.as =
      label (faithful.map (label n) k) := by
  change ((inv ((fixedOver.normalMap fiberA.data (baseArrow n)).fiber)) ≫
    (show (⟨point⟩ : LocallyDiscrete C4) ⟶ ⟨point⟩ from ⟨label k⟩) ≫
    (variableOver.normalMap fiberA.data (baseArrow n)).fiber).as = _
  change ((show Multiplicative (ZMod 4) from (variableOver.normalMap fiberA.data (baseArrow n)).fiber.as) *
    Multiplicative.ofAdd k) * (show Multiplicative (ZMod 4) from (inv (fixedOver.normalMap fiberA.data (baseArrow n)).fiber).as) = _
  rw [variable_normal]
  rw [fixed_inverse_normal]
  change Multiplicative.ofAdd ((n + k) + 0) = Multiplicative.ofAdd (n + k)
  exact congrArg Multiplicative.ofAdd (add_zero (n + k))

-- The same full model admits this ordinary groupoid family.
def client := Examples.TwoFamilyFrozenMemo.client integerContext integerContext emptyA emptyB
def pair := Examples.TwoFamilyFrozenMemo.pair integerContext integerContext emptyA emptyB
-- Infer the large source evaluation propositions once.
set_option linter.defProp false
def pair_twice := Examples.TwoFamilyFrozenMemo.pair_twice integerContext integerContext emptyA emptyB
def certificate_twice := Examples.FrozenMemoSignature.certificate_twice lowerModel emptyA emptyB
def action_twice := Examples.FrozenMemoSignature.dependentAction_twice lowerModel emptyA emptyB

theorem path_labels_injective : Function.Injective pathPoint := by
  intro m n h
  exact labels_injective (congrArg (fun p => p.as.as) h)



def ordinaryFiberEquiv : ZMod 4 ≃ emptyB.data.obj basePoint where
  toFun := pathPoint
  invFun := fun t => Multiplicative.toAdd t.as.as
  left_inv _ := rfl
  right_inv t := by cases t; rfl

theorem ordinary_transport_preserved (n k : ZMod 4) :
    (emptyB.data.map (baseArrow n)).obj (ordinaryFiberEquiv k) =
      ordinaryFiberEquiv (faithful.map (label n) k) := by
  apply LocallyDiscrete.ext
  apply Discrete.ext
  exact faithful_transport n k

theorem transport_moves_zero :
    (emptyB.data.map (baseArrow 1)).obj (pathPoint 0) ≠ pathPoint 0 := by
  intro h
  have hv := (faithful_transport 1 0).symm.trans (congrArg (fun t => t.as.as) h)
  exact (by decide : (1 : ZMod 4) ≠ 0) (labels_injective hv)

theorem no_extra_second_identities {m n : ZMod 4} (α β : pathPoint m ⟶ pathPoint n) :
    α = β := by
  apply Discrete.ext
  exact @Subsingleton.elim ((Discrete.mk (Multiplicative.ofAdd m)) ⟶ Discrete.mk (Multiplicative.ofAdd n)) inferInstance α.as β.as

theorem path_arrow_labels {m n : ZMod 4} (α : pathPoint m ⟶ pathPoint n) : m = n :=
  labels_injective (Discrete.eq_of_hom (show Discrete.mk (label m) ⟶ Discrete.mk (label n) from α.as))

theorem source_path_family : emptyB = lowerModel.identity fiberA ⟨fixedOver⟩ ⟨variableOver⟩ := rfl
end Examples.TwoFamilyLowerPath
