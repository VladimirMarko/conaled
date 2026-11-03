import SquareKit.Internal.MixedSetting
import Examples.FiniteSetting
import Examples.BranchingGraphTransport

/-! The varying family is exchanged by Boolean negation. The graph observes
the original generic partition, with the same source proof along both routes. -/
namespace Examples.MixedSetting
open SquareKit.Internal
open SquareKit.Internal.FiniteSetting SquareKit.Internal.MixedSetting
open Examples.FiniteSetting
open InterpretationRoutes Graph

def leftPoint : Total (varying.subst Bool.not) := ⟨true, .inl ⟨rfl⟩⟩
def rightPoint : Total (varying.subst Bool.not) := ⟨false, .inr ()⟩

/-- At the new true point, the original false fibre allows the left choice. -/
theorem exchanged_left :
    ((pullbackEquiv varying Bool.not).symm leftPoint).original =
      (⟨false, .inl ⟨rfl⟩⟩ : Total varying) := rfl

theorem exchanged_right :
    ((pullbackEquiv varying Bool.not).symm rightPoint).original =
      (⟨true, .inr ()⟩ : Total varying) := rfl

theorem varying_graph :
    (∃ p : Pullback varying Bool.not,
      p = (pullbackEquiv varying Bool.not).symm leftPoint ∧ true = p.original.2.isLeft) ∧
    (∃ c : Total (varying.subst Bool.not), c = rightPoint ∧ false = c.2.isLeft) :=
  ⟨(graph_routes varying Bool.not leftPoint true).1.mpr rfl,
   (graph_routes varying Bool.not rightPoint false).2.mpr rfl⟩

theorem varying_partition :
    (pullbackModel varying Bool.not).P ((pullbackEquiv varying Bool.not).symm leftPoint) :=
  (pullback_partition varying Bool.not _).1.mpr rfl

theorem varying_correspondence_square :
    pullbackEquiv varying Bool.not ∘ pullbackSection varyingModel.toSection Bool.not =
      (varyingSection.subst Bool.not).graph := by
  change pullbackEquiv varying Bool.not ∘
    pullbackSection (modelSectionEquiv varying varyingModel) Bool.not = _
  rw [pullback_correspondence]
  change (varyingModel.toSection.subst Bool.not).graph = _
  rw [show varyingModel.toSection = varyingSection from varying_correspondence]

theorem varying_model_recovered :
    (pullbackModel varying Bool.not).subst (pullbackSection varyingModel.toSection Bool.not) =
      varyingModel.subst Bool.not := pullback_model_recovery _ _

/-- A second exchange is checked at the dependent-pair comparison, not only tags. -/
theorem twice_exchange (a : Pullback (varying.subst Bool.not) Bool.not) :
    pullbackEquiv varying (Bool.not ∘ Bool.not)
      (pullbackRebase varying Bool.not Bool.not a) =
    pullbackEquiv (varying.subst Bool.not) Bool.not a :=
  pullback_composition _ _ _ _

def presentations : Bool → Presentation Bool
  | false => varying
  | true => noneAllowed Bool

def parameters (_ : Bool) : Bool → Bool := Bool.not

/-- Both ambient paths select the varying component, after the parameter
substitution has exchanged its fibres. The other component has no left fibre. -/
theorem swapped_generic_graph :
    formula (reindex (swap (pairedPulled presentations parameters)) (fun _ : Unit => true))
      (composite Arrow.first Arrow.second) ()
      (environment (pullbackEquiv varying Bool.not).symm
        (fun p => p.original.2.isLeft) leftPoint true) := by
  exact (graph_routes varying Bool.not leftPoint true).1.mpr rfl

/-- Reuse the binder-sensitive syntax substitution on the constructed family. -/
theorem substituted_graph :
    formula (reindex (swap (pairedPulled presentations parameters)) (fun _ : Unit => true))
      ((composite Arrow.first Arrow.second).subst BranchingGraphTransport.duplicate) ()
      (fun {s} i => match s, i with
        | _, .zero => leftPoint
        | _, .succ .zero => rightPoint
        | _, .succ (.succ .zero) => true) := by
  apply (graph_substitution presentations parameters BranchingGraphTransport.duplicate _).mpr
  exact (graph_routes varying Bool.not leftPoint true).1.mpr rfl

/-- Ambient projection still has no inverse/reflection contract. -/
theorem no_reflection : BranchingGraphTransport.arrow₀ false = BranchingGraphTransport.arrow₁ false ∧
    BranchingGraphTransport.arrow₀ ≠ BranchingGraphTransport.arrow₁ :=
  BranchingGraphTransport.projection_does_not_reflect
end Examples.MixedSetting
