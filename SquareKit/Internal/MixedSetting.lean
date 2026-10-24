import SquareKit.Internal.FiniteSetting
import SquareKit.Internal.InterpretationRoutes

/-! Experimental mixed substitution square for Set families. The pullback
retains its base point and equality to the original projection. This is not a
geometric-morphism pseudopullback or a slice-topos classifier. -/
namespace SquareKit.Internal.FiniteSetting
universe u v w

/-- Form the original family, then pull its projection back along σ. -/
structure Pullback {X : Type u} {Y : Type v} (T : Presentation X) (σ : Y → X) where
  base : Y
  original : Total T
  over : original.1 = σ base

/-- Compare with forming the substituted presentation's family over Y. -/
def pullbackEquiv {X : Type u} {Y : Type v} (T : Presentation X) (σ : Y → X) :
    Pullback T σ ≃ Total (T.subst σ) where
  toFun a := ⟨a.base, (show Fiber T (σ a.base) from a.over ▸ a.original.2)⟩
  invFun a := ⟨a.1, totalMap T σ a, rfl⟩
  left_inv := by rintro ⟨y, ⟨x, a⟩, h⟩; cases h; rfl
  right_inv := by intro a; rfl

@[simp] theorem pullback_projection {X : Type u} {Y : Type v}
    (T : Presentation X) (σ : Y → X) (a : Pullback T σ) :
    (pullbackEquiv T σ a).1 = a.base := rfl

@[simp] theorem pullback_original {X : Type u} {Y : Type v}
    (T : Presentation X) (σ : Y → X) (a : Pullback T σ) :
    totalMap T σ (pullbackEquiv T σ a) = a.original := by
  rcases a with ⟨y, ⟨x, a⟩, h⟩; cases h; rfl

/-- Both routes carry the same generic section, including its dependent type. -/
theorem pullback_genericSection {X : Type u} {Y : Type v}
    (T : Presentation X) (σ : Y → X) :
    (genericSection (T.subst σ)).subst (pullbackEquiv T σ) =
      (fun a : Pullback T σ => (show Fiber T (σ a.base) from a.over ▸ a.original.2)) := rfl

/-- Transport the generic model from the original total space to the pullback.
The equality over the base is needed before its predicates have the right type. -/
def pullbackModel {X : Type u} {Y : Type v}
    (T : Presentation X) (σ : Y → X) :
    Model ((T.subst σ).subst (fun a : Pullback T σ => a.base)) :=
  Section.toModel (T := (T.subst σ).subst (fun a : Pullback T σ => a.base))
    (fun a => (pullbackEquiv T σ a).2)

theorem pullback_genericModel {X : Type u} {Y : Type v}
    (T : Presentation X) (σ : Y → X) :
    (genericModel (T.subst σ)).subst (pullbackEquiv T σ) = pullbackModel T σ := rfl

/-- Compare the original generic predicates, not just the final carrier. -/
theorem pullback_partition {X : Type u} {Y : Type v}
    (T : Presentation X) (σ : Y → X) (a : Pullback T σ) :
    ((pullbackModel T σ).P a ↔ (genericModel T).P a.original) ∧
    ((pullbackModel T σ).Q a ↔ (genericModel T).Q a.original) := by
  rcases a with ⟨y, ⟨x, a⟩, h⟩; cases h; exact ⟨Iff.rfl, Iff.rfl⟩

def pullbackSection {X : Type u} {Y : Type v} {T : Presentation X}
    (s : Section T) (σ : Y → X) (y : Y) : Pullback T σ :=
  ⟨y, s.graph (σ y), rfl⟩

theorem pullback_section {X : Type u} {Y : Type v} {T : Presentation X}
    (s : Section T) (σ : Y → X) :
    pullbackEquiv T σ ∘ pullbackSection s σ = (s.subst σ).graph := rfl

/-- Every model, not only the generic model, has the same corresponding section. -/
theorem pullback_correspondence {X : Type u} {Y : Type v} {T : Presentation X}
    (M : Model T) (σ : Y → X) :
    pullbackEquiv T σ ∘ pullbackSection (modelSectionEquiv T M) σ =
      (modelSectionEquiv (T.subst σ) (M.subst σ)).graph := rfl

theorem pullback_model_recovery {X : Type u} {Y : Type v} {T : Presentation X}
    (M : Model T) (σ : Y → X) :
    (pullbackModel T σ).subst (pullbackSection M.toSection σ) = M.subst σ := by
  exact (M.subst σ).toSection_toModel

/-- The identity comparison retains the original dependent pair. -/
theorem pullback_identity {X : Type u} (T : Presentation X) (a : Pullback T id) :
    pullbackEquiv T id a = a.original := pullback_original T id a

/-- Rebase a pullback point twice. Its equality certificate is composed explicitly. -/
def pullbackRebase {X : Type u} {Y : Type v} {Z : Type w}
    (T : Presentation X) (σ : Y → X) (τ : Z → Y)
    (a : Pullback (T.subst σ) τ) : Pullback T (σ ∘ τ) :=
  ⟨a.base, totalMap T σ a.original, congrArg σ a.over⟩

/-- Comparison after two substitutions equals comparison after their composite;
the equality compares dependent pairs over Z, not unindexed fibre tags. -/
theorem pullback_composition {X : Type u} {Y : Type v} {Z : Type w}
    (T : Presentation X) (σ : Y → X) (τ : Z → Y)
    (a : Pullback (T.subst σ) τ) :
    pullbackEquiv T (σ ∘ τ) (pullbackRebase T σ τ a) =
      pullbackEquiv (T.subst σ) τ a := by
  rcases a with ⟨z, ⟨y, a⟩, h⟩; cases h; rfl

theorem pullback_model_composition {X : Type u} {Y : Type v} {Z : Type w}
    (T : Presentation X) (σ : Y → X) (τ : Z → Y) :
    (pullbackModel T (σ ∘ τ)).subst (pullbackRebase T σ τ) =
      pullbackModel (T.subst σ) τ := by
  apply Model.ext <;> funext a <;>
    rcases a with ⟨z, ⟨y, a⟩, h⟩ <;> cases h <;> rfl

end SquareKit.Internal.FiniteSetting

namespace SquareKit.Internal.MixedSetting
open FiniteSetting
open InterpretationRoutes Graph

/-- Observe the generic left partition after forming the substituted family. -/
def formed {X Y : Type} (T : Presentation X) (σ : Y → X) :
    Interpretation Arrow :=
  model (id : Total (T.subst σ) → Total (T.subst σ)) (fun a => a.2.isLeft)

/-- Observe the original generic partition after pulling the total family back. -/
def pulled {X Y : Type} (T : Presentation X) (σ : Y → X) :
    Interpretation Arrow :=
  model (pullbackEquiv T σ).symm (fun a => a.original.2.isLeft)

/-- The same two source derivations run on each side. The witness carriers are
respectively the constructed total family and the pullback of the old family. -/
theorem graph_routes {X Y : Type} (T : Presentation X) (σ : Y → X)
    (a : Total (T.subst σ)) (b : Bool) :
    (formula (fun _ : Unit => pulled T σ) (composite Arrow.first Arrow.second) ()
      (environment (pullbackEquiv T σ).symm (fun p => p.original.2.isLeft) a b) ↔
      b = a.2.isLeft) ∧
    (formula (fun _ : Unit => formed T σ) (composite Arrow.first Arrow.second) ()
      (environment id (fun p : Total (T.subst σ) => p.2.isLeft) a b) ↔
      b = a.2.isLeft) :=
  ⟨graph (fun _ : Unit => pulled T σ) Arrow.first Arrow.second () _,
   graph (fun _ : Unit => formed T σ) Arrow.first Arrow.second () _⟩

theorem graph_comparison {X Y : Type} (T : Presentation X) (σ : Y → X)
    (a : Total (T.subst σ)) (b : Bool) :
    (∃ p : Pullback T σ, p = (pullbackEquiv T σ).symm a ∧
      b = p.original.2.isLeft) ↔
    (∃ c : Total (T.subst σ), c = a ∧ b = c.2.isLeft) :=
  (graph_routes T σ a b).1.trans (graph_routes T σ a b).2.symm

/-- The observed value is the generic predicate on both sides. -/
theorem graph_generic {X Y : Type} (T : Presentation X) (σ : Y → X)
    (a : Total (T.subst σ)) :
    (∃ p : Pullback T σ, p = (pullbackEquiv T σ).symm a ∧
      true = p.original.2.isLeft) ↔ (genericModel (T.subst σ)).P a := by
  exact (graph_routes T σ a true).1.trans (eq_comm)

/-- Ambient selection is on the external component index. The parameter maps
σ b act within each component and may have different domains and codomains. -/
def pairedFormed {X Y : Bool → Type} (T : ∀ b, Presentation (X b))
    (σ : ∀ b, Y b → X b) : Pair Arrow NoRelations := fun b => formed (T b) (σ b)

def pairedPulled {X Y : Bool → Type} (T : ∀ b, Presentation (X b))
    (σ : ∀ b, Y b → X b) : Pair Arrow NoRelations := fun b => pulled (T b) (σ b)

/-- Construct componentwise then project, or project presentation and parameter
map first then construct: equality retains the full graph interpretation. -/
theorem ambient_projection {X Y : Bool → Type} (T : ∀ b, Presentation (X b))
    (σ : ∀ b, Y b → X b) (b : Bool) :
    project (pairedFormed T σ) b = formed (T b) (σ b) ∧
    project (pairedPulled T σ) b = pulled (T b) (σ b) := ⟨rfl, rfl⟩

theorem ambient_swap {X Y : Bool → Type} (T : ∀ b, Presentation (X b))
    (σ : ∀ b, Y b → X b) (b : Bool) :
    project (swap (pairedFormed T σ)) (!b) = formed (T b) (σ b) ∧
    project (swap (pairedPulled T σ)) (!b) = pulled (T b) (σ b) :=
  ⟨swap_project _ b, swap_project _ b⟩

/-- The paired ambient route preserves the source derivation after formation. -/
theorem ambient_graph {X Y : Bool → Type} (T : ∀ b, Presentation (X b))
    (σ : ∀ b, Y b → X b) :
    InterpretationRoutes.Valid (reindex (swap (pairedPulled T σ)) (fun _ : Unit => true))
      (composite Arrow.first Arrow.second) (result Arrow.first Arrow.second) :=
  preserve _ _ (derivation _ (Graph.forward Arrow.first Arrow.second))

/-- Typed syntax substitution is separate again from parameter substitution.
It includes the existential binder in the graph formula. -/
theorem graph_substitution {X Y : Bool → Type} (T : ∀ b, Presentation (X b))
    (σ : ∀ b, Y b → X b) (θ : Sub Arrow [.input, .output] Δ)
    (ρ : Context (pairedPulled T σ) Δ false) :
    formula (reindex (swap (pairedPulled T σ)) (fun _ : Unit => true))
      ((composite Arrow.first Arrow.second).subst θ) () ρ ↔
    formula (pairedPulled T σ) (composite Arrow.first Arrow.second) false
      (fun x => term (pairedPulled T σ) (θ x) false ρ) :=
  substitution (swap (pairedPulled T σ)) (fun _ : Unit => true) _ θ () ρ
end SquareKit.Internal.MixedSetting
