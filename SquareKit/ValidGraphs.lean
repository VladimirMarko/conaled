import Mathlib.Logic.Relation

/-! Valid graphs connect separate invariants and observations to the existing
function relator and existential relation composition. The concrete and model
types may live in independent universes. -/

set_option autoImplicit false
set_option warningAsError true

namespace SquareKit.ValidGraphs
universe u v w z

/-- The graph of an observation, restricted to valid concrete inputs. -/
def validGraph {C : Type u} {A : Type v}
    (I : C → Prop) (decode : C → A) : C → A → Prop :=
  fun c a => I c ∧ decode c = a

/-- Preserving a valid graph requires both output validity and the decoder
equation, only on valid concrete inputs. -/
theorem liftFun_iff {C : Type u} {A : Type v} {D : Type w} {B : Type z}
    (I : C → Prop) (decode : C → A)
    (J : D → Prop) (decode' : D → B)
    (impl : C → D) (spec : A → B) :
    Relator.LiftFun (validGraph I decode) (validGraph J decode') impl spec ↔
      ∀ c, I c → J (impl c) ∧ decode' (impl c) = spec (decode c) := by
  constructor
  · intro h c hc
    exact h ⟨hc, rfl⟩
  · intro h c a hca
    rcases hca with ⟨hc, hca⟩
    exact ⟨(h c hc).1, (h c hc).2.trans (congrArg spec hca)⟩

/-- Existential composition retains the intermediate validity premise. -/
theorem comp_iff {C : Type u} {A : Type v} {B : Type w}
    (I : C → Prop) (decode : C → A)
    (J : A → Prop) (decode' : A → B) (c : C) (b : B) :
    Relation.Comp (validGraph I decode) (validGraph J decode') c b ↔
      (I c ∧ J (decode c)) ∧ decode' (decode c) = b := by
  constructor
  · rintro ⟨a, ⟨hc, hca⟩, ⟨ha, hab⟩⟩
    subst a
    exact ⟨⟨hc, ha⟩, hab⟩
  · rintro ⟨⟨hc, ha⟩, hab⟩
    exact ⟨decode c, ⟨hc, rfl⟩, ⟨ha, hab⟩⟩

end SquareKit.ValidGraphs
