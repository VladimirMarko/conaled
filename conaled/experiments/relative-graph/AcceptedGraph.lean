import ArtifactAudit
import PrimitiveLaws
import ClosedGraph

/-! Relative graph observations for the explicit declaration environment.
Checker acceptance remains an explicit equality in the model-existence theorem;
GraphChecks executes that equality check separately. -/
namespace AcceptedGraph
open ConLeche ConLeche.SetTheory ConLeche.SetModel
open GraphAdapter
universe w
variable {V : Type w} [SetTheory V]

/-- Exact signatures remain present after the two graph theorem records. -/
def records : PrimitiveLaws.Records GraphDeclarations.environment where
  eq := ⟨eqA, by rfl, by decide, rfl⟩
  and := ⟨GraphEnvironment.storedProposition andRaw, by rfl, by decide, rfl⟩
  andIntro := ⟨GraphEnvironment.storedProposition andIntroRaw, by rfl, by decide, rfl⟩
  andRec := ⟨GraphEnvironment.storedProposition andRecRaw, by rfl, by decide, rfl⟩
  existsForm := ⟨GraphEnvironment.storedProposition GraphEnvironment.existsRaw, by rfl, by decide, rfl⟩
  existsIntro := ⟨GraphEnvironment.storedProposition GraphEnvironment.existsIntroRaw, by rfl, by decide, rfl⟩
  existsRec := ⟨GraphEnvironment.storedProposition GraphEnvironment.existsRecRaw, by rfl, by decide, rfl⟩

noncomputable def primitives (m : Model V GraphDeclarations.environment)
    (u : Level) (φ : Name → Nat) : Primitives m u φ :=
  PrimitiveLaws.primitives m records u φ

/-- This uses the upstream relative model theorem, with acceptance visible. -/
theorem model_exists
    (accepted : Cached.checkDecls .verified [] GraphDeclarations.declarations =
      .ok GraphDeclarations.environment) : Nonempty (Model V GraphDeclarations.environment) :=
  ConLeche.model_exists V [] GraphDeclarations.declarations GraphDeclarations.environment accepted

variable (m : Model V GraphDeclarations.environment) (φ : Name → Nat)

/-- Formula observation now has no primitive-law premises. -/
theorem comparison (u : Level) (A B C F G : V)
    (hB : B ∈ˢ univ (Level.eval φ u)) (hC : C ∈ˢ univ (Level.eval φ u))
    (hf : ∀ a, a ∈ˢ A → app F a ∈ˢ B) (hg : ∀ b, b ∈ˢ B → app G b ∈ˢ C)
    (x : Member A) (z : Member C) (P Q : V)
    (hP : Denotes m.cval GraphDeclarations.environment φ (assignment x.val z.val A B C F G) (composite u) P)
    (hQ : Denotes m.cval GraphDeclarations.environment φ (assignment x.val z.val A B C F G) (result u) Q) :
    ((pt : V) ∈ˢ P ↔ ∃ y : Member B, y = arrow A B F hf x ∧ z = arrow B C G hg y) ∧
    ((pt : V) ∈ˢ Q ↔ z = arrow B C G hg (arrow A B F hf x)) :=
  graph_comparison (primitives m u φ) A B C F G hB hC hf hg x z P Q hP hQ

theorem formulaTruth (u : Level) (A B C F G : V)
    (hB : B ∈ˢ univ (Level.eval φ u)) (hC : C ∈ˢ univ (Level.eval φ u))
    (hf : ∀ a, a ∈ˢ A → app F a ∈ˢ B) (hg : ∀ b, b ∈ˢ B → app G b ∈ˢ C)
    (x : Member A) (z : Member C) (P Q : V)
    (hP : Denotes m.cval GraphDeclarations.environment φ (assignment x.val z.val A B C F G) (composite u) P)
    (hQ : Denotes m.cval GraphDeclarations.environment φ (assignment x.val z.val A B C F G) (result u) Q) :
    (pt : V) ∈ˢ P ↔ (pt : V) ∈ˢ Q :=
  graph_truth (primitives m u φ) A B C F G hB hC hf hg x z P Q hP hQ

include m
/-- Both implications are recovered from the stored closed theorem memberships.
The stronger carrier and function memberships discharge the full telescope. -/
theorem closedMembership (A B C F G x z : V)
    (hA : A ∈ˢ univ (Level.eval φ GraphDeclarations.carrierLevel))
    (hB : B ∈ˢ univ (Level.eval φ GraphDeclarations.carrierLevel))
    (hC : C ∈ˢ univ (Level.eval φ GraphDeclarations.carrierLevel))
    (hF : F ∈ˢ piV A (fun _ => B)) (hG : G ∈ˢ piV B (fun _ => C))
    (hx : x ∈ˢ A) (hz : z ∈ˢ C) :
    (∃ y, y ∈ˢ B ∧ y = app F x ∧ z = app G y) ↔ z = app G (app F x) := by
  constructor
  · exact ClosedGraph.forwardMembership (primitives m GraphDeclarations.carrierLevel φ)
      (by decide) A B C F G x z hA hB hC hF hG hx hz
  · exact ClosedGraph.backwardMembership (primitives m GraphDeclarations.carrierLevel φ)
      (by decide) A B C F G x z hA hB hC hF hG hx hz

/-- Composition with a third function, using the derived closed comparison
for both pairs. The intermediate function is built as a member of its Pi set. -/
theorem threeStep (A B C D F G H x w : V)
    (hA : A ∈ˢ univ (Level.eval φ GraphDeclarations.carrierLevel))
    (hB : B ∈ˢ univ (Level.eval φ GraphDeclarations.carrierLevel))
    (hC : C ∈ˢ univ (Level.eval φ GraphDeclarations.carrierLevel))
    (hD : D ∈ˢ univ (Level.eval φ GraphDeclarations.carrierLevel))
    (hF : F ∈ˢ piV A (fun _ => B)) (hG : G ∈ˢ piV B (fun _ => C))
    (hH : H ∈ˢ piV C (fun _ => D)) (hx : x ∈ˢ A) (hw : w ∈ˢ D) :
    (∃ y, y ∈ˢ B ∧ y = app F x ∧ ∃ z, z ∈ˢ C ∧ z = app G y ∧ w = app H z) ↔
      w = app H (app G (app F x)) := by
  let GH := lamV B (fun y => app H (app G y))
  have hGH : GH ∈ˢ piV B (fun _ => D) := lamV_mem
    (fun y hy => app_mem_piV (B := fun _ => D) hH (app_mem_piV (B := fun _ => C) hG hy))
    (fun _ _ => IsTy_of_mem_univ hD)
  have hinner (y : V) (hy : y ∈ˢ B) :
      (∃ z, z ∈ˢ C ∧ z = app G y ∧ w = app H z) ↔ w = app GH y := by
    rw [show app GH y = app H (app G y) from app_lamV hy]
    exact closedMembership m φ B C D G H y w hB hC hD hG hH hy hw
  have houter := closedMembership m φ A B D F GH x w hA hB hD hF hGH hx hw
  have hfx : app F x ∈ˢ B := app_mem_piV (B := fun _ => B) hF hx
  rw [show app GH (app F x) = app H (app G (app F x)) from app_lamV hfx] at houter
  apply Iff.trans ?_ houter
  constructor
  · rintro ⟨y, hy, he, hz⟩
    exact ⟨y, hy, he, (hinner y hy).mp hz⟩
  · rintro ⟨y, hy, he, hw⟩
    exact ⟨y, hy, he, (hinner y hy).mpr hw⟩

end AcceptedGraph

#audit_graph_module
