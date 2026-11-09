import AcceptedEmission
/-! Experimental #135 applications of the accepted actual emitted records.
The relative applications retain their explicit SetTheory and membership assumptions.
See [scope report](../../docs/research/relative-emitted-acceptance.md). -/
namespace EmittedApplications
open ConLeche ConLeche.SetTheory ConLeche.SetModel
open SquareKit.Internal EmissionSemantics EmittedComparison
universe w
variable {V : Type w} [SetTheory V]

theorem closed_graph (φ : Name → Nat) (A B C F G : V)
    (hA : A ∈ˢ univ (Level.eval φ carrierLevel))
    (hB : B ∈ˢ univ (Level.eval φ carrierLevel))
    (hC : C ∈ˢ univ (Level.eval φ carrierLevel))
    (hF : F ∈ˢ piV A (fun _ => B)) (hG : G ∈ˢ piV B (fun _ => C))
    (x : GraphAdapter.Member A) (z : GraphAdapter.Member C) :
    (∃ y : GraphAdapter.Member B, y.val = app F x.val ∧ z.val = app G y.val) ↔
      z.val = app G (app F x.val) := by
  let m := AcceptedEmission.model (V := V)
  have hf : ∀ a, a ∈ˢ A → app F a ∈ˢ B := fun _ h => app_mem_piV (B := fun _ => B) hF h
  have hg : ∀ b, b ∈ˢ B → app G b ∈ˢ C := fun _ h => app_mem_piV (B := fun _ => C) hG h
  let L := laws φ A B C F G hA hB hC hf hg
  have hp := formula_denotes (primitives m carrierLevel φ) (em := openModel) rfl
    (compatible m φ A B C F G x.val z.val) (objects_compatible m φ A B C F G L x z)
    GraphTarget.forwardDeclaration.premise _ premise_encoded
  have hq := formula_denotes (primitives m carrierLevel φ) (em := openModel) rfl
    (compatible m φ A B C F G x.val z.val) (objects_compatible m φ A B C F G L x z)
    GraphTarget.forwardDeclaration.conclusion _ conclusion_encoded
  have stored := EmittedClosed.closedTruth m φ A B C F G hA hB hC hF hG x z _ _ hp hq
  have comparison := environment_comparison m φ A B C F G hA hB hC hf hg x z _ _ hp hq
  exact comparison.1.symm.trans (stored.trans comparison.2)

/-- The accepted comparison is reusable for two consecutive graph pairs. -/
theorem three_step (φ : Name → Nat) (A B C D F G H : V)
    (hA : A ∈ˢ univ (Level.eval φ carrierLevel))
    (hB : B ∈ˢ univ (Level.eval φ carrierLevel))
    (hC : C ∈ˢ univ (Level.eval φ carrierLevel))
    (hD : D ∈ˢ univ (Level.eval φ carrierLevel))
    (hF : F ∈ˢ piV A (fun _ => B)) (hG : G ∈ˢ piV B (fun _ => C))
    (hH : H ∈ˢ piV C (fun _ => D)) (x : GraphAdapter.Member A) (z : GraphAdapter.Member D) :
    (∃ y : GraphAdapter.Member B, y.val = app F x.val ∧
      ∃ t : GraphAdapter.Member C, t.val = app G y.val ∧ z.val = app H t.val) ↔
      z.val = app H (app G (app F x.val)) := by
  let GH := lamV B (fun y => app H (app G y))
  have hGH : GH ∈ˢ piV B (fun _ => D) := lamV_mem
    (fun y hy => app_mem_piV (B := fun _ => D) hH (app_mem_piV (B := fun _ => C) hG hy))
    (fun _ _ => IsTy_of_mem_univ hD)
  have hinner (y : GraphAdapter.Member B) :
      (∃ t : GraphAdapter.Member C, t.val = app G y.val ∧ z.val = app H t.val) ↔
        z.val = app GH y.val := by
    rw [show app GH y.val = app H (app G y.val) from app_lamV y.property]
    exact closed_graph φ B C D G H hB hC hD hG hH y z
  have outer := closed_graph φ A B D F GH hA hB hD hF hGH x z
  have hfx : app F x.val ∈ˢ B := app_mem_piV (B := fun _ => B) hF x.property
  rw [show app GH (app F x.val) = app H (app G (app F x.val)) from app_lamV hfx] at outer
  apply Iff.trans ?_ outer
  constructor
  · rintro ⟨y, hy, rest⟩
    exact ⟨y, hy, (hinner y).mp rest⟩
  · rintro ⟨y, hy, rest⟩
    exact ⟨y, hy, (hinner y).mpr rest⟩

/-- A concrete source/target specialization uses the same generated declaration family. -/
example : (∃ y : Nat, y = (3 + 1) ∧ 8 = y * 2) ↔ 8 = (3 + 1) * 2 :=
  GraphTarget.graph_equivalence (fun n : Nat => n + 1) (fun n => n * 2) 3 8

example : GraphEmissionPure.ArtifactTyped (GraphEmissionPure.emit GraphTarget.forwardDeclaration) ∧
    GraphEmissionPure.ArtifactDenotes.{0} (GraphEmissionPure.emit GraphTarget.forwardDeclaration)
      (GraphTarget.Declaration.denote.{0} GraphTarget.forwardDeclaration) :=
  ⟨GraphEmissionPure.emit_typed _, GraphEmissionPure.emit_denotes _⟩

end EmittedApplications
#audit_graph_module
