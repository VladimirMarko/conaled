import ArtifactAudit
import GraphDeclarations

namespace ClosedGraph
open ConLeche ConLeche.SetTheory ConLeche.SetModel
universe w
variable {V : Type w} [SetTheory V] {env : Env}
variable {m : Model V env} {φ : LevelParam → Nat}

theorem specialize {ρ : Nat → V} {dom body : Expr} {T f A a : V}
    (ht : Denotes m.cval env φ ρ (.forallE dom body) T) (hf : f ∈ˢ T)
    (hd : Denotes m.cval env φ ρ dom A) (ha : a ∈ˢ A) :
    ∃ B, Denotes m.cval env φ (push a ρ) body B ∧ app f a ∈ˢ B := by
  cases ht with
  | pi hA hB =>
    obtain rfl := Denotes_functional hd hA
    exact ⟨_, hB a ha, app_mem_piV hf ha⟩

/-- The seven binders shared by the two closed theorem statements. -/
def telescope (body : Expr) : Expr :=
  .forallE (.sort GraphDeclarations.carrierLevel) <|
  .forallE (.sort GraphDeclarations.carrierLevel) <|
  .forallE (.sort GraphDeclarations.carrierLevel) <|
  .forallE (.forallE (.bvar 2) (.bvar 2)) <|
  .forallE (.forallE (.bvar 2) (.bvar 2)) <|
  .forallE (.bvar 4) <| .forallE (.bvar 3) body

example : GraphDeclarations.forwardType = telescope
    (.forallE (GraphAdapter.composite GraphDeclarations.carrierLevel)
      ((GraphAdapter.result GraphDeclarations.carrierLevel).liftLooseBVars 1 0)) := by rfl

/-- Function membership is the full telescope obligation, stronger than closure. -/
theorem specializeTelescope {body : Expr} {T f : V} (A B C F G x z : V)
    (ht : Denotes m.cval env φ (fun _ => A) (telescope body) T) (hf : f ∈ˢ T)
    (hA : A ∈ˢ univ (Level.eval φ GraphDeclarations.carrierLevel))
    (hB : B ∈ˢ univ (Level.eval φ GraphDeclarations.carrierLevel))
    (hC : C ∈ˢ univ (Level.eval φ GraphDeclarations.carrierLevel))
    (hF : F ∈ˢ piV A (fun _ => B)) (hG : G ∈ˢ piV B (fun _ => C))
    (hx : x ∈ˢ A) (hz : z ∈ˢ C) :
    ∃ R, Denotes m.cval env φ (GraphAdapter.assignment x z A B C F G) body R ∧
      app (app (app (app (app (app (app f A) B) C) F) G) x) z ∈ˢ R := by
  obtain ⟨_, ht, hf⟩ := specialize ht hf Denotes.sort hA
  obtain ⟨_, ht, hf⟩ := specialize ht hf Denotes.sort hB
  obtain ⟨_, ht, hf⟩ := specialize ht hf Denotes.sort hC
  obtain ⟨_, ht, hf⟩ := specialize ht hf
    (Denotes.pi Denotes.bvar (fun _ _ => Denotes.bvar)) hF
  obtain ⟨_, ht, hf⟩ := specialize ht hf
    (Denotes.pi Denotes.bvar (fun _ _ => Denotes.bvar)) hG
  obtain ⟨_, ht, hf⟩ := specialize ht hf Denotes.bvar hx
  obtain ⟨R, ht, hf⟩ := specialize ht hf Denotes.bvar hz
  refine ⟨R, ?_, hf⟩
  have he : GraphAdapter.assignment x z A B C F G =
      push z (push x (push G (push F (push C (push B (push A (fun _ => A))))))) := by
    funext n
    cases n with
    | zero => rfl
    | succ n => cases n with
      | zero => rfl
      | succ n => cases n with
        | zero => rfl
        | succ n => cases n with
          | zero => rfl
          | succ n => cases n with
            | zero => rfl
            | succ n => cases n with
              | zero => rfl
              | succ n => cases n <;> rfl
  rw [he]
  exact ht
open GraphAdapter
variable {u : Level}

theorem shiftedGraphDenotes (pr : GraphAdapter.Primitives m u φ) (proof : V) (A B C F G x z : V)
    (hB : B ∈ˢ univ (Level.eval φ u)) (hC : C ∈ˢ univ (Level.eval φ u))
    (hf : ∀ a, a ∈ˢ A → app F a ∈ˢ B)
    (hg : ∀ b, b ∈ˢ B → app G b ∈ˢ C) (hx : x ∈ˢ A) (hz : z ∈ˢ C) :
    Denotes m.cval env φ (push proof (assignment x z A B C F G)) ((composite u).liftLooseBVars 1 0)
      (truthVal (∃ y, y ∈ˢ B ∧ y = app F x ∧ z = app G y)) ∧
    Denotes m.cval env φ (push proof (assignment x z A B C F G)) ((result u).liftLooseBVars 1 0)
      (truthVal (z = app G (app F x))) := by
  exact graph_denotes_shift pr A B C F G x z 1
    (push proof (assignment x z A B C F G))
    (fun i => by simp only [Nat.add_comm, push]) hB hC hf hg hx hz

theorem closedImplication (c : ConstantInfo) (hc : c ∈ env.consts)
    (P Q : Expr) (p q : Prop)
    (hct : c.toConstantVal.type = telescope (.forallE P (Q.liftLooseBVars 1 0)))
    (A B C F G x z : V)
    (hA : A ∈ˢ univ (Level.eval φ GraphDeclarations.carrierLevel))
    (hB : B ∈ˢ univ (Level.eval φ GraphDeclarations.carrierLevel))
    (hC : C ∈ˢ univ (Level.eval φ GraphDeclarations.carrierLevel))
    (hF : F ∈ˢ piV A (fun _ => B)) (hG : G ∈ˢ piV B (fun _ => C))
    (hx : x ∈ˢ A) (hz : z ∈ˢ C)
    (hp : Denotes m.cval env φ (assignment x z A B C F G) P (truthVal p))
    (hq : ∀ proof : V, Denotes m.cval env φ (push proof (assignment x z A B C F G))
      (Q.liftLooseBVars 1 0) (truthVal q)) : p → q := by
  obtain ⟨T, ht, hf⟩ := m.mem c hc φ (fun _ => A)
  rw [hct] at ht
  obtain ⟨R, hr, hfr⟩ := specializeTelescope A B C F G x z ht hf hA hB hC hF hG hx hz
  intro h
  obtain ⟨S, hs, hfs⟩ := specialize hr hfr hp (mem_truthVal.mpr ⟨h, rfl⟩)
  obtain rfl := Denotes_functional hs (hq pt)
  exact of_mem_truthVal hfs

theorem forwardMembership
    (pr : Primitives m GraphDeclarations.carrierLevel φ)
    (hc : ConstantInfo.thmInfo ⟨GraphDeclarations.forwardName, [ConLeche.BasisDSL.vN],
      GraphDeclarations.forwardType⟩ ∈ env.consts)
    (A B C F G x z : V)
    (hA : A ∈ˢ univ (Level.eval φ GraphDeclarations.carrierLevel))
    (hB : B ∈ˢ univ (Level.eval φ GraphDeclarations.carrierLevel))
    (hC : C ∈ˢ univ (Level.eval φ GraphDeclarations.carrierLevel))
    (hF : F ∈ˢ piV A (fun _ => B)) (hG : G ∈ˢ piV B (fun _ => C))
    (hx : x ∈ˢ A) (hz : z ∈ˢ C) :
    (∃ y, y ∈ˢ B ∧ y = app F x ∧ z = app G y) → z = app G (app F x) := by
  have hf := fun (a : V) (ha : a ∈ˢ A) => app_mem_piV (B := fun _ => B) hF ha
  have hg := fun (b : V) (hb : b ∈ˢ B) => app_mem_piV (B := fun _ => C) hG hb
  exact closedImplication _ hc _ _ _ _ rfl A B C F G x z hA hB hC hF hG hx hz
    (graph_denotes pr A B C F G x z hB hC hf hg hx hz).1
    (fun proof => (shiftedGraphDenotes pr proof A B C F G x z hB hC hf hg hx hz).2)

theorem backwardMembership
    (pr : Primitives m GraphDeclarations.carrierLevel φ)
    (hc : ConstantInfo.thmInfo ⟨GraphDeclarations.backwardName, [ConLeche.BasisDSL.vN],
      GraphDeclarations.backwardType⟩ ∈ env.consts)
    (A B C F G x z : V)
    (hA : A ∈ˢ univ (Level.eval φ GraphDeclarations.carrierLevel))
    (hB : B ∈ˢ univ (Level.eval φ GraphDeclarations.carrierLevel))
    (hC : C ∈ˢ univ (Level.eval φ GraphDeclarations.carrierLevel))
    (hF : F ∈ˢ piV A (fun _ => B)) (hG : G ∈ˢ piV B (fun _ => C))
    (hx : x ∈ˢ A) (hz : z ∈ˢ C) :
    z = app G (app F x) → (∃ y, y ∈ˢ B ∧ y = app F x ∧ z = app G y) := by
  have hf := fun (a : V) (ha : a ∈ˢ A) => app_mem_piV (B := fun _ => B) hF ha
  have hg := fun (b : V) (hb : b ∈ˢ B) => app_mem_piV (B := fun _ => C) hG hb
  exact closedImplication _ hc _ _ _ _ rfl A B C F G x z hA hB hC hF hG hx hz
    (graph_denotes pr A B C F G x z hB hC hf hg hx hz).2
    (fun proof => (shiftedGraphDenotes pr proof A B C F G x z hB hC hf hg hx hz).1)
end ClosedGraph


#audit_graph_module
