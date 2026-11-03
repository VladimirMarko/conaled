import EmittedComparison

namespace EmittedClosed
open ConLeche ConLeche.SetTheory ConLeche.SetModel ClosedGraph
universe w
variable {V : Type w} [SetTheory V] {env : Env}
variable {m : Model V env} {φ : LevelParam → Nat}

/-- The seven binders shared by the two closed theorem statements. -/
def telescope (body : Expr) : Expr :=
  .forallE (.sort EmittedComparison.carrierLevel) <|
  .forallE (.sort EmittedComparison.carrierLevel) <|
  .forallE (.sort EmittedComparison.carrierLevel) <|
  .forallE (.forallE (.bvar 2) (.bvar 2)) <|
  .forallE (.forallE (.bvar 2) (.bvar 2)) <|
  .forallE (.bvar 2) <| .forallE (.bvar 5) body

example : EmittedGraph.forwardType = telescope
    (.forallE EmittedComparison.premise (EmittedComparison.conclusion.liftLooseBVars 1 0)) := rfl
example : EmittedGraph.backwardType = telescope
    (.forallE EmittedComparison.conclusion (EmittedComparison.premise.liftLooseBVars 1 0)) := rfl

/-- Function membership is the full telescope obligation, stronger than closure. -/
theorem specializeTelescope {body : Expr} {T f : V} (A B C F G x z : V)
    (ht : Denotes m.cval env φ (fun _ => A) (telescope body) T) (hf : f ∈ˢ T)
    (hA : A ∈ˢ univ (Level.eval φ EmittedComparison.carrierLevel))
    (hB : B ∈ˢ univ (Level.eval φ EmittedComparison.carrierLevel))
    (hC : C ∈ˢ univ (Level.eval φ EmittedComparison.carrierLevel))
    (hF : F ∈ˢ piV A (fun _ => B)) (hG : G ∈ˢ piV B (fun _ => C))
    (hx : x ∈ˢ A) (hz : z ∈ˢ C) :
    ∃ R, Denotes m.cval env φ (EmittedComparison.assignment x z A B C F G) body R ∧
      app (app (app (app (app (app (app f A) B) C) F) G) z) x ∈ˢ R := by
  obtain ⟨_, ht, hf⟩ := specialize ht hf Denotes.sort hA
  obtain ⟨_, ht, hf⟩ := specialize ht hf Denotes.sort hB
  obtain ⟨_, ht, hf⟩ := specialize ht hf Denotes.sort hC
  obtain ⟨_, ht, hf⟩ := specialize ht hf
    (Denotes.pi Denotes.bvar (fun _ _ => Denotes.bvar)) hF
  obtain ⟨_, ht, hf⟩ := specialize ht hf
    (Denotes.pi Denotes.bvar (fun _ _ => Denotes.bvar)) hG
  obtain ⟨_, ht, hf⟩ := specialize ht hf Denotes.bvar hz
  obtain ⟨R, ht, hf⟩ := specialize ht hf Denotes.bvar hx
  refine ⟨R, ?_, hf⟩
  have he : EmittedComparison.assignment x z A B C F G =
      push x (push z (push G (push F (push C (push B (push A (fun _ => A))))))) := by
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


/-- Read an implication from the stored emitted declaration, specializing its
actual telescope and transporting the conclusion across the proof binder. -/
theorem closedImplication (c : ConstantInfo) (hc : c ∈ env.consts)
    (p q : Expr) (qCore : SquareKit.Internal.CoreSyntax.Expr) (P Q : V)
    (hct : c.toConstantVal.type = telescope (.forallE p (q.liftLooseBVars 1 0)))
    (he : EmissionEncoding.encode qCore = some q)
    (heShift : EmissionEncoding.encode qCore.shift = some (q.liftLooseBVars 1 0))
    (A B C F G x z : V)
    (hA : A ∈ˢ univ (Level.eval φ EmittedComparison.carrierLevel))
    (hB : B ∈ˢ univ (Level.eval φ EmittedComparison.carrierLevel))
    (hC : C ∈ˢ univ (Level.eval φ EmittedComparison.carrierLevel))
    (hF : F ∈ˢ piV A (fun _ => B)) (hG : G ∈ˢ piV B (fun _ => C))
    (hx : x ∈ˢ A) (hz : z ∈ˢ C)
    (hp : Denotes m.cval env φ (EmittedComparison.assignment x z A B C F G) p P)
    (hq : Denotes m.cval env φ (EmittedComparison.assignment x z A B C F G) q Q) :
    (pt : V) ∈ˢ P → ∃ witness : V, witness ∈ˢ Q := by
  obtain ⟨T, ht, hf⟩ := m.mem c hc φ (fun _ => A)
  rw [hct] at ht
  obtain ⟨R, hr, hfr⟩ := specializeTelescope A B C F G x z ht hf hA hB hC hF hG hx hz
  intro h
  obtain ⟨S, hs, hfs⟩ := specialize hr hfr hp h
  have hqCore : EmissionSemantics.Holds m φ (EmittedComparison.assignment x z A B C F G) qCore Q :=
    ⟨q, he, hq⟩
  have shifted := (hqCore.shift pt).denotes heShift
  obtain rfl := Denotes_functional hs shifted
  exact ⟨_, hfs⟩


/-- Both actual emitted theorem records induce the graph comparison. -/
theorem closedTruth (m : Model V EmittedEnvironment.environment) (φ : LevelParam → Nat)
    (A B C F G : V)
    (hA : A ∈ˢ univ (Level.eval φ EmittedComparison.carrierLevel))
    (hB : B ∈ˢ univ (Level.eval φ EmittedComparison.carrierLevel))
    (hC : C ∈ˢ univ (Level.eval φ EmittedComparison.carrierLevel))
    (hF : F ∈ˢ piV A (fun _ => B)) (hG : G ∈ˢ piV B (fun _ => C))
    (x : GraphAdapter.Member A) (z : GraphAdapter.Member C) (P Q : V)
    (hp : Denotes m.cval EmittedEnvironment.environment φ
      (EmittedComparison.assignment x.val z.val A B C F G) EmittedComparison.premise P)
    (hq : Denotes m.cval EmittedEnvironment.environment φ
      (EmittedComparison.assignment x.val z.val A B C F G) EmittedComparison.conclusion Q) :
    (pt : V) ∈ˢ P ↔ (pt : V) ∈ˢ Q := by
  let L := EmittedComparison.laws φ A B C F G hA hB hC
    (fun _ hx => app_mem_piV (B := fun _ => B) hF hx)
    (fun _ hy => app_mem_piV (B := fun _ => C) hG hy)
  have hPT := EmissionSemantics.formula_denotes
    (EmittedComparison.primitives m EmittedComparison.carrierLevel φ)
    (em := EmittedComparison.openModel) rfl
    (EmittedComparison.compatible m φ A B C F G x.val z.val)
    (EmittedComparison.objects_compatible m φ A B C F G L x z)
    SquareKit.Internal.GraphTarget.forwardDeclaration.premise _ EmittedComparison.premise_encoded
  have hQT := EmissionSemantics.formula_denotes
    (EmittedComparison.primitives m EmittedComparison.carrierLevel φ)
    (em := EmittedComparison.openModel) rfl
    (EmittedComparison.compatible m φ A B C F G x.val z.val)
    (EmittedComparison.objects_compatible m φ A B C F G L x z)
    SquareKit.Internal.GraphTarget.forwardDeclaration.conclusion _ EmittedComparison.conclusion_encoded
  have forward := closedImplication (m := m)
    (.thmInfo ⟨EmissionEncoding.N.encode `graph_forward, [EmissionEncoding.N.encode `v], EmittedGraph.forwardType⟩)
    (by decide) EmittedComparison.premise EmittedComparison.conclusion EmittedComparison.conclusionCore P Q
    rfl EmittedComparison.conclusion_encoded rfl A B C F G x.val z.val hA hB hC hF hG x.property z.property hp hq
  have backward := closedImplication (m := m)
    (.thmInfo ⟨EmissionEncoding.N.encode `graph_backward, [EmissionEncoding.N.encode `v], EmittedGraph.backwardType⟩)
    (by decide) EmittedComparison.conclusion EmittedComparison.premise EmittedComparison.premiseCore Q P
    rfl EmittedComparison.premise_encoded rfl A B C F G x.val z.val hA hB hC hF hG x.property z.property hq hp
  constructor
  · intro h
    obtain ⟨w, hw⟩ := forward h
    obtain rfl := Denotes_functional hq hQT
    exact mem_truthVal.mpr ⟨of_mem_truthVal hw, rfl⟩
  · intro h
    obtain ⟨w, hw⟩ := backward h
    obtain rfl := Denotes_functional hp hPT
    exact mem_truthVal.mpr ⟨of_mem_truthVal hw, rfl⟩

end EmittedClosed
#audit_graph_module
