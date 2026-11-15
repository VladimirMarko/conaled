import Applications.Sequences.LCA.WordTrace

set_option autoImplicit false
set_option warningAsError true

/-! Online tree queries compose the retained Euler decoder with the packed
RMQ arena. The online state contains no source tree or unprepared input; its
initialization relation is proof-only and applies to every future query. -/
namespace Sequences.LCA.WordLCA
open Resources TreeReduction Dijkstra.Store
variable {n width capacity inputWords frameWords : Nat}

structure State (n width capacity : Nat) where
  decoder : Decoder n
  memory : Store capacity (WordMachine.Word width)

def answer (state : State n width capacity) (q : Query n) : Measured Nat Nat :=
  bind ((reduction n).encode state.decoder q) fun endpoints =>
  bind (WordQuery.answer (tourSize n) state.memory endpoints.1 endpoints.2) fun index =>
  (reduction n).decode state.decoder index.val

theorem answer_cost (state : State n width capacity) (q : Query n) :
    (answer state q).2 ≤ 62 := by
  have he : ((reduction n).encode state.decoder q).2 = 3 := by
    simp [reduction,encodeM_exact]
  have hq := WordQuery.answer_cost (tourSize n) state.memory
    (((reduction n).encode state.decoder q).1).1 (((reduction n).encode state.decoder q).1).2
  have hd := decodeM_cost state.decoder
    (WordQuery.answer (tourSize n) state.memory
      (((reduction n).encode state.decoder q).1).1 (((reduction n).encode state.decoder q).1).2).1.val
  change ((reduction n).decode _ _).2 ≤ 2 at hd
  simp only [answer,Resources.bind]
  omega

/-- A representation of the converted input in reusable prepared memory.
This definition establishes the initialization relation, not an extra online
preparation pass or a measured arena-installation bound. -/
def prepared (source : Source n)
    (h : MachineCapacity.Eligible (tourSize n) width capacity inputWords frameWords) : State n width capacity :=
  let converted := ((reduction n).convert source).1
  ⟨converted.1,PackedBackend.arena converted.2 h⟩

def Valid (source : Source n) (state : State n width capacity) : Prop :=
  ∃ (inputWords frameWords : Nat)
    (h : MachineCapacity.Eligible (tourSize n) width capacity inputWords frameWords),
    state = prepared source h

theorem prepared_valid (source : Source n)
    (h : MachineCapacity.Eligible (tourSize n) width capacity inputWords frameWords) :
    Valid source (prepared source h) := ⟨inputWords,frameWords,h,rfl⟩

theorem prepared_answer (source : Source n)
    (h : MachineCapacity.Eligible (tourSize n) width capacity inputWords frameWords) (q : Query n) :
    (answer (prepared source h) q).1 = sourceLCA source q := by
  simp only [answer,prepared,Resources.bind]
  rw [WordQuery.answer_spec]
  exact translation (@Backend.spec (tourSize n)) (Backend.spec_correct (tourSize n)) source q

theorem answer_correct (source : Source n) (state : State n width capacity)
    (hv : Valid source state) (q : Query n) : (answer state q).1 = sourceLCA source q := by
  obtain ⟨inputWords,frameWords,h,rfl⟩ := hv
  exact prepared_answer source h q

theorem answer_lt (source : Source n) (state : State n width capacity)
    (hv : Valid source state) (q : Query n) : (answer state q).1 < n := by
  rw [answer_correct source state hv q]
  exact sourceLCA_lt source q

/-- Reuse quantifies over arbitrary later queries; no batch is required during
initialization, and evaluation does not return a modified memory state. -/
theorem reusable (source : Source n) (state : State n width capacity) (hv : Valid source state) :
    ∀ q : Query n, (answer state q).1 = sourceLCA source q ∧ (answer state q).2 ≤ 62 :=
  fun q => ⟨answer_correct source state hv q,answer_cost state q⟩

example (source : Source 1) (state : State 1 width capacity) (hv : Valid source state) :
    (answer state (0,0)).1 = sourceLCA source (0,0) ∧ (answer state (0,0)).2 ≤ 62 :=
  reusable source state hv (0,0)

/-- Physical admission additionally reserves the actual packed-query frame.
The source-dependent relation is used only when creating the reusable state. -/
def targetPrepared (source : Source n)
    (h : WordTrace.Machine ((reduction n).convert source).1.2 width capacity) :
    State n width capacity :=
  prepared source (BackendBounds.machine_arena h.toMachine)

theorem target_reusable (source : Source n)
    (h : WordTrace.Machine ((reduction n).convert source).1.2 width capacity) :
    ∀ q : Query n,
      (answer (targetPrepared source h) q).1 = sourceLCA source q ∧
      (answer (targetPrepared source h) q).2 ≤ 62 :=
  reusable source _ (prepared_valid source (BackendBounds.machine_arena h.toMachine))

/-- Every prefix of the executed packed-query trace fits its reserved frame.
Installing it leaves all retained packed table cells unchanged. -/
theorem target_frame (source : Source n)
    (h : WordTrace.Machine ((reduction n).convert source).1.2 width capacity)
    (q : Query n) (ticks : Nat) :
    let state := targetPrepared source h
    let endpoints := ((reduction n).encode state.decoder q).1
    ((WordTrace.registers (tourSize n) state.memory endpoints.1 endpoints.2).take ticks).length ≤ 64 ∧
    ∀ (i : Fin capacity), i.val < PreparationBounds.retainedSlots (tourSize n) →
      lookup (WordTrace.install (m := tourSize n) state.memory
        (WordTrace.frame (tourSize n) state.memory endpoints.1 endpoints.2 ticks)) i =
        lookup state.memory i := by
  dsimp only
  exact ⟨WordTrace.prefix_fits _ _ _ _ _,
    fun i hi => WordTrace.install_preserves_retained _ _ i hi⟩

/-- Every endpoint used by the actual online machine is an admitted finite
word; the Nat-valued rejected-query totalization is not its input interface. -/
theorem translated_endpoints_valid (source : Source n) (q : Query n) :
    let endpoints := ((reduction n).encode ((reduction n).convert source).1.1 q).1
    endpoints.1 ≤ endpoints.2 ∧ endpoints.2 < tourSize n := by
  let maps := (TreeBackend.prepareMapsM source.val).1
  have hv := TreeBackend.prepareMapsM_valid source.val
  have ha := Tree.first_lt (source.val.decode (Fin.cast source.property.symm q.1))
  have hb := Tree.first_lt (source.val.decode (Fin.cast source.property.symm q.2))
  rw [source_length source] at ha hb
  change (encodeM (reindex source maps) q).1.1 ≤ (encodeM (reindex source maps) q).1.2 ∧
    (encodeM (reindex source maps) q).1.2 < tourSize n
  simp only [encodeM_exact, reindex_first source maps hv]
  omega

theorem target_endpoints_fit (source : Source n)
    (h : WordTrace.Machine ((reduction n).convert source).1.2 width capacity) (q : Query n) :
    let endpoints := ((reduction n).encode (targetPrepared source h).decoder q).1
    endpoints.1 < 2^width ∧ endpoints.2 < 2^width := by
  have hv := translated_endpoints_valid source q
  have hw := MachineCapacity.scalar_fits h.words
    (show tourSize n ≤ 4*tourSize n+3 by omega)
  change (((reduction n).encode ((reduction n).convert source).1.1 q).1).1 < 2^width ∧
    (((reduction n).encode ((reduction n).convert source).1.1 q).1).2 < 2^width
  dsimp only at hv
  omega

theorem exists_target_machine (source : Source n) :
    ∃ width, WordTrace.Machine ((reduction n).convert source).1.2 width (512*tourSize n) := by
  obtain ⟨width,h⟩ := BackendBounds.exists_machine ((reduction n).convert source).1.2
  exact ⟨width,WordTrace.machine_of_linear_capacity h⟩

theorem target_guarantee (source : Source n)
    (h : WordTrace.Machine ((reduction n).convert source).1.2 width capacity)
    (q : Query n) (ticks : Nat) :
    let state := targetPrepared source h
    let endpoints := ((reduction n).encode state.decoder q).1
    (answer state q).1 = sourceLCA source q ∧ (answer state q).2 ≤ 62 ∧
    ((WordTrace.registers (tourSize n) state.memory endpoints.1 endpoints.2).take ticks).length ≤ 64 := by
  exact ⟨(target_reusable source h q).1,(target_reusable source h q).2,
    (target_frame source h q ticks).1⟩

example (source : Source 1) :
    ∃ width, WordTrace.Machine ((reduction 1).convert source).1.2 width 512 :=
  exists_target_machine source

example (source : Source 1)
    (h : WordTrace.Machine ((reduction 1).convert source).1.2 width capacity) :
    let endpoints := ((reduction 1).encode (targetPrepared source h).decoder (0,0)).1
    endpoints.1 < 2^width ∧ endpoints.2 < 2^width :=
  target_endpoints_fit source h (0,0)

end Sequences.LCA.WordLCA
