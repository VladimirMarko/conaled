import Applications.Sequences.LCA.TargetPreparation
import Applications.Sequences.LCA.WordTrace

/-! The installed backend charges construction and compact installation before
exposing its immutable query arena. Its phase contract observes the allocated
output bank, including its initialized unused cells. -/
namespace Sequences.LCA.TargetBackend
open Resources Resources.Prepared TreeReduction Dijkstra.Store
variable {m width : Nat}

abbrev State (m width : Nat) := Store (512*m) (WordMachine.Word width)
abbrev Config (m width : Nat) := MachineCapacity.WordEligible m width (2048*m)

def answer (state : State m width) (q : Nat × Nat) : Measured Nat Nat :=
  let run := WordQuery.answer m state q.1 q.2
  (run.1.val,run.2)

def ops (hw : Config m width) : Ops (Input m) (Nat × Nat) Nat (State m width) where
  prepare input := TargetPreparation.prepare input hw
  answer := answer

def Valid (hw : Config m width) (input : Input m) (state : State m width) : Prop :=
  state = (TargetPreparation.prepare input hw).1

theorem laws (hw : Config m width) : Laws (@Backend.spec m) (ops hw) (Valid hw) where
  prepare _ := rfl
  answer input state hv q := by
    cases hv
    change (WordQuery.answer m (TargetPreparation.prepare input hw).1 q.1 q.2).1.val = _
    rw [TargetPreparation.prepare_value]
    exact WordQuery.answer_spec _ _ _ _

/-- The query reserves a fixed finite frame. Every prefix of its actual
instruction-result trace fits, including the radix-packing intermediates. -/
theorem query_frame (state : State m width) (q : Nat × Nat) (ticks : Nat) :
    ((WordTrace.registers m state q.1 q.2).take ticks).length ≤ 64 :=
  WordTrace.prefix_fits _ _ _ _ _

def storage (hw : Config m width) : Storage (Input m) (State m width) where
  retained state := state.toArray.size
  preparePeak input := TargetPreparation.preparationPeak input hw
  queryPeak state := state.toArray.size+64

def profile (m : Nat) : Profile (Input m) where
  preparation _ := 32768*m
  query _ := 57
  maintenance _ := 0
  retained _ := 512*m
  peak _ := 2048*m

theorem bounds (hw : Config m width) : Bounds (ops hw) (Valid hw) (storage hw) (profile m) where
  preparation input := TargetPreparation.prepare_cost input hw
  query _ state _ q := WordQuery.answer_cost m state q.1 q.2
  retained _ state _ := by simp [storage,profile]
  preparePeak input := TargetPreparation.preparationPeak_le input hw
  queryPeak input state _ := by
    have hp := input.positive
    simp only [storage,profile,Vector.size_toArray]
    omega

theorem exists_config (hm : 0 < m) : ∃ width, Config m width :=
  MachineCapacity.exists_width hm (2048*m)

def realtime (m : Nat) : Requirements where
  startup := none
  deadline := 57
  maintenance := 0
  capacity := 512*m
  peak := 2048*m

theorem realtime_feasible (input : Input m) : Feasible (realtime m) (profile m) input := by
  simp [Feasible,realtime,profile]

theorem reusable (hw : Config m width) (input : Input m) :
    ∀ q, ((ops hw).answer ((ops hw).prepare input).1 q).1 = Backend.spec input q ∧
      ((ops hw).answer ((ops hw).prepare input).1 q).2 ≤ 57 :=
  fun q => ⟨agreement (laws hw) input q,
    response_deadline (bounds hw) (realtime_feasible input) ((laws hw).prepare input) q⟩

/-- Changing a source may invalidate reuse even when its dimensions agree. A
single observed answer difference is enough; no pointer identity is assumed. -/
theorem stale_rejected (hw : Config m width) (old fresh : Input m)
    (q : Nat × Nat) (hd : Backend.spec old q ≠ Backend.spec fresh q) :
    ¬ Valid hw fresh ((ops hw).prepare old).1 := by
  intro hv
  exact hd ((agreement (laws hw) old q).symm.trans ((laws hw).answer fresh _ hv q))

variable {n : Nat}

def lcaOps (hw : Config (tourSize n) width) := (TreeReduction.reduction n).apply (ops hw)
def lcaValid (hw : Config (tourSize n) width) := (TreeReduction.reduction n).Valid (Valid hw)
def lcaStorage (hw : Config (tourSize n) width) :=
  (TreeReduction.reduction n).storage (ops hw) (TreeReduction.arena n) (storage hw)
def lcaProfile (n : Nat) :=
  (TreeReduction.reduction n).profile (profile (tourSize n)) (TreeReduction.capacity n)

theorem lca_laws (hw : Config (tourSize n) width) :
    Laws sourceLCA (lcaOps hw) (lcaValid hw) :=
  TreeReduction.laws Backend.spec (Backend.spec_correct _) (ops hw) (Valid hw) (laws hw)

theorem lca_bounds (hw : Config (tourSize n) width) :
    Bounds (lcaOps hw) (lcaValid hw) (lcaStorage hw) (lcaProfile n) :=
  TreeReduction.bounds n (bounds hw)

def lcaRealtime (n : Nat) : Requirements where
  startup := none
  deadline := 62
  maintenance := 0
  capacity := n+514*tourSize n
  peak := n+2052*tourSize n+8

theorem lca_feasible (source : Source n) : Feasible (lcaRealtime n) (lcaProfile n) source := by
  have hn : 0<n := by simpa only [source.property] using source.val.size_pos
  have hm : 0<tourSize n := by unfold tourSize; omega
  simp only [Feasible,lcaRealtime,lcaProfile,Reduction.profile,TreeReduction.capacity,profile]
  simp only [Option.mem_def,reduceCtorEq,false_implies,forall_const,true_and]
  omega

theorem lca_reusable (hw : Config (tourSize n) width) (source : Source n) :
    ∀ q : Query n,
      ((lcaOps hw).answer ((lcaOps hw).prepare source).1 q).1 = sourceLCA source q ∧
      ((lcaOps hw).answer ((lcaOps hw).prepare source).1 q).2 ≤ 62 :=
  fun q => ⟨agreement (lca_laws hw) source q,
    response_deadline (lca_bounds hw) (lca_feasible source) ((lca_laws hw).prepare source) q⟩

example : Config 1 12 := by constructor <;> decide
example : ¬ Config 1 10 := by intro h; have hh := h.addresses; norm_num at hh
example (source : Source 1) :
    Feasible (lcaRealtime 1) (lcaProfile 1) source := lca_feasible source

end Sequences.LCA.TargetBackend
