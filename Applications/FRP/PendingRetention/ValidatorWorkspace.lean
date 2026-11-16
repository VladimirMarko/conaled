import Applications.FRP.PendingRetention.Workspace

/-! Finite scratch for the actual predecessor validator, including candidates
that fail comparison. A proposal may temporarily advance the counter to K+1. -/
namespace FRPSpec.PendingRetention
open PendingCrash PendingMigration
namespace ValidatorWorkspace

structure FieldsBound (limit : Nat) (f : Frame) : Prop where
  counter : f.nextIdentity ≤ limit
  order : f.order.length ≤ 2
  requests : ∀ slot r, r ∈ f.requests.get slot →
    r.identity ≤ limit ∧ ∀ receipt ∈ r.receipt, receipt.identity ≤ limit

theorem FieldsBound.mono {n m : Nat} {f : Frame} (h : FieldsBound n f) (nm : n ≤ m) : FieldsBound m f :=
  ⟨h.counter.trans nm,h.order,fun s r hr => ⟨(h.requests s r hr).1.trans nm,
    fun t ht => ((h.requests s r hr).2 t ht).trans nm⟩⟩

theorem FieldsBound.of_valid {n : Nat} {f : Frame} (h : f.Valid) (hn : f.nextIdentity ≤ n) :
    FieldsBound n f := by
  have enc := Encoding.frame_success_of_valid n f h hn
  simp only [Encoding.frame,Encoding.fields_success,Encoding.product_success,
    Encoding.optional_success,Encoding.number_success,Encoding.request_success] at enc
  refine ⟨hn,h.2.1,?_⟩
  intro slot r hr
  cases slot
  · exact enc.2.2.1.1 r hr
  · exact enc.2.2.1.2 r hr

theorem FieldsBound.encodes {n : Nat} {f : Frame} (h : FieldsBound n f) :
    (Encoding.frame n).encode f ≠ none := by
  simpa [Encoding.frame,Encoding.identity,Encoding.sequence,Encoding.cells_success,
    Encoding.number_success,Encoding.request_success,Slots.get] using
    And.intro (And.intro (h.requests false) (h.requests true)) (And.intro h.order h.counter)

theorem FieldsBound.update {n : Nat} {f : Frame} (h : FieldsBound n f) (slot : Bool) (r : PendingCrash.Request)
    (hr : r.identity ≤ n ∧ ∀ receipt ∈ r.receipt, receipt.identity ≤ n) : FieldsBound n (f.update slot r) := by
  refine ⟨h.counter,h.order,?_⟩
  intro other request mem
  by_cases eq : other = slot
  · subst other
    simp only [Frame.update,slots_get_put_same,Option.mem_some_iff] at mem
    cases mem; exact hr
  · simp only [Frame.update,slots_get_put,ite_eq_right eq] at mem
    exact h.requests other request mem

theorem receive_fields {n : Nat} {f g : Frame} (h : FieldsBound n f)
    (receipt : Receipt) (done : receive f receipt = .changed g) : FieldsBound n g := by
  unfold receive at done
  split at done <;> try contradiction
  rename_i slot r found
  have present := (find_request_eq f receipt.identity slot r found).1
  have rb := h.requests slot r (by simpa using present)
  split at done
  all_goals repeat' first | split at done | contradiction
  all_goals cases done
  all_goals apply h.update
  all_goals exact ⟨rb.1,by intro t ht; cases ht; exact rb.1⟩

theorem propose_fields {n : Nat} {f g : Frame} (h : FieldsBound n f)
    (command : FrameCommand) (done : propose f command = .changed g) : FieldsBound (n+1) g := by
  have old := h.mono (Nat.le_succ n)
  cases command with
  | receive receipt => exact (receive_fields h receipt done).mono (Nat.le_succ n)
  | migrate kind => cases done; exact ⟨old.counter,old.order,old.requests⟩
  | accept input =>
    simp only [propose] at done
    repeat' first | split at done | contradiction
    cases done
    refine ⟨by dsimp only; have := h.counter; omega,?_,?_⟩
    · simp only [List.length_append,List.length_singleton]
      omega
    · intro other r mem
      simp only [slots_get_put] at mem
      split at mem
      · simp only [Option.mem_some_iff] at mem
        cases mem
        exact ⟨old.counter,by simp⟩
      · exact old.requests other r mem
  | evaluate | tickCommit | close | release =>
    simp only [propose] at done
    split at done <;> try contradiction
    rename_i slot r head
    have rb := old.requests slot r (by simpa using head_request_eq f slot r head)
    all_goals repeat' first | split at done | contradiction
    all_goals cases done
    all_goals first
      | exact old.update slot _ rb
      | exact ⟨old.counter,old.order,(old.update slot {r with phase := .committed} rb).requests⟩
      | refine ⟨old.counter,?_,?_⟩
        · simp only [List.length_tail]; have := old.order; omega
        · intro other request mem
          simp only [slots_get_put] at mem
          split at mem
          · simp at mem
          · exact old.requests other request mem

theorem possibleCommands_length (f : Frame) : (possibleCommands f).length ≤ 12 := by
  cases hl : f.requests.get false <;> cases hr : f.requests.get true
  all_goals simp [possibleCommands,hl,hr]
  case none.some r => cases r.output <;> simp_all
  case some.none r => cases r.output <;> simp_all
  case some.some l r => cases l.output <;> cases r.output <;> simp_all

theorem possibleCommands_bound {n : Nat} {f : Frame} (h : FieldsBound n f)
    (c : FrameCommand) (hc : c ∈ possibleCommands f) : CommandBound ⟨n,0,0⟩ c := by
  simp only [possibleCommands,List.mem_append,List.mem_flatMap] at hc
  rcases hc with base | ⟨slot,_,mem⟩
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at base
    rcases base with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  · split at mem
    · simp at mem
    · rename_i r hr
      have rb := (h.requests slot r (by simpa using hr)).1
      simp only [List.mem_append,List.mem_singleton,List.mem_map] at mem
      rcases mem with rfl | ⟨y,_,rfl⟩ <;> exact rb

theorem commands_encodable {n : Nat} {f : Frame} (h : FieldsBound n f) :
    (Encoding.sequence (Encoding.frameCommand n) 12).encode (possibleCommands f) ≠ none := by
  exact (Encoding.cells_success _ _ _).mpr ⟨possibleCommands_length f,
    fun c hc => (Encoding.frameCommand_success ⟨n,0,0⟩ c).mpr (possibleCommands_bound h c hc)⟩

/-- `any` only examines a prefix of the concrete generated command list. -/
theorem visited_commands_bound (f : Frame) (cut : Nat) :
    ((possibleCommands f).take cut).length ≤ 12 := by
  have := possibleCommands_length f
  simp only [List.length_take]
  omega

/-- Covers every comparison candidate, including a changed proposal that does
not equal the requested successor and is discarded by the validator. -/
theorem successor_candidate_encodes {cfg : Config} {f candidate : Frame}
    (valid : f.Valid) (counter : f.nextIdentity ≤ cfg.lifetime)
    (command : FrameCommand) (proposed : propose f command = .changed candidate) :
    (Encoding.frame (cfg.lifetime+1)).encode candidate ≠ none :=
  (propose_fields (FieldsBound.of_valid valid counter) command proposed).encodes

theorem commands_prefix_encodable {n : Nat} {f : Frame} (h : FieldsBound n f) (cut : Nat) :
    (Encoding.sequence (Encoding.frameCommand n) 12).encode ((possibleCommands f).take cut) ≠ none :=
  (Encoding.cells_success _ _ _).mpr ⟨visited_commands_bound f cut,
    fun c hc => (Encoding.frameCommand_success ⟨n,0,0⟩ c).mpr
      (possibleCommands_bound h c (List.mem_of_mem_take hc))⟩

theorem commands_suffix_encodable {n : Nat} {f : Frame} (h : FieldsBound n f) (cut : Nat) :
    (Encoding.sequence (Encoding.frameCommand n) 12).encode ((possibleCommands f).drop cut) ≠ none := by
  apply (Encoding.cells_success _ _ _).mpr
  refine ⟨?_,fun c hc => (Encoding.frameCommand_success ⟨n,0,0⟩ c).mpr
    (possibleCommands_bound h c (List.mem_of_mem_drop hc))⟩
  have := possibleCommands_length f
  simp only [List.length_drop]
  omega

open Encoding
abbrev Code (cfg : Config) :=
  Cells (FrameCommandCode cfg.lifetime) 12 × Cells (FrameCommandCode cfg.lifetime) 12 ×
  Cells (FrameCommandCode cfg.lifetime) 12 × FrameCode (cfg.lifetime+1) ×
  FrameCode (cfg.lifetime+1) × Fin 13
abbrev PeakCode (cfg : Config) := Workspace.PeakCode cfg × Code cfg
set_option synthInstance.maxSize 16384 in
abbrev packing (cfg : Config) : Bits (PeakCode cfg) := inferInstance

theorem code_width (cfg : Config) : Bits.width (α := Code cfg) = Layout.validatorBits cfg := by
  simp only [Code,product_width,cells_width,Layout.validatorBits,Layout.validatorListBits,
    Layout.validatorCommandBits,Layout.validatorFrameBits]
  dsimp only [Bits.width]
  norm_num [Nat.clog]
  ring

theorem peak_width (cfg : Config) : (packing cfg).width ≤ Layout.bound cfg := by
  change (Workspace.peakPacking cfg).width + Bits.width (α := Code cfg) ≤ Layout.bound cfg
  rw [code_width]
  exact Workspace.peak_width_with_validator cfg

def peakCode (cfg : Config) (code : PeakCode cfg) : Fin (2 ^ Layout.bound cfg) :=
  ⟨((packing cfg).pack code).val,((packing cfg).pack code).isLt.trans_le
    (Nat.pow_le_pow_right (by decide) (peak_width cfg))⟩

/-- The list, its construction prefix, and its remaining tail have separate
finite codes. Both frame slots can contain a K+1 comparison proposal. -/
theorem actual_codes {cfg : Config} {f candidate : Frame}
    (valid : f.Valid) (counter : f.nextIdentity ≤ cfg.lifetime)
    (command : FrameCommand) (proposed : propose f command = .changed candidate) (cut : Fin 13) :
    ∃ code : Code cfg,
      (Encoding.sequence (Encoding.frameCommand cfg.lifetime) 12).decode code.1 = possibleCommands f ∧
      (Encoding.frame (cfg.lifetime+1)).decode code.2.2.2.1 = candidate := by
  have fields := FieldsBound.of_valid valid counter
  let commands := Encoding.sequence (Encoding.frameCommand cfg.lifetime) 12
  let cmd := (commands.encode (possibleCommands f)).get (Option.isSome_iff_ne_none.mpr (commands_encodable fields))
  let front := (commands.encode ((possibleCommands f).take cut.val)).get
    (Option.isSome_iff_ne_none.mpr (commands_prefix_encodable fields cut.val))
  let back := (commands.encode ((possibleCommands f).drop cut.val)).get
    (Option.isSome_iff_ne_none.mpr (commands_suffix_encodable fields cut.val))
  let frame := Encoding.frame (cfg.lifetime+1)
  let candidateCode := (frame.encode candidate).get
    (Option.isSome_iff_ne_none.mpr (successor_candidate_encodes valid counter command proposed))
  exact ⟨(cmd,front,back,candidateCode,candidateCode,cut),
    commands.recover _ _ (Option.some_get _).symm,frame.recover _ _ (Option.some_get _).symm⟩

/-- Connects enumeration and scratch to the actual selected source of an
arbitrary execution, including executions ending in rejection or recovery. -/
theorem execution_validator_workspace (cfg : Config) (history : List Command)
    (command : FrameCommand) (candidate : Frame)
    (proposed : propose (execute cfg initial history).system.localBank.selected.frame command = .changed candidate)
    (cut : Fin 13) :
    ∃ code : Code cfg,
      (Encoding.sequence (Encoding.frameCommand cfg.lifetime) 12).decode code.1 =
        possibleCommands (execute cfg initial history).system.localBank.selected.frame ∧
      (Encoding.frame (cfg.lifetime+1)).decode code.2.2.2.1 = candidate := by
  have h := (execution_resourceBound cfg history).localBanks.selected
  exact actual_codes h.1 h.2.1 command proposed cut

/-- Three frame traversals cover the outer proposal and the two validity
checks. Each enumerated command adds its code read, proposal and comparison.
These are abstract encoded-field traversals, not native instruction counts. -/
def validationWork (cfg : Config) (f : Frame) (cut : Nat) : Nat :=
  3 * Layout.validatorFrameBits cfg +
    ((possibleCommands f).take cut).length *
      (Layout.validatorCommandBits cfg + 2 * Layout.validatorFrameBits cfg)

def validationBudget (cfg : Config) : Nat :=
  3 * Layout.validatorFrameBits cfg +
    12 * (Layout.validatorCommandBits cfg + 2 * Layout.validatorFrameBits cfg)

theorem validationWork_le_budget (cfg : Config) (f : Frame) (cut : Nat) :
    validationWork cfg f cut ≤ validationBudget cfg := by
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (visited_commands_bound f cut)) _

/-- A conservative price for each emitted validation event. The generic event
fold continues to retain failure work and compose at the real intermediate state. -/
def boundedPrice (cfg : Config) : Event → Nat
  | .validate => validationBudget cfg
  | event => cellWork event

theorem billed_append (cfg : Config) (state : System) (xs ys : List Command) :
    executionBill (boundedPrice cfg) cfg state (xs ++ ys) =
      executionBill (boundedPrice cfg) cfg state xs +
      executionBill (boundedPrice cfg) cfg (execute cfg state xs).system ys :=
  executionBill_append _ _ _ _ _

private def saturated : Frame := {initialFrame with nextIdentity := 1}
private def comparison : Frame :=
  {saturated with
    requests := saturated.requests.put false (some {identity := 1,input := true})
    order := [false]
    nextIdentity := 2}
example : saturated.Valid := by decide
example : propose saturated (.accept true) = .changed comparison := by decide
example : (Encoding.frame 1).encode comparison = none := by decide
example : (Encoding.frame 2).encode comparison ≠ none :=
  successor_candidate_encodes (cfg := ⟨1,0,0⟩) (f := saturated) (by decide) (by decide) (.accept true) (by decide)

end ValidatorWorkspace
end FRPSpec.PendingRetention
