import Applications.FRP.RegionalPendingSource

/-! Internal shared-dependency evaluation preserves the independent source until
its joined payload is effectively published by the peer. -/
namespace FRPSpec.Regional.Pending

@[simp] theorem source_updateResidual (s : Active) (slot : Bool) (r : Residual) :
    source (updateResidual s slot r) = source s := rfl

/-- The source depends on the complete protocol observation, not cut packing. -/
theorem source_of_protocol_source (a b : Active)
    (h : PendingMigration.source a.protocol = PendingMigration.source b.protocol) :
    source a = source b := by
  have hs := congrArg PendingMigration.Source.state h
  have hw := congrArg PendingMigration.Source.waiting h
  exact congrArg₂ Source.mk hs hw

theorem headResidual_fields (s : Active) (slot : Bool) (r : PendingMigration.Request) (localState : Residual)
    (h : headResidual s = some (slot,r,localState)) :
    PendingMigration.head s.protocol = some (slot,r) ∧ s.residuals.get slot = some localState := by
  unfold headResidual at h
  cases hh : PendingMigration.head s.protocol with
  | none => simp [hh] at h
  | some pair =>
    obtain ⟨i,request⟩ := pair
    simp only [hh] at h
    cases hr : s.residuals.get i with
    | none => simp [hr] at h
    | some value =>
      simp [hr] at h
      rcases h with ⟨rfl,rfl,rfl⟩
      exact ⟨rfl,hr⟩

theorem producer_source (s : Session) : source (producer s).session.active = source s.active := by
  unfold producer
  repeat' first | rfl | split

theorem deliver_source (s : Session) (toD : Bool) :
    source (deliver s toD).session.active = source s.active := by
  cases toD <;> unfold deliver
  all_goals repeat' first | rfl | split | (dsimp only)

/-- Internal construction emits no acceptance, cancellation or peer effect. -/
theorem producer_refines (s : Session) :
    SourceStep (source s.active) (producer s) (source (producer s).session.active) := by
  rw [producer_source]
  apply SourceStep.internal
  all_goals unfold producer
  all_goals repeat' first | rfl | split | simp [reject]

theorem deliver_refines (s : Session) (toD : Bool) :
    SourceStep (source s.active) (deliver s toD) (source (deliver s toD).session.active) := by
  rw [deliver_source]
  apply SourceStep.internal
  all_goals cases toD <;> unfold deliver
  all_goals repeat' first | rfl | split | (dsimp only) | simp [reject]

@[simp] theorem residual_update (s : Active) (slot : Bool) (r : Residual) :
    (updateResidual s slot r).residuals = s.residuals.put slot (some r) := with_residuals _ _

theorem get_put_ne {α : Type} (s : PendingMigration.Slots α) (slot other : Bool)
    (value : Option α) (h : other ≠ slot) : (s.put slot value).get other = s.get other := by
  cases slot <;> cases other <;> simp_all [PendingMigration.Slots.put,PendingMigration.Slots.get]

theorem replace_deliveries (s : Active) (h : Invariant s) (q : Deliveries)
    (owned : ∀ slot, q.references slot = true →
      ∃ request r, s.protocol.requests.get slot = some request ∧
        s.residuals.get slot = some r ∧ r.cached.isSome = true ∧
        (request.phase = .accepted ∨ request.phase = .cancelled)) :
    Invariant {s with deliveries := q} :=
  ⟨h.protocol,h.residual,h.current,owned,h.cancellation,h.cache_head,h.completed_cache⟩

/-- Replacing one head residual preserves every other slot and reference. -/
theorem replace_residual (s : Active) (h : Invariant s) (slot : Bool)
    (request : PendingMigration.Request) (next : Residual)
    (hr : s.protocol.requests.get slot = some request)
    (head : s.protocol.order.head? = some slot)
    (correct : ResidualCorrect request.input next)
    (current : (request.phase = .accepted ∨ request.phase = .computed ∨ request.phase = .confirmed) →
      next.cached.isSome = true → next.oldState = s.protocol.active.logical)
    (cancelled : next.cancelled = true ↔ request.phase = .cancelled)
    (complete : (next.dResult.isSome = true ∨ next.nResult.isSome = true ∨ next.candidate.isSome = true) →
      next.cached.isSome = true)
    (retained : s.deliveries.references slot = true → next.cached.isSome = true) :
    Invariant (updateResidual s slot next) := by
  constructor
  · exact h.protocol
  · intro i r hi
    change s.protocol.requests.get i = some r at hi
    by_cases same : i = slot
    · subst i
      have eq : r = request := Option.some.inj (hi.symm.trans hr)
      subst r
      exact ⟨next,by simp,correct⟩
    · obtain ⟨old,ho,hc⟩ := h.residual i r hi
      exact ⟨old,by simpa only [residual_update,get_put_ne _ slot i _ same] using ho,hc⟩
  · intro i r localState hi hl phase cache
    change s.protocol.requests.get i = some r at hi
    rw [residual_update] at hl
    by_cases same : i = slot
    · subst i
      simp only [PendingMigration.slots_get_put_same,Option.some.injEq] at hl
      subst localState
      have eq : r = request := Option.some.inj (hi.symm.trans hr)
      subst r
      exact current phase cache
    · rw [get_put_ne _ slot i _ same] at hl
      exact h.current i r localState hi hl phase cache
  · intro i reference
    change s.deliveries.references i = true at reference
    obtain ⟨r,old,hi,ho,hcache,phase⟩ := h.delivery i reference
    by_cases same : i = slot
    · subst i
      have eq : r = request := Option.some.inj (hi.symm.trans hr)
      subst r
      exact ⟨request,next,hr,by simp,retained reference,phase⟩
    · exact ⟨r,old,hi,by simpa only [residual_update,get_put_ne _ slot i _ same] using ho,hcache,phase⟩
  · intro i r localState hi hl
    change s.protocol.requests.get i = some r at hi
    rw [residual_update] at hl
    by_cases same : i = slot
    · subst i
      simp only [PendingMigration.slots_get_put_same,Option.some.injEq] at hl
      subst localState
      have eq : r = request := Option.some.inj (hi.symm.trans hr)
      subst r
      exact cancelled
    · rw [get_put_ne _ slot i _ same] at hl
      exact h.cancellation i r localState hi hl
  · intro i localState hl cache
    rw [residual_update] at hl
    by_cases same : i = slot
    · subst i; exact head
    · rw [get_put_ne _ slot i _ same] at hl
      exact h.cache_head i localState hl cache
  · intro i localState hl hc
    rw [residual_update] at hl
    by_cases same : i = slot
    · subst i
      simp only [PendingMigration.slots_get_put_same,Option.some.injEq] at hl
      subst localState
      exact complete hc
    · rw [get_put_ne _ slot i _ same] at hl
      exact h.completed_cache i localState hl hc

theorem producer_invariant (s : Session) (h : Invariant s.active) :
    Invariant (producer s).session.active := by
  unfold producer
  split
  · exact h
  · cases hh : headResidual s.active with
    | none => exact h
    | some triple =>
      obtain ⟨slot,r,localState⟩ := triple
      dsimp only
      split
      · exact h
      · rename_i guard
        have facts : r.phase = .accepted ∧ localState.cached = none ∧ localState.cancelled = false := by
          simpa [Bool.or_eq_true,and_assoc] using guard
        obtain ⟨headPair,localEq⟩ := headResidual_fields s.active slot r localState hh
        obtain ⟨headEq,requestEq⟩ := PendingMigration.head_fields s.active.protocol slot r headPair
        have emptyD : localState.dResult = none := by
          cases hd : localState.dResult with
          | none => rfl
          | some value =>
            have := h.completed_cache slot localState localEq (Or.inl (by simp [hd]))
            simp [facts.2.1] at this
        have emptyN : localState.nResult = none := by
          cases hn : localState.nResult with
          | none => rfl
          | some value =>
            have := h.completed_cache slot localState localEq (Or.inr (Or.inl (by simp [hn])))
            simp [facts.2.1] at this
        have emptyCandidate : localState.candidate = none := by
          cases hc : localState.candidate with
          | none => rfl
          | some value =>
            have := h.completed_cache slot localState localEq (Or.inr (Or.inr (by simp [hc])))
            simp [facts.2.1] at this
        let next := {localState with cached := some (produce r.input),oldState := s.active.protocol.active.logical}
        have updated : Invariant (updateResidual s.active slot next) :=
          replace_residual s.active h slot r next requestEq headEq
            (by simp [next,ResidualCorrect,produce_correct,emptyD,emptyN,emptyCandidate])
            (by intros; rfl)
            (by simp [next,facts.1,facts.2.2])
            (by simp [next]) (by simp [next])
        apply replace_deliveries _ updated ⟨some slot,some slot⟩
        intro i reference
        have same : i = slot := by
          cases i <;> cases slot <;> simp_all [Deliveries.references]
        subst i
        exact ⟨r,next,requestEq,by simp,by simp [next],Or.inl facts.1⟩

def drained (q : Deliveries) (toD : Bool) : Deliveries :=
  if toD then {q with d := none} else {q with n := none}

theorem drained_subset (q : Deliveries) (toD slot : Bool)
    (h : (drained q toD).references slot = true) : q.references slot = true := by
  cases toD <;> simp_all [drained,Deliveries.references]

theorem drain_invariant (s : Active) (h : Invariant s) (toD : Bool) :
    Invariant {s with deliveries := drained s.deliveries toD} :=
  replace_deliveries s h _ (fun slot reference => h.delivery slot (drained_subset _ _ _ reference))

def consumerResidual (r : Residual) (toD d : Bool) : Residual :=
  if toD then {r with dResult := some r.oldState,candidate := some d}
  else {r with nResult := some (!d)}

theorem consumer_invariant (s : Active) (h : Invariant s) (slot : Bool)
    (request : PendingMigration.Request) (localState : Residual) (toD d : Bool)
    (hr : s.protocol.requests.get slot = some request)
    (hl : s.residuals.get slot = some localState)
    (hc : localState.cached = some d) (phase : request.phase = .accepted) :
    Invariant (updateResidual {s with deliveries := drained s.deliveries toD} slot
      (consumerResidual localState toD d)) := by
  obtain ⟨old,ho,correct⟩ := h.residual slot request hr
  have eq : old = localState := Option.some.inj (ho.symm.trans hl)
  subst old
  have value : d = request.input := correct.1 d hc
  have cache : localState.cached.isSome = true := by simp [hc]
  have current := h.current slot request localState hr hl (Or.inl phase) cache
  have head := h.cache_head slot localState hl cache
  apply replace_residual _ (drain_invariant s h toD) slot request _ hr head
  · cases toD <;> simp_all [consumerResidual,ResidualCorrect]
  · cases toD <;> simpa [consumerResidual] using (fun _ _ => current)
  · cases toD <;> simpa [consumerResidual] using h.cancellation slot request localState hr hl
  · cases toD <;> simp [consumerResidual,hc]
  · cases toD <;> simp [consumerResidual,hc]

@[simp] theorem native_not (d : Bool) : Applications.Circuits.Circuit.not.execute d = !d := by
  cases d <;> rfl
@[simp] theorem native_delay (d b : Bool) : Indefinite.delay.machine.step (d,b) = (b,d) := by
  cases d <;> cases b <;> rfl

theorem deliver_owned_invariant (s : Session) (h : Invariant s.active) (toD slot : Bool)
    (hp : s.prepared.isSome = false)
    (cell : (if toD then s.active.deliveries.d else s.active.deliveries.n) = some slot) :
    Invariant (deliver s toD).session.active := by
  have reference : s.active.deliveries.references slot = true := by
    cases toD <;> simp_all [Deliveries.references]
  obtain ⟨request,localState,hr,hl,cache,phase⟩ := h.delivery slot reference
  by_cases cancelled : localState.cancelled = true
  · have result := drain_invariant s.active h toD
    cases toD with
    | false =>
      have cellN : s.active.deliveries.n = some slot := cell
      simpa [deliver,hp,cellN,hl,cancelled,drained] using result
    | true =>
      have cellD : s.active.deliveries.d = some slot := cell
      simpa [deliver,hp,cellD,hl,cancelled,drained] using result
  · have accepted : request.phase = .accepted := phase.resolve_right (by
      intro phase
      exact cancelled ((h.cancellation slot request localState hr hl).mpr phase))
    cases hc : localState.cached with
    | none => simp [hc] at cache
    | some d =>
      have result := consumer_invariant s.active h slot request localState toD d hr hl hc accepted
      cases toD with
      | false =>
        have cellN : s.active.deliveries.n = some slot := cell
        simpa [deliver,hp,cellN,hl,cancelled,hc,drained,consumerResidual] using result
      | true =>
        have cellD : s.active.deliveries.d = some slot := cell
        simp only [deliver,hp,Bool.false_eq_true,↓reduceIte,cellD,hl,hc,cancelled]
        rw [native_delay d localState.oldState]
        simpa [drained,consumerResidual,hc,cancelled] using result

theorem deliver_invariant (s : Session) (h : Invariant s.active) (toD : Bool) :
    Invariant (deliver s toD).session.active := by
  cases hp : s.prepared.isSome with
  | true => simpa [deliver,hp,reject] using h
  | false =>
    cases cell : (if toD then s.active.deliveries.d else s.active.deliveries.n) with
    | none => simpa only [deliver,hp,Bool.false_eq_true,↓reduceIte,cell,reject] using h
    | some slot => exact deliver_owned_invariant s h toD slot hp cell

theorem ownerInput_update (s : PendingMigration.Session) (slot i : Bool)
    (old next : PendingMigration.Request) (hr : s.requests.get slot = some old)
    (hi : next.input = old.input) : ownerInput (PendingMigration.update s slot next) i = ownerInput s i := by
  cases slot <;> cases i <;>
    simp_all [ownerInput,PendingMigration.update,PendingMigration.Slots.put,PendingMigration.Slots.get]

theorem projection_update (s : PendingMigration.Session) (slot : Bool)
    (old next : PendingMigration.Request) (hr : s.requests.get slot = some old)
    (hi : next.input = old.input) :
    delayProjection (PendingMigration.update s slot next) =
      PendingMigration.update (delayProjection s) slot (requestPayload next) := by
  have masks : ∀ i, ownerInput (PendingMigration.update s slot next) i = ownerInput s i :=
    fun i => ownerInput_update s slot i old next hr hi
  unfold delayProjection
  simp only [masks]
  cases slot <;> rfl

theorem compute_protocol_valid (s : Active) (h : Invariant s) (slot : Bool)
    (r : PendingMigration.Request) (head : PendingMigration.head s.protocol = some (slot,r))
    (phase : r.phase = .accepted) (output : Bool)
    (correct : output = (oracle r.input s.protocol.active.logical).1) :
    PendingMigration.Valid (delayProjection (PendingMigration.update s.protocol slot
      {r with output := output,phase := .computed})) := by
  obtain ⟨_,hr⟩ := PendingMigration.head_fields s.protocol slot r head
  rw [projection_update s.protocol slot r {r with output := output,phase := .computed} hr rfl]
  have mask : payload r.input output = s.protocol.active.logical := by
    rw [correct]
    exact payload_involutive r.input s.protocol.active.logical
  have transported : requestPayload {r with output := output,phase := .computed} =
      {requestPayload r with output := s.protocol.active.logical,phase := .computed} := by
    simp [requestPayload,mask]
  rw [transported]
  apply PendingMigration.evaluate_head_valid _ slot (requestPayload r) h.protocol
  · rw [projected_head,head]; rfl
  · exact phase

theorem compute_invariant (s : Active) (h : Invariant s) (slot : Bool)
    (r : PendingMigration.Request) (head : PendingMigration.head s.protocol = some (slot,r))
    (phase : r.phase = .accepted) (output : Bool)
    (correct : output = (oracle r.input s.protocol.active.logical).1)
    (empty : s.deliveries = {}) :
    Invariant {s with protocol := (PendingMigration.update s.protocol slot {r with output := output,phase := .computed})} := by
  obtain ⟨headEq,hr⟩ := PendingMigration.head_fields s.protocol slot r head
  constructor
  · exact compute_protocol_valid s h slot r head phase output correct
  · intro i request hi
    change (s.protocol.requests.put slot (some _)).get i = some request at hi
    by_cases same : i = slot
    · subst i
      simp only [PendingMigration.slots_get_put_same,Option.some.injEq] at hi
      subst request
      exact h.residual slot r hr
    · rw [get_put_ne _ slot i _ same] at hi
      exact h.residual i request hi
  · intro i request localState hi hl phases cache
    change (s.protocol.requests.put slot (some _)).get i = some request at hi
    by_cases same : i = slot
    · subst i
      simp only [PendingMigration.slots_get_put_same,Option.some.injEq] at hi
      subst request
      exact h.current slot r localState hr hl (Or.inl phase) cache
    · rw [get_put_ne _ slot i _ same] at hi
      exact h.current i request localState hi hl phases cache
  · intro i reference
    change s.deliveries.references i = true at reference
    simp [empty,Deliveries.references] at reference
  · intro i request localState hi hl
    change (s.protocol.requests.put slot (some _)).get i = some request at hi
    by_cases same : i = slot
    · subst i
      simp only [PendingMigration.slots_get_put_same,Option.some.injEq] at hi
      subst request
      simpa [phase] using h.cancellation slot r localState hr hl
    · rw [get_put_ne _ slot i _ same] at hi
      exact h.cancellation i request localState hi hl
  · exact h.cache_head
  · exact h.completed_cache

theorem no_head_references (s : Active) (h : Invariant s) (slot : Bool)
    (head : s.protocol.order.head? = some slot)
    (none : s.deliveries.references slot = false) : s.deliveries = {} := by
  have absent (i : Bool) : s.deliveries.references i = false := by
    cases hi : s.deliveries.references i with
    | false => rfl
    | true =>
      obtain ⟨r,localState,_,hl,cache,_⟩ := h.delivery i hi
      have same : i = slot := Option.some.inj ((h.cache_head i localState hl cache).symm.trans head)
      subst i
      simp [none] at hi
  have d : s.deliveries.d = Option.none := by
    cases hd : s.deliveries.d with
    | none => rfl
    | some i => have := absent i; simp [Deliveries.references,hd] at this
  have n : s.deliveries.n = Option.none := by
    cases hn : s.deliveries.n with
    | none => rfl
    | some i => have := absent i; simp [Deliveries.references,hn] at this
  exact congrArg₂ Deliveries.mk d n

@[simp] theorem native_xor (a b : Bool) : Applications.Circuits.Circuit.xor.execute (a,b) = Bool.xor a b := by
  cases a <;> cases b <;> rfl

theorem join_invariant (s : Session) (h : Invariant s.active) :
    Invariant (join s).session.active := by
  unfold join
  split
  · exact h
  · cases hh : headResidual s.active with
    | none => exact h
    | some triple =>
      obtain ⟨slot,r,localState⟩ := triple
      dsimp only
      split
      · exact h
      · rename_i guard
        have facts : r.phase = .accepted ∧ localState.cancelled = false ∧
            s.active.deliveries.references slot = false := by
          simpa [Bool.or_eq_true,and_assoc] using guard
        obtain ⟨headPair,localEq⟩ := headResidual_fields s.active slot r localState hh
        obtain ⟨headEq,requestEq⟩ := PendingMigration.head_fields s.active.protocol slot r headPair
        have empty := no_head_references s.active h slot headEq facts.2.2
        obtain ⟨old,ho,correct⟩ := h.residual slot r requestEq
        have eq : old = localState := Option.some.inj (ho.symm.trans localEq)
        subst old
        cases hd : localState.dResult <;> cases hn : localState.nResult <;> cases hc : localState.candidate
        all_goals try exact h
        rename_i d n candidate
        have cache := h.completed_cache slot localState localEq (Or.inl (by simp [hd]))
        have current := h.current slot r localState requestEq localEq (Or.inl facts.1) cache
        have output : Applications.Circuits.Circuit.xor.execute (d,n) =
            (oracle r.input s.active.protocol.active.logical).1 := by
          rw [native_xor,correct.2.1 d hd,correct.2.2.1 n hn,current]
          rfl
        exact compute_invariant s.active h slot r headPair facts.1 _ output empty

theorem whole_invariant (s : Session) (h : Invariant s.active) :
    Invariant (whole s).session.active := by
  unfold whole
  split
  · exact h
  · cases hh : headResidual s.active with
    | none => exact h
    | some triple =>
      obtain ⟨slot,r,localState⟩ := triple
      dsimp only
      split
      · exact h
      · rename_i guard
        have facts : r.phase = .accepted ∧ localState.cancelled = false ∧
            localState.dResult = none ∧ localState.nResult = none ∧
            s.active.deliveries.d = some slot ∧ s.active.deliveries.n = some slot := by
          simpa [Bool.or_eq_true,and_assoc] using guard
        obtain ⟨headPair,localEq⟩ := headResidual_fields s.active slot r localState hh
        obtain ⟨headEq,requestEq⟩ := PendingMigration.head_fields s.active.protocol slot r headPair
        cases cacheEq : localState.cached with
        | none => exact h
        | some d =>
          obtain ⟨old,ho,correct⟩ := h.residual slot r requestEq
          have eq : old = localState := Option.some.inj (ho.symm.trans localEq)
          subst old
          have cache : localState.cached.isSome = true := by simp [cacheEq]
          have current := h.current slot r localState requestEq localEq (Or.inl facts.1) cache
          have value := correct.1 d cacheEq
          let result := wholeResult s.active.cut d localState.oldState
          have semantics : result = oracle r.input s.active.protocol.active.logical := by
            simpa [result,value,current] using whole_correct s.active.cut d localState.oldState
          let computed := {r with output := result.1,phase := PendingMigration.Phase.computed}
          let base : Active := {s.active with
            protocol := PendingMigration.update s.active.protocol slot computed
            deliveries := {}}
          have cleared : Invariant {s.active with deliveries := {}} :=
            replace_deliveries s.active h {} (by intro i reference; simp [Deliveries.references] at reference)
          have baseValid : Invariant base := compute_invariant _ cleared slot r headPair facts.1 _
            (congrArg Prod.fst semantics) rfl
          let next := {localState with candidate := some result.2}
          have finished : Invariant (updateResidual base slot next) := by
            apply replace_residual base baseValid slot computed next
            · simp [base,PendingMigration.update]
            · exact headEq
            · have nextState : result.2 = r.input := congrArg Prod.snd semantics
              simp only [next,computed,ResidualCorrect]
              exact ⟨correct.1,correct.2.1,correct.2.2.1,by intro v hv; exact (Option.some.inj hv).symm.trans nextState⟩
            · intro _ _; exact current
            · simp [next,computed,facts.2.1]
            · simp [next,cacheEq]
            · simp [next,cacheEq]
          simpa [base,next,computed,result,cacheEq] using finished

theorem join_source (s : Session) : source (join s).session.active = source s.active := by
  unfold join
  split
  · rfl
  · cases hh : headResidual s.active with
    | none => rfl
    | some triple =>
      obtain ⟨slot,r,localState⟩ := triple
      dsimp only
      split
      · rfl
      · cases hd : localState.dResult <;> cases hn : localState.nResult <;> cases hc : localState.candidate
        all_goals try rfl
        apply source_of_protocol_source
        exact PendingMigration.head_update_source s.active.protocol slot r _
          (headResidual_fields s.active slot r localState hh).1 rfl

theorem whole_source (s : Session) : source (whole s).session.active = source s.active := by
  unfold whole
  split
  · rfl
  · cases hh : headResidual s.active with
    | none => rfl
    | some triple =>
      obtain ⟨slot,r,localState⟩ := triple
      dsimp only
      split
      · rfl
      · cases hc : localState.cached with
        | none => rfl
        | some d =>
          apply source_of_protocol_source
          exact PendingMigration.head_update_source s.active.protocol slot r _
            (headResidual_fields s.active slot r localState hh).1 rfl

theorem join_refines (s : Session) :
    SourceStep (source s.active) (join s) (source (join s).session.active) := by
  rw [join_source]
  apply SourceStep.internal
  all_goals unfold join
  all_goals repeat' first | rfl | split | (dsimp only) | simp [reject]

theorem whole_refines (s : Session) :
    SourceStep (source s.active) (whole s) (source (whole s).session.active) := by
  rw [whole_source]
  apply SourceStep.internal
  all_goals unfold whole
  all_goals repeat' first | rfl | split | (dsimp only) | simp [reject]

@[simp] theorem transported_message_slot (owner : Bool) (m : PendingMigration.Message) :
    (messagePayload owner m).slot = m.slot := by cases m <;> rfl

theorem queued_request_owner (s : PendingMigration.Session) (m : PendingMigration.Message)
    (hm : m ∈ s.queue.messages) (hs : PendingMigration.Valid (delayProjection s)) :
    ∃ r, s.requests.get m.slot = some r := by
  have valid := hs.messages (messagePayload (ownerInput s m.slot) m)
    (List.mem_map.mpr ⟨m,hm,rfl⟩)
  obtain ⟨_,q,hq,_⟩ := valid
  simp only [transported_message_slot,delayProjection,get_mapSlots,Option.map_eq_some_iff] at hq
  obtain ⟨r,hr,_⟩ := hq
  exact ⟨r,hr⟩

theorem mapSlots_put {α β : Type} (f : α → β) (s : PendingMigration.Slots α)
    (slot : Bool) (v : Option α) :
    mapSlots f (s.put slot v) = (mapSlots f s).put slot (v.map f) := by
  cases slot <;> rfl

theorem projection_admission (s : PendingMigration.Session) (slot input : Bool)
    (hs : PendingMigration.Valid (delayProjection s)) (free : s.requests.get slot = none) :
    delayProjection (PendingMigration.admission s slot input) =
      PendingMigration.admission (delayProjection s) slot input := by
  have messages : s.queue.messages.map (fun m =>
      messagePayload (ownerInput (PendingMigration.admission s slot input) m.slot) m) =
      s.queue.messages.map (fun m => messagePayload (ownerInput s m.slot) m) := by
    apply List.map_congr_left
    intro m hm
    obtain ⟨r,hr⟩ := queued_request_owner s m hm hs
    have ne : m.slot ≠ slot := by intro eq; simp [eq,free] at hr
    simp [ownerInput,PendingMigration.admission,PendingMigration.slots_get_put,ne]
  simp only [delayProjection,PendingMigration.admission,mapSlots_put,Option.map_some]
  simp only [requestPayload,ownLedger]
  congr 1
  congr 1

@[simp] theorem residual_protocol_replace (s : Active) (p : PendingMigration.Session) :
    ({s with protocol := p} : Active).residuals = s.residuals := rfl

/-- Admission installs an empty internal continuation only in a free owner slot. -/
theorem admission_invariant (s : Active) (slot input : Bool) (hs : Invariant s)
    (free : s.protocol.requests.get slot = none) :
    Invariant (updateResidual {s with protocol := PendingMigration.admission s.protocol slot input}
      slot {}) := by
  have pf : (delayProjection s.protocol).requests.get slot = none := by
    simp [delayProjection,free]
  have pv := PendingMigration.admission_valid (delayProjection s.protocol) slot input hs.protocol pf
  rw [← projection_admission s.protocol slot input hs.protocol free] at pv
  have absent : slot ∉ s.protocol.order := by
    intro hm
    have := (hs.protocol.occupied slot).mp hm
    simp [delayProjection,free] at this
  constructor
  · exact pv
  · intro i r hr
    by_cases eq : i = slot
    · subst i
      simp only [updateResidual,Active.withResiduals,PendingMigration.admission,PendingMigration.slots_get_put_same,
        Option.some.injEq] at hr
      subst r
      exact ⟨{},by simp [residual_update],by simp [ResidualCorrect]⟩
    · have old : s.protocol.requests.get i = some r := by
        simpa [updateResidual,Active.withResiduals,PendingMigration.admission,PendingMigration.slots_get_put,eq] using hr
      obtain ⟨localState,hl,hc⟩ := hs.residual i r old
      exact ⟨localState,by simpa [residual_update,residual_protocol_replace,PendingMigration.slots_get_put,eq] using hl,hc⟩
  · intro i r localState hr hl hp hc
    by_cases eq : i = slot
    · subst i
      simp only [residual_update,residual_protocol_replace,PendingMigration.slots_get_put_same,Option.some.injEq] at hl
      subst localState
      simp at hc
    · apply hs.current i r localState
      · simpa [updateResidual,Active.withResiduals,PendingMigration.admission,PendingMigration.slots_get_put,eq] using hr
      · simpa [residual_update,residual_protocol_replace,PendingMigration.slots_get_put,eq] using hl
      · exact hp
      · exact hc
  · intro i hi
    obtain ⟨r,localState,hr,hl,hc,hp⟩ := hs.delivery i hi
    have ne : i ≠ slot := by intro eq; simp [eq,free] at hr
    exact ⟨r,localState,by simpa [updateResidual,Active.withResiduals,PendingMigration.admission,
      PendingMigration.slots_get_put,ne] using hr,
      by simpa [residual_update,residual_protocol_replace,PendingMigration.slots_get_put,ne] using hl,hc,hp⟩
  · intro i r localState hr hl
    by_cases eq : i = slot
    · subst i
      simp only [residual_update,residual_protocol_replace,PendingMigration.slots_get_put_same,Option.some.injEq] at hl
      subst localState
      simp [updateResidual,Active.withResiduals,PendingMigration.admission] at hr
      subst r
      simp
    · apply hs.cancellation i r localState
      · simpa [updateResidual,Active.withResiduals,PendingMigration.admission,PendingMigration.slots_get_put,eq] using hr
      · simpa [residual_update,residual_protocol_replace,PendingMigration.slots_get_put,eq] using hl
  · intro i localState hl hc
    by_cases eq : i = slot
    · subst i
      simp only [residual_update,residual_protocol_replace,PendingMigration.slots_get_put_same,Option.some.injEq] at hl
      subst localState
      simp at hc
    · have old : s.residuals.get i = some localState := by
        simpa [residual_update,residual_protocol_replace,PendingMigration.slots_get_put,eq] using hl
      have hh := hs.cache_head i localState old hc
      have nonempty : s.protocol.order ≠ [] := by intro h; simp [h] at hh
      simpa [updateResidual,Active.withResiduals,PendingMigration.admission,List.head?_append_of_ne_nil _ nonempty] using hh
  · intro i localState hl hc
    by_cases eq : i = slot
    · subst i
      simp only [residual_update,residual_protocol_replace,PendingMigration.slots_get_put_same,Option.some.injEq] at hl
      subst localState
      simp at hc
    · apply hs.completed_cache i localState _ hc
      simpa [residual_update,residual_protocol_replace,PendingMigration.slots_get_put,eq] using hl

theorem admission_source_joint (s : Active) (slot input : Bool) (hs : Invariant s)
    (free : s.protocol.requests.get slot = none) :
    source (updateResidual {s with protocol := PendingMigration.admission s.protocol slot input} slot {}) =
      ⟨(source s).state,(source s).waiting ++ [input]⟩ := by
  have pf : (delayProjection s.protocol).requests.get slot = none := by simp [delayProjection,free]
  have hh := PendingMigration.admission_source (delayProjection s.protocol) slot input hs.protocol pf
  rw [← projection_admission s.protocol slot input hs.protocol free,
    projection_source,projection_source] at hh
  exact congrArg (fun p : PendingMigration.Source => Source.mk p.state p.waiting) hh

theorem accept_invariant (s : Session) (input : Bool) (hs : Invariant s.active) :
    Invariant (accept s input).session.active := by
  unfold accept
  split
  · exact hs
  · simp only [PendingMigration.step]
    split
    · exact hs
    · split
      · exact hs
      · split
        · exact hs
        · rename_i slot heq
          have free : s.active.protocol.requests.get slot = none := by
            split at heq
            · rename_i hf
              have eq := Option.some.inj heq
              subst slot
              exact Option.isNone_iff_eq_none.mp hf
            · split at heq
              · rename_i ht
                have eq := Option.some.inj heq
                subst slot
                exact Option.isNone_iff_eq_none.mp ht
              · contradiction
          simpa [PendingMigration.admission] using admission_invariant s.active slot input hs free

theorem accept_rejected_refines (s : Session) (input : Bool) (status : PendingMigration.Status)
    (ho : s.prepared.isSome ≠ true) (hstatus : status ≠ .accepted)
    (he : PendingMigration.step s.active.protocol (.accept input) = PendingMigration.reject s.active.protocol status) :
    SourceStep (source s.active) (accept s input) (source (accept s input).session.active) := by
  unfold accept
  rw [ite_eq_right ho,he]
  dsimp only [PendingMigration.reject]
  simp only [beq_iff_eq,hstatus,↓reduceIte]
  exact .internal _ _ rfl rfl (by simp)

theorem accept_admitted_refines (s : Session) (slot input : Bool) (hs : Invariant s.active)
    (ho : s.prepared.isSome ≠ true) (free : s.active.protocol.requests.get slot = none)
    (he : PendingMigration.step s.active.protocol (.accept input) =
      ⟨PendingMigration.admission s.active.protocol slot input,.accepted,some input,none,none,[]⟩) :
    SourceStep (source s.active) (accept s input) (source (accept s input).session.active) := by
  unfold accept
  rw [ite_eq_right ho,he]
  dsimp only
  simp only [beq_self_eq_true,↓reduceIte]
  simp only [PendingMigration.admission,List.getLast?_append,List.getLast?_singleton,Option.some_or]
  change SourceStep _ _ (source (updateResidual
    {s.active with protocol := PendingMigration.admission s.active.protocol slot input} slot {}))
  rw [admission_source_joint s.active slot input hs free]
  exact .accept _ _ input rfl rfl rfl

theorem accept_refines (s : Session) (input : Bool) (hs : Invariant s.active) :
    SourceStep (source s.active) (accept s input) (source (accept s input).session.active) := by
  by_cases ho : s.prepared.isSome = true
  · simp only [accept,ho,↓reduceIte]
    exact .internal _ _ rfl rfl (by simp [reject])
  by_cases hp : s.active.protocol.prepared.isSome = true
  · apply accept_rejected_refines s input .busy ho (by decide)
    simp [PendingMigration.step,hp]
  by_cases hf : s.active.protocol.order.length ≥ 2
  · apply accept_rejected_refines s input .full ho (by decide)
    simp [PendingMigration.step,hp,hf]
  by_cases hl : (s.active.protocol.requests.get false).isNone = true
  · apply accept_admitted_refines s false input hs ho (Option.isNone_iff_eq_none.mp hl)
    simp [PendingMigration.step,PendingMigration.admission,hp,hf,hl]
  by_cases hr : (s.active.protocol.requests.get true).isNone = true
  · apply accept_admitted_refines s true input hs ho (Option.isNone_iff_eq_none.mp hr)
    simp [PendingMigration.step,PendingMigration.admission,hp,hf,hl,hr]
  · apply accept_rejected_refines s input .full ho (by decide)
    simp [PendingMigration.step,hp,hf,hl,hr]

end FRPSpec.Regional.Pending
