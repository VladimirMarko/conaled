import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Data.Fintype.Sets

/-!
# Same-count restriction of supported native primitive machines

The existing machine map commutes with each supported native transition.
Transport the actual optional iterates and evaluation witnesses with unchanged
steps, then restrict control to its actual finite support. The original supplied
default and entire tape are retained. Ambient control need not be finite.

The proof-side retraction is noncomputable. The separate support-closed
transition evaluates the original transition and attaches the closure proof,
performing no runtime membership decision or fallback. Its extensional equality
to the map restriction transfers the same-count facts. This does not extract a
numeric state enumeration or transition table.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.TuringSimulation.FiniteControl

open Function Turing

section MapTiming

variable {Γ Γ' Q Q' : Type*}
variable [Inhabited Γ] [Inhabited Γ'] [Inhabited Q] [Inhabited Q']
variable (M : TM0.Machine Γ Q)
variable (f₁ : PointedMap Γ Γ') (f₂ : PointedMap Γ' Γ)
variable (g₁ : Q → Q') (g₂ : Q' → Q)
variable {S : Set Q} (ss : TM0.Supports M S)
variable (hf : Function.RightInverse f₁ f₂)
variable (hg : ∀ q ∈ S, g₂ (g₁ q) = q)

include ss hf hg

/-- Exact optional-iterate transport for the existing native machine map.
Every member of the starting option is supported; the statement also covers
an absent start and live runs that later return outer `none`. -/
theorem map_iterate_option (n : ℕ) (x : Option (TM0.Cfg Γ Q))
    (hx : ∀ c ∈ x, c.q ∈ S) :
    ((flip Bind.bind (TM0.step M))^[n] x).map (TM0.Cfg.map f₁ g₁) =
      (flip Bind.bind (TM0.step (M.map f₁ f₂ g₁ g₂)))^[n]
        (x.map (TM0.Cfg.map f₁ g₁)) := by
  induction n generalizing x with
  | zero => rfl
  | succ n IH =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    cases x with
    | none =>
      change ((flip Bind.bind (TM0.step M))^[n] none).map (TM0.Cfg.map f₁ g₁) =
        (flip Bind.bind (TM0.step (M.map f₁ f₂ g₁ g₂)))^[n] none
      exact IH none (by intro c h; cases h)
    | some c =>
      change ((flip Bind.bind (TM0.step M))^[n] (TM0.step M c)).map
          (TM0.Cfg.map f₁ g₁) =
        (flip Bind.bind (TM0.step (M.map f₁ f₂ g₁ g₂)))^[n]
          (TM0.step (M.map f₁ f₂ g₁ g₂) (TM0.Cfg.map f₁ g₁ c))
      rw [← M.map_step f₁ f₂ g₁ g₂ hf hg c (hx c rfl)]
      apply IH
      intro c' hc'
      exact TM0.step_supports M ss hc' (hx c rfl)

/-- Supported source configurations have the same exact optional-iteration
count after mapping. The target option preserves live halt versus outer none. -/
theorem map_iterate (n : ℕ) (c : TM0.Cfg Γ Q) (hc : c.q ∈ S) :
    ((flip Bind.bind (TM0.step M))^[n] (some c)).map (TM0.Cfg.map f₁ g₁) =
      (flip Bind.bind (TM0.step (M.map f₁ f₂ g₁ g₂)))^[n]
        (some (TM0.Cfg.map f₁ g₁ c)) :=
  map_iterate_option M f₁ f₂ g₁ g₂ ss hf hg n (some c) (by
    intro c' h
    cases h
    exact hc)

/-- Transport an actual native evaluation witness without changing `steps`. -/
def mapEvalsTo (c : TM0.Cfg Γ Q) (hc : c.q ∈ S)
    (b : Option (TM0.Cfg Γ Q))
    (h : StateTransition.EvalsTo (TM0.step M) c b) :
    StateTransition.EvalsTo (TM0.step (M.map f₁ f₂ g₁ g₂))
      (TM0.Cfg.map f₁ g₁ c) (b.map (TM0.Cfg.map f₁ g₁)) where
  steps := h.steps
  evals_in_steps := by
    have transported := map_iterate M f₁ f₂ g₁ g₂ ss hf hg h.steps c hc
    rw [h.evals_in_steps] at transported
    exact transported.symm

@[simp] theorem mapEvalsTo_steps (c : TM0.Cfg Γ Q) (hc : c.q ∈ S)
    (b : Option (TM0.Cfg Γ Q))
    (h : StateTransition.EvalsTo (TM0.step M) c b) :
    (mapEvalsTo M f₁ f₂ g₁ g₂ ss hf hg c hc b h).steps = h.steps := rfl

/-- The original time bound is retained literally because the actual native
evaluation count is unchanged. No witness of a desired new count is assumed. -/
def mapEvalsToInTime (c : TM0.Cfg Γ Q) (hc : c.q ∈ S)
    (b : Option (TM0.Cfg Γ Q)) (B : ℕ)
    (h : StateTransition.EvalsToInTime (TM0.step M) c b B) :
    StateTransition.EvalsToInTime (TM0.step (M.map f₁ f₂ g₁ g₂))
      (TM0.Cfg.map f₁ g₁ c) (b.map (TM0.Cfg.map f₁ g₁)) B where
  toEvalsTo := mapEvalsTo M f₁ f₂ g₁ g₂ ss hf hg c hc b h.toEvalsTo
  steps_le_m := h.steps_le_m

@[simp] theorem mapEvalsToInTime_steps (c : TM0.Cfg Γ Q) (hc : c.q ∈ S)
    (b : Option (TM0.Cfg Γ Q)) (B : ℕ)
    (h : StateTransition.EvalsToInTime (TM0.step M) c b B) :
    (mapEvalsToInTime M f₁ f₂ g₁ g₂ ss hf hg c hc b B h).steps = h.steps := rfl

end MapTiming

end Resources.TuringSimulation.FiniteControl


namespace Resources.TuringSimulation.FiniteControl

open Function Turing

section Identity

variable (Γ : Type*) [Inhabited Γ]

/-- Identity of the actual tape alphabet, including its existing blank. -/
def identityPointed : PointedMap Γ Γ := ⟨id, rfl⟩

variable {Γ}

theorem listBlank_map_identity (L : ListBlank Γ) :
    L.map (identityPointed Γ) = L := by
  refine L.induction_on ?_
  intro l
  change ListBlank.mk (l.map id) = ListBlank.mk l
  rw [List.map_id]

theorem tape_map_identity (T : Tape Γ) :
    T.map (identityPointed Γ) = T := by
  cases T with
  | mk a L R =>
    change Tape.mk a (L.map (identityPointed Γ)) (R.map (identityPointed Γ)) =
      Tape.mk a L R
    rw [listBlank_map_identity, listBlank_map_identity]

end Identity

section Labels

variable {Q : Type*} [Inhabited Q]

/-- The original default as an element of the actual finite support. This is
an explicit value, rather than an instance selecting a different start state. -/
@[instance_reducible] def restrictedInhabited (S : Finset Q) (hdefault : default ∈ S) :
    Inhabited {q : Q // q ∈ S} :=
  ⟨⟨default, hdefault⟩⟩

/-- Total label map into the finite support. The fallback is unreachable
along runs certified by `TM0.Supports`. -/
noncomputable def restrictLabel (S : Finset Q) (hdefault : default ∈ S)
    (q : Q) : {q : Q // q ∈ S} := by
  classical
  exact if h : q ∈ S then ⟨q, h⟩ else ⟨default, hdefault⟩

theorem restrictLabel_val (S : Finset Q) (hdefault : default ∈ S)
    (q : Q) (hq : q ∈ S) :
    (restrictLabel S hdefault q).val = q := by
  classical
  simp only [restrictLabel, dite_eq_left hq]

theorem restrictLabel_default (S : Finset Q) (hdefault : default ∈ S) :
    restrictLabel S hdefault default = ⟨default, hdefault⟩ := by
  apply Subtype.ext
  exact restrictLabel_val S hdefault default hdefault

/-- The supported retraction sends the actual original default to the actual
subtype default, as required by native TM0 initialization. -/
noncomputable def restrictPointed (S : Finset Q) (hdefault : default ∈ S) :
    @PointedMap Q {q : Q // q ∈ S} _ (restrictedInhabited S hdefault) := by
  letI : Inhabited {q : Q // q ∈ S} := restrictedInhabited S hdefault
  exact ⟨restrictLabel S hdefault, restrictLabel_default S hdefault⟩

end Labels

section Machine

variable {Γ Q : Type*} [Inhabited Γ] [Inhabited Q]

/-- The existing machine map with both alphabet maps the pointed identity
and the control maps the supported retraction and subtype inclusion. -/
noncomputable def restrictMachine (M : TM0.Machine Γ Q)
    (S : Finset Q) (hdefault : default ∈ S) :
    @TM0.Machine Γ {q : Q // q ∈ S} (restrictedInhabited S hdefault) := by
  letI : Inhabited {q : Q // q ∈ S} := restrictedInhabited S hdefault
  exact M.map (identityPointed Γ) (identityPointed Γ)
    (restrictLabel S hdefault) Subtype.val

/-- The corresponding native configuration map retains the whole tape. -/
noncomputable def restrictCfg (S : Finset Q) (hdefault : default ∈ S) :
    TM0.Cfg Γ Q → TM0.Cfg Γ {q : Q // q ∈ S} :=
  TM0.Cfg.map (identityPointed Γ) (restrictLabel S hdefault)

theorem restrictCfg_eq (S : Finset Q) (hdefault : default ∈ S)
    (c : TM0.Cfg Γ Q) :
    restrictCfg S hdefault c = ⟨restrictLabel S hdefault c.q, c.Tape⟩ := by
  cases c with
  | mk q T =>
    change TM0.Cfg.mk (restrictLabel S hdefault q) (T.map (identityPointed Γ)) =
      TM0.Cfg.mk (restrictLabel S hdefault q) T
    rw [tape_map_identity]

theorem restrictCfg_supported (S : Finset Q) (hdefault : default ∈ S)
    (c : TM0.Cfg Γ Q) (hc : c.q ∈ S) :
    restrictCfg S hdefault c = ⟨⟨c.q, hc⟩, c.Tape⟩ := by
  rw [restrictCfg_eq]
  apply congrArg (fun q => (⟨q, c.Tape⟩ : TM0.Cfg Γ {q : Q // q ∈ S}))
  apply Subtype.ext
  exact restrictLabel_val S hdefault c.q hc

/-- One actual primitive step commutes with finite-control restriction. The
explicit default instance prevents a hidden change of initial state. -/
theorem restrict_step (M : TM0.Machine Γ Q) (S : Finset Q)
    (ss : TM0.Supports M (↑S)) (c : TM0.Cfg Γ Q) (hc : c.q ∈ S) :
    letI : Inhabited {q : Q // q ∈ S} := restrictedInhabited S ss.1
    (TM0.step M c).map (restrictCfg S ss.1) =
      TM0.step (restrictMachine M S ss.1) (restrictCfg S ss.1 c) := by
  let : Inhabited {q : Q // q ∈ S} := restrictedInhabited S ss.1
  exact M.map_step (identityPointed Γ) (identityPointed Γ)
    (restrictLabel S ss.1) Subtype.val (fun _ => rfl)
    (fun q hq => restrictLabel_val S ss.1 q hq) c hc

/-- The finite restriction starts at its actual native default on the same
input tape. There is no extra transition for relabeling control. -/
theorem restrict_init (S : Finset Q) (hdefault : default ∈ S) (l : List Γ) :
    letI : Inhabited {q : Q // q ∈ S} := restrictedInhabited S hdefault
    restrictCfg S hdefault (TM0.init l : TM0.Cfg Γ Q) =
      (TM0.init l : TM0.Cfg Γ {q : Q // q ∈ S}) := by
  let : Inhabited {q : Q // q ∈ S} := restrictedInhabited S hdefault
  rw [restrictCfg_eq]
  change TM0.Cfg.mk (restrictLabel S hdefault default) (Tape.mk₁ l) =
    TM0.Cfg.mk ⟨default, hdefault⟩ (Tape.mk₁ l)
  rw [restrictLabel_default]

end Machine

end Resources.TuringSimulation.FiniteControl


namespace Resources.TuringSimulation.FiniteControl

open Function Turing

variable {Γ Q : Type*} [Inhabited Γ] [Inhabited Q]

/-- Finite support restriction preserves the actual native evaluation witness
and its upper bound, with the original supported default as the finite default.
The ambient control carrier need not have a Fintype instance. -/
noncomputable def restrictEvalsToInTime
    (M : TM0.Machine Γ Q) (S : Finset Q) (ss : TM0.Supports M (↑S))
    (c : TM0.Cfg Γ Q) (hc : c.q ∈ S)
    (b : Option (TM0.Cfg Γ Q)) (B : ℕ)
    (h : StateTransition.EvalsToInTime (TM0.step M) c b B) :
    letI : Inhabited {q : Q // q ∈ S} := restrictedInhabited S ss.1
    StateTransition.EvalsToInTime (TM0.step (restrictMachine M S ss.1))
      (restrictCfg S ss.1 c) (b.map (restrictCfg S ss.1)) B := by
  letI : Inhabited {q : Q // q ∈ S} := restrictedInhabited S ss.1
  exact mapEvalsToInTime M (identityPointed Γ) (identityPointed Γ)
    (restrictLabel S ss.1) Subtype.val ss (fun _ => rfl)
    (fun q hq => restrictLabel_val S ss.1 q hq) c hc b B h

@[simp] theorem restrictEvalsToInTime_steps
    (M : TM0.Machine Γ Q) (S : Finset Q) (ss : TM0.Supports M (↑S))
    (c : TM0.Cfg Γ Q) (hc : c.q ∈ S)
    (b : Option (TM0.Cfg Γ Q)) (B : ℕ)
    (h : StateTransition.EvalsToInTime (TM0.step M) c b B) :
    (restrictEvalsToInTime M S ss c hc b B h).steps = h.steps := rfl

/-- Native TM0 initialization is transported on the same input tape, using
the actual default supplied by support. The source count remains literal. -/
noncomputable def restrictInitialEvalsToInTime
    (M : TM0.Machine Γ Q) (S : Finset Q) (ss : TM0.Supports M (↑S))
    (l : List Γ) (b : Option (TM0.Cfg Γ Q)) (B : ℕ)
    (h : StateTransition.EvalsToInTime (TM0.step M) (TM0.init l) b B) :
    letI : Inhabited {q : Q // q ∈ S} := restrictedInhabited S ss.1
    StateTransition.EvalsToInTime (TM0.step (restrictMachine M S ss.1))
      (TM0.init l : TM0.Cfg Γ {q : Q // q ∈ S})
      (b.map (restrictCfg S ss.1)) B := by
  letI : Inhabited {q : Q // q ∈ S} := restrictedInhabited S ss.1
  refine {
    toEvalsTo := {
      steps := h.steps
      evals_in_steps := ?_ }
    steps_le_m := h.steps_le_m }
  have e := (restrictEvalsToInTime M S ss
    (TM0.init l) ss.1 b B h).evals_in_steps
  change (flip Bind.bind (TM0.step (restrictMachine M S ss.1)))^[h.steps]
      (some (restrictCfg S ss.1 (TM0.init l))) =
    b.map (restrictCfg S ss.1) at e
  rw [restrict_init] at e
  exact e

@[simp] theorem restrictInitialEvalsToInTime_steps
    (M : TM0.Machine Γ Q) (S : Finset Q) (ss : TM0.Supports M (↑S))
    (l : List Γ) (b : Option (TM0.Cfg Γ Q)) (B : ℕ)
    (h : StateTransition.EvalsToInTime (TM0.step M) (TM0.init l) b B) :
    (restrictInitialEvalsToInTime M S ss l b B h).steps = h.steps := rfl

end Resources.TuringSimulation.FiniteControl


namespace Resources.TuringSimulation.FiniteControl

open Turing

variable {Γ Q : Type*} [Inhabited Γ] [Inhabited Q]

/-- A supported transition can be restricted constructively: the source
transition itself identifies the next label, and closure supplies its proof.
No classical choice, ambient equality or fallback branch occurs in this def. -/
def closedRestrictMachine (M : TM0.Machine Γ Q) (S : Finset Q)
    (ss : TM0.Supports M (↑S)) :
    @TM0.Machine Γ {q : Q // q ∈ S} (restrictedInhabited S ss.1) :=
  fun q a =>
    match h : M q.val a with
    | none => none
    | some (q', act) => some (⟨q', ss.2 h q.property⟩, act)

omit [Inhabited Γ] in
theorem closedRestrictMachine_none (M : TM0.Machine Γ Q) (S : Finset Q)
    (ss : TM0.Supports M (↑S)) (q : {q : Q // q ∈ S}) (a : Γ)
    (h : M q.val a = none) : closedRestrictMachine M S ss q a = none := by
  unfold closedRestrictMachine
  split <;> simp_all

omit [Inhabited Γ] in
theorem closedRestrictMachine_some (M : TM0.Machine Γ Q) (S : Finset Q)
    (ss : TM0.Supports M (↑S)) (q : {q : Q // q ∈ S}) (a : Γ)
    (q' : Q) (act : TM0.Stmt Γ) (h : M q.val a = some (q', act)) :
    closedRestrictMachine M S ss q a = some (⟨q', ss.2 h q.property⟩, act) := by
  unfold closedRestrictMachine
  split
  · simp_all
  · rename_i qNext actNext hstep
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (hstep.symm.trans h))
    rfl

omit [Inhabited Q] in
theorem stmt_map_identity (act : TM0.Stmt Γ) :
    act.map (identityPointed Γ) = act := by
  cases act <;> rfl

/-- Extensional equality to the existing native-map restriction. Existing
exact-step and optional-iterate transport therefore apply without any change
of time or endpoint. The equality proof does not add a runtime decision. -/
theorem closedRestrictMachine_eq (M : TM0.Machine Γ Q) (S : Finset Q)
    (ss : TM0.Supports M (↑S)) :
    closedRestrictMachine M S ss = restrictMachine M S ss.1 := by
  funext q a
  cases h : M q.val a with
  | none =>
    calc
      closedRestrictMachine M S ss q a = none :=
        closedRestrictMachine_none M S ss q a h
      _ = (M q.val a).map
          (Prod.map (restrictLabel S ss.1) (TM0.Stmt.map (identityPointed Γ))) := by
        simp only [h, Option.map_none]
      _ = restrictMachine M S ss.1 q a := rfl
  | some next =>
    rcases next with ⟨q', act⟩
    have hq' : q' ∈ S := ss.2 h q.property
    calc
      closedRestrictMachine M S ss q a = some (⟨q', hq'⟩, act) :=
        closedRestrictMachine_some M S ss q a q' act h
      _ = some (restrictLabel S ss.1 q', act) := by
        apply congrArg (fun label => some (label, act))
        apply Subtype.ext
        exact (restrictLabel_val S ss.1 q' hq').symm
      _ = (M q.val a).map
          (Prod.map (restrictLabel S ss.1) (TM0.Stmt.map (identityPointed Γ))) := by
        simp only [h, Option.map_some, Prod.map, stmt_map_identity]
      _ = restrictMachine M S ss.1 q a := rfl

end Resources.TuringSimulation.FiniteControl
