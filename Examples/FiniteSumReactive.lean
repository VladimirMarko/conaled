import Applications.FRP.FiniteSumReactive

/-! Retained alternatives, a compiled first-order consumer and explicit delay.
The reference transition was frozen before the lowering implementation. -/
namespace Examples.FiniteSumReactive
open FRPSpec.FiniteSum Applications.Circuits Progress.Feedback

abbrev S := Ty.sum .bool (.prod .bool .bool)
abbrev NativeState := Sum Bool (Bool × Bool)

def referenceStep (input : Bool) (state : NativeState) : Bool × NativeState :=
  match state with
  | .inl b => (b, if input then .inr (!b,b) else .inl b)
  | .inr (u,v) => (!u, if input then .inl u else .inr (u,v))

def reference : Initialized Bool Bool NativeState := ⟨fun (x,s) => referenceStep x s,.inl false⟩

def observation (s : Term Γ S) : Term Γ .bool :=
  .caseE s (.var .here) (.not (.fst (.var .here)))

def toggle (s : Term Γ S) : Term Γ S :=
  .caseE s (.inr (.pair (.not (.var .here)) (.var .here)))
    (.inl (.fst (.var .here)))

/-- The output let binder and both case binders retain the old state correctly. -/
def source : Source .bool .bool S where
  seed := .inl (.constant false)
  body := .letE (observation (.var (.there .here)))
    (.pair (.var .here)
      (.caseE (.test (.var (.there .here)))
        (.var (.there (.there (.there .here))))
        (toggle (.var (.there (.there (.there .here)))))))

theorem source_reference : source.meaning = reference := by
  have h : source.meaning.step = reference.step := by
    funext xs
    rcases xs with ⟨x,s⟩
    cases s with
    | inl b => cases x <;> cases b <;> rfl
    | inr p => rcases p with ⟨u,v⟩; cases x <;> cases u <;> cases v <;> rfl
  exact congrArg (fun f => Initialized.mk f (.inl false)) h

def inputs := [true,false,true,false,true]

example : run reference.mealy reference.initial inputs =
    ([false,false,false,true,true], .inr (false,true)) := by decide

/-- The computed circuit result is connected to the source preservation theorem. -/
theorem lowered_run (xs : List Bool) :
    List.Forall₂ (fun y bits => admit .bool bits = some y)
      (run reference.mealy reference.initial xs).1
      (run source.program.machine.mealy source.program.initial xs).1 ∧
    admit S (run source.program.machine.mealy source.program.initial xs).2 =
      some (run reference.mealy reference.initial xs).2 := by
  have hi : List.Forall₂ (fun x bits => admit .bool bits = some x) xs xs := by
    induction xs with
    | nil => exact .nil
    | cons x xs ih => exact .cons (admit_encode .bool x) ih
  have h := source.run_correct xs xs hi
  rw [source_reference] at h
  exact h

example : run source.program.machine.mealy source.program.initial inputs =
    ([false,false,false,true,true], (true,(false,(false,true)))) := by decide

example : (inputs.map fun x => (referenceStep x (.inl false)).1) ≠
    (run source.program.machine.mealy source.program.initial inputs).1 := by decide
example : (!false) ≠ (source.program.body.execute (false,source.program.initial)).1 := by decide

example : admit S (false,(true,(false,false))) = some (.inl true) := by decide
example : admit S (true,(false,(true,false))) = some (.inr (true,false)) := by decide
example : admit S (false,(true,(true,false))) = none := by decide
example : admit S (true,(true,(true,false))) = none := by decide
-- Invalid active nested sum is rejected even when the outer inactive slot is canonical.
example : admit (.sum S .bool) (false,((false,(true,(true,false))),false)) = none := by decide
example : source.tick false (true,(true,(true,false))) = none := by decide

/-- Invalid external sum inputs are rejected before a stateless regional body. -/
def sumInputSource : Source S .bool .unit where
  seed := .unit
  body := .pair (observation (.var .here)) .unit

example : sumInputSource.tick (false,(true,(true,false))) () = none := by decide
example : sumInputSource.tick (true,(false,(false,true))) () = some (true,()) := by decide

/-- Neither regional interface changes FirstOrderCompiler.Target. -/
def downstreamTerm : FirstOrderCompiler.Term Gate [.base] .base :=
  .prim (.not 0) (.var .here)
def downstream : Circuit .base .base :=
  .compose (FirstOrderCompiler.compile Circuit.target downstreamTerm) (.pair .terminate .identity)

theorem downstream_correct (x : Bool) : downstream.execute x = !x := by
  change (FirstOrderCompiler.compile Circuit.target downstreamTerm).execute ((),x) = !x
  exact (Circuit.execute_correct _ _).trans (Circuit.compile_value downstreamTerm ((),x))

def pipeline := (source.program.seq (FRPSpec.Indefinite.Program.pure downstream)).seq
  (FRPSpec.Indefinite.Program.delay (a := .base) false)

example : (run pipeline.machine.mealy pipeline.initial inputs).1 =
    [false,true,true,true,false] := by decide

/-- The ordinary first-order consumer and delay compose through the existing
ordered runner law; the retained state includes all three regional states. -/
theorem pipeline_run (xs : List Bool) :
    run pipeline.machine.mealy pipeline.initial xs =
      let first := run source.program.machine.mealy source.program.initial xs
      let middle := run (FRPSpec.Indefinite.Program.pure downstream).machine.mealy () first.1
      let last := run (FRPSpec.Indefinite.Program.delay (a := .base) false).machine.mealy false middle.1
      (last.1,((first.2,middle.2),last.2)) := by
  change run (Progress.Feedback.seq
    (Progress.Feedback.seq source.program.machine
      (FRPSpec.Indefinite.Program.pure downstream).machine)
    (FRPSpec.Indefinite.Program.delay (a := .base) false).machine).mealy _ xs = _
  rw [run_seq, run_seq]
  rfl

/-- A sum-valued boundary adapter converts a canonical four-cell payload into
one Boolean. The second region still compiles against the original target. -/
def regionTerm : Term [S] .bool := observation (.var .here)
def region : Circuit S.storage .base :=
  .compose (lower regionTerm) (.pair .terminate .identity)
def regions : Circuit S.storage .base := .compose downstream region

theorem region_correct (st : NativeState) : region.execute (encode (a := S) st) =
    (referenceStep false st).1 := by
  change (lower regionTerm).execute (encodeEnv (Γ := [S]) ((),st)) = _
  rw [lower_correct]
  cases st <;> rfl

theorem regions_admitted (raw : Bits S) (st : NativeState) (h : admit S raw = some st) :
    regions.execute raw = !(referenceStep false st).1 := by
  rw [(admit_iff S raw st).mp h]
  change downstream.execute (region.execute (encode st)) = _
  rw [region_correct, downstream_correct]

theorem regions_work : regions.work = region.work + downstream.work + 1 := rfl

example : (validator S).execute (false,(true,(true,false))) = false := by decide
example : (validator S).execute (true,(false,(true,false))) = true := by decide
example : regions.execute (false,(true,(false,false))) = false := by decide
example : regions.execute (true,(false,(false,true))) = false := by decide

/-- Every boundary intermediate and retained payload is charged by the circuit
arena. Sequencing overhead is the existing checked cost, not a new estimate. -/
theorem pipeline_work : pipeline.body.work = source.program.body.work +
    (FRPSpec.Indefinite.Program.pure downstream).body.work +
    (FRPSpec.Indefinite.Program.delay (a := .base) false).body.work + 62 := by
  simp only [pipeline, FRPSpec.Indefinite.Program.seq_work]
  omega

theorem pipeline_space (input : Progress.Stream Bool) (n k : Nat) :
    FRPSpec.Indefinite.Program.retained (state pipeline.machine input n) +
      (pipeline.body.allocations.take k).sum ≤ 5 + pipeline.body.arena :=
  pipeline.uniform input n k

/-- Tags are consumed by the sum region. Its Boolean boundary has one cell and
canonical admission is total; the downstream target needs only cartesian gates. -/
example : cells Ty.bool.storage = 1 ∧ ∀ b : Bool, admit .bool b = some b :=
  ⟨rfl,admit_encode .bool⟩
example : cells S.storage = 4 := rfl
example : downstream.work = 7 := rfl

/-- An inactive arm still has work. Both nontrivial arms are present in the actual block. -/
def leftArm : Circuit (.prod .unit .base) .base := .compose Circuit.not .second
def rightArm : Circuit (.prod .unit (.prod .base .base)) .base :=
  .compose Circuit.not (.compose .first .second)
example : leftArm.work = 3 ∧ rightArm.work = 5 ∧ (mux .base).work = 25 := ⟨rfl,rfl,rfl⟩
example : (caseCircuit leftArm rightArm).work = 55 := by
  rw [caseCircuit_work]
  rfl
example : (caseCircuit leftArm rightArm).execute ((),(false,(false,(true,false)))) = true := by decide
example : (caseCircuit leftArm rightArm).execute ((),(true,(false,(true,false)))) = false := by decide

example : (caseCircuit leftArm rightArm).execute ((),(false,(false,(true,false)))) ≠
    (caseCircuit leftArm rightArm).execute ((),(true,(false,(true,false)))) := by decide

-- Concrete resource values are checked against actual generated code.
example : source.program.body.work = 543 ∧ source.program.body.arena = 4272 := ⟨rfl,rfl⟩
example : source.tickWork = 641 ∧ 4 + source.tickArena = 4736 := ⟨rfl,rfl⟩
example : (validator S).work = 85 ∧ (validator S).arena = 395 := ⟨rfl,rfl⟩
example : region.work = 61 ∧ region.arena = 454 := ⟨rfl,rfl⟩
example : regions.work = 69 ∧ regions.arena = 480 := ⟨rfl,rfl⟩
example : pipeline.body.work = 619 ∧ 5 + pipeline.body.arena = 4891 := ⟨rfl,rfl⟩

end Examples.FiniteSumReactive
