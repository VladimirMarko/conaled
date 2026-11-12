import Applications.Wasm.Correctness

/-! Discriminating cases for the selected Core 2 transcription. -/
namespace Examples.WasmCircuit
open Applications.Wasm

private def identityModule : Module := ⟨⟨[.i32], [.i32]⟩, [], [.get 0]⟩

/-- Existing function contents and nonfunction reference fields are retained.
The generated address is two, while its index in the new module is zero. -/
private def ambient : Store String (List Value) :=
  ⟨["arbitrary standard body", "host function"], [.funcref (some 1), .externref (some 37)]⟩

example : (identityModule.instantiate ambient).2.export "run" = some (.func 2) :=
  Module.export_run _ _

example : (identityModule.instantiate ambient).1.other =
    [.funcref (some 1), .externref (some 37)] := Store.extend_other _ _

example : (identityModule.instantiate ambient).1.funcs[1]? =
    some (.inl "host function") := Store.extend_old _ _ 1 (by decide)

example (encode : Function → String) :
    Store.reconstruct encode (identityModule.instantiate ambient).1 =
      ⟨["arbitrary standard body", "host function", encode (identityModule.function 2)],
        [.funcref (some 1), .externref (some 37)]⟩ :=
  Store.reconstruct_extend _ _ _

/-- Zero-testing uses the full i32 word, independently of Boolean admission. -/
example (s : ExtendedStore F O) (fr : Frame) :
    Step (I := Empty) s fr [.value (.i32 2), .instr .eqz] fr [.value (.i32 0)] :=
  Step.eqz _ _

/-- An i64 operand prefix and pending continuation survive the segment. -/
example (s : ExtendedStore F O) (fr : Frame) (rest : List (Admin Empty)) :
    Step (I := Empty) s fr ([.value (.i64 91)] ++ [.value (.i32 1), .value (.i32 1),
      .instr (.binary .xor)] ++ rest)
      fr ([.value (.i64 91)] ++ [.value (.i32 0)] ++ rest) :=
  Step.context (.seq [.i64 91] .hole rest) (Step.binary _ .xor 1 1)

example (s : Store F O) (x : BitVec 32) :
    Steps (I := Empty) (identityModule.instantiate s).1 dummyFrame
      (values [.i32 x] ++ [.invoke s.funcs.length]) dummyFrame (values [.i32 x]) := by
  apply invoke_of_body _ _ (identityModule.function s.funcs.length) _ _
    ⟨[.i32 x], identityModule.instance s.funcs.length⟩
  · exact Module.instantiate_lookup _ _
  · rfl
  · rfl
  · exact Steps.single (.get _ 0 _ rfl)

private def nested : FRPSpec.FiniteSum.Ty :=
  .sum (.sum .bool .unit) (.prod .bool .bool)

example : ABI.decodeSum nested [.i32 0, .i32 0, .i32 1, .i32 0, .i32 0] =
    some (.inl (.inl true)) := (ABI.decodeSum_iff _ _ _).2 rfl

example : ABI.decodeSum nested [.i32 0, .i32 1, .i32 0, .i32 0, .i32 0] =
    some (.inl (.inr ())) := (ABI.decodeSum_iff _ _ _).2 rfl

example : ABI.decodeSum nested [.i32 1, .i32 0, .i32 0, .i32 0, .i32 1] =
    some (.inr (false, true)) := (ABI.decodeSum_iff _ _ _).2 rfl

/-- Inactive nested payloads are rejected even though every slot is Boolean. -/
example : ABI.decodeSum nested [.i32 0, .i32 1, .i32 1, .i32 0, .i32 0] = none := by decide
example : ABI.decodeSum nested [.i32 1, .i32 1, .i32 0, .i32 0, .i32 1] = none := by decide
example : ABI.decode .base [.i32 2] = none := by decide
example : ABI.decode .base [.i64 1] = none := by decide
example : ABI.decode .base [.i32 1, .i32 0] = none := by decide
example : ABI.decode .base [] = none := by decide

/-- The retained foreign instruction is outside the segment. In particular,
this does not claim that resuming an unreachable instruction avoids a trap. -/
example (s : ExtendedStore F O) (fr : Frame) :
    Step (I := String) s fr
      [.value (.i32 1), .instr .eqz, .foreign "unreachable"]
      fr [.value (.i32 0), .foreign "unreachable"] :=
  Step.context (.seq [] .hole [.foreign "unreachable"]) (Step.eqz _ _)

example (r : Reconstruction String) (before : List (Admin String)) :
    (before ++ [Admin.foreign "memory.grow", Admin.foreign "unreachable"]).map (Admin.reconstruct r) =
      before.map (Admin.reconstruct r) ++ ["memory.grow", "unreachable"] :=
  reconstruct_foreign_suffix r before ["memory.grow", "unreachable"]

open FirstOrderCompiler Applications.Circuits Applications.Wasm.Lowering

example : (assemble (Circuit.identity (a := .unit))).validate = true := assemble_validate _
example (s : Store F O) :
    Steps (I := String) ((assemble (Circuit.identity (a := .unit))).instantiate s).1 dummyFrame
      [.invoke s.funcs.length] dummyFrame [] := invoke_compiled s _ ()

example : (assemble (.gate (.constant true))).body = [.const 1, .set 0, .get 0] := rfl
example : (assemble (.gate (.constant true))).locals.map Value.default = [.i32 0] := rfl
example (s : Store F O) :
    Steps (I := String) ((assemble (.gate (.constant true))).instantiate s).1 dummyFrame
      [.invoke s.funcs.length] dummyFrame [.value (.i32 1)] := invoke_compiled s _ ()

private def sharedFrame : Frame :=
  ⟨[.i32 1, .i32 42, .i32 99, .i64 77], dummyFrame.module⟩

/-- Aliased read-only inputs are permitted; the fresh result overwrites only
local two. The two asymmetric sentinels and i64 operand remain unchanged. -/
example : evalCode (gate (.xor 0 0) 2 (0,0)).code sharedFrame [.i64 91] =
    some (⟨[.i32 1, .i32 42, .i32 0, .i64 77], dummyFrame.module⟩, [.i64 91]) := by
  exact gate_eval (.xor 0 0) 2 (0,0) (true,true) sharedFrame [.i64 91] ⟨rfl,rfl⟩ (by decide)

example (s : ExtendedStore F O) (fr : Frame) (foreign : String) :
    ¬ Blocked s [.value (.i32 1), .instr .eqz, .foreign foreign] := by
  intro blocked
  apply blocked.not_focus (fr := fr) (fr' := fr) (out := [.value (.i32 0), .foreign foreign])
  simp [focus, evalInstr, values, eqz]

/-- The older and newer free variables are deliberately unequal. The let-bound
older value is returned before the newer value. -/
private def frontend : Term Gate [.base,.base] (.prod .base .base) :=
  .letE (.var (.there .here)) (.pair (.var .here) (.var (.there .here)))

example (s : Store F O) :
    Steps (I := String) ((assemble (compile Circuit.target frontend)).instantiate s).1 dummyFrame
      (values [.i32 1,.i32 0] ++ [.invoke s.funcs.length]) dummyFrame
      (values [.i32 1,.i32 0]) := compile_source s frontend (((),true),false)

/-- Width two exposes both overflow and the complete LSB-first result order. -/
example (s : Store F O) :
    Steps (I := String) ((assemble (Words.selector 2)).instantiate s).1 dummyFrame
      (values (ABI.encode (a := .prod .base (.prod (Words.shape 2) (Words.shape 2))) (true,(Words.encode (3#2),Words.encode (1#2)))) ++ [.invoke s.funcs.length])
      dummyFrame (values [.i32 0,.i32 0,.i32 1,.i32 1,.i32 1,.i32 0]) :=
  word_source s true (3#2) (1#2)

/-- Universal word correctness preserves 96 output bits, with no FRP wrapper. -/
example (s : Store F O) (tag : Bool) (x y : BitVec 32) :
    Steps (I := String) ((assemble (Words.selector 32)).instantiate s).1 dummyFrame
      (values (ABI.encode (a := .prod .base (.prod (Words.shape 32) (Words.shape 32))) (tag,(Words.encode x,Words.encode y))) ++ [.invoke s.funcs.length]) dummyFrame
      (values (ABI.encode (a := .prod (Words.shape 32) (.prod (Words.shape 32) (Words.shape 32)))
        (Words.encode (if tag then x+y else x ^^^ y),(Words.encode x,Words.encode y)))) :=
  word_source s tag x y

example (s : Store F O) :
    Steps (I := String) ((assemble (Words.selector 32)).instantiate s).1 dummyFrame
      (values (ABI.encode (a := .prod .base (.prod (Words.shape 32) (Words.shape 32))) (true,(Words.encode (0xffffffff#32),Words.encode (1#32)))) ++ [.invoke s.funcs.length]) dummyFrame
      (values (ABI.encode (a := .prod (Words.shape 32) (.prod (Words.shape 32) (Words.shape 32)))
        (Words.encode (0#32),(Words.encode (0xffffffff#32),Words.encode (1#32))))) :=
  word_source s true (0xffffffff#32) (1#32)

private def twoDelay : FRPSpec.Indefinite.Program .base .base (.prod .base .base) :=
  (FRPSpec.Indefinite.Program.delay false).seq (FRPSpec.Indefinite.Program.delay false)

example : twoDelay.initial = (false,false) := rfl

/-- This universal statement covers all eight state/input combinations, with
independently stated shift-register meaning. -/
theorem twoDelay_step (s : Store F O) (x old recent : Bool) :
    Steps (I := String) ((assemble twoDelay.body).instantiate s).1 dummyFrame
      (values (ABI.encode (a := .prod .base (.prod .base .base)) (x,(old,recent))) ++ [.invoke s.funcs.length]) dummyFrame
      (values (ABI.encode (a := .prod .base (.prod .base .base)) (recent,(x,old)))) :=
  state_step s twoDelay x (old,recent)

/-- Three calls use the same post-instantiation store and feed each returned
state to the next call. The outputs are false, false, true. -/
example (s : Store F O) :
    Steps (I := String) ((assemble twoDelay.body).instantiate s).1 dummyFrame
      (values [.i32 1,.i32 0,.i32 0] ++ [.invoke s.funcs.length]) dummyFrame
      (values [.i32 0,.i32 1,.i32 0]) ∧
    Steps (I := String) ((assemble twoDelay.body).instantiate s).1 dummyFrame
      (values [.i32 0,.i32 1,.i32 0] ++ [.invoke s.funcs.length]) dummyFrame
      (values [.i32 0,.i32 0,.i32 1]) ∧
    Steps (I := String) ((assemble twoDelay.body).instantiate s).1 dummyFrame
      (values [.i32 1,.i32 0,.i32 1] ++ [.invoke s.funcs.length]) dummyFrame
      (values [.i32 1,.i32 1,.i32 0]) :=
  ⟨twoDelay_step s true false false, twoDelay_step s false true false,
    twoDelay_step s true false true⟩

example : (Applications.Wasm.Module.mk ⟨[],[.i32]⟩ [] [.get 0]).validate = false := by decide
example : (Applications.Wasm.Module.mk ⟨[.i32],[.i32,.i32]⟩ [] [.get 0]).validate = false := by decide
example : (identityModule.instance 2).export "missing" = none := by decide
example : externalInvoke (I := String) (identityModule.instantiate ambient).1 0 [.i32 1] = none := by decide
example : externalInvoke (I := String) (identityModule.instantiate ambient).1 2 [.i64 1] = none := by decide

example (s : Store F O) (c : Circuit a b) (x : Val Bool a)
    (path : Steps (I := String) ((assemble c).instantiate s).1 dummyFrame
      (values (ABI.encode x) ++ [.invoke s.funcs.length]) fr code) :
    code ≠ [.trap] := (invoke_correct s c x path).2.1

namespace NestedCase
open FRPSpec.FiniteSum

/-- Both nested alternatives preserve a separate free Boolean. -/
def source : FRPSpec.FiniteSum.Term [nested,.bool] (.prod (.prod .bool .bool) .bool) :=
  .caseE (.var .here)
    (.caseE (.var .here)
      (.pair (.pair (.var .here) (.constant false)) (.var (.there (.there (.there .here)))))
      (.pair (.pair (.constant false) (.constant true)) (.var (.there (.there (.there .here))))))
    (.pair (.pair (.not (.fst (.var .here))) (.snd (.var .here))) (.var (.there (.there .here))))

def expected (z : FRPSpec.FiniteSum.Value nested) (free : Bool) : (Bool × Bool) × Bool :=
  ((match z with | .inl (.inl b) => (b,false) | .inl (.inr _) => (false,true) | .inr (b,c) => (!b,c)), free)

theorem source_meaning (z : FRPSpec.FiniteSum.Value nested) (free : Bool) :
    FRPSpec.FiniteSum.eval source (((),free),z) = expected z free := by
  cases z with
  | inl inner => cases inner <;> rfl
  | inr pair => rfl

theorem invocation (s : Store F O) (z : FRPSpec.FiniteSum.Value nested) (free : Bool) :
    Steps (I := String) ((assemble (FRPSpec.FiniteSum.lower source)).instantiate s).1 dummyFrame
      (values (ABI.encode (FRPSpec.FiniteSum.encodeEnv (Γ := [nested,.bool]) (((),free),z))) ++ [.invoke s.funcs.length])
      dummyFrame (values (ABI.encodeSum (a := .prod (.prod .bool .bool) .bool) (expected z free))) := by
  have run := finite_sum_source (I := String) s source (((),free),z)
  rw [source_meaning] at run
  exact run

example (s : Store F O) :
    Steps (I := String) ((assemble (FRPSpec.FiniteSum.lower source)).instantiate s).1 dummyFrame
      (values [.i32 1,.i32 1,.i32 0,.i32 0,.i32 0,.i32 1] ++ [.invoke s.funcs.length])
      dummyFrame (values [.i32 1,.i32 1,.i32 1]) :=
  invocation s (.inr (false,true)) true

end NestedCase

/- These are counts of the generated instruction syntax and scanned operand
heights, connected to #509's plan through `actualPlan_eq`. -/
set_option maxRecDepth 10000 in
theorem selector32_profile : actualPlan (Words.selector 32) = ⟨3266,866,96⟩ := by
  rw [actualPlan_eq]
  decide

example : (assemble (Words.selector 32)).withinLimits = true := by
  have instructions := congrArg Words.Plan.instructions selector32_profile
  have locals := congrArg Words.Plan.locals selector32_profile
  change (assemble (Words.selector 32)).body.length = 3266 at instructions
  change (assemble (Words.selector 32)).type.params.length +
    (assemble (Words.selector 32)).locals.length = 866 at locals
  simp only [Module.withinLimits, assemble_validate, Bool.true_and, decide_eq_true_eq]
  rw [instructions, locals]
  decide

/-- All eight expected rows are listed independently of the compiler. -/
example (s : Store F O) : ∀ row ∈
    [((false,(false,false)),(false,(false,false))),
     ((false,(false,true)),(true,(false,false))),
     ((false,(true,false)),(false,(false,true))),
     ((false,(true,true)),(true,(false,true))),
     ((true,(false,false)),(false,(true,false))),
     ((true,(false,true)),(true,(true,false))),
     ((true,(true,false)),(false,(true,true))),
     ((true,(true,true)),(true,(true,true)))],
    Steps (I := String) ((assemble twoDelay.body).instantiate s).1 dummyFrame
      (values (ABI.encode (a := .prod .base (.prod .base .base)) row.1) ++ [.invoke s.funcs.length])
      dummyFrame (values (ABI.encode (a := .prod .base (.prod .base .base)) row.2)) := by
  intro row member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact twoDelay_step s _ _ _

/-- No standard evaluation context can select the retained foreign instruction
before the pending eqz step. The suffix may execute after that cutpoint. -/
example (s : ExtendedStore F O) (fr : Frame) (c : Context String) :
    c.fill [.foreign "unreachable"] ≠ [.value (.i32 1), .instr .eqz, .foreign "unreachable"] := by
  intro equality
  have blocked := (foreign_blocked s "unreachable").context c
  rw [equality] at blocked
  apply blocked.not_focus (fr := fr) (fr' := fr) (out := [.value (.i32 0), .foreign "unreachable"])
  simp [focus, evalInstr, values, eqz]

example (s : Store F O) (c : Circuit a b) (x : Val Bool a)
    (path : Steps (I := String) ((assemble c).instantiate s).1 dummyFrame
      (values (ABI.encode x) ++ [.invoke s.funcs.length]) fr code)
    (normal : ∀ f body, ¬ Step ((assemble c).instantiate s).1 fr code f body) :
    fr = dummyFrame ∧ code = values (ABI.encode (c.execute x)) := by
  apply (invoke_compiled s c x).normal_result _ path normal
  rw [traps_append, traps_values]
  simp [traps, Admin.traps]

example (s : Store F O) (c : Circuit a b) (x : Val Bool a)
    (path : Steps (I := String) ((assemble c).instantiate s).1 dummyFrame
      (values (ABI.encode x) ++ [.invoke s.funcs.length]) fr code) :
    (fr = dummyFrame ∧ code = values (ABI.encode (c.execute x))) ∨
      ∃ f body, Step ((assemble c).instantiate s).1 fr code f body := by
  apply (invoke_compiled s c x).progress _ path
  rw [traps_append, traps_values]
  simp [traps, Admin.traps]

example (s : Store F O) :
    Steps (I := String) ((assemble (.gate (.nand 0 0))).instantiate s).1 dummyFrame
      (values [.i32 0,.i32 1] ++ [.invoke s.funcs.length]) dummyFrame (values [.i32 1]) :=
  invoke_compiled s (.gate (.nand 0 0)) (false,true)

example (s : Store F O) :
    Steps (I := String) ((assemble (.gate (.nor 0 0))).instantiate s).1 dummyFrame
      (values [.i32 0,.i32 0] ++ [.invoke s.funcs.length]) dummyFrame (values [.i32 1]) :=
  invoke_compiled s (.gate (.nor 0 0)) (false,false)

example (s : Store F O) :
    Steps (I := String) ((assemble (Circuit.pair (Circuit.second (a := .base) (b := .base)) .first)).instantiate s).1 dummyFrame
      (values [.i32 1,.i32 0] ++ [.invoke s.funcs.length]) dummyFrame (values [.i32 0,.i32 1]) :=
  invoke_compiled s (.pair (Circuit.second (a := .base) (b := .base)) .first) (true,false)

example (s : Store F O) :
    Steps (I := String) ((assemble (Words.selector 32)).instantiate s).1 dummyFrame
      (values (ABI.encode (a := .prod .base (.prod (Words.shape 32) (Words.shape 32)))
        (false,(Words.encode (0xffffffff#32),Words.encode (1#32)))) ++ [.invoke s.funcs.length]) dummyFrame
      (values (ABI.encode (a := .prod (Words.shape 32) (.prod (Words.shape 32) (Words.shape 32)))
        (Words.encode (0xfffffffe#32),(Words.encode (0xffffffff#32),Words.encode (1#32))))) :=
  word_source s false (0xffffffff#32) (1#32)

example (s : Store F O) (c : Circuit a b) (x : Val Bool a) (caller : Frame)
    (suffix continuation : List (Admin String)) :
    Steps ((assemble c).instantiate s).1 caller
      [.frame 2 dummyFrame ((Context.seq [.i64 91] (.label 7 continuation .hole) suffix).fill
        (values (ABI.encode x) ++ [.invoke s.funcs.length]))]
      caller [.frame 2 dummyFrame ((Context.seq [.i64 91] (.label 7 continuation .hole) suffix).fill
        (values (ABI.encode (c.execute x))))] :=
  ((invoke_compiled s c x).context (.seq [.i64 91] (.label 7 continuation .hole) suffix)).inFrame caller 2

end Examples.WasmCircuit
