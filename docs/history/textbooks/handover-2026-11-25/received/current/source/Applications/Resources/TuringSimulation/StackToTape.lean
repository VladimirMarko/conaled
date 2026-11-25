import Mathlib.Computability.TuringMachine.StackTuringMachine
import Lean.Elab.Tactic.Omega

/-!
# Quantitative simulation of stack machines by the native tape machine

The existing Mathlib TM2-to-TM1 simulator preserves every encoded stack track
and the actual register/control state. Its exact stack-action shuttle takes
old selected length + new selected length + 1 native TM1 transitions, ending
at the bottom `ret` configuration before continuation activation.

`tailSteps` follows the actual source statement path. `normal_step_witness`
adds the initial dispatch, while `finite_run_bounded` composes actual source
prefixes into a native `EvalsToInTime` witness. If each pre-step source stack
has length at most B and each selected statement has at most A stack actions,
a T-step source run takes at most T * (1 + A * (2 * (B + A) + 2)) target steps.
The reserve induction accounts for stack growth inside each source statement.

A step here is `TM1.step`: its `stepAux` fuses primitive operations until a
label boundary. Primitive TM0 time, visited space, serialization, separate
input/output tracks, finite-control packaging and formal NP remain separate.
In particular, an empty peek's internal left excursion is not a boundary state.

The outward, action and return calculations adapt the existing Mathlib
`Turing.TM2to1` proofs at 56a005855ea17e0b0958f73ec801ae140b0a1679,
copyright (c) 2018 Mario Carneiro, licensed under Apache 2.0.
-/

set_option autoImplicit false
set_option warningAsError true

namespace Resources.TuringSimulation.StackToTape

open Function
open Turing Turing.TM2to1

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq K]

/-- Exact outward scan of the existing simulator. The complete family
of encoded tracks is retained, as is the entire native tape in the endpoint.
The action has not run: the final label is still `go`. The count is the number
of actual TM1 transitions in this witness, not a least-time assertion. -/
theorem outward_exact
    (M : Λ → TM2.Stmt Γ Λ σ)
    (k : K) (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀ j, List (Γ j)) (L : ListBlank (∀ j, Option (Γ j)))
    (hL : ∀ j, L.map (Turing.proj j) =
      ListBlank.mk ((S j).map some).reverse)
    (n : ℕ) (hn : n ≤ (S k).length) :
    (flip bind (TM1.step (tr M)))^[n]
      (some ⟨some (Λ'.go k o q), v, Tape.mk' ∅ (addBottom L)⟩) =
      some ⟨some (Λ'.go k o q), v,
        (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
  induction n with
  | zero => rfl
  | succ n IH =>
    rw [Function.iterate_succ_apply', IH (Nat.le_of_lt hn)]
    change TM1.step (tr M)
      ⟨some (Λ'.go k o q), v,
        (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ =
      some ⟨some (Λ'.go k o q), v,
        (Tape.move Dir.right)^[n + 1] (Tape.mk' ∅ (addBottom L))⟩
    rw [Function.iterate_succ_apply']
    simp only [TM1.step, TM1.stepAux, tr, Tape.mk'_nth_nat,
      Tape.move_right_n_head, addBottom_nth_snd]
    rw [stk_nth_val _ (hL k), List.getElem?_eq_getElem]
    · rfl
    · rwa [List.length_reverse]

/-- The same exact equality packaged in the existing native evaluation
record. No alternate transition system or cost datatype is introduced. -/
def outwardEvalsTo
    (M : Λ → TM2.Stmt Γ Λ σ)
    (k : K) (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀ j, List (Γ j)) (L : ListBlank (∀ j, Option (Γ j)))
    (hL : ∀ j, L.map (Turing.proj j) =
      ListBlank.mk ((S j).map some).reverse)
    (n : ℕ) (hn : n ≤ (S k).length) :
    StateTransition.EvalsTo (TM1.step (tr M))
      ⟨some (Λ'.go k o q), v, Tape.mk' ∅ (addBottom L)⟩
      (some ⟨some (Λ'.go k o q), v,
        (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩) where
  steps := n
  evals_in_steps := outward_exact M k o q v S L hL n hn

theorem outwardEvalsTo_steps
    (M : Λ → TM2.Stmt Γ Λ σ)
    (k : K) (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀ j, List (Γ j)) (L : ListBlank (∀ j, Option (Γ j)))
    (hL : ∀ j, L.map (Turing.proj j) =
      ListBlank.mk ((S j).map some).reverse)
    (n : ℕ) (hn : n ≤ (S k).length) :
    (outwardEvalsTo M k o q v S L hL n hn).steps = n := rfl

/-- Native composition accounting. `tail` remains an explicit obligation:
this theorem does not manufacture the action or return-scan witness. Mathlib's
composition stores the second count plus the first count, in that order. -/
theorem outward_then_steps
    (M : Λ → TM2.Stmt Γ Λ σ)
    (k : K) (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀ j, List (Γ j)) (L : ListBlank (∀ j, Option (Γ j)))
    (hL : ∀ j, L.map (Turing.proj j) =
      ListBlank.mk ((S j).map some).reverse)
    (n : ℕ) (hn : n ≤ (S k).length)
    (finish : Option (TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ))
    (tail : StateTransition.EvalsTo (TM1.step (tr M))
      ⟨some (Λ'.go k o q), v,
        (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ finish) :
    (StateTransition.EvalsTo.trans (TM1.step (tr M))
      ⟨some (Λ'.go k o q), v, Tape.mk' ∅ (addBottom L)⟩
      ⟨some (Λ'.go k o q), v,
        (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩
      finish (outwardEvalsTo M k o q v S L hL n hn) tail).steps =
      tail.steps + n := rfl


/-- Exact return from displacement `n`, stopping at the bottom `ret`
configuration before activation of `q`. The complete marked native tape stays
the same. The return calculation only needs its marker, not a stack-length bound. -/
theorem return_exact
    (M : Λ → TM2.Stmt Γ Λ σ) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (L : ListBlank (∀ j, Option (Γ j))) (n : ℕ) :
    (flip bind (TM1.step (tr M)))^[n]
      (some ⟨some (Λ'.ret q), v,
        (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩) =
      some ⟨some (Λ'.ret q), v, Tape.mk' ∅ (addBottom L)⟩ := by
  induction n with
  | zero => rfl
  | succ n IH =>
    have oneStep : TM1.step (tr M)
        ⟨some (Λ'.ret q), v,
          (Tape.move Dir.right)^[n + 1] (Tape.mk' ∅ (addBottom L))⟩ =
        some ⟨some (Λ'.ret q), v,
          (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩ := by
      simp only [TM1.step]
      rw [Option.some_inj, tr, TM1.stepAux, Tape.move_right_n_head,
        Tape.mk'_nth_nat, addBottom_nth_succ_fst, TM1.stepAux,
        Function.iterate_succ', Function.comp_apply, Tape.move_right_left]
      rfl
    rw [Function.iterate_succ_apply (flip bind (TM1.step (tr M)))]
    change (flip bind (TM1.step (tr M)))^[n]
      (TM1.step (tr M)
        ⟨some (Λ'.ret q), v,
          (Tape.move Dir.right)^[n + 1] (Tape.mk' ∅ (addBottom L))⟩) = _
    rw [oneStep]
    exact IH

def returnEvalsTo
    (M : Λ → TM2.Stmt Γ Λ σ) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (L : ListBlank (∀ j, Option (Γ j))) (n : ℕ) :
    StateTransition.EvalsTo (TM1.step (tr M))
      ⟨some (Λ'.ret q), v,
        (Tape.move Dir.right)^[n] (Tape.mk' ∅ (addBottom L))⟩
      (some ⟨some (Λ'.ret q), v, Tape.mk' ∅ (addBottom L)⟩) where
  steps := n
  evals_in_steps := return_exact M q v L n

/-- One actual target transition from the first blank of the selected old stack
to `ret` at the first blank of its updated stack. All encoded tracks are retained. -/
theorem action_step
    (M : Λ → TM2.Stmt Γ Λ σ)
    (k : K) (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀ j, List (Γ j)) (L : ListBlank (∀ j, Option (Γ j)))
    (hL : ∀ j, L.map (Turing.proj j) =
      ListBlank.mk ((S j).map some).reverse) :
    let v' := stVar v (S k) o
    let S' := Function.update S k (stWrite v (S k) o)
    ∃ L' : ListBlank (∀ j, Option (Γ j)),
      (∀ j, L'.map (Turing.proj j) =
        ListBlank.mk ((S' j).map some).reverse) ∧
      TM1.step (tr M)
        ⟨some (Λ'.go k o q), v,
          (Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩ =
        some ⟨some (Λ'.ret q), v',
          (Tape.move Dir.right)^[(S' k).length] (Tape.mk' ∅ (addBottom L'))⟩ := by
  dsimp only
  obtain ⟨L', hL', hact⟩ := tr_respects_aux₂ (Λ := Λ)
    (k := k) (q := TM1.Stmt.goto (fun _ _ => Λ'.ret q))
    (v := v) (S := S) (L := L) hL o
  refine ⟨L', hL', ?_⟩
  rw [TM1.step, tr, TM1.stepAux, Tape.move_right_n_head,
    Tape.mk'_nth_nat, addBottom_nth_snd, stk_nth_val _ (hL k),
    List.getElem?_eq_none (le_of_eq List.length_reverse),
    Option.isNone, cond, hact, TM1.stepAux]

/-- Native action-plus-return witness. Its count is the new selected
stack length plus one, and its final label is still `ret q`. The outward scan
and continuation activation are not included. -/
theorem action_return_witness
    (M : Λ → TM2.Stmt Γ Λ σ)
    (k : K) (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀ j, List (Γ j)) (L : ListBlank (∀ j, Option (Γ j)))
    (hL : ∀ j, L.map (Turing.proj j) =
      ListBlank.mk ((S j).map some).reverse) :
    let v' := stVar v (S k) o
    let S' := Function.update S k (stWrite v (S k) o)
    ∃ L' : ListBlank (∀ j, Option (Γ j)),
      (∀ j, L'.map (Turing.proj j) =
        ListBlank.mk ((S' j).map some).reverse) ∧
      ∃ run : StateTransition.EvalsTo (TM1.step (tr M))
        ⟨some (Λ'.go k o q), v,
          (Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩
        (some ⟨some (Λ'.ret q), v', Tape.mk' ∅ (addBottom L')⟩),
        run.steps = (S' k).length + 1 := by
  dsimp only
  obtain ⟨L', hL', hstep⟩ := action_step M k o q v S L hL
  refine ⟨L', hL', ?_⟩
  let actionRun : StateTransition.EvalsTo (TM1.step (tr M))
      ⟨some (Λ'.go k o q), v,
        (Tape.move Dir.right)^[(S k).length] (Tape.mk' ∅ (addBottom L))⟩
      (some ⟨some (Λ'.ret q), stVar v (S k) o,
        (Tape.move Dir.right)^[(Function.update S k (stWrite v (S k) o) k).length]
          (Tape.mk' ∅ (addBottom L'))⟩) :=
    { steps := 1
      evals_in_steps := by
        simpa only [Function.iterate_one, Function.flip_def, bind, Option.bind_some] using hstep }
  let back := returnEvalsTo M q (stVar v (S k) o) L'
    (Function.update S k (stWrite v (S k) o) k).length
  exact ⟨StateTransition.EvalsTo.trans (TM1.step (tr M))
    _ _ _ actionRun back, rfl⟩

/-- Complete shuttle for the unchanged native simulator. It starts at
`go` over the bottom marker and stops at `ret` over that marker, retaining every
updated stack track and the actual register effect. Its count is the old
selected length plus the new selected length plus one action transition.
The following bottom-marker transition that activates `q` is not included. -/
theorem shuttle_witness
    (M : Λ → TM2.Stmt Γ Λ σ)
    (k : K) (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀ j, List (Γ j)) (L : ListBlank (∀ j, Option (Γ j)))
    (hL : ∀ j, L.map (Turing.proj j) =
      ListBlank.mk ((S j).map some).reverse) :
    let v' := stVar v (S k) o
    let S' := Function.update S k (stWrite v (S k) o)
    ∃ L' : ListBlank (∀ j, Option (Γ j)),
      (∀ j, L'.map (Turing.proj j) =
        ListBlank.mk ((S' j).map some).reverse) ∧
      ∃ run : StateTransition.EvalsTo (TM1.step (tr M))
        ⟨some (Λ'.go k o q), v, Tape.mk' ∅ (addBottom L)⟩
        (some ⟨some (Λ'.ret q), v', Tape.mk' ∅ (addBottom L')⟩),
        run.steps = (S k).length + (S' k).length + 1 := by
  dsimp only
  obtain ⟨L', hL', back, hback⟩ := action_return_witness M k o q v S L hL
  refine ⟨L', hL', StateTransition.EvalsTo.trans (TM1.step (tr M))
    _ _ _ (outwardEvalsTo M k o q v S L hL (S k).length le_rfl) back, ?_⟩
  change back.steps + (S k).length = _
  rw [hback]
  simp only [Nat.add_comm, Nat.add_left_comm]

/-- The same complete shuttle expressed directly as native iteration.
There is no separately chosen cost function or reachability-to-time inference. -/
theorem shuttle_exact
    (M : Λ → TM2.Stmt Γ Λ σ)
    (k : K) (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀ j, List (Γ j)) (L : ListBlank (∀ j, Option (Γ j)))
    (hL : ∀ j, L.map (Turing.proj j) =
      ListBlank.mk ((S j).map some).reverse) :
    let v' := stVar v (S k) o
    let S' := Function.update S k (stWrite v (S k) o)
    ∃ L' : ListBlank (∀ j, Option (Γ j)),
      (∀ j, L'.map (Turing.proj j) =
        ListBlank.mk ((S' j).map some).reverse) ∧
      (flip bind (TM1.step (tr M)))^[(S k).length + (S' k).length + 1]
        (some ⟨some (Λ'.go k o q), v, Tape.mk' ∅ (addBottom L)⟩) =
        some ⟨some (Λ'.ret q), v', Tape.mk' ∅ (addBottom L')⟩ := by
  dsimp only
  obtain ⟨L', hL', run, hsteps⟩ := shuttle_witness M k o q v S L hL
  refine ⟨L', hL', ?_⟩
  rw [← hsteps]
  exact run.evals_in_steps


open Function
open Turing Turing.TM2to1

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq K]

/-- The native target transitions remaining after the initial `trNormal` body
has run. Each executed stack action pays its complete shuttle plus activation
of the following continuation. Loads and branches follow the actual register
state and do not insert additional target label boundaries. -/
def tailSteps : TM2.Stmt Γ Λ σ → σ → (∀ j, List (Γ j)) → ℕ
  | .push k f q, v, S =>
      (S k).length + (f v :: S k).length + 2 +
        tailSteps q v (Function.update S k (f v :: S k))
  | .peek k f q, v, S =>
      (S k).length + (S k).length + 2 + tailSteps q (f v (S k).head?) S
  | .pop k f q, v, S =>
      (S k).length + (S k).tail.length + 2 +
        tailSteps q (f v (S k).head?) (Function.update S k (S k).tail)
  | .load a q, v, S => tailSteps q (a v) S
  | .branch p q₁ q₂, v, S => cond (p v) (tailSteps q₁ v S) (tailSteps q₂ v S)
  | .goto _, _, _ => 0
  | .halt, _, _ => 0

theorem tailSteps_run
    (k : K) (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ)
    (v : σ) (S : ∀ j, List (Γ j)) :
    tailSteps (stRun o q) v S =
      (S k).length + (stWrite v (S k) o).length + 2 +
        tailSteps q (stVar v (S k) o) (Function.update S k (stWrite v (S k) o)) := by
  cases o <;> simp only [stRun, tailSteps, stWrite, stVar, Function.update_eq_self]

/-- At the bottom marker, one actual `ret` transition activates the translated
continuation. All its non-stack work is part of this native TM1 boundary step. -/
theorem ret_activate_step
    (M : Λ → TM2.Stmt Γ Λ σ) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (L : ListBlank (∀ j, Option (Γ j))) :
    TM1.step (tr M) ⟨some (Λ'.ret q), v, Tape.mk' ∅ (addBottom L)⟩ =
      some (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom L))) := by
  rw [TM1.step, tr, TM1.stepAux, Tape.mk'_head, addBottom_head_fst]
  rfl

/-- Exact remaining native target time after translating the first normal body.
The resulting configuration retains the existing full `TrCfg` relation to the
literal source `TM2.stepAux` result. -/
theorem statement_tail_witness
    (M : Λ → TM2.Stmt Γ Λ σ) (q : TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀ j, List (Γ j)) (L : ListBlank (∀ j, Option (Γ j)))
    (hL : ∀ j, L.map (Turing.proj j) =
      ListBlank.mk ((S j).map some).reverse) :
    ∃ b : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ,
      TrCfg (TM2.stepAux q v S) b ∧
      ∃ run : StateTransition.EvalsTo (TM1.step (tr M))
        (TM1.stepAux (trNormal q) v (Tape.mk' ∅ (addBottom L))) (some b),
        run.steps = tailSteps q v S := by
  induction q using stmtStRec generalizing v S L with
  | run k o q IH =>
    rw [trNormal_run, step_run, tailSteps_run]
    change ∃ b, TrCfg (TM2.stepAux q (stVar v (S k) o)
      (Function.update S k (stWrite v (S k) o))) b ∧
      ∃ run : StateTransition.EvalsTo (TM1.step (tr M))
        ⟨some (Λ'.go k o q), v, Tape.mk' ∅ (addBottom L)⟩ (some b),
        run.steps = (S k).length + (stWrite v (S k) o).length + 2 +
          tailSteps q (stVar v (S k) o) (Function.update S k (stWrite v (S k) o))
    obtain ⟨L', hL', shuttle, hshuttle⟩ := shuttle_witness M k o q v S L hL
    obtain ⟨b, hb, tail, htail⟩ := IH
      (stVar v (S k) o) (Function.update S k (stWrite v (S k) o)) L' hL'
    let activation : StateTransition.EvalsTo (TM1.step (tr M))
        ⟨some (Λ'.ret q), stVar v (S k) o, Tape.mk' ∅ (addBottom L')⟩
        (some (TM1.stepAux (trNormal q) (stVar v (S k) o)
          (Tape.mk' ∅ (addBottom L')))) :=
      { steps := 1
        evals_in_steps := by
          simp only [Function.iterate_one, Function.flip_def, bind, Option.bind_some]
          change TM1.step (tr M) _ = _
          exact ret_activate_step M q (stVar v (S k) o) L' }
    let finish := StateTransition.EvalsTo.trans (TM1.step (tr M)) _ _ _ activation tail
    refine ⟨b, hb, StateTransition.EvalsTo.trans (TM1.step (tr M))
      _ _ _ shuttle finish, ?_⟩
    change (tail.steps + 1) + shuttle.steps = _
    rw [htail, hshuttle, Function.update_self]
    omega
  | load a q IH =>
    simpa only [TM2.stepAux, trNormal, TM1.stepAux, tailSteps] using IH (a v) S L hL
  | branch p q₁ q₂ IH₁ IH₂ =>
    have start_eq : TM1.stepAux (trNormal (.branch p q₁ q₂)) v
        (Tape.mk' ∅ (addBottom L)) =
        cond (p v) (TM1.stepAux (trNormal q₁) v (Tape.mk' ∅ (addBottom L)))
          (TM1.stepAux (trNormal q₂) v (Tape.mk' ∅ (addBottom L))) := rfl
    rw [start_eq]
    change ∃ b, TrCfg (cond (p v) (TM2.stepAux q₁ v S) (TM2.stepAux q₂ v S)) b ∧
      ∃ run : StateTransition.EvalsTo (TM1.step (tr M))
        (cond (p v) (TM1.stepAux (trNormal q₁) v (Tape.mk' ∅ (addBottom L)))
          (TM1.stepAux (trNormal q₂) v (Tape.mk' ∅ (addBottom L)))) (some b),
        run.steps = cond (p v) (tailSteps q₁ v S) (tailSteps q₂ v S)
    cases p v
    · exact IH₂ v S L hL
    · exact IH₁ v S L hL
  | goto l =>
    exact ⟨_, TrCfg.mk L hL, StateTransition.EvalsTo.refl _ _, rfl⟩
  | halt =>
    exact ⟨_, TrCfg.mk L hL, StateTransition.EvalsTo.refl _ _, rfl⟩

/-- Exact simulation of one live source label-boundary transition. The target
reaches its live normal or halted configuration after `tailSteps + 1` steps;
an additional outer-`none` transition is not included. -/
theorem normal_step_witness
    (M : Λ → TM2.Stmt Γ Λ σ) (l : Λ) (v : σ)
    (S : ∀ j, List (Γ j)) (L : ListBlank (∀ j, Option (Γ j)))
    (hL : ∀ j, L.map (Turing.proj j) =
      ListBlank.mk ((S j).map some).reverse) :
    ∃ b : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ,
      TrCfg (TM2.stepAux (M l) v S) b ∧
      ∃ run : StateTransition.EvalsTo (TM1.step (tr M))
        ⟨some (Λ'.normal l), v, Tape.mk' ∅ (addBottom L)⟩ (some b),
        run.steps = tailSteps (M l) v S + 1 := by
  obtain ⟨b, hb, tail, htail⟩ := statement_tail_witness M (M l) v S L hL
  let dispatch : StateTransition.EvalsTo (TM1.step (tr M))
      ⟨some (Λ'.normal l), v, Tape.mk' ∅ (addBottom L)⟩
      (some (TM1.stepAux (trNormal (M l)) v (Tape.mk' ∅ (addBottom L)))) :=
    { steps := 1
      evals_in_steps := by
        simp only [Function.iterate_one, Function.flip_def, bind, Option.bind_some]
        rfl }
  refine ⟨b, hb, StateTransition.EvalsTo.trans (TM1.step (tr M))
    _ _ _ dispatch tail, ?_⟩
  change tail.steps + 1 = _
  rw [htail]

/-- A syntax-only maximum number of stack actions on any branch of the statement.
It is independent of the initial stacks and register values. -/
def actionBound : TM2.Stmt Γ Λ σ → ℕ
  | .push _ _ q => actionBound q + 1
  | .peek _ _ q => actionBound q + 1
  | .pop _ _ q => actionBound q + 1
  | .load _ q => actionBound q
  | .branch _ q₁ q₂ => max (actionBound q₁) (actionBound q₂)
  | .goto _ => 0
  | .halt => 0

omit [DecidableEq K] in
theorem actionBound_run
    (k : K) (o : StAct K Γ σ k) (q : TM2.Stmt Γ Λ σ) :
    actionBound (stRun o q) = actionBound q + 1 := by
  cases o <;> rfl

omit [DecidableEq K] in
theorem stWrite_length_le
    (k : K) (o : StAct K Γ σ k) (v : σ) (S : List (Γ k)) :
    (stWrite v S o).length ≤ S.length + 1 := by
  cases o <;> simp only [stWrite, List.length_cons, List.length_tail] <;> omega

/-- Reserve-style bound: the current length plus every possible future stack
action fits in `H`. Thus both old and new selected lengths of every executed
shuttle are at most `H`, including statement-internal stack states. -/
theorem tailSteps_le_reserved
    (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ j, List (Γ j)) (H : ℕ)
    (hS : ∀ j, (S j).length + actionBound q ≤ H) :
    tailSteps q v S ≤ actionBound q * (2 * H + 2) := by
  induction q using stmtStRec generalizing v S with
  | run k o q IH =>
    simp only [actionBound_run] at hS ⊢
    rw [tailSteps_run]
    have hS' : ∀ j,
        ((Function.update S k (stWrite v (S k) o)) j).length + actionBound q ≤ H := by
      intro j
      by_cases hj : j = k
      · subst j
        rw [Function.update_self]
        have hgrow := stWrite_length_le k o v (S k)
        have hreserve := hS k
        omega
      · rw [Function.update_of_ne hj]
        have hreserve := hS j
        omega
    have htail := IH (stVar v (S k) o)
      (Function.update S k (stWrite v (S k) o)) hS'
    have hold := hS k
    have hnew := hS' k
    rw [Function.update_self] at hnew
    have hpart : (S k).length + (stWrite v (S k) o).length + 2 ≤ 2 * H + 2 := by
      omega
    calc
      _ ≤ (2 * H + 2) + actionBound q * (2 * H + 2) := Nat.add_le_add hpart htail
      _ = (actionBound q + 1) * (2 * H + 2) := by
        rw [Nat.add_mul, Nat.one_mul]
        exact Nat.add_comm _ _
  | load a q IH =>
    exact IH (a v) S hS
  | branch p q₁ q₂ IH₁ IH₂ =>
    have h₁ : ∀ j, (S j).length + actionBound q₁ ≤ H := fun j =>
      le_trans (Nat.add_le_add_left (Nat.le_max_left _ _) _) (hS j)
    have h₂ : ∀ j, (S j).length + actionBound q₂ ≤ H := fun j =>
      le_trans (Nat.add_le_add_left (Nat.le_max_right _ _) _) (hS j)
    cases hp : p v
    · simp only [tailSteps, hp, Bool.cond_false, actionBound]
      exact le_trans (IH₂ v S h₂) (Nat.mul_le_mul_right _ (Nat.le_max_right _ _))
    · simp only [tailSteps, hp, Bool.cond_true, actionBound]
      exact le_trans (IH₁ v S h₁) (Nat.mul_le_mul_right _ (Nat.le_max_left _ _))
  | goto l => simp only [tailSteps, actionBound, Nat.zero_mul, le_refl]
  | halt => simp only [tailSteps, actionBound, Nat.zero_mul, le_refl]

/-- Per-statement polynomial bound from a uniform starting stack-length bound.
The syntax constant is chosen from the source statement before its input. -/
theorem tailSteps_le
    (q : TM2.Stmt Γ Λ σ) (v : σ) (S : ∀ j, List (Γ j)) (B : ℕ)
    (hS : ∀ j, (S j).length ≤ B) :
    tailSteps q v S ≤ actionBound q * (2 * (B + actionBound q) + 2) :=
  tailSteps_le_reserved q v S (B + actionBound q)
    (fun j => Nat.add_le_add_right (hS j) (actionBound q))

/-- One source transition has the established native endpoint with the stated
target-boundary-time upper bound. This is local simulation, not whole-run
composition, finite-support packaging, raw encoding, or conventional NP. -/
theorem normal_step_bounded
    (M : Λ → TM2.Stmt Γ Λ σ) (l : Λ) (v : σ)
    (S : ∀ j, List (Γ j)) (L : ListBlank (∀ j, Option (Γ j)))
    (hL : ∀ j, L.map (Turing.proj j) =
      ListBlank.mk ((S j).map some).reverse)
    (B : ℕ) (hS : ∀ j, (S j).length ≤ B) :
    ∃ b : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ,
      TrCfg (TM2.stepAux (M l) v S) b ∧
      Nonempty (StateTransition.EvalsToInTime (TM1.step (tr M))
        ⟨some (Λ'.normal l), v, Tape.mk' ∅ (addBottom L)⟩ (some b)
        (1 + actionBound (M l) * (2 * (B + actionBound (M l)) + 2))) := by
  obtain ⟨b, hb, run, hrun⟩ := normal_step_witness M l v S L hL
  refine ⟨b, hb, ⟨{ toEvalsTo := run, steps_le_m := ?_ }⟩⟩
  rw [hrun]
  have hbound := tailSteps_le (M l) v S B hS
  omega


open Function
open Turing Turing.TM2to1

variable {K : Type*} {Γ : K → Type*} {Λ σ : Type*} [DecidableEq K]

/-- One actual source transition with a uniform source-program action bound.
The hypotheses concern the actual source configuration and current label; the
target run is constructed from the native simulator lemmas. -/
theorem source_step_bounded_uniform
    (M : Λ → TM2.Stmt Γ Λ σ)
    (a b : TM2.Cfg Γ Λ σ) (d : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ)
    (hrel : TrCfg a d) (hstep : TM2.step M a = some b)
    (A B : ℕ) (hcells : ∀ j, (a.stk j).length ≤ B)
    (hactions : ∀ l, a.l = some l → actionBound (M l) ≤ A) :
    ∃ e : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ,
      TrCfg b e ∧
      Nonempty (StateTransition.EvalsToInTime (TM1.step (tr M)) d (some e)
        (1 + A * (2 * (B + A) + 2))) := by
  cases hrel with
  | @mk q v S L hL =>
    cases q with
    | none => cases hstep
    | some l =>
      have hb : TM2.stepAux (M l) v S = b := Option.some.inj hstep
      obtain ⟨e, he, ⟨run⟩⟩ := normal_step_bounded M l v S L hL B hcells
      refine ⟨e, ?_, ⟨{ toEvalsTo := run.toEvalsTo, steps_le_m := ?_ }⟩⟩
      · rw [← hb]
        exact he
      · have ha : actionBound (M l) ≤ A := hactions l rfl
        have hinside : 2 * (B + actionBound (M l)) + 2 ≤ 2 * (B + A) + 2 :=
          Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.add_le_add_left ha B)) 2
        exact le_trans run.steps_le_m
          (Nat.add_le_add_left (Nat.mul_le_mul ha hinside) 1)

/-- Quantitative simulation of an actual finite native TM2 run. For every live
source prefix strictly before `T`, the selected statement has action bound `A`
and every source stack has length at most `B`. The target run ends at the full
related live configuration in at most `T * (1 + A * (2 * (B + A) + 2))` native
TM1 boundary transitions. No outer-`none` transition, input serialization,
output projection, finite-control packaging or primitive-command cost is hidden
in this statement. -/
theorem finite_run_bounded
    (M : Λ → TM2.Stmt Γ Λ σ)
    (a b : TM2.Cfg Γ Λ σ) (d : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ)
    (hrel : TrCfg a d) (T A B : ℕ)
    (hrun : (flip bind (TM2.step M))^[T] (some a) = some b)
    (hprefix : ∀ (i : ℕ) (c : TM2.Cfg Γ Λ σ), i < T →
      (flip bind (TM2.step M))^[i] (some a) = some c →
      (∀ j, (c.stk j).length ≤ B) ∧
      (∀ l, c.l = some l → actionBound (M l) ≤ A)) :
    ∃ e : TM1.Cfg (Γ' K Γ) (Λ' K Γ Λ σ) σ,
      TrCfg b e ∧
      Nonempty (StateTransition.EvalsToInTime (TM1.step (tr M)) d (some e)
        (T * (1 + A * (2 * (B + A) + 2)))) := by
  induction T generalizing b with
  | zero =>
    simp only [Function.iterate_zero_apply, Option.some.injEq] at hrun
    subst b
    refine ⟨d, hrel, ⟨?_⟩⟩
    simpa only [Nat.zero_mul] using StateTransition.EvalsToInTime.refl (TM1.step (tr M)) d
  | succ n IH =>
    have hrun' := hrun
    rw [Function.iterate_succ_apply'] at hrun'
    cases hmid : (flip bind (TM2.step M))^[n] (some a) with
    | none =>
      rw [hmid] at hrun'
      change (none : Option (TM2.Cfg Γ Λ σ)) = some b at hrun'
      cases hrun'
    | some c =>
      rw [hmid] at hrun'
      have hstep : TM2.step M c = some b := by
        simpa only [Function.flip_def, bind, Option.bind_some] using hrun'
      have hprefix' : ∀ (i : ℕ) (c : TM2.Cfg Γ Λ σ), i < n →
          (flip bind (TM2.step M))^[i] (some a) = some c →
          (∀ j, (c.stk j).length ≤ B) ∧
          (∀ l, c.l = some l → actionBound (M l) ≤ A) := by
        intro i c hi hc
        exact hprefix i c (Nat.lt_trans hi (Nat.lt_succ_self n)) hc
      obtain ⟨d', hd', ⟨before⟩⟩ := IH c hmid hprefix'
      obtain ⟨hcells, hactions⟩ := hprefix n c (Nat.lt_succ_self n) hmid
      obtain ⟨e, he, ⟨after⟩⟩ :=
        source_step_bounded_uniform M c b d' hd' hstep A B hcells hactions
      let run := StateTransition.EvalsTo.trans (TM1.step (tr M)) d d' (some e)
        before.toEvalsTo after.toEvalsTo
      refine ⟨e, he, ⟨{ toEvalsTo := run, steps_le_m := ?_ }⟩⟩
      change after.steps + before.steps ≤
        (n + 1) * (1 + A * (2 * (B + A) + 2))
      calc
        _ ≤ (1 + A * (2 * (B + A) + 2)) +
            n * (1 + A * (2 * (B + A) + 2)) :=
          Nat.add_le_add after.steps_le_m before.steps_le_m
        _ = (n + 1) * (1 + A * (2 * (B + A) + 2)) := by
          rw [Nat.add_mul, Nat.one_mul]
          exact Nat.add_comm _ _


end Resources.TuringSimulation.StackToTape
