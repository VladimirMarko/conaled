import Applications.FRP.StaticFunctionReactive

/-! Static bodies, open binding separators, independent delay observations,
and real regional execution through the public residualization theorems. -/
namespace Examples.StaticFunctionReactive
open FirstOrderCompiler Applications.Circuits StaticFunction Progress.Feedback
open FRPSpec.StaticFunctionReactive

def inputs : List Pair := [(false,false),(true,false),(true,true),(false,true)]
def expected : List Pair := [(false,true),(true,true),(false,true),(false,false)]
def initial : Pair := (false,true)
def bodies : List StaticBody := [negationBody]

/-- Ordinary Lean authoring, with no source interpreter in the transition. -/
def ordinary : Initialized Pair Pair Pair :=
  ⟨fun (x,s) => (s,(!x.1,!x.2)),initial⟩

theorem ordinary_correct : (program bodies initial).machine = ordinary := by
  rw [machine_correct]
  rfl

theorem ordinary_oracle : run ordinary.mealy initial inputs = (expected,(true,false)) := rfl

theorem native_oracle : run (native bodies initial).mealy initial inputs = (expected,(true,false)) := rfl

theorem compiled_oracle : run (program bodies initial).machine.mealy initial inputs = (expected,(true,false)) :=
  by rw [ordinary_correct]; exact ordinary_oracle

theorem prefix_continuation :
    run (program bodies initial).machine.mealy initial (inputs.take 2) =
      ([(false,true),(true,true)],(false,true)) := by
  rw [run_correct]; rfl

theorem restart : run (program bodies initial).machine.mealy (false,true) (inputs.drop 2) =
    ([(false,true),(false,false)],(true,false)) := by rw [run_correct]; rfl

/-- Fresh let binder must not capture the open argument being substituted. -/
def captureBody : Term Gate [.base,.base] .base :=
  .letE (literal false) (.var (.there .here))
def captureExpr : Expr Gate [.base] .base := .apply captureBody (.value (.var .here))

theorem capture_separator (x : Bool) : eval Gate.meaning captureExpr.residual ((),x) = x := by
  rw [Expr.residual_correct]; rfl

theorem captured_mask (mask x y : Bool) :
    eval Gate.meaning (Expr.mapPair (liftBody (maskBody mask))
      (.value (.var .here)) : Expr Gate [pairTy] pairTy).residual ((),(x,y)) =
      (Bool.xor x mask,Bool.xor y mask) := by
  rw [Expr.residual_correct]
  simp only [Expr.meaning, eval, lookup, liftBody_correct (Γ := [pairTy]), maskBody, literal, Gate.meaning]

/-- Open substitution changes the runtime environment and preserves the source
meaning. The argument remains open under captureBody's fresh let binder. -/
theorem open_substitution (x : Bool) :
    eval Gate.meaning (Term.subst (Term.single (literal x)) captureExpr.residual) () = x := by
  exact Expr.residual_substitution Gate.meaning captureExpr (Term.single (literal x)) ((),x) ()
    (fun v => by cases v with | here => rfl | there v => nomatch v)

/-- Direct first-order authoring of the same delay, retained for comparison. -/
def directBody : Term Gate [pairTy,pairTy] (.prod pairTy pairTy) :=
  .pair (.var (.there .here))
    (.pair (.prim (.not 0) (.fst (.var .here))) (.prim (.not 0) (.snd (.var .here))))
def direct := FRPSpec.Indefinite.Program.compiled
  (ReactiveCompiler.compile Circuit.target (seed initial) directBody)

theorem direct_same : direct.machine = (program bodies initial).machine := by
  rw [machine_correct]
  unfold direct
  rw [FRPSpec.Indefinite.Program.compiled_source]
  rfl

theorem nested_correct (x : Pair) : nativeMap [negationBody,negationBody] x = x := by
  rcases x with ⟨x,y⟩
  cases x <;> cases y <;> rfl

theorem identity_size (n : Nat) :
    nodes (duplication (P := Gate) n).residual + 3 = 4 * 2^n := duplication_nodes n

theorem rich_case (s : Pair) : regionalStep bodies initial (.inr (true,false)) s = (s,(false,false)) := by
  rw [regional_correct]; rfl

theorem capacity_accept : (assess (.static bodies initial)
    (cells pairTy + (program bodies initial).body.arena)).status = .accepted :=
  (admitted_iff _ _ _).mpr (Nat.le_refl _)

theorem capacity_reject : (assess (.static bodies initial) 0).status = .rejectedCapacity := by decide

/-- The public admission seam executes the selected stored seed and code. -/
theorem selected_oracle :
    (assess (.static bodies initial) (cells pairTy + (program bodies initial).body.arena)).execute
      none inputs = some (expected,(true,false)) :=
  (selected_execution bodies initial _ (Nat.le_refl _) none inputs).trans
    (congrArg some native_oracle)

theorem rejected_nonexecution : (assess (.static bodies initial) 0).execute
    (some (true,false)) inputs = none :=
  negative_nonexecution _ (by rw [capacity_reject]; decide) _ _

end Examples.StaticFunctionReactive
