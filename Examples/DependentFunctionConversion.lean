import SquareKit.Internal.DependentFunctionConversion

/-! Open generated terms, direct derivations, and independent rejection controls.
These development fixtures are not the later frozen author-trial tasks. -/
namespace Examples.DependentFunctionConversion
open SquareKit.Internal.DependentFunctions
open SquareKit.Internal.DependentStructural (Base)

abbrev Γ : Ctx 1 := .function (.base .nil) (.var 0)
abbrev parameter : Func Γ := .var .top
abbrev body : Dep (.base Γ) := .app (.var (.base .top)) (.neg (.var 0))
abbrev generated : Dep Γ := .app (.lam body) (.neg (.var 0))
abbrev expected : Dep Γ := .app parameter (.neg (.neg (.var 0)))

def negate : Sub Γ Γ where
  base i := .neg (.var i)
  dep | .function (.base v) => nomatch v
  func
    | .top => .var .top
    | .function (.base v) => nomatch v

theorem negate_typed : negate.Typed where
  dep | .function (.base v) => nomatch v
  func
    | .top => rfl
    | .function (.base v) => nomatch v

-- Direct helper controls precede use of the optional service.
theorem direct_beta : DepEq generated expected := .beta body (.neg (.var 0))
theorem direct_eta : FuncEq (.lam (.app ((Ren.weaken Γ).funcMap parameter) (.var 0)))
    parameter := .eta parameter

theorem direct_twice_beta :
    DepEq (negate.depSub (negate.depSub generated))
      (negate.depSub (negate.depSub expected)) :=
  .sub negate negate_typed (.sub negate negate_typed direct_beta)

theorem direct_twice_eta :
    FuncEq (negate.funcSub (negate.funcSub (.lam (.app ((Ren.weaken Γ).funcMap parameter) (.var 0)))))
      (negate.funcSub (negate.funcSub parameter)) :=
  .sub negate negate_typed (.sub negate negate_typed direct_eta)

theorem service_beta : DepEq generated expected := by
  letI := generated.decideEq expected
  decide

theorem service_twice_beta :
    DepEq (negate.depSub (negate.depSub generated))
      (negate.depSub (negate.depSub expected)) :=
  (Dep.convertible_iff _ _).mpr rfl

theorem service_twice_eta :
    FuncEq (negate.funcSub (negate.funcSub (.lam (.app ((Ren.weaken Γ).funcMap parameter) (.var 0)))))
      (negate.funcSub (negate.funcSub parameter)) :=
  (Func.convertible_iff _ _).mpr rfl

-- The actual generated dependent output retains its nonconstant index.
def generatedTerm : Tm Γ (.family (.neg (.neg (.var 0)))) := ⟨generated, rfl⟩
def repairedTerm : Tm Γ (.family (.neg (.neg (.var 0)))) :=
  ⟨expected, (DepEq.type service_beta).symm.trans generatedTerm.2⟩

theorem literal_index : generated.type = .neg (.neg (.var 0)) := rfl

theorem changed_index_rejected : ¬ DepEq generated (.app parameter (.neg (.var 0))) := by
  intro h
  have k := DepEq.type h
  cases k

abbrev two : Ctx 1 := .function Γ (.var 0)
abbrev newest : Func two := .var .top
abbrev older : Func two := .var (.function .top)

theorem changed_head_rejected : ¬ FuncEq newest older := by
  intro h
  have k := FuncEq.normal_eq h
  cases k

-- Equal expected indices do not identify distinct free functions.
theorem same_index_heads : newest.type = older.type := rfl

theorem normal_substitution (t : Dep Γ) :
    (negate.depSub (negate.depSub t)).normal = (t.normal.sub negate).sub negate := by
  rw [Dep.normal_sub, Dep.normal_sub]

-- A real repair changes a formerly constant substitution to another free base
-- variable in an enlarged context. The old expected index must be replaced.
abbrev repairCtx : Ctx 2 := .function (.base (.base .nil)) (.var 0)

def repairSub (a : Base 2) : Sub repairCtx Γ where
  base _ := a
  dep | .function (.base v) => nomatch v
  func
    | .top => .var .top
    | .function (.base v) => nomatch v

theorem repairSub_typed (a : Base 2) : (repairSub a).Typed where
  dep | .function (.base v) => nomatch v
  func
    | .top => rfl
    | .function (.base v) => nomatch v

abbrev dependentRepair := (repairSub (.var 1)).depSub generated
abbrev repairedExpected : Dep repairCtx :=
  .app (.var .top) (.neg (.neg (.var 1)))

theorem repair_direct : DepEq dependentRepair repairedExpected :=
  .sub (repairSub (.var 1)) (repairSub_typed _) direct_beta

theorem repair_converted : DepEq dependentRepair repairedExpected := by
  letI := dependentRepair.decideEq repairedExpected
  decide

def repairedDependentTerm : Tm repairCtx (.family (.neg (.neg (.var 1)))) :=
  ⟨dependentRepair, rfl⟩

theorem obsolete_annotation_rejected : dependentRepair.type ≠ .neg (.neg .zero) := by
  intro h; cases h

theorem bound_stays_bound : (repairSub (.var 1)).lift.base 0 = .var 0 := rfl

theorem free_moves_under_binder : (repairSub (.var 1)).lift.base 1 = .var 2 := rfl

theorem weakened_consumer :
    ((Ren.weaken Γ).depMap generated).normal = generated.normal.map (Ren.weaken Γ) :=
  Dep.normal_map _ _

def etaExpand {n} {Δ : Ctx n} (f : Func Δ) : Func Δ :=
  .lam (.app ((Ren.weaken Δ).funcMap f) (.var 0))

abbrev generatedFunction := negate.funcSub (negate.funcSub
  (etaExpand (etaExpand parameter)))

theorem generated_function_direct : FuncEq generatedFunction
    (negate.funcSub (negate.funcSub parameter)) :=
  .sub negate negate_typed (.sub negate negate_typed
    (.trans (.eta (etaExpand parameter)) (.eta parameter)))

theorem generated_function_converted : FuncEq generatedFunction
    (negate.funcSub (negate.funcSub parameter)) := by
  letI := generatedFunction.decideEq (negate.funcSub (negate.funcSub parameter))
  decide

end Examples.DependentFunctionConversion
