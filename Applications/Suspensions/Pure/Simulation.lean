import Applications.Suspensions.Pure.History
import Applications.Suspensions.Pure.Memory

/-!
# Related control states and pending continuations

The relation pairs the existing raw and pure control constructors. Source code
and patterns are retained literally; values and captures use the immutable
world. Raw memoize frames pair with pure force frames and retain their address
meaning. Recursive creation's intermediate frames are handled by its separate
finite creation prefix, so they are not part of this stable-state relation.

ConfigRep combines structural correspondence, represented memory and the
executed prefix for each pending force occurrence. It does not assert a
transition simulation or hereditary source-code validity by definition.
-/
set_option autoImplicit false
set_option warningAsError true

namespace Suspensions.Pure.Simulation
open Representation Memory History

variable {Primitive : Type}

inductive ControlRep (world : World Primitive) :
    Core.Machine.Control Primitive → Machine.Control Primitive → Prop
  | eval {raw : Core.Env Primitive} {view : Env Primitive} (expression : Core.Expr Primitive)
      (captured : EnvRep world raw view) : ControlRep world (.eval raw expression) (.eval view expression)
  | value {raw : Core.Value Primitive} {view : Value Primitive} (represented : ValueRep world raw view) :
      ControlRep world (.value raw) (.value view)
  | raised {raw : Core.Value Primitive} {view : Value Primitive} (represented : ValueRep world raw view) :
      ControlRep world (.raised raw) (.raised view)
  | pattern {raw : Core.Env Primitive} {view : Env Primitive}
      {rawValue : Core.Value Primitive} {viewValue : Value Primitive} (pattern : Core.Pattern)
      (captured : EnvRep world raw view) (represented : ValueRep world rawValue viewValue) :
      ControlRep world (.pattern raw pattern rawValue) (.pattern view pattern viewValue)
  | matched {raw : Core.Env Primitive} {view : Env Primitive} (bindings : EnvRep world raw view) :
      ControlRep world (.matched raw) (.matched view)
  | mismatch : ControlRep world .mismatch .mismatch
  | clauses {raw : Core.Env Primitive} {view : Env Primitive}
      {rawValue : Core.Value Primitive} {viewValue : Value Primitive}
      (clauses : List (Core.Pattern × Core.Expr Primitive))
      (captured : EnvRep world raw view) (represented : ValueRep world rawValue viewValue) :
      ControlRep world (.clauses raw clauses rawValue) (.clauses view clauses viewValue)
  | rows {raw : Core.Env Primitive} {view : Env Primitive}
      {rawFields rawBindings : Core.Env Primitive} {viewFields viewBindings : Env Primitive}
      (patterns : List (Nat × Core.Pattern)) (captured : EnvRep world raw view)
      (fields : EnvRep world rawFields viewFields) (bindings : EnvRep world rawBindings viewBindings) :
      ControlRep world (.rows raw patterns rawFields rawBindings)
        (.rows view patterns viewFields viewBindings)

inductive FrameRep (world : World Primitive) :
    Core.Machine.Frame Primitive → Machine.Frame Primitive → Prop
  | constructor (tag : Nat) : FrameRep world (.constructor tag) (.constructor tag)
  | record {raw : Core.Env Primitive} {view : Env Primitive}
      {rawDone : Core.Env Primitive} {viewDone : Env Primitive} (label : Nat)
      (remaining : List (Nat × Core.Expr Primitive)) (captured : EnvRep world raw view)
      (done : EnvRep world rawDone viewDone) :
      FrameRep world (.record raw label remaining rawDone) (.record view label remaining viewDone)
  | function {raw : Core.Env Primitive} {view : Env Primitive} (argument : Core.Expr Primitive)
      (captured : EnvRep world raw view) : FrameRep world (.function raw argument) (.function view argument)
  | argument {raw : Core.Value Primitive} {view : Value Primitive} (represented : ValueRep world raw view) :
      FrameRep world (.argument raw) (.argument view)
  | bindValue {raw : Core.Env Primitive} {view : Env Primitive}
      (pattern : Core.Pattern) (body : Core.Expr Primitive) (captured : EnvRep world raw view) :
      FrameRep world (.bindValue raw pattern body) (.bindValue view pattern body)
  | bindMatch {raw : Core.Env Primitive} {view : Env Primitive} (body : Core.Expr Primitive)
      (captured : EnvRep world raw view) : FrameRep world (.bindMatch raw body) (.bindMatch view body)
  | branch {raw : Core.Env Primitive} {view : Env Primitive} (yes no : Core.Expr Primitive)
      (captured : EnvRep world raw view) : FrameRep world (.branch raw yes no) (.branch view yes no)
  | raise : FrameRep world .raise .raise
  | handler {raw : Core.Env Primitive} {view : Env Primitive}
      (clauses : List (Core.Pattern × Core.Expr Primitive)) (captured : EnvRep world raw view) :
      FrameRep world (.handler raw clauses) (.handler view clauses)
  | handlerResult {raw : Core.Value Primitive} {view : Value Primitive}
      (represented : ValueRep world raw view) : FrameRep world (.handlerResult raw) (.handlerResult view)
  | applicationResult : FrameRep world .applicationResult .applicationResult
  | clause {raw : Core.Env Primitive} {view : Env Primitive}
      {rawValue : Core.Value Primitive} {viewValue : Value Primitive}
      (body : Core.Expr Primitive) (remaining : List (Core.Pattern × Core.Expr Primitive))
      (captured : EnvRep world raw view) (represented : ValueRep world rawValue viewValue) :
      FrameRep world (.clause raw body remaining rawValue) (.clause view body remaining viewValue)
  | memoize {raw : Core.Env Primitive} {view : Env Primitive} {address : Nat}
      {meaning : Meaning Primitive} (inner : Core.Pattern)
      (found : world address = some meaning) (captured : EnvRep world raw view) :
      FrameRep world (.memoize address raw inner) (.force view inner)
  | row {raw : Core.Env Primitive} {view : Env Primitive}
      {rawFields rawEarlier : Core.Env Primitive} {viewFields viewEarlier : Env Primitive}
      (remaining : List (Nat × Core.Pattern)) (captured : EnvRep world raw view)
      (fields : EnvRep world rawFields viewFields) (earlier : EnvRep world rawEarlier viewEarlier) :
      FrameRep world (.row raw remaining rawFields rawEarlier) (.row view remaining viewFields viewEarlier)
  | layered {raw : Core.Value Primitive} {view : Value Primitive} (name : Nat)
      (represented : ValueRep world raw view) : FrameRep world (.layered name raw) (.layered name view)

def FramesRep (world : World Primitive) :
    List (Core.Machine.Frame Primitive) → List (Machine.Frame Primitive) → Prop :=
  List.Forall₂ (FrameRep world)

structure ConfigRep (parameters : Machine.Parameters Primitive) (world : World Primitive)
    (raw : Core.Machine.Config Primitive) (view : Machine.Config Primitive) : Prop where
  memory : StateRep parameters world raw.memory
  control : ControlRep world raw.control view.control
  frames : FramesRep world raw.stack view.stack
  histories : ActiveHistories parameters world raw.stack view.control view.stack

theorem ControlRep.mono {before after : World Primitive}
    (extension : Durability.Extends before after)
    {raw : Core.Machine.Control Primitive} {view : Machine.Control Primitive}
    (represented : ControlRep before raw view) : ControlRep after raw view := by
  cases represented with
  | eval expression captured => exact .eval expression (captured.mono extension)
  | value value => exact .value (value.mono extension)
  | raised value => exact .raised (value.mono extension)
  | pattern pattern captured value => exact .pattern pattern (captured.mono extension) (value.mono extension)
  | matched bindings => exact .matched (bindings.mono extension)
  | mismatch => exact .mismatch
  | clauses clauses captured value => exact .clauses clauses (captured.mono extension) (value.mono extension)
  | rows patterns captured fields bindings =>
      exact .rows patterns (captured.mono extension) (fields.mono extension) (bindings.mono extension)

theorem FrameRep.mono {before after : World Primitive}
    (extension : Durability.Extends before after)
    {raw : Core.Machine.Frame Primitive} {view : Machine.Frame Primitive}
    (represented : FrameRep before raw view) : FrameRep after raw view := by
  cases represented with
  | constructor tag => exact .constructor tag
  | record label remaining captured done =>
      exact .record label remaining (captured.mono extension) (done.mono extension)
  | function argument captured => exact .function argument (captured.mono extension)
  | argument value => exact .argument (value.mono extension)
  | bindValue pattern body captured => exact .bindValue pattern body (captured.mono extension)
  | bindMatch body captured => exact .bindMatch body (captured.mono extension)
  | branch yes no captured => exact .branch yes no (captured.mono extension)
  | raise => exact .raise
  | handler clauses captured => exact .handler clauses (captured.mono extension)
  | handlerResult value => exact .handlerResult (value.mono extension)
  | applicationResult => exact .applicationResult
  | clause body remaining captured value =>
      exact .clause body remaining (captured.mono extension) (value.mono extension)
  | memoize inner found captured => exact .memoize inner (extension _ _ found) (captured.mono extension)
  | row remaining captured fields earlier =>
      exact .row remaining (captured.mono extension) (fields.mono extension) (earlier.mono extension)
  | layered name value => exact .layered name (value.mono extension)

theorem FramesRep.mono {before after : World Primitive}
    (extension : Durability.Extends before after)
    {raw : List (Core.Machine.Frame Primitive)} {view : List (Machine.Frame Primitive)}
    (represented : FramesRep before raw view) : FramesRep after raw view := by
  induction represented with
  | nil => exact .nil
  | cons head tail ih => exact .cons (head.mono extension) ih

theorem ConfigRep.start {parameters : Machine.Parameters Primitive} {world : World Primitive}
    {memory : Core.Machine.Memory Primitive} {raw : Core.Env Primitive} {view : Env Primitive}
    (valid : StateRep parameters world memory) (captured : EnvRep world raw view)
    (expression : Core.Expr Primitive) :
    ConfigRep parameters world (Core.Machine.start memory raw expression) (Machine.start view expression) :=
  ⟨valid, .eval expression captured, .nil, ActiveHistories.empty _ _ _ _⟩

theorem ConfigRep.startPattern {parameters : Machine.Parameters Primitive} {world : World Primitive}
    {memory : Core.Machine.Memory Primitive} {raw : Core.Env Primitive} {view : Env Primitive}
    {rawValue : Core.Value Primitive} {viewValue : Value Primitive}
    (valid : StateRep parameters world memory) (captured : EnvRep world raw view)
    (represented : ValueRep world rawValue viewValue) (pattern : Core.Pattern) :
    ConfigRep parameters world (Core.Machine.startPattern memory raw pattern rawValue)
      (Machine.startPattern view pattern viewValue) :=
  ⟨valid, .pattern pattern captured represented, .nil, ActiveHistories.empty _ _ _ _⟩

end Suspensions.Pure.Simulation
