import SquareKit.StateException
import Applications.Interaction.Measurement

/-! # Selected witnesses and retained measurement observations

The mutable Boolean cell is local scratch state. Measurement observations live
outside that cell, so rolling it back does not erase a recorded external attempt.
-/
namespace StateException.Examples

abbrev W := {n : Nat // n < 2}
def witness (s : Bool) : W := if s then ⟨1, by decide⟩ else ⟨0, by decide⟩

def failed : Tree Bool Unit W := .write true (.raise ())
def captured (s : Bool) : Scoped Bool Unit W :=
  .handle (.body failed) (fun _ => .body (.ret (witness s)))
def recomputed : Scoped Bool Unit W :=
  .handle (.body failed) (fun _ => .body (.read (fun s => .ret (witness s))))

/-- P captures before entering the protected scope. -/
def pKeep : Keep Bool Unit W :=
  Keep.bind Keep.get (fun s => scopedFold (keepAlgebra Bool Unit) Keep.handle (captured s))
def pUndo : Undo Bool Unit W :=
  Undo.bind Undo.get (fun s => scopedFold (undoAlgebra Bool Unit) Undo.handle (captured s))

theorem p_keep (s : Bool) : pKeep s = (.ok (witness s), true) := rfl
theorem p_undo (s : Bool) : pUndo s = .ok (witness s, s) := rfl

/-- Exact result equality forgets final state deliberately, not subtype data. -/
def SameSelected {S E A : Type} (k : Except E A × S) (u : Except E (A × S)) : Prop :=
  ∃ a sk su, k = (.ok a, sk) ∧ u = .ok (a, su)

theorem selected_preserved (s : Bool) : SameSelected (pKeep s) (pUndo s) := by
  exact ⟨witness s, true, s, p_keep s, p_undo s⟩

theorem final_states_differ : (pKeep false).2 ≠
    (match pUndo false with | .ok (_, s) => s | .error _ => true) := by decide

theorem q_keep : scopedFold (keepAlgebra Bool Unit) Keep.handle recomputed false =
    (.ok (witness true), true) := rfl
theorem q_undo : scopedFold (undoAlgebra Bool Unit) Undo.handle recomputed false =
    .ok (witness false, false) := rfl

theorem recomputation_changes_selection :
    ¬ SameSelected (scopedFold (keepAlgebra Bool Unit) Keep.handle recomputed false)
      (scopedFold (undoAlgebra Bool Unit) Undo.handle recomputed false) := by
  rintro ⟨a, sk, su, hk, hu⟩
  have h1 : witness true = a := by injection hk with h; exact Except.ok.inj h
  have h0 : witness false = a := by injection hu with h; exact (Prod.mk.inj h).1
  have bad := congrArg Subtype.val (h1.trans h0.symm)
  contradiction

/-- Composition is derived from the four local laws, for arbitrary continuations. -/
example (p : Tree Bool Unit Nat) (k : Nat → Tree Bool Unit W) :
    fold (keepAlgebra Bool Unit) (p.bind k) =
      Keep.bind (fold (keepAlgebra Bool Unit) p) (fun n => fold (keepAlgebra Bool Unit) (k n)) :=
  fold_bind _ (keep_local _ _) _ _
example (p : Tree Bool Unit Nat) (k : Nat → Tree Bool Unit W) :
    fold (undoAlgebra Bool Unit) (p.bind k) =
      Undo.bind (fold (undoAlgebra Bool Unit) p) (fun n => fold (undoAlgebra Bool Unit) (k n)) :=
  fold_bind _ (undo_local _ _) _ _

/-- A state/exception tensor cannot be claimed for Keep. -/
theorem bad_mixed_law :
    Keep.bind (Keep.put true) (fun _ => Keep.throw ()) ≠
      (Keep.throw () : Keep Bool Unit W) := by
  intro h
  have bad := congrFun h false
  have := congrArg Prod.snd bad
  contradiction

/-- Moving a write into an Undo scope requires restoring it in the handler. -/
theorem keep_catch_law_fails_for_undo :
    Undo.bind (Undo.put true) (fun _ => Undo.handle (Undo.throw ()) (fun _ => Undo.get)) ≠
      Undo.handle (Undo.bind (Undo.put true) (fun _ => Undo.throw ()))
        (fun _ => (Undo.get : Undo Bool Unit Bool)) := by
  intro h
  have bad := congrFun h false
  change Except.ok (true, true) = Except.ok (false, false) at bad
  cases bad

/-- Adding that reset to Keep loses the protected computation's last state. -/
theorem undo_catch_law_fails_for_keep :
    Keep.bind (Keep.put false) (fun _ => Keep.handle
      (Keep.bind (Keep.put true) (fun _ => Keep.throw ())) (fun _ => Keep.get)) ≠
    Keep.handle (Keep.bind (Keep.put false) (fun _ =>
      Keep.bind (Keep.put true) (fun _ => Keep.throw ())))
      (fun _ => Keep.bind (Keep.put false) (fun _ => (Keep.get : Keep Bool Unit Bool))) := by
  intro h
  have bad := congrFun h false
  change (Except.ok true, true) = (Except.ok false, false) at bad
  cases bad

open Interaction.Measurement

/-- Actual existing record operation is committed before local tentative work.
The returned Controller carries the observation even when local state is undone. -/
def recorded (s : Controller) (o : Observation) : Controller := record s o

def measurementKeep (s : Controller) (o : Observation) : Keep Bool Unit Controller :=
  Keep.handle (Keep.bind (Keep.put true) (fun _ => Keep.throw ()))
    (fun _ => Keep.ret (recorded s o))
def measurementUndo (s : Controller) (o : Observation) : Undo Bool Unit Controller :=
  Undo.handle (Undo.bind (Undo.put true) (fun _ => Undo.throw ()))
    (fun _ => Undo.ret (recorded s o))

def measurementTree (s : Controller) (o : Observation) : Scoped Bool Unit Controller :=
  .handle (.body (.write true (.raise ()))) (fun _ => .body (.ret (record s o)))

theorem measurement_handler_keep (s : Controller) (o : Observation) :
    scopedFold (keepAlgebra Bool Unit) Keep.handle (measurementTree s o) = measurementKeep s o := rfl
theorem measurement_handler_undo (s : Controller) (o : Observation) :
    scopedFold (undoAlgebra Bool Unit) Undo.handle (measurementTree s o) = measurementUndo s o := rfl

/-- Native and handler routes retain exactly the existing operation's evidence. -/
theorem measurement_contract (s : Controller) (o : Observation) (b : Bool) :
    measurementKeep s o b = (.ok (record s o), true) ∧
    measurementUndo s o b = .ok (record s o, b) ∧
    (record s o).observation = some o ∧ ResultValid (record s o) := by
  exact ⟨rfl, rfl, rfl, recording_safe s o⟩

theorem measurement_no_retry (s : Controller) (o : Observation) (hs : s.started = true) :
    begin (record s o) = none :=
  no_reexecution hs (Relation.ReflTransGen.single ⟨o, rfl⟩)

/-- The existing primitive trust assumptions remain necessary for external success. -/
theorem measurement_world (s : Controller) (o : Observation) (w : World)
    (truth : Corresponds w o) (success : successful (record s o) = true) : Completed w :=
  successful_world (record s o) o w rfl truth success

def missingReply : Observation := ⟨.unknown, false, .confirmed, .unknown⟩
def attempted : Controller := ⟨true, none⟩

theorem missing_reply_retained :
    measurementUndo attempted missingReply false = .ok (record attempted missingReply, false) ∧
    (record attempted missingReply).observation = some missingReply ∧
    successful (record attempted missingReply) = false ∧
    begin (record attempted missingReply) = none := by
  exact ⟨(measurement_contract _ _ _).2.1, rfl, rfl, measurement_no_retry _ _ rfl⟩

end StateException.Examples
