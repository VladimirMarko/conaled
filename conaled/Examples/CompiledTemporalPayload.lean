import SquareKit.CurryHowardRelations
import SquareKit.Temporal.BatchRelations
import Applications.FRP.TemporalPayload
import Examples.TemporalFRP

/-! One proof/program, related representations, finite timing, and honest batches. -/
namespace Examples.CompiledTemporalPayload
open SquareKit.CurryHoward Temporal

/-- The cross-kind contract has arbitrary payload relations and waiting families. -/
theorem compiled_batch_related {R S : Type} {A C : Nat → Type}
    (RA : ∀ n, A n → C n → Prop) (E : R → S → Prop)
    (fR : R → R) (fS : S → S) (hf : ∀ x y, E x y → E (fR x) (fS y))
    {t : Until A (fun _ => List R) n} {s : Until C (fun _ => List S) n}
    (h : Until.Rel RA (fun _ => List.Forall₂ E) t s) :
    Until.Rel RA (fun _ => List.Forall₂ E)
      (mapBatch (compiledTwice E fR) t) (mapBatch (twice fS) s) :=
  mapBatch_related _ _ (fun _ _ hxy => twice_related E fR fS hf hxy) h

example (x : Nat) : twice Nat.succ x = x + 2 := rfl
example (x : Nat) : compiledTwice (Eq : Nat → Nat → Prop) Nat.succ x = x + 2 := rfl
example (x : Nat) : compiledTwice (Eq : Nat → Nat → Prop) (fun x => x * 2) x = x * 4 := by
  simp [twice, Nat.mul_assoc]

/-- One source value relates to either tag; the relation has no chosen inverse. -/
def tagged (x : Nat) (y : Nat × Bool) : Prop := x = y.1
def bump (y : Nat × Bool) : Nat × Bool := (y.1+1, !y.2)
def double (y : Nat × Bool) : Nat × Bool := (y.1*2, y.2)
theorem bump_related (x y) (h : tagged x y) : tagged (x+1) (bump y) :=
  congrArg (· + 1) h
theorem double_related (x y) (h : tagged x y) : tagged (x*2) (double y) :=
  congrArg (· * 2) h
example : tagged 1 (1,false) ∧ tagged 1 (1,true) ∧ (1,false) ≠ (1,true) := by unfold tagged; decide

abbrev Cert (X : Type) := Until (fun _ => Unit) (fun _ => List X) 0
def source : Cert Nat := .wait () (.wait () (.now [1,1,2]))
def target : Cert (Nat × Bool) := .wait () (.wait () (.now [(1,false),(1,true),(2,false)]))
theorem source_related : Until.Rel (fun _ => Eq) (fun _ => List.Forall₂ tagged) source target :=
  .wait rfl (.wait rfl (.now (.cons rfl (.cons rfl (.cons rfl .nil)))))

theorem mapped_related : Until.Rel (fun _ => Eq) (fun _ => List.Forall₂ tagged)
    (mapBatch (compiledTwice tagged (· + 1)) source) (mapBatch (twice bump) target) :=
  compiled_batch_related _ _ _ _ bump_related source_related
example : Until.terminal (mapBatch (compiledTwice tagged (· + 1)) source) = [3,3,4] := rfl
example : (mapBatch (compiledTwice tagged (· + 1)) source).horizon = 2 :=
  mapBatch_horizon _ _
example : (mapBatch (twice bump) target).horizon = 2 := mapBatch_horizon _ _

/-- Two independently supplied related functions compose through the same lifting. -/
example : Until.Rel (fun _ => Eq) (fun _ => List.Forall₂ tagged)
    (mapBatch (compiledTwice tagged (· * 2)) (mapBatch (compiledTwice tagged (· + 1)) source))
    (mapBatch (twice double) (mapBatch (twice bump) target)) :=
  compiled_batch_related _ _ _ _ double_related mapped_related
example : mapBatch (twice (· * 2)) (mapBatch (twice (· + 1)) source) =
    mapBatch (twice (· * 2) ∘ twice (· + 1)) source := mapBatch_comp _ _ _
example : Until.terminal (mapBatch (twice (· * 2)) (mapBatch (twice (· + 1)) source)) =
    [12,12,16] := rfl
example : Until.Rel (fun _ => Eq) (fun _ => List.Forall₂ tagged)
    (mapBatch (compiledTwice tagged (· + 1)) (.now [] : Cert Nat))
    (mapBatch (twice bump) (.now [] : Cert (Nat × Bool))) :=
  compiled_batch_related _ _ _ _ bump_related (.now .nil)

/-- The window presentation and relational composition retain the same timing. -/
example : Until.Rel (fun _ => Eq) (fun _ => List.Forall₂ tagged)
    (Until.ofWindow (A := fun _ => Unit) (B := fun _ => List Nat) 0 2 (fun _ => ()) [1,1,2])
    (Until.ofWindow (A := fun _ => Unit) (B := fun _ => List (Nat × Bool)) 0 2 (fun _ => ()) [(1,false),(1,true),(2,false)]) :=
  Until.Rel.ofWindow 0 2 _ _ _ _ (fun _ => rfl)
    (.cons rfl (.cons rfl (.cons rfl .nil)))
example : Until.Rel (fun _ a c => ∃ b, a = b ∧ b = c)
    (fun _ xs zs => ∃ ys, List.Forall₂ tagged xs ys ∧ ys = zs) source target :=
  source_related.comp (Until.Rel.refl target)

/-- Terminal values alone cannot reconstruct a finite witness's horizon. -/
def immediate : Cert Nat := .now [7,7]
def delayed : Cert Nat := .wait () (.now [7,7])
example : Until.terminal immediate = Until.terminal delayed := rfl
theorem horizon_lost : ¬ ∃ recover : List Nat → Nat,
    ∀ w : Cert Nat, recover (Until.terminal w) = w.horizon := by
  rintro ⟨recover,h⟩
  have bad := (h immediate).symm.trans (h delayed)
  exact (by decide : (0 : Nat) ≠ 1) bad
example : ¬ Until.Rel (fun _ => Eq) (fun _ => Eq) immediate delayed := by
  intro h
  exact (by decide : (0 : Nat) ≠ 1) h.horizon_eq
example : ¬ Synchronous (Progress.shift (A := Nat)) := shift_not_synchronous

open FRPSpec.Frontier FRPSpec.Frontier.Trace FRPSpec.Frontier.Demand
open FRPSpec.Frontier.Demand.Temporal
open Examples.FRPTrace Examples.FRPDemand Examples.TemporalFRP

def mappedEarly := mapPayload start packets early 2 truth honest
  (compiledTwice (Eq : Nat → Nat → Prop) Nat.succ) earlyWitness
example : mappedEarly.horizon = 4 := mapPayload_horizon _ _ _ _ _ _ _ _
example : (Until.terminal mappedEarly).val = [5,6,5] :=
  mapPayload_value _ _ _ _ _ _ _ _

/-- Explicit data, including known-empty delivery, need no existence-to-program choice. -/
def lateWitness : Arrival start packets late 2 3 := .now ⟨[3,4,3], ⟨by decide⟩⟩
def emptyWitness : Arrival start packets emptyQuery 1 1 := .now ⟨[], ⟨by decide⟩⟩
example : (mapPayload start packets late 2 truth honest (twice Nat.succ) lateWitness).horizon = 0 :=
  mapPayload_horizon _ _ _ _ _ _ _ _
example : (Until.terminal (mapPayload start packets emptyQuery 1 truth honest
    (twice Nat.succ) emptyWitness)).val = [] := mapPayload_value _ _ _ _ _ _ _ _
example : ∃ fuel result, searchArrival start packets early 2 fuel 1 (by decide) = some result :=
  arrival_has_fuel start packets early 2 earlyWitness (by decide)

end Examples.CompiledTemporalPayload
