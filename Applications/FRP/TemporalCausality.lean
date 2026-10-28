import Applications.FRP.Temporal

/-! Processing-index causality is independent of eventual event delivery. -/
namespace Temporal
open Progress
universe u
variable {A B S : Type u}

def Synchronous (f : Stream A → Stream B) : Prop :=
  ∀ x y n, prefixOf x n = prefixOf y n → prefixOf (f x) n = prefixOf (f y) n

theorem synchronous_of_delivery (p : Processor A B) (work : Nat → Nat)
    (delivers : DeliversWithin p work) (demand : ∀ n, p.demand n ≤ n) :
    Synchronous p.meaning := by
  intro x y n h
  apply delivery_causal delivers x y n
  rw [← prefix_take x (demand n), ← prefix_take y (demand n), h]

theorem mealy_synchronous (op : Mealy S A B) (s : S) : Synchronous (runStream op s) :=
  synchronous_of_delivery (mealyProcessor op s) _ (mealy_delivery op s) (fun _ => le_rfl)

/-- A total function can anticipate the next input. -/
theorem shift_not_synchronous : ¬ Synchronous (shift (A := Nat)) := by
  intro h
  have e := h (fun _ => 0) (fun n => if n = 0 then 0 else 1) 1 rfl
  norm_num [prefixOf, shift] at e
end Temporal

namespace FRPSpec.Frontier.Demand.Temporal
open FRPSpec.Frontier.Trace
variable {T α : Type} [LinearOrder T]

theorem count_le (schedule : Schedule) (source : Source) (n : Nat) :
    count schedule source n ≤ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [count]; split <;> omega

/-- States before step n depend only on earlier actions and bounded source prefixes. -/
theorem state_prefix (s : Inputs T α) (ms ns : Streams T α)
    (a b : Nat → Action T) (n : Nat)
    (actions : ∀ j, j < n → a j = b j)
    (messages : ∀ source k, k < n → ms source k = ns source k) :
    (∀ source, count (sourceSchedule a) source n = count (sourceSchedule b) source n) ∧
    run s ms (sourceSchedule a) n = run s ns (sourceSchedule b) n ∧
    request s ms a n = request s ns b n := by
  induction n with
  | zero => exact ⟨fun _ => rfl, rfl, rfl⟩
  | succ n ih =>
    obtain ⟨hc,hr,hq⟩ := ih (fun j hj => actions j (by omega))
      (fun source k hk => messages source k (by omega))
    have ha := actions n (by omega)
    have hs : sourceSchedule a n = sourceSchedule b n := by simp [sourceSchedule,ha]
    refine ⟨?_,?_,?_⟩
    · intro source
      simp only [count, hc, hs]
    · funext source
      rw [run_step, run_step, hs, hr, hc]
      rw [messages source (count (sourceSchedule b) source n)
        (by have := count_le (sourceSchedule b) source n; omega)]
    · simp only [request, hr, hq, ha]

/-- The response at n additionally reads action n, but no later action or message. -/
theorem response_prefix (s : Inputs T α) (ms ns : Streams T α)
    (a b : Nat → Action T) (n : Nat)
    (actions : ∀ j, j ≤ n → a j = b j)
    (messages : ∀ source k, k < n → ms source k = ns source k) :
    response s ms a n = response s ns b n := by
  obtain ⟨_,hr,hq⟩ := state_prefix s ms ns a b n (fun j hj => actions j (by omega)) messages
  simp only [response,hr,hq,actions n le_rfl]

end FRPSpec.Frontier.Demand.Temporal
