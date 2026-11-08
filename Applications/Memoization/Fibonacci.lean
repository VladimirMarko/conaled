import Applications.Memoization.Slots
import Applications.Memoization.Client

namespace Applications.Memoization
namespace Fibonacci

def meaning {N : Nat} (k : Fin (N+1)) : Nat := Client.fib k.val
abbrev State (N : Nat) := (Slots.storage (N+1)).State Nat
abbrev Result (N : Nat) := (Slots.storage (N+1)).Result Nat

/-- Both smaller calls use this very evaluator and thread its returned cache.
Termination is by the natural argument, never by an assumed cache property. -/
def eval {N : Nat} : (n : Nat) → n ≤ N → State N → Result N
  | 0, _, s => (Slots.storage (N+1)).call 0 (fun t => ((0,t),0)) s
  | 1, h, s => (Slots.storage (N+1)).call ⟨1,by omega⟩ (fun t => ((1,t),0)) s
  | n+2, h, s => (Slots.storage (N+1)).call ⟨n+2,by omega⟩ (fun t =>
      let a := eval (n+1) (by omega) t
      let b := eval n (by omega) a.1.2
      ((a.1.1+b.1.1,b.1.2), a.2+b.2)) s

theorem correct {N : Nat} (n : Nat) (h : n ≤ N) (s : State N)
    (hs : (Slots.storage (N+1)).Valid meaning s) :
    (eval n h s).1.1 = Client.fib n ∧
      (Slots.storage (N+1)).Valid meaning (eval n h s).1.2 ∧
      (Slots.representation (N+1)).lookup (eval n h s).1.2 ⟨n,by omega⟩ =
        some (Client.fib n) := by
  induction n using Nat.twoStepInduction generalizing s with
  | zero => exact (Slots.storage (N+1)).call_correct meaning 0 _ (fun t ht => ⟨rfl,ht⟩) s hs
  | one =>
    exact (Slots.storage (N+1)).call_correct meaning ⟨1,by omega⟩ _
      (fun t ht => ⟨rfl,ht⟩) s hs
  | more n ih ih' =>
    apply (Slots.storage (N+1)).call_correct meaning ⟨n+2,by omega⟩ _ _ s hs
    intro t ht
    have ha := ih' (by omega) t ht
    have hb := ih (by omega) (eval (n+1) (by omega) t).1.2 ha.2.1
    exact ⟨by simp only [meaning, Client.fib]; rw [ha.1,hb.1], hb.2.1⟩

theorem hit {N : Nat} (n : Nat) (h : n ≤ N) (s : State N) (v : Nat)
    (hs : (Slots.representation (N+1)).lookup s ⟨n,by omega⟩ = some v) :
    eval n h s = ((v,s),(1,0,n+1,0)) := by
  match n with
  | 0 => rw [eval, Storage.call_hit _ _ _ _ _ hs]; simp only [Slots.storage_read_cost]; rfl
  | 1 => rw [eval, Storage.call_hit _ _ _ _ _ hs]; simp only [Slots.storage_read_cost]
  | n+2 => rw [eval, Storage.call_hit _ _ _ _ _ hs]; simp only [Slots.storage_read_cost]

theorem repeated {N : Nat} (n : Nat) (h : n ≤ N) (s : State N)
    (hs : (Slots.storage (N+1)).Valid meaning s) :
    eval n h (eval n h s).1.2 =
      ((Client.fib n,(eval n h s).1.2),(1,0,n+1,0)) :=
  hit n h _ _ (correct n h s hs).2.2

theorem retains {N : Nat} (n : Nat) (h : n ≤ N) (s : State N) :
    (Slots.storage (N+1)).Retains s (eval n h s).1.2 := by
  induction n using Nat.twoStepInduction generalizing s with
  | zero => exact (Slots.storage (N+1)).call_retains 0 _ (fun _ _ _ hv => hv) s
  | one => exact (Slots.storage (N+1)).call_retains ⟨1,by omega⟩ _ (fun _ _ _ hv => hv) s
  | more n ih ih' =>
    apply (Slots.storage (N+1)).call_retains ⟨n+2,by omega⟩ _ _ s
    intro t k v hv
    exact ih (by omega) _ k v (ih' (by omega) t k v hv)

/-- A stateful workload uses the library executor and discards only the answer. -/
def step {N : Nat} (k : Fin (N+1)) (s : State N) : Resources.Measured (State N) Storage.Cost :=
  let r := eval k.val (by omega) s
  (r.1.2,r.2)

theorem workload_valid {N : Nat} (ks : List (Fin (N+1))) (s : State N)
    (hs : (Slots.storage (N+1)).Valid meaning s) :
    (Slots.storage (N+1)).Valid meaning (Resources.run step ks s).1 :=
  Resources.run_invariant step _ (fun k t ht => (correct k.val (by omega) t ht).2.1) ks s hs

def cold (n : Nat) : Result n := eval n (Nat.le_refl n) (Slots.storage (n+1)).empty

theorem cold_value (n : Nat) : (cold n).1.1 = Client.fib n :=
  (correct n (Nat.le_refl n) _ ((Slots.storage (n+1)).empty_valid meaning)).1

example : (cold 0).1.1 = 0 ∧ (cold 0).2 = (0,1,1,1) := by decide
example : (cold 1).1.1 = 1 ∧ (cold 1).2 = (0,1,2,2) := by decide
example : (cold 10).1.1 = 55 ∧ (cold 10).2.1 = 8 ∧ (cold 10).2.2.1 = 11 := by decide
example : (cold 10).2 = (8,11,110,66) := by decide
example : (eval 10 (by decide) (cold 10).1.2).2 = (1,0,11,0) := by decide
example : (Resources.run (step (N := 10)) [10,10] (Slots.storage 11).empty).2.2.1 = 11 := by decide
example : (cold 10).2.2.1 + (cold 10).2.2.1 = 22 := by decide
example : (cold 10).2.2.1 < (Client.ordinary 10).2 := by decide

end Fibonacci
end Applications.Memoization
