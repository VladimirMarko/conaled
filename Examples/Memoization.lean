import Applications.Memoization.Words
import Applications.Memoization.Fibonacci

/-! Concrete carriers, extended keys and retained-state controls for #263. -/
namespace Examples.Memoization
open Applications.Memoization

example : Representation.empty.tabulate (fun e => e.elim : Empty → Nat) = () := rfl
example : Representation.unit.lookup (7 : Nat) () = 7 := rfl
example : Representation.bool.lookup (3,9) false = 3 := rfl
example : Representation.bool.lookup (3,9) true = 9 := rfl
example : (Representation.sum .bool .unit).lookup (V := Nat) ((3,9),(5 : Nat)) (.inr ()) = 5 := rfl
example : (Representation.prod .bool .bool).lookup ((1,2),(3,4)) (true,false) = 3 := rfl
example (r : (Nat × Nat) × (Nat × Nat)) :
    (Representation.prod .bool .bool).tabulate
      ((Representation.prod .bool .bool).lookup r) = r :=
  (Representation.prod .bool .bool).tabulate_lookup r

def boolFin : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := decide (i = 1)
  left_inv := by intro b; cases b <;> rfl
  right_inv := by intro i; fin_cases i <;> rfl

def flags : Bool × Bool ≃ Fin 4 :=
  (Equiv.prodCongr boolFin boolFin).trans finProdFinEquiv

def four : Representation (Fin 4) := (Representation.prod .bool .bool).transport flags

def incrementFour (r : four.Carrier Nat) : four.Carrier Nat :=
  ((r.1.1+1,r.1.2+1),(r.2.1+1,r.2.2+1))

theorem incrementFour_lookup (r : four.Carrier Nat) (i : Fin 4) :
    four.lookup (incrementFour r) i = Nat.succ (four.lookup r i) := by
  fin_cases i <;> rfl

theorem incrementFour_eq_map (r : four.Carrier Nat) : incrementFour r = four.map Nat.succ r :=
  four.operation_eq_map Nat.succ incrementFour incrementFour_lookup r

/-- The existing map-observation theorem is reused at the new key interface. -/
example (r : four.Carrier Nat) (i : Fin 4) :
    four.lookup (four.map (fun x => x+10) r) i = four.lookup r i + 10 :=
  four.lookup_map _ r i
example : four.lookup ((1,2),(3,4)) 2 = 3 := by decide
example : four.lookup (four.map Nat.succ ((1,2),(3,4))) 3 = 5 := by
  exact four.lookup_map Nat.succ ((1,2),(3,4)) 3
example (f : Nat → Nat) (r : four.Carrier Nat) :
    four.map f r = (Representation.prod .bool .bool).map f r :=
  (Representation.prod .bool .bool).transport_map flags f r

example (s : Applications.Parallel.Factor) (r : s.Data Nat) (k : s.Index) :
    (Representation.factor s).lookup ((Representation.factor s).map Nat.succ r) k =
      s.get r k + 1 := (Representation.factor s).lookup_map _ r k

example (t : Words.Table 5 Nat) :
    Words.restrict (by decide : 1 ≤ 3) (Words.restrict (by decide : 3 ≤ 5) t) =
      Words.restrict (by decide : 1 ≤ 5) t := Words.restrict_restrict _ _ t

/-- Direct nonrecursive cache clients reuse the same generic call law. -/
def body (k : Fin 4) (s : (Slots.storage 4).State Nat) : (Slots.storage 4).Result Nat :=
  ((k.val+10,s),0)

theorem repeat_direct (k : Fin 4) :
    (Slots.storage 4).call k (body k)
      ((Slots.storage 4).call k (body k) (Slots.storage 4).empty).1.2 =
      ((k.val+10,((Slots.storage 4).call k (body k) (Slots.storage 4).empty).1.2),
        (1,0,k.val+1,0)) := by
  have h := (Slots.storage 4).repeat_hit (fun k => k.val+10) k (body k)
    (fun _ hs => ⟨rfl,hs⟩) _ ((Slots.storage 4).empty_valid _)
  simpa using h

/-- An old function instance is not a valid cache for a changed meaning. -/
def stale : (Slots.storage 1).State Nat := (some 7,())
example : (Slots.storage 1).Valid (fun _ => 7) stale := by
  intro k v h
  have hk : k = 0 := Subsingleton.elim _ _
  subst k
  exact (Option.some.inj h).symm
example : ¬ (Slots.storage 1).Valid (fun _ => 8) stale := by
  intro h
  have bad : 7 = 8 := h 0 7 rfl
  omega
example : ((Slots.storage 1).call 0 (fun s => ((8,s),0)) stale).1.1 = 7 := rfl

/-- A malformed entry similarly defeats a caller that omits validity. -/
example : ¬ (Slots.storage 2).Valid Fibonacci.meaning ((some 99),(none,())) := by
  intro h
  have bad : 99 = 0 := h 0 99 rfl
  omega

example : (Slots.setup (V := Nat) 11).2 = 11 := Slots.setup_cost 11
example : (Slots.setup (V := Nat) 1).2 + (Fibonacci.cold 0).2.2.1 >
    (Client.ordinary 0).2 := by decide

end Examples.Memoization
