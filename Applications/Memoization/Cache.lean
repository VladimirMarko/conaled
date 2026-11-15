import Applications.Memoization.Representation
import Applications.Resources.Workload
import Mathlib.Tactic

namespace Applications.Memoization

/-- Concrete operations count traversed table nodes. Their implementation, not
representation equivalence, determines these observations. -/
structure Storage (K : Type) [DecidableEq K] where
  representation : Representation K
  read : {V : Type} → representation.Carrier V → K → Resources.Measured V Nat
  read_value : ∀ {V} (s : representation.Carrier V) k,
    (read s k).1 = representation.lookup s k
  write : {V : Type} → representation.Carrier V → K → V →
    Resources.Measured (representation.Carrier V) Nat
  write_lookup : ∀ {V} (s : representation.Carrier V) k v j,
    representation.lookup (write s k v).1 j =
      if j = k then v else representation.lookup s j

namespace Storage
variable {K V : Type} [DecidableEq K]
abbrev State (S : Storage K) (V : Type) := S.representation.Carrier (Option V)
/-- Hits, body evaluations/misses, read-node visits, written path nodes. -/
abbrev Cost := Nat × Nat × Nat × Nat
abbrev Result (S : Storage K) (V : Type) := Resources.Measured (V × S.State V) Cost

def Valid (S : Storage K) (f : K → V) (s : S.State V) : Prop :=
  ∀ k v, S.representation.lookup s k = some v → v = f k

def Retains (S : Storage K) (s t : S.State V) : Prop :=
  ∀ k v, S.representation.lookup s k = some v → S.representation.lookup t k = some v

def empty (S : Storage K) : S.State V := S.representation.tabulate (fun _ => none)
theorem empty_valid (S : Storage K) (f : K → V) : S.Valid f S.empty := by
  intro k v h
  have := congrFun (S.representation.lookup_tabulate (fun _ => (none : Option V))) k
  simp [empty, this] at h

def call (S : Storage K) (k : K) (body : S.State V → S.Result V)
    (s : S.State V) : S.Result V :=
  let r := S.read s k
  match r.1 with
  | some v => ((v,s), (1,0,r.2,0))
  | none =>
    let b := body s
    let w := S.write b.1.2 k (some b.1.1)
    ((b.1.1,w.1), (0,1,r.2,w.2) + b.2)

theorem call_hit (S : Storage K) (k : K) (body : S.State V → S.Result V)
    (s : S.State V) (v : V) (h : S.representation.lookup s k = some v) :
    S.call k body s = ((v,s),(1,0,(S.read s k).2,0)) := by
  simp [call, S.read_value, h]

/-- Body correctness is local: miss execution must preserve prior valid entries. -/
theorem call_correct (S : Storage K) (f : K → V) (k : K)
    (body : S.State V → S.Result V)
    (body_correct : ∀ s, S.Valid f s →
      (body s).1.1 = f k ∧ S.Valid f (body s).1.2)
    (s : S.State V) (hs : S.Valid f s) :
    (S.call k body s).1.1 = f k ∧ S.Valid f (S.call k body s).1.2 ∧
      S.representation.lookup (S.call k body s).1.2 k = some (f k) := by
  cases h : S.representation.lookup s k with
  | some v => rw [S.call_hit k body s v h]; exact ⟨hs k v h, hs, by rw [h, hs k v h]⟩
  | none =>
    have hb := body_correct s hs
    simp only [call, S.read_value, h]
    refine ⟨hb.1, ?_, ?_⟩
    · intro j v hj
      rw [S.write_lookup] at hj
      split_ifs at hj with he
      · exact (Option.some.inj hj).symm.trans (hb.1.trans (congrArg f he).symm)
      · exact hb.2 j v hj
    · rw [S.write_lookup]; simp [hb.1]

/-- Repeating a successful call uses the stored result without invoking its body. -/
theorem repeat_hit (S : Storage K) (f : K → V) (k : K)
    (body : S.State V → S.Result V)
    (hb : ∀ s, S.Valid f s → (body s).1.1 = f k ∧ S.Valid f (body s).1.2)
    (s : S.State V) (hs : S.Valid f s) :
    S.call k body (S.call k body s).1.2 =
      ((f k,(S.call k body s).1.2),(1,0,(S.read (S.call k body s).1.2 k).2,0)) :=
  S.call_hit _ _ _ _ (S.call_correct f k body hb s hs).2.2

theorem call_retains (S : Storage K) (k : K) (body : S.State V → S.Result V)
    (hb : ∀ s, S.Retains s (body s).1.2) (s : S.State V) :
    S.Retains s (S.call k body s).1.2 := by
  cases h : S.representation.lookup s k with
  | some v => rw [S.call_hit k body s v h]; exact fun _ _ hv => hv
  | none =>
    intro j v hv
    simp only [call, S.read_value, h]
    rw [S.write_lookup]
    have hj : j ≠ k := by intro e; subst j; rw [h] at hv; contradiction
    simp only [ite_eq_right hj]
    exact hb s j v hv

end Storage
end Applications.Memoization
