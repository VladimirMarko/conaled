import Mathlib.Computability.RecursiveIn
import Mathlib.Computability.TuringDegree

/-! Finite programs for the full partial-recursive closure of one supplied oracle. -/

namespace OracleComputation

/-- The query has no embedded function or correctness proof. -/
inductive Code where
  | zero | succ | left | right | query
  | pair : Code → Code → Code
  | comp : Code → Code → Code
  | prec : Code → Code → Code
  | rfind : Code → Code
  deriving DecidableEq, Repr

/-- Partial minimization retains undefined earlier tests. -/
def search (f : Nat →. Nat) (a : Nat) : Part Nat :=
  Nat.rfind fun n => (fun m => m = 0) <$> f (Nat.pair a n)

/-- Primitive recursion with the same argument layout as `Nat.RecursiveIn`. -/
def recur (f g : Nat →. Nat) (p : Nat) : Part Nat :=
  let (a, n) := Nat.unpair p
  n.rec (f a) fun y ih => do
    let i ← ih
    g (Nat.pair a (Nat.pair y i))

/-- Mathematical denotation, parameterized by a possibly partial oracle. -/
def eval (oracle : Nat →. Nat) : Code → Nat →. Nat
  | .zero => fun _ => .some 0
  | .succ => fun n => .some (n + 1)
  | .left => fun n => .some n.unpair.1
  | .right => fun n => .some n.unpair.2
  | .query => oracle
  | .pair f g => fun n => Nat.pair <$> eval oracle f n <*> eval oracle g n
  | .comp f g => fun n => eval oracle g n >>= eval oracle f
  | .prec f g => recur (eval oracle f) (eval oracle g)
  | .rfind f => search (eval oracle f)

/-- Every syntactic program belongs to Mathlib's actual relative closure. -/
theorem eval_recursiveIn (oracle : Nat →. Nat) (c : Code) :
    Nat.RecursiveIn {oracle} (eval oracle c) := by
  induction c with
  | zero => exact .zero
  | succ => exact .succ
  | left => exact .left
  | right => exact .right
  | query => exact .oracle oracle (by simp)
  | pair f g hf hg => exact .pair hf hg
  | comp f g hf hg => exact .comp hf hg
  | prec f g hf hg => exact .prec hf hg
  | rfind f hf => exact .rfind hf

/-- Coverage is of relative-recursive functions, never all native functions. -/
theorem recursiveIn_iff_exists_code {oracle f : Nat →. Nat} :
    Nat.RecursiveIn {oracle} f ↔ ∃ c, eval oracle c = f := by
  constructor
  · intro h
    induction h with
    | zero => exact ⟨.zero, rfl⟩
    | succ => exact ⟨.succ, rfl⟩
    | left => exact ⟨.left, rfl⟩
    | right => exact ⟨.right, rfl⟩
    | oracle g hg => exact ⟨.query, (Set.mem_singleton_iff.mp hg).symm⟩
    | pair _ _ hf hg =>
      obtain ⟨cf, rfl⟩ := hf
      obtain ⟨cg, rfl⟩ := hg
      exact ⟨.pair cf cg, rfl⟩
    | comp _ _ hf hg =>
      obtain ⟨cf, rfl⟩ := hf
      obtain ⟨cg, rfl⟩ := hg
      exact ⟨.comp cf cg, rfl⟩
    | prec _ _ hf hg =>
      obtain ⟨cf, rfl⟩ := hf
      obtain ⟨cg, rfl⟩ := hg
      exact ⟨.prec cf cg, rfl⟩
    | rfind _ hf =>
      obtain ⟨cf, rfl⟩ := hf
      exact ⟨.rfind cf, rfl⟩
  · rintro ⟨c, rfl⟩
    exact eval_recursiveIn oracle c

/-- Supplying an ordinary partial-recursive oracle recovers ordinary computation. -/
theorem eval_partrec {oracle : Nat →. Nat} (h : Nat.Partrec oracle) (c : Code) :
    Nat.Partrec (eval oracle c) :=
  (eval_recursiveIn oracle c).partrec_of_oracle fun g hg => by
    simpa only [Set.mem_singleton_iff.mp hg] using h

/-- An oracle implementation in another setting realizes each source denotation there. -/
theorem eval_subst {oracle target : Nat →. Nat}
    (h : Nat.RecursiveIn {target} oracle) (c : Code) :
    Nat.RecursiveIn {target} (eval oracle c) :=
  (eval_recursiveIn oracle c).subst fun g hg => by
    simpa only [Set.mem_singleton_iff.mp hg] using h

/-- Replacement requires agreement of the actual partial answers. -/
theorem eval_oracle_eq {oracle target : Nat →. Nat}
    (h : ∀ n, oracle n = target n) (c : Code) : eval oracle c = eval target c := by
  cases funext h
  rfl

/-- Search of an input-independent total test terminates exactly when it is zero. -/
theorem search_constant_dom (d : Nat → Nat) (n : Nat) :
    (search (fun p => Part.some (d p.unpair.1)) n).Dom ↔ d n = 0 := by
  simp only [search, Nat.unpair_pair]
  exact Nat.rfind_dom.trans (by simp)

end OracleComputation
