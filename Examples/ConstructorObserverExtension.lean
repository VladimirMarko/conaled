import Examples.IndexedCompositional
import SquareKit.ObservationComposition

/-! Extend the native finite-vector client with scalar shift and sum observation.
Local laws cover all four old/new constructor/observer combinations. -/
namespace Examples.ConstructorObserverExtension
open SquareKit.IndexedCompositional
open SquareKit.ObservationExtension
open IndexedCompositionalExamples.Vectors (Vec)

inductive Op : Nat → Type
  | old {n} : IndexedCompositionalExamples.Vectors.Op n → Op n
  | shift (n amount : Nat) : Op (n+1)

abbrev signature : Signature Nat where
  Op := Op
  arity | .old op => IndexedCompositionalExamples.Vectors.signature.arity op | .shift _ _ => 1
  child | .old op, k => IndexedCompositionalExamples.Vectors.signature.child op k
        | .shift n _, _ => n+1

abbrev behavior : Behavior Nat where
  Output n := IndexedCompositionalExamples.Vectors.behavior.Output n × Nat
  Request := IndexedCompositionalExamples.Vectors.behavior.Request
  next := IndexedCompositionalExamples.Vectors.behavior.next

def total : {n : Nat} → Vec n → Nat
  | 0, _ => 0
  | _+1, v => v 0 + total (fun k => v k.succ)

theorem total_shift {n} (v : Vec n) (a : Nat) :
    total (fun k => v k + a) = total v + n*a := by
  induction n with
  | zero => simp [total]
  | succ n ih =>
    simp only [total, ih, Nat.succ_mul]
    omega

theorem total_double {n} (v : Vec n) : total (fun k => 2*v k) = 2*total v := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [total, ih, Nat.mul_add]

def native : behavior.Coalgebra Vec
  | 0, _ => (((),0), fun r => nomatch r)
  | _+1, v => ((v 0,total v), fun _ k => v k.succ)

def algebra : {n : Nat} → (op : signature.Op n) → (∀ k, Vec (signature.child op k)) → Vec n
  | _, .old op, xs => IndexedCompositionalExamples.Vectors.algebra op xs
  | _, .shift _ a, xs => fun k => xs 0 k + a

/-- The unchanged old syntax embeds without adding observations or hypotheses. -/
def embed {X : Nat → Type u} : {n : Nat} →
    Term IndexedCompositionalExamples.Vectors.signature X n → Term signature X n
  | _, .leaf x => .leaf x
  | _, .node op ts => .node (.old op) (fun k => embed (ts k))

theorem fold_embed {X : Nat → Type u} (f : ∀ n, X n → Vec n)
    {n} (t : Term IndexedCompositionalExamples.Vectors.signature X n) :
    Term.fold algebra f (embed t) =
      Term.fold IndexedCompositionalExamples.Vectors.algebra f t := by
  induction t with
  | leaf => rfl
  | node op ts ih => simp only [embed, Term.fold, algebra]; congr 1; funext k; exact ih k

/-- At length zero scalar shift is the identity; no extra constructor is needed. -/
def shift (amount : Nat) {n} (t : Term signature Vec n) : Term signature Vec n :=
  match n with
  | 0 => t
  | n+1 => .node (.shift n amount) (fun _ => t)

theorem fold_shift (a : Nat) {n} (t : Term signature Vec n) :
    Term.fold algebra (fun _ v => v) (shift a t) =
      fun k => Term.fold algebra (fun _ v => v) t k + a := by
  cases n with
  | zero => funext k; exact Fin.elim0 k
  | succ n => rfl

/-- Sum-cell policy for the new constructor. Other cells remain fixed. -/
def rule (shiftSum : Nat → Nat → Nat → Nat) : Rule signature behavior where
  out op xs := match op with
    | .old .nil => ((),0)
    | .old (.cons _ a) => (a,a + (xs 0).2)
    | .old (.double 0) => ((),2*(xs 0).2)
    | .old (.double (_+1)) => (2*(xs 0).1,2*(xs 0).2)
    | .shift n a => ((xs 0).1+a,shiftSum (n+1) a (xs 0).2)
  step {j} op := by
    cases op with
    | old op => cases op with
      | nil => exact fun _ r => nomatch r
      | cons n a => exact fun _ _ => .leaf (.ret 0)
      | double => cases j with
        | zero => exact fun _ r => nomatch r
        | succ n => exact fun _ _ => .node (.old (.double n)) (fun _ => .leaf (.succ 0 ()))
    | shift n a => cases n with
      | zero => exact fun _ _ => .leaf (.succ 0 ())
      | succ n => exact fun _ _ => .node (.shift n a) (fun _ => .leaf (.succ 0 ()))

/-- The new/new interaction is the one additional sum equation. -/
def ShiftSumLaw (shiftSum : Nat → Nat → Nat → Nat) : Prop :=
  ∀ n a (v : Vec (n+1)), shiftSum (n+1) a (total v) = total v + (n+1)*a

def constructorThenObserver : Rule signature behavior := rule (fun n a s => s+n*a)
def observerThenConstructor : Rule signature behavior := rule (fun n a s => n*a+s)

/-- Old constructor/old observation cells are unchanged; all new sum cells and
shift's old head cell are proved against native vectors. -/
theorem compatible (shiftSum : Nat → Nat → Nat → Nat) (h : ShiftSumLaw shiftSum) :
    (rule shiftSum).Compatible algebra native where
  output n op xs := by
    cases op with
    | old op => cases op with
      | nil => rfl
      | cons n a => cases n <;> rfl
      | double n => cases n with
        | zero => rfl
        | succ n =>
          apply Prod.ext
          · rfl
          · exact total_double (xs 0)
    | shift n a =>
      apply Prod.ext
      · rfl
      · exact (total_shift (xs 0) a).trans (h n a (xs 0)).symm
  next n op xs r := by
    cases op with
    | old op => cases op with
      | nil => exact nomatch r
      | cons n a => rfl
      | double n => cases n with
        | zero => exact nomatch r
        | succ n => rfl
    | shift n a => cases n with
      | zero => funext k; exact Fin.elim0 k
      | succ n => rfl

theorem constructorFirst_compatible : constructorThenObserver.Compatible algebra native :=
  compatible _ (fun _ _ _ => rfl)
theorem observerFirst_compatible : observerThenConstructor.Compatible algebra native :=
  compatible _ (fun _ _ _ => Nat.add_comm _ _)

/-- All mixed finite terms, not only old constructors, use the shared law. -/
theorem correct (shiftSum : Nat → Nat → Nat → Nat) (h : ShiftSumLaw shiftSum)
    {n k} (t : Term signature Vec n) (path : behavior.Path n k) :
    behavior.observe ((rule shiftSum).lift native) path t =
      behavior.observe native path (Term.fold algebra (fun _ v => v) t) :=
  (behavior.observe_morphism _ _ _
    ((rule shiftSum).fold_morphism algebra native (compatible shiftSum h) native
      (fun _ v => v) ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩) path t).symm

/-- Extension order comparison explicitly requires the local cross-cell law
on both sides, and retains the entire head/sum observation at the final index. -/
theorem order_comparison (left right : Nat → Nat → Nat → Nat)
    (hl : ShiftSumLaw left) (hr : ShiftSumLaw right)
    {n k} (t : Term signature Vec n) (path : behavior.Path n k) :
    behavior.observe ((rule left).lift native) path t =
      behavior.observe ((rule right).lift native) path t :=
  Rule.compare_observations _ _ algebra native (compatible left hl) (compatible right hr)
    native (fun _ v => v) ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩ path t

/-- The original theorem is reused with exactly its original term and coordinate. -/
theorem old_client {n} (t : Term IndexedCompositionalExamples.Vectors.signature Vec n) (k : Fin n) :
    Term.fold algebra (fun _ v => v) (embed t) k =
      IndexedCompositionalExamples.Vectors.read
        (IndexedCompositionalExamples.Vectors.rule.lift IndexedCompositionalExamples.Vectors.native) t k := by
  rw [fold_embed]
  exact (IndexedCompositionalExamples.Vectors.correct t k).symm

/-- Forget only the added sum observation, retaining every request and length. -/
def forget {X : Nat → Type u} (c : behavior.Coalgebra X) :
    IndexedCompositionalExamples.Vectors.behavior.Coalgebra X :=
  fun n x => ((c n x).1.1,(c n x).2)

theorem forget_native : forget native = IndexedCompositionalExamples.Vectors.native := by
  funext n v
  cases n <;> rfl

theorem read_correct (shiftSum : Nat → Nat → Nat → Nat) (h : ShiftSumLaw shiftSum)
    {n} (t : Term signature Vec n) (k : Fin n) :
    IndexedCompositionalExamples.Vectors.read (forget ((rule shiftSum).lift native)) t k =
      Term.fold algebra (fun _ v => v) t k := by
  have hm := (rule shiftSum).fold_morphism algebra native (compatible shiftSum h)
    native (fun _ v => v) ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  have hf : IndexedCompositionalExamples.Vectors.behavior.Morphism
      (forget ((rule shiftSum).lift native)) (forget native)
      (fun _ => Term.fold algebra (fun _ v => v)) :=
    ⟨fun n x => congrArg Prod.fst (hm.output n x), hm.next⟩
  rw [forget_native] at hf
  exact (IndexedCompositionalExamples.Vectors.read_morphism _ _ _ hf t k).symm.trans
    (IndexedCompositionalExamples.Vectors.read_native _ _)

/-- All original coordinates survive the embedding and observation extension.
The caller has exactly the original theorem's term and coordinate premises. -/
theorem embedded_client {n}
    (t : Term IndexedCompositionalExamples.Vectors.signature Vec n) (k : Fin n) :
    IndexedCompositionalExamples.Vectors.read (forget (constructorThenObserver.lift native)) (embed t) k =
      IndexedCompositionalExamples.Vectors.read
        (IndexedCompositionalExamples.Vectors.rule.lift IndexedCompositionalExamples.Vectors.native) t k :=
  (read_correct _ (fun _ _ _ => rfl) (embed t) k).trans (old_client t k)

abbrev meaning {n} (t : Term signature Vec n) : Vec n := Term.fold algebra (fun _ v => v) t

def old (n : Nat) : Setoid (Term signature Vec n) :=
  agreement (fun k t => meaning t k) Set.univ

def sumObservation {n} (t : Term signature Vec n) : Nat :=
  (constructorThenObserver.output native t).2

theorem sum_square {n} (t : Term signature Vec n) : sumObservation t = total (meaning t) := by
  have h := congrArg Prod.snd (correct (fun n a s => s+n*a) (fun _ _ _ => rfl) t .stop)
  change sumObservation t = (native n (meaning t)).1.2 at h
  cases n <;> exact h

theorem sum_compatible (n : Nat) : Compatible (old n) sumObservation :=
  compatible_of_factor (old n) meaning (fun {_ _} h => funext (fun k => h k (Set.mem_univ k)))
    sumObservation total sum_square

/-- The admitted observer does not refine the original coordinate equality. -/
theorem enriched_iff {n} (t u : Term signature Vec n) :
    (extend (old n) sumObservation).r t u ↔ (old n).r t u :=
  extend_iff (old n) sumObservation (sum_compatible n) t u

example {n} (t : Term signature Vec n) :
    descend (old n) sumObservation (sum_compatible n) (Quotient.mk (old n) t) =
      total (meaning t) :=
  (descend_mk _ _ _ _).trans (sum_square t)

/-- No choice of the new/new cell changes any old-constructor output cell. -/
theorem old_cells (left right : Nat → Nat → Nat → Nat)
    {n} (op : IndexedCompositionalExamples.Vectors.Op n)
    (xs : ∀ k, behavior.Output (signature.child (.old op) k)) :
    (rule left).out (.old op) xs = (rule right).out (.old op) xs := by
  cases op with
  | nil => rfl
  | cons => rfl
  | double n => cases n <;> rfl

theorem old_head_cells (policy : Nat → Nat → Nat → Nat)
    {n} (op : IndexedCompositionalExamples.Vectors.Op n)
    (xs : ∀ k, behavior.Output (signature.child (.old op) k)) :
    ((rule policy).out (.old op) xs).1 =
      IndexedCompositionalExamples.Vectors.rule.out op (fun k => (xs k).1) := by
  cases op with
  | nil => rfl
  | cons => rfl
  | double n => cases n <;> rfl

/-- A proposed interaction forgets the contribution of scalar shift. -/
def incompatibleRule : Rule signature behavior := rule (fun _ _ s => s)

theorem failed_sum_law : ¬ ShiftSumLaw (fun _ _ s => s) := by
  intro h
  have bad := h 0 1 (fun _ => 0)
  change (0 : Nat) = 1 at bad
  cases bad

theorem incompatible : ¬ incompatibleRule.Compatible algebra native := by
  intro h
  have bad := congrArg Prod.snd (h.output 1 (.shift 0 1) (fun _ _ => 0))
  change (1 : Nat) = 0 at bad
  cases bad

/-- Presentation size is a different proposed observer, outside the native
coordinate contract. It counts constructors rather than coordinates. -/
def constructors {n} : Term signature Vec n → Nat
  | .leaf _ => 0
  | .node op ts => match op with
    | .old .nil => 1
    | .old (.cons _ _) => 1 + constructors (ts 0)
    | .old (.double _) => 1 + constructors (ts 0)
    | .shift _ _ => 1 + constructors (ts 0)

def plain : Term signature Vec 1 := .leaf (fun _ => 7)
def shiftedZero : Term signature Vec 1 := .node (.shift 0 0) (fun _ => plain)

theorem same_old : (old 1).r plain shiftedZero := fun _ _ => rfl

theorem constructors_different : constructors plain ≠ constructors shiftedZero := by decide

theorem constructors_incompatible : ¬ Compatible (old 1) constructors :=
  fun h => constructors_different (h same_old)

theorem constructors_no_factor :
    ¬ ∃ f : Quotient (old 1) → Nat, ∀ t, f (Quotient.mk (old 1) t) = constructors t :=
  no_factor (old 1) constructors same_old constructors_different

/-- Shift, doubling and insertion occur in the same finite term. -/
def mixed : Term signature Vec 2 := .node (.old (.double 2)) (fun _ =>
  .node (.shift 1 3) (fun _ => embed (IndexedCompositionalExamples.Vectors.cons 7
    (IndexedCompositionalExamples.Vectors.cons 11 IndexedCompositionalExamples.Vectors.nil))))

example : behavior.observe (constructorThenObserver.lift native) .stop mixed = (20,48) := by
  rw [constructorThenObserver, correct _ (fun _ _ _ => rfl)]
  rfl

example : behavior.observe (observerThenConstructor.lift native) (.step () .stop) mixed = (28,28) := by
  rw [observerThenConstructor, correct _ (fun _ _ _ => Nat.add_comm _ _)]
  rfl

/-- Preserving the old cells does not repair the omitted cross interaction. -/
example : behavior.observe (incompatibleRule.lift native) .stop mixed = (20,36) := rfl

example {n k} (t : Term signature Vec n) (path : behavior.Path n k) :
    behavior.observe (constructorThenObserver.lift native) path t =
      behavior.observe (observerThenConstructor.lift native) path t :=
  order_comparison _ _ (fun _ _ _ => rfl) (fun _ _ _ => Nat.add_comm _ _) t path

example : (extend (old 1) sumObservation).r plain shiftedZero :=
  (enriched_iff plain shiftedZero).mpr same_old

end Examples.ConstructorObserverExtension
