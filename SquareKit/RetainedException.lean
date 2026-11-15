import SquareKit.StateException

/-! # Local rollback with retained operation state

Experimental bounded semantics for #381. `R` belongs to the operation interpreter;
catch resets only `S`. No physical execution follows from interpreting syntax.
-/
namespace RetainedException

inductive Policy where
  | keep | undo
  deriving DecidableEq

abbrev Run (S R E A : Type) := S → R → (Except E A × S) × R

namespace Run
variable {S R E A B C : Type}
def ret (a : A) : Run S R E A := fun s r => ((.ok a, s), r)
def bind (m : Run S R E A) (k : A → Run S R E B) : Run S R E B := fun s r =>
  match m s r with
  | ((.ok a, t), u) => k a t u
  | ((.error e, t), u) => ((.error e, t), u)
def raise (e : E) : Run S R E A := fun s r => ((.error e, s), r)
def handle (p : Policy) (m : Run S R E A) (h : E → Run S R E A) : Run S R E A :=
  fun s r => match m s r with
  | ((.ok a, t), u) => ((.ok a, t), u)
  | ((.error e, t), u) => h e (match p with | .keep => t | .undo => s) u

theorem bind_assoc (m : Run S R E A) (f : A → Run S R E B)
    (g : B → Run S R E C) : bind (bind m f) g = bind m (fun a => bind (f a) g) := by
  funext s r
  rcases hm : m s r with ⟨⟨a, t⟩, u⟩
  cases a <;> simp [bind, hm]

/-- An outer scope receives the inner handler's retained state, even when that
handler raises again. Undo restarts each handler at its own scope entry cell. -/
theorem nested_failure (p : Policy) (m : Run S R E A) (h k : E → Run S R E A)
    (s t v : S) (r u w : R) (e f : E)
    (hm : m s r = ((.error e, t), u))
    (hh : h e (match p with | .keep => t | .undo => s) u = ((.error f, v), w)) :
    handle p (handle p m h) k s r =
      k f (match p with | .keep => v | .undo => s) w := by
  cases p <;> simp_all [handle]
end Run

/-- Operation response types are fixed here to keep this experiment bounded. -/
inductive Tree (S O V E A : Type) where
  | ret : A → Tree S O V E A
  | read : (S → Tree S O V E A) → Tree S O V E A
  | write : S → Tree S O V E A → Tree S O V E A
  | act : O → (V → Tree S O V E A) → Tree S O V E A
  | raise : E → Tree S O V E A

namespace Tree
variable {S O V E A B : Type}
def bind (m : Tree S O V E A) (k : A → Tree S O V E B) : Tree S O V E B :=
  match m with
  | .ret a => k a
  | .read f => .read (fun s => bind (f s) k)
  | .write s m => .write s (bind m k)
  | .act o f => .act o (fun v => bind (f v) k)
  | .raise e => .raise e
end Tree

/-- Extend the #373 operations with a retained operation, reusing its state and
exception interface and local laws. -/
structure Algebra (S O V E : Type) (M : Type → Type) extends StateException.Algebra S E M where
  act : {A : Type} → O → (V → M A) → M A

structure LocalLaws {S O V E : Type} {M : Type → Type} (a : Algebra S O V E M) : Prop
    extends StateException.LocalLaws a.toAlgebra where
  act_bind : ∀ {A B} o (f : V → M A) (k : A → M B),
    a.bind (a.act o f) k = a.act o (fun v => a.bind (f v) k)

def fold {S O V E A : Type} {M : Type → Type} (a : Algebra S O V E M) :
    Tree S O V E A → M A
  | .ret v => a.ret v
  | .read f => a.read (fun s => fold a (f s))
  | .write s m => a.write s (fold a m)
  | .act o f => a.act o (fun v => fold a (f v))
  | .raise e => a.raise e

theorem fold_bind {S O V E A B : Type} {M : Type → Type}
    (a : Algebra S O V E M) (laws : LocalLaws a) (m : Tree S O V E A)
    (k : A → Tree S O V E B) :
    fold a (m.bind k) = a.bind (fold a m) (fun v => fold a (k v)) := by
  induction m with
  | ret v => exact (laws.ret_bind v (fun v => fold a (k v))).symm
  | read f ih => simp only [Tree.bind, fold, laws.read_bind]; exact congrArg a.read (funext ih)
  | write s m ih => simp only [Tree.bind, fold, laws.write_bind, ih]
  | act o f ih => simp only [Tree.bind, fold, laws.act_bind]; exact congrArg (a.act o) (funext ih)
  | raise e => exact (laws.raise_bind _ _).symm

def algebra {S R O V E : Type} (step : O → R → V × R) : Algebra S O V E (Run S R E) where
  ret := Run.ret
  read f := fun s r => f s s r
  write t m := fun _ r => m t r
  act o f := fun s r => let (v, u) := step o r; f v s u
  raise := Run.raise
  bind := Run.bind

theorem local_laws {S R O V E : Type} (step : O → R → V × R) :
    LocalLaws (algebra (S := S) (E := E) step) :=
  ⟨⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩,
    fun _ _ _ => rfl⟩

inductive Scoped (S O V E A : Type) where
  | body : Tree S O V E A → Scoped S O V E A
  | handle : Scoped S O V E A → (E → Scoped S O V E A) → Scoped S O V E A

def scopedFold {S R O V E A : Type} (step : O → R → V × R) (p : Policy) :
    Scoped S O V E A → Run S R E A
  | .body m => fold (algebra step) m
  | .handle m h => Run.handle p (scopedFold step p m) (fun e => scopedFold step p (h e))

/-- Composition of scopes needs equality of their meanings, not a new global law. -/
theorem scoped_congr {S R O V E A : Type} (step : O → R → V × R) (p : Policy)
    (m n : Scoped S O V E A) (h k : E → Scoped S O V E A)
    (hm : scopedFold step p m = scopedFold step p n)
    (hh : ∀ e, scopedFold step p (h e) = scopedFold step p (k e)) :
    scopedFold step p (.handle m h) = scopedFold step p (.handle n k) := by
  simp only [scopedFold, hm, funext hh]
/-- Local operation preservation lifts to arbitrary bodies and nested scopes. -/
theorem fold_retained {S R O V E A : Type} (step : O → R → V × R)
    (rel : R → R → Prop) (refl : ∀ r, rel r r)
    (trans : ∀ {r u v}, rel r u → rel u v → rel r v)
    (step_preserves : ∀ o r, rel r (step o r).2) (m : Tree S O V E A) (s : S) (r : R) :
    rel r (fold (algebra step) m s r).2 := by
  induction m generalizing s r with
  | ret a => exact refl r
  | read f ih => exact ih s s r
  | write t m ih => exact ih t r
  | raise e => exact refl r
  | act o f ih => exact trans (step_preserves o r) (ih (step o r).1 s (step o r).2)

theorem scoped_retained {S R O V E A : Type} (step : O → R → V × R)
    (rel : R → R → Prop) (refl : ∀ r, rel r r)
    (trans : ∀ {r u v}, rel r u → rel u v → rel r v)
    (step_preserves : ∀ o r, rel r (step o r).2) (m : Scoped S O V E A) (p : Policy)
    (s : S) (r : R) : rel r (scopedFold step p m s r).2 := by
  induction m generalizing s r with
  | body m => exact fold_retained step rel refl trans step_preserves m s r
  | handle m h ih ihh =>
    have hm := ih s r
    rcases heq : scopedFold step p m s r with ⟨⟨a, t⟩, u⟩
    simp only [heq] at hm
    cases a with
    | ok a => simpa [scopedFold, Run.handle, heq] using hm
    | error e =>
      cases p with
      | keep => simpa [scopedFold, Run.handle, heq] using trans hm (ihh e t u)
      | undo => simpa [scopedFold, Run.handle, heq] using trans hm (ihh e s u)
end RetainedException
